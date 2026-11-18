import Rel.Kernel.Coc
import Rel.Kernel.Op

/-! The part of `Rel.Kernel.Scan` the Rel kernels reach; `Rel.Kernel.Scan` imports it. -/


namespace Rel.Kernel.Scan


/-- The five verbs of `q.k` line 11, in the order `rust/src/scan.rs`'s `SC_*` names them. A Lean
enumeration reaches C as a `uint8_t` in constructor order, so this declaration *is* that enum. -/
inductive Verb | sums | prds | mins | maxs | fills
  deriving DecidableEq, Repr, Inhabited

/-- The element layouts a scan reads, in the order `rust/src/scan.rs`'s `SK_*` names them. A layout, not a
q type: `int`, `date` and `minute` are one entry here because they are one loop, and what tells them
apart — which of them q answers a given scan at — is the caller's business and never this file's.

A layout is a **width and a null test**, which is why `c8` stands beside `u8` rather than being the
same entry: both read one unsigned byte, and `char`'s null is the blank where `byte` has none. -/
inductive Kind | bit | u8 | i16 | i32 | i64 | f32 | f64 | c8
  deriving DecidableEq, Repr, Inhabited

namespace Kind

/-- Bytes one element occupies in a dense payload. `bit` answers 1 rather than nothing: that is the
width the three element-typed verbs would *write* at, and `scanColumn` declines them there rather
than letting this stand in for a `Column.bits` result. `avail` below does not read it. -/
def width : Kind → Nat
  | .bit | .u8 | .c8 => 1
  | .i16 => 2
  | .i32 | .f32 => 4
  | .i64 | .f64 => 8

/-- Elements the payload actually holds, which every kernel here clamps its `n` to. `rust/src/scan.rs`
clamps by the same formula, so the two never part company; the point of it is that reading past the
array is the one failure worse than a wrong answer. A boolean payload is why `n` is passed at all —
three bytes hold between 17 and 24 booleans, so the size does not determine it. -/
def avail (k : Kind) (b : ByteArray) : Nat :=
  match k with
  | .bit => b.size * 8
  | k => b.size / k.width

/-- The raw bits of element `i`: one bit for a boolean, LSB first within its byte, which is what
`Column.bits` stores; `k.width` little-endian bytes for everything else. -/
def bitsAt (k : Kind) (b : ByteArray) (i : Nat) : UInt64 :=
  match k with
  | .bit => if Column.bitAt b i then 1 else 0
  | k => Column.bitsAt b (i * k.width) k.width

/-- q's `0N` at this layout: the minimum of each signed integral width, any NaN at the two float
widths, and the **blank** at `char`. `byte` and `boolean` have no null, and a test that is constantly
false is what says so.

`char`'s null is measured and is the whole reason `c8` exists: `fills "a b"` is `"aab"`,
`mins " \001"` is `"\377\001"` — the seed left standing where the blank was skipped — and
`mcount` over `"a b"` at any window is `1 1 1i`. -/
def isNull : Kind → UInt64 → Bool
  | .bit, _ | .u8, _ => false
  | .c8, u => u == 32
  | .i16, u => u.toUInt16.toInt16 == Int16.minValue
  | .i32, u => u.toUInt32.toInt32 == Int32.minValue
  | .i64, u => u.toInt64 == Int64.minValue
  | .f32, u => Bits.f32IsNaN u.toUInt32
  | .f64, u => Bits.f64IsNaN u

/-- These bits as a signed integer of this layout's width: `byte` zero-extended, q's byte being
unsigned, and a boolean read as its one bit. At `f32` and `f64` it is the bit pattern read as a
signed integer, which is what those bits are — nothing calls it there, the float kinds having their
own accumulator, and it is total rather than a `panic!` because a specification has to reduce. -/
def signed : Kind → UInt64 → Int64
  | .bit, u | .u8, u | .c8, u => u.toInt64
  | .i16, u => u.toUInt16.toInt16.toInt64
  | .i32, u => u.toUInt32.toInt32.toInt64
  | .i64, u | .f32, u | .f64, u => u.toInt64

/-- These bits as the `Float` q's `avg` adds in: the integral widths widened, the float widths
decoded. `QLean/Eval/Mon.lean`'s `wideFloat` is the same function over a boxed atom. -/
def toFloat (k : Kind) (u : UInt64) : Float :=
  match k with
  | .f32 => (Float32.ofBits u.toUInt32).toFloat
  | .f64 => Float.ofBits u
  | k => (k.signed u).toFloat

end Kind

/-- The layout q answers a scan at. `sums` and `prds` widen everything below `int` to `int`, which
is the accumulator type of the matching aggregate; the other three stay at the element's own layout.
`rust/src/scan.rs`'s `sc_out_width` is this function composed with `Kind.width`. -/
def outKind : Verb → Kind → Kind
  | .sums, k | .prds, k => match k with
    | .bit | .u8 | .i16 => .i32
    -- `c8` is not among them: q's `sums "ab"` and `prds "ab"` are `'type`, so no caller ever asks
    -- for a `char` scan at another layout and the identity here is what declines them
    | k => k
  | _, k => k

/-- One element of a scan: fold the step in where the element is not q's null — which is where every
verb's null rule lives, and the only place it lives — then write the accumulator out at `w`
little-endian bytes. Named rather than left inline in `scanOf` so that the size of the answer can be
proved by induction over the very function the definition folds. -/
def scanStep (w : Nat) (rd : Nat → UInt64) (isNull : UInt64 → Bool) (step : α → UInt64 → α)
    (emit : α → UInt64) (p : ByteArray × α) (i : Nat) : ByteArray × α :=
  let x := rd i
  let acc := if isNull x then p.2 else step p.2 x
  (Column.pushBits p.1 (emit acc) w, acc)

/-- The one scan, and the only fold in this file: `scanStep` across the `n` elements from the verb's
seed. Every verb below is this function at a different seed and step, which is what `q.k` line 11
says by spelling the five as one adverb over five dyads. -/
def scanOf (n w : Nat) (rd : Nat → UInt64) (isNull : UInt64 → Bool)
    (seed : α) (step : α → UInt64 → α) (emit : α → UInt64) : ByteArray :=
  ((List.range n).foldl (scanStep w rd isNull step emit) (ByteArray.empty, seed)).1

/-- What `sums` writes: the 64-bit running total narrowed to the accumulator type, and that type's
`0N` where it does not fit. Measured — `sums 4#1000000000i` is `1000000000 2000000000 0N 0Ni`, and
the total behind it keeps its full width, so this narrows the *answer* and never the accumulator.

`w` is `(outKind .sums k).width`, which is 4 or 8 and nothing else. At 8 the test cannot fail, so
the branch is the identity there rather than a case that had to be excluded. -/
def narrow (w : Nat) (x : Int64) : UInt64 :=
  if w = 4 then (if x == x.toInt32.toInt64 then x.toUInt64 else Int32.minValue.toInt64.toUInt64)
  else x.toUInt64

/-- The five verbs at an integral layout. The accumulator is `Int64` for all of them — q's own, at
`long`, and wide enough at every narrower width for `narrow` to answer what q answers — and the
seeds `hi`, `lo` and `nl` are the layout's `0W`, `-0W` and `0N`. -/
def intScan (v : Verb) (k : Kind) (b : ByteArray) (n w : Nat) (hi lo nl : Int64) : ByteArray :=
  let rd := k.bitsAt b
  let val := k.signed
  match v with
  | .sums => scanOf n w rd k.isNull 0 (fun a x => a + val x) (narrow w)
  | .prds => scanOf n w rd k.isNull 1 (fun a x => a * val x) Int64.toUInt64
  | .mins => scanOf n w rd k.isNull hi (fun a x => let y := val x; if y < a then y else a)
      Int64.toUInt64
  | .maxs => scanOf n w rd k.isNull lo (fun a x => let y := val x; if a < y then y else a)
      Int64.toUInt64
  | .fills => scanOf n w rd k.isNull nl (fun _ x => val x) Int64.toUInt64

/-- The same five at a float layout, with `Float` as the accumulator for both widths and a rounding
step for `real`: q accumulates a `real` scan at 32 bits, and rounding the 64-bit result of each step
back to 32 is that same accumulator — the exact sum or product of two `real`s is a `Float` and the
rounding is therefore single. `QLean/Eval/Mon.lean`'s `roundAcc` is the same argument.

A NaN reaching `emit` is written as q's own `0n` rather than as whatever pattern the arithmetic left
behind, so the answer does not depend on that: `sums 0w -0w` is `0w 0n`, so it is reachable. -/
def fltScan (v : Verb) (k : Kind) (b : ByteArray) (n w : Nat) : ByteArray :=
  let rd := k.bitsAt b
  let val := k.toFloat
  let round : Float → Float := match k with
    | .f32 => fun x => (Float.toFloat32 x).toFloat
    | _ => id
  let emit : Float → UInt64 := match k with
    | .f32 => fun x => let u := (Float.toFloat32 x).toBits
                       (if Bits.f32IsNaN u then Rel.nanBits32 else u).toUInt64
    | _ => fun x => let u := x.toBits; if Bits.f64IsNaN u then Rel.nanBits else u
  match v with
  | .sums => scanOf n w rd k.isNull 0.0 (fun a x => round (a + val x)) emit
  | .prds => scanOf n w rd k.isNull 1.0 (fun a x => round (a * val x)) emit
  | .mins => scanOf n w rd k.isNull (Float.ofBits 0x7ff0000000000000)
      (fun a x => let y := val x; if y < a then y else a) emit
  | .maxs => scanOf n w rd k.isNull (Float.ofBits 0xfff0000000000000)
      (fun a x => let y := val x; if a < y then y else a) emit
  | .fills => scanOf n w rd k.isNull (Float.ofBits Rel.nanBits) (fun _ x => val x) emit

/-- q's `sums prds mins maxs fills` over a dense payload of `n` elements at layout `k`: `n` elements
of `(outKind v k).width` bytes each, the `i`th being the accumulator after element `i` of the fold
`scanOf` states. The seeds are the layout's, and they are what q answers when the skip leaves
nothing — `mins 0N 0N` is `0W`, `maxs 0N 0N` is `-0W`, and `-0W` is the minimum plus one, never the
minimum itself, which is the null.

At `bit` the three element-typed verbs write one byte per element, which is not what a boolean
column holds; `scanBits` below is that same fold packed a bit an element, and this entry is what it
is stated in terms of.

A `fills` whose payload holds no null is the identity, and the C answers the argument's own
`ByteArray` there rather than a copy of it — the same bytes this fold states, so the same spec, and
512 MB not written at 64M elements. `rust/src/scan.rs`'s `scan_any_null` carries q's measurements. -/
@[extern "qlean_scan"]
def scan (v : Verb) (k : Kind) (n : USize) (b : @& ByteArray) : ByteArray :=
  let m := min n.toNat (k.avail b)
  let w := (outKind v k).width
  match k with
  | .bit => intScan v .bit b m w 1 0 0
  | .u8 => intScan v .u8 b m w 255 0 0
  -- the same byte and the same two extreme seeds as `u8`; the third is `fills`'s, and at `char`
  -- alone it is reachable, the blank being the null: `fills " ab"` is `" ab"`, not `"aab"`
  | .c8 => intScan v .c8 b m w 255 0 32
  | .i16 => intScan v .i16 b m w Int16.maxValue.toInt64 (-Int16.maxValue.toInt64)
      Int16.minValue.toInt64
  | .i32 => intScan v .i32 b m w Int32.maxValue.toInt64 (-Int32.maxValue.toInt64)
      Int32.minValue.toInt64
  | .i64 => intScan v .i64 b m w Int64.maxValue (-Int64.maxValue) Int64.minValue
  | .f32 => fltScan v .f32 b m w
  | .f64 => fltScan v .f64 b m w

end Rel.Kernel.Scan

namespace Rel.Kernel

open Rel.Kernel.Scan

/-- `e`'s `n` raw words at `t`, or how many it holds instead: `Enc.raw` answers none at a type the form does not hold
(a `syms` or `gen` column, a `bits` one read at a non-boolean type), and `kscan` reads every column at all `n` rows. -/
def rawAll (t : QAtomicType) (n : USize) (e : Enc) : Except String (Array UInt64) :=
  if (e.raw t n).size = n.toNat then .ok (e.raw t n)
  else .error s!"kscan: a column holds {(e.raw t n).size} raw elements, not {n.toNat}"

/-- Row `i` of `kscan` after the rows before it, `out`: the carry is the previous row's answer, or the seed's row `i`
where `seg` starts a segment (and at row 0); `op` then folds every other column's row `i` into it, left to right. -/
def kscanRow (op : Op) (seg seed : Array UInt64) (xs : List (Array UInt64)) (out : Array UInt64) (i : Nat) :
    Except String (Array UInt64) :=
  -- every array holds `n` words (`rawAll`) and `i < n`, so no `getD` here answers its default
  out.push <$> xs.foldlM (fun a x => op.eval a (x[i]?.getD 0))
    (if 0 < i ∧ seg[i]?.getD 0 = 0 then out[i - 1]?.getD 0 else seed[i]?.getD 0)

/-- **The scan primitive** (design §4, `raw_kscan`): the segmented prefix fold of `op` over the `n` rows of `es`, read
at `s`. `seg`, read as booleans, marks the rows that start a segment; the first column of `es` is the seed a segment
starts from and the others are folded into each row. So a map is every row a segment (`out[i] = op(a[i], b[i])`), a
scan one segment from a seed column, a fold a scan's last row, and `es = [e]` fills `e` forward from the marked rows.
The answer is `foR` at `t`, the words encoded whole by `Coc.encode` at 8 bytes and read back by `Enc.raw` cut to `t`'s
width; a boolean `t` answers `bits`, each word's low bit, because `Enc.WF` admits `foR` at no boolean. An `Op.eval`
error, a column short of `n` raw words, an empty `es` or a `t` of no width is the `.error`, never a default. Temporary
name until 6.11: `Kernel.scan` (`Driver.lean`) and `qlean_scan` exist. -/
@[extern "qlean_k_scan"]
def kscan (op : Op) (s t : QAtomicType) (n : USize) (seg : @& Enc) (es : @& List Enc) : Except String Enc := do
  let g ← rawAll .boolean n seg
  match ← es.mapM (rawAll s n) with
  | [] => .error "kscan: es is empty; its first column is the seed"
  | seed :: xs =>
    let out ← (List.range n.toNat).foldlM (kscanRow op g seed xs) #[]
    match t.width with
    | none => .error "kscan: the answer type has no fixed width"
    | some _ =>
      if t = .boolean then pure (.bits (Column.packIds 1 n.toNat fun i => (out[i]?.getD 0).toNat % 2))
      else
        -- `ofNat32`, not the literal `8`, whose `toNat` is `8 % 2 ^ numBits` and stops `decide` at the opaque `numBits`
        let r := Coc.encode (USize.ofNat32 8 (by decide)) (out.foldl (init := .empty) fun acc w => Column.pushBits acc w 8)
        pure (.foR r.1 r.2)

end Rel.Kernel


namespace Rel.Kernel.Scan

namespace Kind

end Kind

private theorem foldSize (w : Nat) (rd : Nat → UInt64) (isNull : UInt64 → Bool)
    (step : α → UInt64 → α) (emit : α → UInt64) (l : List Nat) (p : ByteArray × α) :
    (l.foldl (scanStep w rd isNull step emit) p).1.size = p.1.size + l.length * w := by
  induction l generalizing p with
  | nil => simp
  | cons i l ih => simp [ih, scanStep, Rel.Column.pushBits_size, Nat.succ_mul]; omega

/-- A scan answers exactly one element per element, which is what `Column.count` of the answer is
read off. The dispatch below needs it to be the count of its *argument*, and that step is the
caller's: `QLean/Kernel/Coc.lean` owns how many elements a `.foR` payload decodes to. -/
theorem scanOf_size (n w : Nat) (rd : Nat → UInt64) (isNull : UInt64 → Bool)
    (seed : α) (step : α → UInt64 → α) (emit : α → UInt64) :
    (scanOf n w rd isNull seed step emit).size = n * w := by
  simp [scanOf, foldSize]

end Rel.Kernel.Scan

namespace Rel.Kernel

open Rel.Kernel.Scan

end Rel.Kernel
