import Rel.Kernel.Coc
import Rel.Kernel.Value
import Rel.Kernel.Elementwise

/-! The part of `Rel.Kernel.Reduce` the Rel kernels reach; `Rel.Kernel.Reduce` imports it. -/


namespace Rel.Kernel

/-- The `i`th `Int64`, little-endian. Reads past the end answer `0`: the specification is only
called under `wellFormed`, where the length is a multiple of the width, and the bounds check
belongs to the caller. -/
def atI64 (b : ByteArray) (i : Nat) : Int64 :=
  let o := i * 8
  (b.get! o).toUInt64 |||
  ((b.get! (o+1)).toUInt64 <<< 8) ||| ((b.get! (o+2)).toUInt64 <<< 16) |||
  ((b.get! (o+3)).toUInt64 <<< 24) ||| ((b.get! (o+4)).toUInt64 <<< 32) |||
  ((b.get! (o+5)).toUInt64 <<< 40) ||| ((b.get! (o+6)).toUInt64 <<< 48) |||
  ((b.get! (o+7)).toUInt64 <<< 56)
  |>.toInt64

/-- What the fold answers when nothing survives, at the class the payload is read as. For a signed
type this is `Over.seed`: its null is its minimum, so `~~~nul` is the type's maximum and `nul + 1`
the least element that is not the null. The two unsigned classes have no null and every value from
`0` to `255` is an element, so their extremes are those — measured, `min 0#0x00` is `0xff`,
`max 0#0x00` is `0x00`, and the same at `char`. Every other verb seeds with a constant that no null
enters, which is why they come straight from `Over.seed`. -/
def Coc.Over.denseSeed (op : Coc.Over) (cls : UInt8) (nul : Int64) : Int64 :=
  if cls != Ew.u8 || (op != .lesser && op != .greater) then op.seed nul
  else if op == .lesser then 255 else 0

/-- q's `f/` over a dense payload, at one of the four integral classes. `Coc.over` is this same fold
over the encoded form — the same `Over.seed`, `Over.step` and `Over.boolCast` — and the two differ
only in where an element comes from, which is what `~/q/q.k` line 7's one `/aggr` family asks for.

Reading an element is `Ew.signed`'s rule and not a second one, so `byte` and `char` zero-extend and
everything else sign-extends, which is exactly what makes `min "a b"` the blank. -/
@[extern "qlean_over_bytes"]
def overBytes (op : Coc.Over) (cls : UInt8) (nul : Int64) (b : @& ByteArray) : Int64 :=
  (List.range (b.size / Ew.width cls)).foldl (init := op.denseSeed cls nul) fun acc i =>
    let x := Ew.signed cls (Ew.elem cls b i)
    if !op.boolCast && x == nul then acc else op.step acc x

/-- q's `f/` over every group of a dense payload at once, as `2 * ng` little-endian `Int64` slots:
each group's fold, then how many elements it stepped on — `~/q/q.k` line 11's `+\~^x`, which is what
`avg` divides by.

`Over.denseSeed`, `Over.step` and `Over.boolCast` are `overBytes`' own three and `gid` chooses the
accumulator, so a group's answer *is* `overBytes` over that group's elements.

An id at or past `ng` names no group and is dropped. Nothing `Kernel.Order.groupIds` answers is one;
the kernel is what has to hold when the payload did not come from there.

Only the first `n` rows are read, `n` being how many the ids cover: at width `0` the ids store nothing
and at 1, 2 and 4 the last byte's padding reads as id `0`, so without it rows past the key fall in group 0. -/
@[extern "qlean_over_groups"]
def overGroups (op : Coc.Over) (cls : UInt8) (nul : Int64) (ng w n : USize) (gid : @& ByteArray)
    (b : @& ByteArray) : ByteArray :=
  let (fold, live) := (List.range (Column.idsCap gid w.toNat (min n.toNat (b.size / Ew.width cls)))).foldl
      (init := (Array.replicate ng.toNat (op.denseSeed cls nul),
        Array.replicate ng.toNat (0 : Int64)))
      fun (fold, live) i =>
        let g := Column.idAt gid w.toNat i
        let x := Ew.signed cls (Ew.elem cls b i)
        if g ≥ ng.toNat || (!op.boolCast && x == nul) then (fold, live)
        else (fold.set! g (op.step fold[g]! x), live.set! g (live[g]! + 1))
  (fold ++ live).foldl (init := ByteArray.empty) fun acc v => Column.pushBits acc v.toUInt64 8

/-- Segment `r`'s rows `[lo, hi)` among `n`: the offsets clamped into `[0, n]`, and empty where they
descend, so every offsets payload names some rows and the kernel never reads past the payload. -/
def segRange (offs : ByteArray) (n r : Nat) : Nat × Nat :=
  let cut (k : Nat) := min (atI64 offs k).toNatClampNeg n
  (cut r, max (cut r) (cut (r + 1)))

/-- `n` bits from `f`, packed LSB first with the tail of the last byte left zero. `Column.packBits`
records why the tail matters: trailing set bits make two equal boolean vectors compare unequal under
`~`. One definition for the bit-payload kernels (`bitRowsOver` here, four in `Structural`), which differ only in `f`. -/
def packOf (n : Nat) (f : Nat → Bool) : ByteArray :=
  (List.range ((n + 7) / 8)).foldl (init := ByteArray.empty) fun acc k =>
    acc.push ((List.range 8).foldl (init := (0 : UInt8)) fun byte t =>
      if k * 8 + t < n && f (k * 8 + t) then byte ||| (1 <<< t.toUInt8) else byte)

/-- Row `g` of the answer, `w` bits, folds the rows `idx[k]` of the bit matrix `m` (row `i` at bits
`[i·w, (i+1)·w)`) over `k` in segment `g` of `offs` (`segRange`, clamped into `idx`'s longs): by `∨`
(`all = false`) or `∧` (`all = true`), an empty segment answering zeros or ones. k's `|/'` and `&/'`
on bit rows; a composition is its `∨` instance, a left division its `∧`. A negative row reads row `0`
and a row past `m` reads zeros (`Column.bitAt`), as the C does. -/
@[extern "qlean_bit_rows_over"]
def bitRowsOver (all : Bool) (w : USize) (offs idx m : @& ByteArray) : ByteArray :=
  let w := w.toNat
  packOf ((offs.size / 8 - 1) * w) fun i =>
    let (lo, hi) := segRange offs (idx.size / 8) (i / w)
    let bit (k : Nat) := Column.bitAt m ((atI64 idx k).toNatClampNeg * w + i % w)
    if all then (List.range' lo (hi - lo)).all bit else (List.range' lo (hi - lo)).any bit

/-- How `groupCells` reads a group's cell off its fold `s` and live count `k`. -/
inductive GroupCell where
  /-- `s`'s low `w` bytes: an integral fold, wrapped or not narrowed at all -/
  | wrap
  /-- `s`, or the `int` null where it leaves the `int` range: `Coc.narrowed`'s `prd` -/
  | clamp
  /-- `s / k` as a float, `0n` at `k = 0`: an integral `avg` -/
  | avgInt
  /-- `s` as float bits, rounded to `real` at `w = 4` -/
  | float
  /-- `s / k`, `s` float bits, `0n` at `k = 0` or a NaN quotient: a float `avg` -/
  | avgFloat
  deriving BEq

/-- One grouped aggregate's answer column, the groups in `order` (a `long` payload of group ids):
each cell read off `overGroups`' or `overGroupsFloat`'s `2 * ng` slots by `kind`, written at `w`
bytes. Every grouped aggregate's answer is built here, in one pass — one `pushBits` per group in the
evaluator was 30% of `select sum x by g` at 100k groups. An id at or past `ng` reads `0` slots. -/
@[extern "qlean_group_cells"]
def groupCells (kind : GroupCell) (w ng : USize) (m order : @& ByteArray) : ByteArray :=
  (List.range (order.size / 8)).foldl (init := ByteArray.empty) fun acc i =>
    let g := (atI64 order i).toNatClampNeg
    let (s, k) := if g < ng.toNat then (atI64 m g, atI64 m (ng.toNat + g)) else (0, 0)
    match kind with
    | .wrap => Column.pushBits acc s.toUInt64 w.toNat
    | .clamp => Column.pushBits acc
        (if -2147483648 < s && s < 2147483648 then s else -2147483648).toUInt64 w.toNat
    | .avgInt => Column.pushBits acc (if k == 0 then nanBits else (s.toFloat / k.toFloat).toBits) 8
    | .float => if w == 4 then Column.pushBits acc (Float.ofBits s.toUInt64).toFloat32.toBits.toUInt64 4
        else Column.pushBits acc s.toUInt64 8
    | .avgFloat => Column.pushBits acc (let r := (Float.ofBits s.toUInt64 / k.toFloat).toBits
        if k == 0 || Bits.f64IsNaN r then nanBits else r) 8


end Rel.Kernel


namespace Rel.Kernel

/-- The null of an encoded type as the fold has to skip it, and `none` at a type the encoding is not
for. The encoded form holds a narrow column's elements sign-extended, so a `short` null is `-32768`
there and not `Int64.minValue`; the block structure is unchanged, the null still being the smallest
value the type has. -/
def Coc.nullOf : QAtomicType → Option Int64
  | .short => some (-32768)
  | .int | .month | .date | .minute | .second | .time => some (-2147483648)
  | .long | .timestamp | .timespan => some Int64.minValue
  | _ => none

/-- The fold on the encoded form, before the narrowing `sum` and `prd` put on top of it. It is
separate because `avg` divides *this* one and not the narrowed one: measured, `avg 1000000#3000i` is
`3000f` where `sum` of the same is `0Ni`. -/
def overFoR (op : Coc.Over) (t : QAtomicType) (n : USize) (e : Ext.Enc X) : Option Int64 :=
  match e with
  | .foR metadata pack => (Coc.nullOf t).map (Coc.over op · metadata pack n)
  | _ => none


end Rel.Kernel
