import Rel.Kernel.Coc
import Rel.Kernel.Value

/-! The part of `Rel.Kernel.Search` the Rel kernels reach; `Rel.Kernel.Search` imports it. -/


open Rel.Ext
namespace Rel.Kernel

/-- The key an equality compares, with the values q holds equal folded together: the two zeros onto
one, and **every NaN onto one**. At a width whose equality is bit equality this is the identity.

Measured against q 4.1 with a second NaN built as `abs 0n`, whose bits are `0x7ff8…` against `0n`'s
`0xfff8…`: `(abs 0n)~0n` is `1b`, `0n=abs 0n` is `1b`, `(0n,1.0)?abs 0n` is `0`, `(abs 0n) in 0n,1.0`
is `1b`, and `count distinct (0n;1.0;-1.0;abs 0n)` is `3`. The same at `real` with `abs 0Ne`.

`(0n;-0n)` proves none of that and is not evidence for anything: `type -0n` is `-16h`, a *timespan*,
so that pair is a general list of a float and a timespan and nothing about NaN payloads follows from
it. An earlier version of this rule rested on exactly that reading and folded only the zeros.

Masking the sign off leaves `abs`, and IEEE puts every NaN above `+inf` and nothing else there, so
one comparison decides it. -/
def normalise (w : Nat) (float : Bool) (v : UInt64) : UInt64 :=
  if !float then v else
  let abs := v &&& (2 ^ (8 * w - 1) - 1).toUInt64
  let inf : UInt64 := if w == 8 then 0x7ff0000000000000 else 0x7f800000
  if abs == 0 then 0
  else if inf < abs then (if w == 8 then 0xfff8000000000000 else 0xffc00000)
  else v

/-- Element `i` of a dense payload of `w`-byte elements, as the key a search compares. -/
def key (w : Nat) (float : Bool) (b : ByteArray) (i : Nat) : UInt64 :=
  normalise w float (Column.bitsAt b (i * w) w)

/-- q's `x?y` at an atom `y`: the least index whose key is `y`'s, and `count x` when there is none.
Measured — `1 1 2?1` is `0`, so a repeat answers with its *first* index; `1 1 2?9` is `3`, so an
absent element answers the count and not a null; and `(0#0)?5` is `0`, which is that same rule at an
empty left argument. -/
@[extern "qlean_search_find_scalar"]
def findScalar (w : USize) (float : Bool) (hay : @& ByteArray) (needle : UInt64) : USize :=
  let n := hay.size / w.toNat
  let k := normalise w.toNat float needle
  -- `none` here is q's "absent", not a failed lookup, and `n` is the answer it calls for
  (((List.range n).find? fun i => key w.toNat float hay i == k).getD n).toUSize

/-- q's `x?y` at a vector `y`: `findScalar` at each element of `y`, as little-endian `Int64`s.
Measured — `1 2 3?2 3 9` is `1 2 3`, and `1 2 3?0#0` is the empty long vector. -/
@[extern "qlean_search_find_vec"]
def findVec (w : USize) (float : Bool) (hay : @& ByteArray) (ndl : @& ByteArray) : ByteArray :=
  let sl (b : ByteArray) (i : Nat) := (b.extract (i * w.toNat) (i * w.toNat + w.toNat)).data
  (List.range (ndl.size / w.toNat)).foldl (init := ByteArray.empty) fun acc j =>
    Column.pushBits acc
      -- an element wider than eight bytes does not fit the `UInt64` a `findScalar` needle is, so above eight
      -- the element is compared whole, which is what the C probe's two-word equality is
      (if w.toNat ≤ 8 then (findScalar w float hay (Column.bitsAt ndl (j * w.toNat) w.toNat)).toNat
       else ((List.range (hay.size / w.toNat)).find? (sl hay · == sl ndl j)).getD
         (hay.size / w.toNat)).toUInt64 8

/-- Where element `j` of a gather reads from, out of a source of `n` elements, and `none` at an index
q answers the element type's null for.

Measured — `(til 10)@9 10 -1 0N` is `9 0N 0N 0N`, so past the end, negative and `0N` are one case and
not three. Reading the index as **unsigned** is what makes them one: `0N` is `Int64.minValue`, whose
unsigned value is `2 ^ 63`, and every negative index wraps above it, so a single `i < n` rejects all
three. The C does the same single compare. -/
def gatherAt (n : Nat) (idx : ByteArray) (j : Nat) : Option Nat :=
  let i := (Column.bitsAt idx (j * 8) 8).toNat
  if i < n then some i else none

/-- q's `x@i` at a dense payload: element `idx[j]` of `src`, or `fill` where `gatherAt` declines.
Here beside `findVec` rather than with the rest of `x@i` in `QLean/Kernel/Structural.lean` because
`distinct` and `group` over an element wider than eight bytes are a probe and this gather, and `QLean/Kernel/Sort.lean` sits below
that module.

`fill` is the type's null as raw bits, and it is `Kernel.nullBits` and no second table — measured,
`1 2 3@5` is `0N`, `1 2 3h@5` is `0Nh`, `1 2 3e@5` is `0Ne`, `"abc"@5` is `" "` and `0x010203@5` is
`0x00`, which is `nullBits` at each of them with its `none` read as zero. -/
@[extern "qlean_structural_gather"]
def gatherBytes (w : USize) (fill : UInt64) (src : @& ByteArray) (idx : @& ByteArray) : ByteArray :=
  (List.range (idx.size / 8)).foldl (init := ByteArray.empty) fun acc j =>
    match gatherAt (src.size / w.toNat) idx j with
    -- above eight bytes the element does not fit a `UInt64` and is copied whole
    | some i => if w.toNat ≤ 8 then Column.pushBits acc (Column.bitsAt src (i * w.toNat) w.toNat) w.toNat
                else acc ++ src.extract (i * w.toNat) (i * w.toNat + w.toNat)
    | none => Column.pushBits acc fill w.toNat

/-- q's `x in y` at vectors on both sides, as a bit per element of `x`. The body is q's own
`(y?x) < count y`, and the `i < m` guard is what leaves the tail bits of the last byte zero —
`Column.packBits` records why that matters: trailing set bits make two equal boolean vectors compare
unequal under `~`. -/
@[extern "qlean_search_member_vec"]
def memberVec (w : USize) (float : Bool) (xs : @& ByteArray) (hay : @& ByteArray) : ByteArray :=
  let m := xs.size / w.toNat
  let n := hay.size / w.toNat
  -- a `List`, not `findVec`'s `Array`: membership needs `LawfulBEq`, and `Array`'s brings `Classical.choice`
  let sl (b : ByteArray) (i : Nat) := (b.extract (i * w.toNat) (i * w.toNat + w.toNat)).data.toList
  (List.range ((m + 7) / 8)).foldl (init := ByteArray.empty) fun acc b =>
    acc.push ((List.range 8).foldl (init := (0 : UInt8)) fun byte t =>
      let i := b * 8 + t
      -- above eight bytes the element is compared whole, as in `findVec`
      if i < m && (if w.toNat ≤ 8 then findScalar w float hay (Column.bitsAt xs (i * w.toNat) w.toNat) < n.toUSize
                   else ((List.range n).find? (sl hay · == sl xs i)).getD n < n)
      then byte ||| (1 <<< t.toUInt8) else byte)

/-- Bytes an id key takes where one side's ids are at `a` bits and the other's at `b`: the narrowest
search width that holds both lanes. -/
def idKeyWidth (a b : USize) : USize :=
  let m := max a b
  if m ≤ 8 then 1 else if m ≤ 16 then 2 else if m ≤ 32 then 4 else 8

/-- `n` ids of `ids` at `w` bits, `Column.idsCap`-clamped, repacked at `k` bytes: what the C's id
operand reads, as `operandBytes` is what it reads of an encoded one. -/
def idsOperand (k w : USize) (ids : ByteArray) (n : USize) : ByteArray :=
  Column.packIds (8 * k.toNat) (Column.idsCap ids w.toNat n.toNat) (Column.idAt ids w.toNat)

/-- `findVec` over two id payloads — `hay`'s `hn` ids at `hw` bits and `ndl`'s `nn` at `nw`, either
any lane `Column.laneWidth` answers — compared at `idKeyWidth`'s bytes. The C reads them where they
lie: `opnd_blk` restores a block of ids at a time through `id_at` into an L1 buffer, as it restores
an encoded pack, so neither payload is widened whole. -/
@[extern "qlean_search_find_ids_vec"]
def findIdsVec (hw : USize) (hay : @& ByteArray) (hn : USize) (nw : USize) (ndl : @& ByteArray) (nn : USize) :
    ByteArray :=
  let k := idKeyWidth hw nw
  findVec k false (idsOperand k hw hay hn) (idsOperand k nw ndl nn)

/-- `findIdsVec`'s answer as a bitmap, which is `memberVec` to `findVec`. -/
@[extern "qlean_search_member_ids_vec"]
def memberIdsVec (xw : USize) (xs : @& ByteArray) (xn : USize) (hw : USize) (hay : @& ByteArray) (hn : USize) :
    ByteArray :=
  let k := idKeyWidth xw hw
  memberVec k false (idsOperand k xw xs xn) (idsOperand k hw hay hn)

/-- The least index at which the boolean column holds `needle`, and `n` when it holds it nowhere.
Measured — `101b?1b` is `0`, `101b?0b` is `1`, and `(0#0b)?1b` is `0`. -/
@[extern "qlean_search_find_bit"]
def findBit (n : USize) (bits : @& ByteArray) (needle : Bool) : USize :=
  (((List.range n.toNat).find? fun i => Column.bitAt bits i == needle).getD n.toNat).toUSize

/-- `findBit` at each element of a boolean needle vector. -/
@[extern "qlean_search_find_bit_vec"]
def findBitVec (n : USize) (hay : @& ByteArray) (m : USize) (ndl : @& ByteArray) : ByteArray :=
  (List.range m.toNat).foldl (init := ByteArray.empty) fun acc j =>
    Column.pushBits acc (findBit n hay (Column.bitAt ndl j)).toUInt64 8

/-- `x in y` at booleans on both sides, `? < count` again. -/
@[extern "qlean_search_member_bits"]
def memberBits (m : USize) (xs : @& ByteArray) (n : USize) (hay : @& ByteArray) : ByteArray :=
  (List.range ((m.toNat + 7) / 8)).foldl (init := ByteArray.empty) fun acc b =>
    acc.push ((List.range 8).foldl (init := (0 : UInt8)) fun byte t =>
      let i := b * 8 + t
      if i < m.toNat && findBit n hay (Column.bitAt xs i) < n
      then byte ||| (1 <<< t.toUInt8) else byte)

/-- q's `where` over a boolean vector: the ascending indices whose bit is set, as `Int64`s.
Measured — `where 101b` is `0 2`, and `where 000b` and `where 0#0b` are both the empty long vector.

Only the boolean form is a kernel. Over a vector of *counts* `where` has to raise `'limit` for a
null, a negative count and a result that would exceed 2^31-1 — `Eval.whereLongs` carries all three —
and a kernel returning a `ByteArray` has no way to say which of them happened. -/
@[extern "qlean_search_where_bits"]
def whereBits (n : USize) (bits : @& ByteArray) : ByteArray :=
  ((List.range n.toNat).filter (Column.bitAt bits)).foldl (init := ByteArray.empty) fun acc i =>
    Column.pushBits acc (Int64.ofNat i).toUInt64 8

/-- The least index whose symbol bytes are `ndl`, and the symbol count when there is none. -/
@[extern "qlean_search_find_sym_scalar"]
def findSymScalar (blob : @& ByteArray) (offs : @& Array Nat) (ndl : @& ByteArray) : USize :=
  let n := offs.size - 1
  (((List.range n).find? fun i => (Column.symKey blob offs i).data == ndl.data).getD n).toUSize

/-- A **monotone unsigned key**: `x < y` in q's order exactly when this is smaller. Ordering is what
`bin` needs and `normalise` above gives equality, so the two are separate maps over the same bits.

The signed widths flip their sign bit, which turns two's complement into unsigned order and puts q's
null — the least value of the type — lowest, where q has it: `10 20 30 bin 0N` is `-1`. The float
widths fold `-0.0` and every NaN first, exactly as `normalise` does, and then flip: a negative
double's bits descend as its value ascends, so complementing them is the ascending key, and the one
NaN pattern `0xfff8…` complements to a value below every number. -/
def ordKey (w : Nat) (float signed : Bool) (v : UInt64) : UInt64 :=
  let mask : UInt64 := if w == 8 then 0xffffffffffffffff else (2 ^ (8 * w) - 1).toUInt64
  let top : UInt64 := (2 ^ (8 * w - 1)).toUInt64
  if float then
    let u := normalise w true (v &&& mask)
    if u &&& top != 0 then (~~~u) &&& mask else u ||| top
  else if signed then (v &&& mask) ^^^ top
  else v &&& mask

/-- The partition point: the first index the test fails at, over `[lo, hi)`. `bin` advances while
`hay[mid] ≤ k` and answers one below it, `binr` advances while `hay[mid] < k` and answers it — so
the two differ in the test and in nothing else. The `fuel` is `hi - lo`, which strictly shrinks each
step and so is a measure.

**The sentinels are `0` and `n`, not `-1` and `n`**, and on an unsorted operand the two forms visit
different elements and answer differently: measured against q 4.1, `5 1 bin 3` is `1` and
`1 9 3 5 bin 4` is `2`, where a halving seeded at `-1` answers `-1` and `0`. That matters here
because `~/q/q.k` line 46 and line 49 build `aj` and `asof` on `bin` and neither sorts its operand
first, so which index comes back is part of what those two answer.

`order` is an **index payload the walk reads `hay` through**, `Int64` per position, and empty where
each position is its own index. That is the one difference between `bin` over a whole column and the
halving a join runs inside one group of it, so it is a parameter here rather than a second walk. -/
def binStep (w : Nat) (float signed right : Bool) (hay order : ByteArray) (k : UInt64) :
    Nat → Nat → Nat → Nat
  | 0, lo, _ => lo
  | fuel + 1, lo, hi =>
    if hi ≤ lo then lo
    else
      let mid := lo + (hi - lo) / 2
      let ix := if order.isEmpty then mid else (Column.bitsAt order (mid * 8) 8).toNat
      let v := ordKey w float signed (Column.bitsAt hay (ix * w) w)
      if (if right then v < k else v ≤ k) then
        binStep w float signed right hay order k fuel (mid + 1) hi
      else binStep w float signed right hay order k fuel lo mid

/-- q's `x bin y` and `x binr y` at dense payloads of one class, as little-endian `Int64`s. -/
@[extern "qlean_search_bin"]
def binBytes (w : USize) (float signed right : Bool) (hay : @& ByteArray) (keys : @& ByteArray) :
    ByteArray :=
  let w := w.toNat
  let n := hay.size / w
  (List.range (keys.size / w)).foldl (init := ByteArray.empty) fun acc j =>
    let p := binStep w float signed right hay ByteArray.empty
      (ordKey w float signed (Column.bitsAt keys (j * w) w)) (n + 1) 0 n
    Column.pushBits acc ((if right then (p : Int) else (p : Int) - 1)).toInt64.toUInt64 8

/-- The **run starts** of a dense payload whose equal elements are contiguous, ending in the element
count: `0, i₁, …, n`, one entry per run and then a terminator, as little-endian `Int64`s. Equality is
`key`'s, the same one `findColumn` matches with, so on such a payload a first occurrence *is* a run
start and the two agree on where a group begins.

An empty payload answers `,0`: no run, and the terminator that says so. -/
@[extern "qlean_search_run_starts"]
def runStarts (w : USize) (float : Bool) (hay : @& ByteArray) : ByteArray :=
  let w := w.toNat
  let n := hay.size / w
  Column.pushBits ((List.range n).foldl (init := ByteArray.empty) fun acc i =>
    if i == 0 || key w float hay i != key w float hay (i - 1)
    then Column.pushBits acc i.toUInt64 8 else acc) n.toUInt64 8

/-- `runStarts` over an interned column's ids. The dictionary is distinct, so two elements are equal
exactly when their ids are and no symbol is compared at all. -/
@[extern "qlean_search_run_starts_ids"]
def runStartsIds (n w : USize) (ids : @& ByteArray) : ByteArray :=
  Column.pushBits ((List.range n.toNat).foldl (init := ByteArray.empty) fun acc i =>
    if i == 0 || Column.idAt ids w.toNat i != Column.idAt ids w.toNat (i - 1)
    then Column.pushBits acc i.toUInt64 8 else acc) n.toUInt64 8

/-- `runStarts` over a bitmap of `n` booleans, `Column.bitAt`'s layout: a run starts at `0` and
wherever a bit differs from the one before it. The C reads a word at a time, the set bits of
`x ^ (x << 1)`, where a byte widened per element was 8x the bytes read. -/
@[extern "qlean_search_run_starts_bits"]
def runStartsBits (n : USize) (bits : @& ByteArray) : ByteArray :=
  Column.pushBits ((List.range n.toNat).foldl (init := ByteArray.empty) fun acc i =>
    if i == 0 || Column.bitAt bits i != Column.bitAt bits (i - 1)
    then Column.pushBits acc i.toUInt64 8 else acc) n.toUInt64 8

/-- The width the dense engine is instantiated at, and `none` at the two types that never reach
it: `boolean` is a `bits` payload and `symbol` has no fixed width. That is a statement
about the dense *engine* and not about what a kernel can answer — `binColumn` reads both, each
by its own payload — so this gate is never the place to add one. Everything else has
a width of 1, 2, 4 or 8, so adding a q type is an entry in `QAtomicType.width` and nothing here. -/
def denseWidth : QAtomicType → Option Nat
  | .boolean | .symbol => none
  | t => t.width

/-- An encoded column at a type the encoding is *for*, which is what every kernel that reads one
where it lies asks first: `?` and `bin` here, `x@i`, `reverse` and a shift in
`QLean/Kernel/Structural.lean`. A `.foR` at any other type is not one `Column.encode` built — the
kernels below take its elements as signed and never as float, which is what `Column.encodes` says —
and it takes the dense path.

Nor is one with an empty `metadata`, which no encoder writes (`rust/src/coc.rs`'s `COC_META(0)` is 16 bytes and
`rust/src/own.rs` refuses less): `operandBytes` reads an empty `metadata` as a dense pack, so handing such a
column over where it lies made `~` read its pack while `Column.bytesOf`, and with it the hash, decoded
it. Declined, it is read through `bytesOf` like any other column, so `operandBytes ∘ operand` is
`bytesOf` on every column. `t` is the header the payload sits under, so the C and `bytesOf` read the
pack at one width. -/
def foRColumn (t : QAtomicType) (n : USize) (e : Ext.Enc X) : Option (USize × ByteArray × ByteArray) :=
  match e with
  | .foR m p => if Column.encodes t && !m.isEmpty then some (n, m, p) else none
  | _ => none

/-- An interned needle naming few of its dictionary's entries — one record typed against a
million-symbol key column — as the blob of its own `n` symbols, so a search asks `n` questions and
not the `d` its dictionary holds. `none` where asking the dictionary costs no more. -/
def fewSyms : USize → Ext.Enc X → Option (ByteArray × Array Nat)
  | n, .enum dict dof ids =>
    if 8 * n.toNat < dof.size - 1 then
      let w := Column.idWidth dof
      some (Nat.fold n.toNat (init := (ByteArray.empty, #[0])) fun i _ (b, o) =>
        let e := Column.idAt ids w i
        let b := dict.copySlice dof[e]! b b.size (dof[e + 1]! - dof[e]!)
        (b, o.push b.size))
    else none
  | _, _ => none

end Rel.Kernel


namespace Rel.Kernel

/-- A search operand as the C reads it where it lies: an encoded column's `metadata` and `pack`
holding `n` elements, or — under an empty `metadata` — the dense payload `pack` itself. -/
def operandBytes (w : USize) (metadata pack : ByteArray) (n : USize) : ByteArray :=
  if metadata.isEmpty then pack else Coc.decode w metadata pack n

/-- The types whose equality folds `-0.0` onto `0.0`. `datetime` is one: it is an eight-byte IEEE
value and `QAtom.identical` treats it exactly as `float`. -/
def foldsZero : QAtomicType → Bool
  | .real | .float | .datetime => true
  | _ => false

/-- A column as `operandBytes` reads it: encoded where it lies, and otherwise its dense payload under
an empty metadata. -/
def operand (t : QAtomicType) (n : USize) (e : Ext.Enc X) : Option (USize × ByteArray × ByteArray) :=
  match foRColumn t n e with
  | some s => some s
  | none => (Enc.bytesOf t n e).map fun b => (0, ByteArray.empty, b)

end Rel.Kernel
