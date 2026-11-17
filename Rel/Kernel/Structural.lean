import Rel.Kernel.Need
import Rel.Kernel.Sort
import Rel.Kernel.Coc
import Rel.Kernel.Reduce
import Rel.Kernel.Value
import Rel.Kernel.Search
import Rel.Kernel.Elementwise

/-! The part of `Rel.Kernel.Structural` the Rel kernels reach; `Rel.Kernel.Structural` imports it. -/


namespace Rel.Kernel

/-- `gatherBytes` over `spreadColumn`'s index, with that index never written: element `i` of `src`
repeated `widths[i]` times. The two are one operation because the index between them is a run of the
same number — `ungroup`'s repeat of a column of atoms is the only shape that builds one — so the
composition writes and reads back eight bytes an answer element to say nothing the widths had not
already said. `widths` is a dense `long` payload, so a caller holding a long column passes it as it
is; a negative count is a run of none. -/
@[extern "qlean_structural_expand"]
def expandBytes (w : USize) (fill : UInt64) (src : @& ByteArray) (widths : @& ByteArray) :
    ByteArray :=
  (Array.range (widths.size / 8)).foldl (init := ByteArray.empty) fun acc i =>
    (Array.range (Column.bitsAt widths (i * 8) 8).toInt64.toInt.toNat).foldl (init := acc) fun acc _ =>
      Column.pushBits acc
        (if i < src.size / w.toNat then Column.bitsAt src (i * w.toNat) w.toNat else fill) w.toNat

/-- `gatherBytes` over an interned column's ids: the same index rule, on a payload of `w`-bit fields
rather than `w`-byte ones, and written out at `wout` because the answer's dictionary can be one entry
longer than the argument's — a miss is the empty symbol and `gatherIds` appends it when the
dictionary has none. -/
@[extern "qlean_structural_gather_ids"]
def gatherPacked (n w wout : USize) (fill : UInt64) (src : @& ByteArray) (idx : @& ByteArray) :
    ByteArray :=
  Column.packIds wout.toNat (idx.size / 8) fun j =>
    match gatherAt n.toNat idx j with
    | some i => Column.idAt src w.toNat i
    | none => fill.toNat

/-- `cycleBytes` over an interned column's ids: `m` elements from `off`, cycling. Not a byte-range
extract — at a sub-byte width a slice can start inside a byte — so the fields are moved one at a
time, over a payload that is a fraction of the dense one's size. `off < n` and `0 < n`, which
`sliceColumn` establishes. -/
@[extern "qlean_structural_cycle_ids"]
def cycleIds (n off m w : USize) (ids : @& ByteArray) : ByteArray :=
  Column.packIds w.toNat m.toNat fun j => Column.idAt ids w.toNat ((off.toNat + j) % n.toNat)

/-- Where element `j` of a shift by `k` reads from, and `none` where that is off either end.

The same shape as `gatherAt` because it is the same question asked of an index the caller did not
have to build: a shift is a gather at `til n - k`, and the C runs the identical unsigned compare, so
`j - k` wrapping below zero and running past `n` are one rejection and not two. -/
def shiftAt (n : Nat) (k : Int) (j : Nat) : Option Nat :=
  let i := (j : Int) - k
  if 0 ≤ i && i < (n : Int) then some i.toNat else none

/-- q's shift at a dense payload: element `j - k`, or `fill` where that is off either end. A positive
`k` moves elements later, which is `prev`.

`fill` is the type's null, exactly as `gatherBytes` takes it, and the family that uses this is why the
null and not a zero: measured, `prev "abc"` is `" ab"` and `prev 0x0105` is `0x0001`, the blank at
`char` and zero at `byte` being what `Kernel.nullBits` already says for each. -/
@[extern "qlean_structural_shift"]
def shiftBytes (w : USize) (fill : UInt64) (k : Int64) (b : @& ByteArray) : ByteArray :=
  let n := b.size / w.toNat
  (List.range n).foldl (init := ByteArray.empty) fun acc j =>
    Column.pushBits acc
      (match shiftAt n k.toInt j with
        | some i => Column.bitsAt b (i * w.toNat) w.toNat
        | none => fill) w.toNat

/-- `,` and `raze` at a dense payload, which at one element type is concatenation.

One kernel for both and not a fold of a two-argument join: folding `++` copies the accumulated prefix
once per part, so `raze` over `k` columns would be quadratic where q is linear. -/
@[extern "qlean_structural_concat"]
def concatBytes (parts : Array ByteArray) : ByteArray :=
  parts.foldl (init := ByteArray.empty) (· ++ ·)

/-- An append the encoded form takes without re-encoding: `n` elements at `metadata` and `pack`, and
`tail` the elements to add as dense eight-byte values. It answers the **first part's own metadata**
and its pack with the appended residuals written into the positions the new elements take, which is
the answer only when the block they land in keeps its minimum, its maximum and its residual width.

Five ways it declines, and each would be a wrong column if it did not:

* `lo = 0` — the count fills its blocks, so the new elements start a block the metadata has not got.
  Where that is the whole of the join, `concatFoR`'s move branch below already has it;
* `Column.blk metadata < lo + m` — more elements than the block has room for, and the ones past it need a
  block of their own;
* an element outside `[base, maxv]` — its residual does not exist at this block's base and width, so
  the block needs a fresh minimum and a fresh width, which is `Coc.encode`'s work rather than a
  write. A `0N` is `Int64.minValue` and the smallest value there is, so appending one always widens
  its block unless the block already holds one, where its residual is the zero it already reads as;
* an element whose residual does not fit the block's width. A residual is measured from the block's
  frame, `Column.foRFrame`, which is the base except in a patched block with a low outlier, and a
  patched block's width need not hold its whole range: the outliers sit in the patch list;
* a part not in the writer's form, `Coc.foRStd`: a pack that does not cover the block, where
  `Column.resAt` answers zeros and this would write bytes, or an exception at or past `lo`, which
  `Column.foRExc` would read in place of an appended element. The writer's form says where a patch
  list ends, not where its exceptions lie, so that is asked of the list itself.

The patch list rides along untouched in the pack's tail: its positions are the first part's and,
past that test, the block's own exceptions lie before `lo`.

The `t upsert (1;2)` of `tools/bench-matrix.txt` is the third: `b` is the sorted `xa`, whose last
block runs 999424110 to 999999956, so appending `2` widens it and the join is re-encoded.
`insert[`ti;(1;2)]` is the claim — `sm` is `til 1000`, one block of base 0 and maximum 999, and 1
and 2 lie in it. -/
def appendFoR (n : USize) (metadata pack tail : ByteArray) : Option (ByteArray × ByteArray) :=
  let lo := n.toNat % Column.blk metadata
  let b := n.toNat / Column.blk metadata
  let m := tail.size / 8
  let w := Column.widthAt metadata b
  let s := Column.blockStart metadata b
  let base := Column.baseAt metadata b
  let frame := base + Column.foRFrame metadata pack b
  -- unsigned throughout: a residual is a difference taken with `UInt64` wrapping, which is what
  -- `Column.foRBits` adds back, so `v - base ≤ maxv - base` is `base ≤ v ≤ maxv` in q's own order
  let span := Column.maxvAt metadata b - base
  let v (j : Nat) : UInt64 := Column.bitsAt tail (j * 8) 8
  let res (j : Nat) : UInt64 := v j - frame
  if lo == 0 || Column.blk metadata < lo + m || !Coc.foRStd n metadata pack
      || (List.range (Column.blk metadata - lo)).any fun j => (Column.foRExc metadata pack (n.toNat + j)).isSome then none
  else if (List.range m).any fun j => span < v j - base || 2 ^ w ≤ (res j).toNat then none
  else some (metadata,
    pack.extract 0 s
      ++ Coc.packRes (Column.blk metadata) w (fun j =>
           if lo ≤ j && j < lo + m then res (j - lo) else Column.resAt pack s w j)
      ++ pack.extract (s + Column.blk metadata * w / 8) pack.size)

/-- `concatFoR`'s move: every part's blocks in turn and its residuals after them. `none` where a part
but the last misses the grid, where any part is not in the writer's form, `Coc.foRStd` — a short
pack puts the next part's residuals in its own blocks, and a block past a part's count is copied into
the join — or where any part has a patch list: the list's block offsets and positions are its own
column's, and joining packs whole would put one part's list where the next part's residuals start.
Not an `@[extern]`, so `#guard` runs it. -/
def moveFoR (ps : Array ((USize × ByteArray) × ByteArray)) : Option (ByteArray × ByteArray) :=
  -- the parts' block size, the first's; a part at another one declines, so the join is re-encoded
  let lg := (ps[0]?.map (Column.lgOf ·.1.2)).getD Column.lgEnc
  if !ps.pop.all (fun p => p.1.1.toNat % Column.blk p.1.2 == 0) || ps.any fun p => Column.lgOf p.1.2 != lg ||
      !Coc.foRStd p.1.1 p.1.2 p.2 || Column.blockStart p.1.2 (Column.nblk p.1.2) < p.2.size then none else
  -- every part's blocks are full here, so each block's cached sum moves with it; the answer keeps
  -- them only where every part carried them at the same null, one part without being one block
  -- whose sum is unknown
  let nb := ps.foldl (init := 0) fun acc p => acc + Column.nblk p.1.2
  let nul := ps.foldl (init := (ps[0]?.map (Column.sumNulAt ·.1.2)).getD 0) fun acc p =>
    if Column.sumNulAt p.1.2 != acc || Column.sumCountAt p.1.2 != Column.nblk p.1.2 * 2 ^ lg
    then 0 else acc
  some (Coc.foRMeta lg nul.toUInt64 (if nul == 0 then 0 else nb * 2 ^ lg)
     (ps.foldl (init := #[]) fun acc p =>
      acc ++ (Array.range (Column.nblk p.1.2)).map fun b =>
        (Column.baseAt p.1.2 b, Column.maxvAt p.1.2 b, Column.bsumAt p.1.2 b,
         Column.widthAt p.1.2 b)),
   concatBytes (ps.map (·.2)))

/-- `,` and `raze` at Frame-of-Reference payloads: every part's blocks in turn, and its residuals
after them, when `moveFoR` claims the join; the appended residuals written into the
first part's last block when `appendFoR` claims it; and the parts decoded, joined and encoded again
when neither holds, because a part that ends part way through a block puts every part after it out of
step with the grid. `zip` truncates to the shortest array, which is the minimum the C takes.

The append is what `insert` and `upsert` reach: appending a row to a thousand re-encoded both
columns whole, 17.4 instructions an element for two elements of answer. `ew` is `reverseFoR`'s.

The C claims the append and the move only where the answer is still the writer's form — the grown
block keeping the frame, width and no exception the writer would give it, every part the writer's
own — so it can answer the re-encode where this answers the append; the values are the same.

`ns` is the parts' counts, 8-byte little-endian (`countBytes`); the parts past
`min (ns.size / 8) (min metas.size packs.size)` are not read, and the C takes the same minimum. -/
@[extern "qlean_structural_concat_foR"]
def concatFoR (ew : USize) (ns : @& ByteArray) (metas : Array ByteArray) (packs : Array ByteArray) :
    ByteArray × ByteArray :=
  let ps := (Array.range (min (ns.size / 8) (min metas.size packs.size))).map fun k =>
    (((Column.bitsAt ns (8 * k) 8).toUSize, metas[k]!), packs[k]!)
  match moveFoR ps with
  | some out => out
  | none =>
    let dense := ps.map fun p => Coc.decode ew p.1.2 p.2 p.1.1
    let ((n, metadata), pack) := ps[0]!
    let tail := (ps.extract 1 ps.size).map fun p => Coc.decode 8 p.1.2 p.2 p.1.1
    match appendFoR n metadata pack (concatBytes tail) with
    | some out => out
    | none => Coc.encode ew (concatBytes dense)

/-- Counts as an extern takes a list of them: 8 bytes each, little-endian, read back by
`Column.bitsAt ns (8 * k) 8`. -/
def countBytes (ns : Array USize) : ByteArray :=
  ns.foldl (init := ByteArray.empty) fun acc n => Column.pushBits acc n.toUInt64 8

/-- A shift at a Frame-of-Reference payload, re-encoded rather than moved. `reverse` and `,` have a
move case and this has none: a shift keeps the 1024-element grid aligned only when `k` is a multiple
of 1024, and the family that uses it — `deltas`, `prev`, `next`, `mavg` — shifts by one.

Decoding instead is what made `deltas xl` 124ms at 64M against q's 97: the shift materialised 512MB
and the subtraction then decoded its other operand as well. The C walks the pack a block at a time.
`ew` is `reverseFoR`'s. -/
@[extern "qlean_structural_shift_foR"]
def shiftFoR (ew : USize) (metadata : @& ByteArray) (pack : @& ByteArray) (n : USize) (k : Int64)
    (fill : UInt64) : ByteArray × ByteArray :=
  Coc.encode ew (shiftBytes ew fill k (Coc.decode ew metadata pack n))

/-- `x@i` with the source left encoded: `n` elements at width `w` in it, and a dense `long` index.
The answer is dense, as the dense gather's is.

The source's decode was the wasteful one and it was a whole column — at 64M longs `xl@xd` spent 48ms
of its 80 on it, 1 GB of dense payload written so that a gather could read a part of it once. This
is the shape `where` and the element-wise verbs hand it: a source that is a stored column and an
index of a handful of positions, freshly built and dense. `gatherFoRIdx` below is the other one. -/
@[extern "qlean_structural_gather_foR"]
def gatherFoR (w : USize) (fill : UInt64) (smeta : @& ByteArray) (spack : @& ByteArray) (n : USize)
    (idx : @& ByteArray) : ByteArray :=
  gatherBytes w fill (Coc.decode w smeta spack n) idx

/-- `x@i` with **both** operands encoded: `n` elements at width `w` in the source, `m` in the index.
The answer is dense, as the other two gathers' are.

The index is read straight through, one element once, so decoding it whole writes `8m` bytes for a
pass that reads each of them once and never again. Measured single-threaded at a million longs, that
decode alone is 73.5 µs — `xl@xg` 296 µs with a dense index against 370 with an encoded one, and
`xg@xd` 283 against 356, the same figure both times because an index is eight bytes an element
whatever the source is.

A **dense** source with an encoded index has no kernel and still decodes its index. The encoded form
is the representation, so a source that is dense at a type `Column.encodes` is a transient — `til`,
`where`, a grade — while an encoded index is a stored column, and the two do not meet. -/
@[extern "qlean_structural_gather_foR_idx"]
def gatherFoRIdx (w : USize) (fill : UInt64) (smeta spack : @& ByteArray) (n : USize)
    (imeta ipack : @& ByteArray) (m : USize) : ByteArray :=
  gatherFoR w fill smeta spack n (Coc.decode 8 imeta ipack m)

/-- `dst` with the `wb`-bit field at each long of `idx` replaced, in order, by field `soff + k` of
`src` — field `soff` for every `k` under `bcast`. Fields below a byte pack low field first, which is
`Column.resAt`'s layout, so a bitmap is `wb = 1` and an interned column's ids are `Column.idWidth`.
In order, so the last write to a repeated index stays: q's `:`. An index past `dst` writes nothing,
`amendRounds` having raised it already. -/
@[extern "qlean_structural_scatter"]
def scatterPacked (wb : USize) (dst : ByteArray) (idx : @& ByteArray) (src : @& ByteArray) (soff : USize)
    (bcast : Bool) : ByteArray :=
  let wb := wb.toNat
  if wb == 0 then dst else
  (List.range (idx.size / 8)).foldl (init := dst) fun acc k =>
    let u := (Column.bitsAt idx (k * 8) 8).toNat
    let e := soff.toNat + (if bcast then 0 else k)
    if acc.size * 8 / wb ≤ u then acc
    else if 8 ≤ wb then src.copySlice (e * (wb / 8)) acc (u * (wb / 8)) (wb / 8)
    else
      let per := 8 / wb
      let sh := ((u % per) * wb).toUInt8
      let mask : UInt8 := (1 <<< wb.toUInt8) - 1
      acc.set! (u / per) ((acc.get! (u / per) &&& ~~~(mask <<< sh)) |||
        ((Column.resAt src 0 wb e).toUInt8 <<< sh))

/-- `scatterPacked` at an interned column's `n` ids, `wa` bits each, whose dictionary has grown to
one whose ids take `wb`: the ids are widened first — copied where `wa = wb`, in place when nothing
else holds them — and `yids`, already ids of the grown dictionary, are written at `idx` in order, so
the last write to a repeated index stays. -/
@[extern "qlean_structural_scatter_ids"]
def scatterIds (wa wb n : USize) (ids : ByteArray) (idx : @& ByteArray) (yids : @& ByteArray) (bcast : Bool) :
    ByteArray :=
  scatterPacked wb (if wa == wb then ids else Column.packIds wb.toNat n.toNat (Column.idAt ids wa.toNat ·))
    idx yids 0 bcast

/-- `scatterPacked` at a symbol blob: element `idx[k]` of `b`/`o` replaced, in order, by symbol `k`
of `yb`/`yo` — symbol `0` under `bcast` — so the last write to a repeated index stays. An index past
the column writes nothing, `amendRounds` having raised it already. -/
@[extern "qlean_structural_scatter_syms"]
def scatterSyms (b : @& ByteArray) (o : @& Array Nat) (idx : @& ByteArray) (yb : @& ByteArray)
    (yo : @& Array Nat) (bcast : Bool) : ByteArray × Array Nat :=
  let n := o.size - 1
  let src := (List.range (idx.size / 8)).foldl (init := Array.replicate n none) fun acc k =>
    let u := (Column.bitsAt idx (k * 8) 8).toNat
    if u < n then acc.set! u (some (if bcast then 0 else k)) else acc
  Nat.fold n (init := (ByteArray.empty, #[0])) fun i _ (ob, oo) =>
    let (sb, so, e) := match src[i]! with | some k => (yb, yo, k) | none => (b, o, i)
    let ob := sb.copySlice so[e]! ob ob.size (so[e + 1]! - so[e]!)
    (ob, oo.push ob.size)

/-- q's `til`, as little-endian `Int64`s. Measured — `til 5` is `0 1 2 3 4`, `til 0` is the empty long
vector, `type til 5` is `7h` and `til 2h` is `0 1`, so the answer is `long` whatever the count's own
type was; `til -1` and `til 0N` are both `'domain`, which `tilColumn` declines rather than encodes. -/
@[extern "qlean_structural_til"]
def tilLongs (n : USize) : ByteArray :=
  (List.range n.toNat).foldl (init := ByteArray.empty) fun acc i =>
    Column.pushBits acc (Int64.ofNat i).toUInt64 8

/-- `x@i` at a bit payload. Measured — `1101b@3 2 1 0` is `1011b` and `101b@0 5` is `10b`, so an index
q cannot serve answers `0b`, which is `Eval.nullAtom`'s boolean null. -/
@[extern "qlean_structural_gather_bits"]
def gatherBits (n : USize) (bits : @& ByteArray) (idx : @& ByteArray) : ByteArray :=
  packOf (idx.size / 8) fun j =>
    match gatherAt n.toNat idx j with
    | some i => Column.bitAt bits i
    | none => false

/-- `concatFoR` at ALP payloads of `ew`-byte floats: a block that is one part's own block on the
answer's grid moves with its exponent and exceptions, and the blocks straddling a part boundary are
restored and handed to ALP's block steps, so `x,y` with `x` long re-encodes `x`'s last partial block
and `y`, and copies the rest. Decoding every part to join them was what `{x,y}` over a million floats
paid on every append. The values are the specification's; a moved block keeps the exponent it had,
which is the writer's for a column in the writer's form and an equally exact one otherwise. `ns` is
`concatFoR`'s: 8-byte little-endian counts. -/
@[extern "qlean_structural_concat_alp"]
def concatALP (ew : USize) (ns : @& ByteArray) (metas packs alps : @& Array ByteArray) :
    ByteArray × ByteArray × ByteArray :=
  Coc.alpEncodeAt (ew == 4) (concatBytes ((Array.range (min (ns.size / 8) (min metas.size
    (min packs.size alps.size)))).map fun k =>
      Coc.alpDecode (if ew == 4 then 4 else 8) metas[k]! packs[k]! alps[k]!
        (Column.bitsAt ns (8 * k) 8).toNat.toUSize))

/-- `cycleBytes` at a bit payload, and C where that one is not: a slice starting off a byte boundary
has to shift every byte it moves. Measured — `3 rotate 110100001b` is `100001110b`, `-3 rotate` it is
`001110100b` (which is `off = 6`), `-5#101b` is `01101b` and `5#101b` is `10110b`. A count of `0`
never divides: `packOf 0` folds over an empty range. -/
@[extern "qlean_structural_cycle_bits"]
def cycleBits (n off m : USize) (b : @& ByteArray) : ByteArray :=
  packOf m.toNat fun j => Column.bitAt b ((off.toNat + j) % n.toNat)

/-- `,` and `raze` at bit payloads. Measured — `101b,11b` is `10111b` and `raze (11111111b;1b)` is
`111111111b`, so a part starts wherever the one before it ended and not on a byte.

`counts` is each part's element count, which `Enc.bits` stores because `⌈n/8⌉` is not invertible, as
8-byte little-endian counts (`countBytes`); the parts past `min (counts.size / 8) parts.size` are not
read, and the C takes the same minimum. -/
@[extern "qlean_structural_concat_bits"]
def concatBits (counts : @& ByteArray) (parts : @& Array ByteArray) : ByteArray :=
  let bs := (Array.range (min (counts.size / 8) parts.size)).flatMap fun k =>
    (Array.range (Column.bitsAt counts (8 * k) 8).toNat).map (Column.bitAt parts[k]!)
  packOf bs.size fun j => (bs[j]?).getD false

/-- Symbol payloads concatenated. `Enc.syms`' invariant is `n + 1` starts with `offs[0] = 0` and
`offs[n] = blob.size`, so each part after the first contributes its starts *without* its leading `0`,
shifted past the blob built so far. Pure Lean: `++` on a `ByteArray` is one `copySlice`, and the
offsets are `Nat`s, which are tagged scalars rather than allocations. -/
def concatSyms (parts : Array (ByteArray × Array Nat)) : QValue :=
  let p := parts.foldl (init := (ByteArray.empty, #[0])) fun (blob, offs) (b, o) =>
    (blob ++ b, offs ++ (o.extract 1 o.size).map (· + blob.size))
  .vector .symbol (needSize (p.2.size - 1) "concatSyms: symbols" (fun _ => 0) id) (.syms p.1 p.2) none

/-- The ids of an enumerated column file: q writes one 8-byte domain index per element, and this is
those indices packed at the dictionary's own width, with `0Nj` — the null symbol, which q gives no
domain entry — sent to `nullId`. The second component is the first element that is neither an index
below `d` nor `0Nj`, and `n` when every one of them is; the caller reads that element back to name it
and raises.

`@[extern]` because this **is** reading a partition's symbol column, the longest column in the
system: the loop it replaces boxed one `QAtom.long` per element and resolved each to a `String`. -/
@[extern "qlean_structural_enum_ids"]
def enumIds (n d nullId w : USize) (b : @& ByteArray) : ByteArray × USize :=
  let val := fun i => (Column.bitsAt b (i * 8) 8).toInt64
  (Column.packIds w.toNat n.toNat
    (fun i => if val i == Int64.minValue then nullId.toNat else (val i).toInt.toNat),
   (((List.range n.toNat).find? fun i =>
      val i != Int64.minValue && !(0 ≤ val i && (val i).toInt.toNat < d.toNat)).getD
        n.toNat).toUSize)

/-- `,` and `raze` at interned payloads: each part's ids read through the map that takes its own
dictionary's entries to the joined dictionary's, laid down end to end. `maps[k]` and the answer are
ids of the **joined** dictionary and are read and written at `wout`, while part `k`'s ids are at
`widths[k]`.

`Kernel.remapIds` is this at one part; what a join needs beyond it is that the parts land in one
payload, and at a width below eight a part does not start on a byte — the reason `concatBits` is a
kernel and not an append. `counts` is the parts' counts, 8-byte little-endian (`countBytes`); the parts
past `min (counts.size / 8) parts.size` are not read, and the C takes the same minimum. `widths` stay
`Nat`s: they are bit widths (`Column.idWidth`, at most 64), not counts. -/
@[extern "qlean_structural_concat_ids"]
def concatIds (wout : USize) (counts : @& ByteArray) (widths : @& Array Nat) (maps parts : @& Array ByteArray) :
    ByteArray :=
  let ids := (Array.range (min (counts.size / 8) parts.size)).flatMap fun k =>
    (Array.range (Column.bitsAt counts (8 * k) 8).toNat).map fun i =>
      Column.idAt maps[k]! wout.toNat (Column.idAt parts[k]! widths[k]! i)
  Column.packIds wout.toNat ids.size (ids[·]!)

/-- The interned parts of a `,` joined: the dictionaries concatenated and interned **once**, which is
both the joined dictionary and — `internSyms` answering the ids of what it was given — the map from
every part's entry to its place in it; then one pass over the ids. The symbols are compared d₁+d₂
times and the elements not at all, which is the cost `Enc.enum`'s docstring gives a cross-column
verb.

Two parts over one dictionary land here too rather than in a shortcut: interning `d` entries that are
already distinct answers the identity map, and the pass over the ids is the one that has to happen
either way. -/
def internConcat (ps : Array (USize × ByteArray × Array Nat × ByteArray)) : ByteArray × Array Nat × ByteArray :=
  let ds := ps.map fun (_, dict, offs, _) => (dict, offs)
  let (cb, co) := match concatSyms ds with | .vector _ _ (.syms b o) _ => (b, o) | _ => (ByteArray.empty, #[0])
  let (db, dbo, dmap) := Order.internSyms cb co
  let w := Column.idWidth dbo
  let bases := ds.foldl (init := #[0]) fun acc (_, o) => acc.push (acc[acc.size - 1]! + o.size - 1)
  (db, dbo, concatIds w.toUSize (countBytes (ps.map fun (n, _, _, _) => n)) (ds.map fun (_, o) => Column.idWidth o)
      ((Array.range ds.size).map fun k =>
        Column.packIds w (ds[k]!.2.size - 1) fun j => Column.idAt dmap w (bases[k]! + j))
      (ps.map fun (_, _, _, ids) => ids))

/-- `internConcat` answered from the first part's **kept dictionary hash** (`rust/src/structural.rs`, "the
dictionary hash"): where that dictionary holds no symbol twice, the joined one is it with the symbols
new to it after, so a `,` of `k` symbols probes `k` times and the first part's ids are copied, never
remapped. `.error ps`, the parts handed back so the caller's fallback holds no reference of its own
while the first part's ids may be grown in place, where it holds a repeat, and past `2^32 - 2` entries in all, which the table's
32-bit slots do not reach. The first part's ids are copied as they are, so an id at or past its
dictionary — which no well-formed column holds — stays where `internConcat` reads it as `0`. -/
@[extern "qlean_symdict_concat"]
def hashConcat (ps : Array (USize × ByteArray × Array Nat × ByteArray)) :
    Except (Array (USize × ByteArray × Array Nat × ByteArray)) (ByteArray × Array Nat × ByteArray) :=
  let e := ps.foldl (init := 0) fun s (_, _, o, _) => s + (o.size - 1)
  match ps[0]? with
  | some (_, d, o, _) =>
    if e < 4294967294 && (Order.internSyms d o).2.1.size - 1 == o.size - 1 then .ok (internConcat ps) else .error ps
  | none => .error ps

/-- `,` and `raze` at interned payloads: `hashConcat`, and `internConcat` where it declines. The parts
come back with the decline, so this holds no reference of its own while the kernel may grow the first
part's ids in place. A part after the first that names few of its dictionary's entries (`fewSyms`)
joins as its own symbols, its ids counting them: the entries it does not name are no value of the
answer, and resolving them was a pass over a whole dictionary — a row read off a million-symbol key
column — per append. -/
def concatEnum (ps : Array (USize × ByteArray × Array Nat × ByteArray)) : QValue :=
  let ps := ps.mapIdx fun i p => if i == 0 then p else match p with
    | (n, d, o, ids) => match fewSyms n (.enum d o ids) with
      | some (b, bo) => (n, b, bo, Column.packIds (Column.idWidth bo) n.toNat fun j => j)
      | none => p
  -- the count first: read after the kernel, it kept `ps` alive across it and its ids shared
  let n := ps.foldl (init := 0) fun s (n, _, _, _) => s + n.toNat
  .vector .symbol (needSize n "concatEnum: symbols" (fun _ => 0) id) (match hashConcat ps with
    | .ok (db, dbo, ids) => .enum db dbo ids
    | .error ps => match internConcat ps with | (db, dbo, ids) => .enum db dbo ids) none

/-- `x@i` over an interned column: the ids are gathered and the dictionary does not move. No
`@[extern]`, because the only pass over the column is `gatherBytes`, which is already one — the rest
is the dictionary's size.

A miss is q's empty symbol, so the answer's dictionary is the source's with the empty symbol *ensured
present* and misses pointing at it. Appending it unconditionally would leave the dictionary holding
two of them where it already had one, and `distinct` would then answer the empty symbol twice; the
lookup that avoids that reads `d` entries, never the column. A gather that cannot miss — `inRange`,
asked only where the empty symbol is absent — keeps the dictionary *object*, and with it the kept hash
(`CLAUDE.md`, "An interned dictionary keeps its hash"): copying a million entries to add a symbol no
element names was every keyed `upsert`'s cost on a symbol key. -/
def gatherIds (dict : @& ByteArray) (dof : @& Array Nat) (inRange : Unit → Bool)
    (gather : USize → USize → UInt64 → ByteArray) : ByteArray × Array Nat × ByteArray :=
  let nd := dof.size - 1
  let e := (findSymScalar dict dof ByteArray.empty).toNat
  let (db, dbo) := if e < nd || inRange () then (dict, dof) else (dict.push 0, dof.push (dict.size + 1))
  (db, dbo, gather (Column.idWidth dof).toUSize (Column.idWidth dbo).toUSize e.toUInt64)

/-- `gatherPacked` with the index left encoded: an enumeration's values are its domain's ids
gathered by its indices, a stored `long` column, and decoding that whole was most of every verb
over an enumerated column — 160 MB written at 20M rows for a pass that reads each element once. -/
@[extern "qlean_structural_gather_ids_foR"]
def gatherPackedFoR (n w wout : USize) (fill : UInt64) (src : @& ByteArray)
    (imeta ipack : @& ByteArray) (m : USize) : ByteArray :=
  gatherPacked n w wout fill src (Coc.decode 8 imeta ipack m)

/-- `:` of `y`'s symbols at the rows `ix` of the `n`-element symbol column `e` — field `k` of the
`ny`-element `ye` at `ix[k]`, field `0` at every one under `bcast`, the last write to a repeated row
kept — under `,`'s policy (`razeColumn`): two blobs scatter as a blob, and where either side is
interned the other is interned to meet it. `y` then resolves through `e`'s kept dictionary hash
(`hashConcat`), its new symbols appended, so `e`'s ids are widened at most and never remapped, and
`e`'s dictionary object and table stay where `y` adds nothing. A dictionary `hashConcat` declines (one
holding a repeat) is joined by `concatEnum` instead and re-interned by a gather over `til n`. `none`:
a payload that is no symbol column. -/
def assignSyms (n : USize) (e : Enc) (ny : USize) (ye : Enc) (ix : ByteArray) (bcast : Bool) : Option Enc :=
  match e, ye with
  | .syms b o, .syms yb yo => match scatterSyms b o ix yb yo bcast with | (b', o') => some (.syms b' o')
  | e, ye => match Column.intern e, Column.intern ye with
    | .enum d o ids, .enum yd yo yi =>
      match hashConcat #[(0, d, o, .empty), (ny, yd, yo, yi)] with
      | .ok (db, dbo, yids) =>
        some (.enum db dbo (scatterIds (Column.idWidth o).toUSize (Column.idWidth dbo).toUSize n ids ix yids bcast))
      | .error _ => match concatEnum #[(n, d, o, ids), (ny, yd, yo, yi)] with
        | .vector _ _ (.enum db dbo all) _ =>
          let all := scatterPacked (Column.idWidth dbo).toUSize all ix all n bcast
          let (gb, gbo, gids) := gatherIds db dbo (fun _ => true) fun w wo e =>
            gatherPacked (n + ny) w wo e all (tilLongs n)
          some (.enum gb gbo gids)
        | _ => none
    | _, _ => none

/-- The symbol a gather's index names, and the empty symbol — which is `symbol`'s null — where it
misses. Measured: `` `a`b@0 5 ``, `` `a`b@0 -1 `` and `` `a`b@0 0N `` are all `` `a` ``, the same
one unsigned comparison `gatherBytes` folds its three misses into.

The blob and the offsets are built in one pass rather than two because the offsets are the running
total of what the blob has taken, and a `Enc.syms` payload is exactly those two. -/
@[extern "qlean_structural_gather_syms"]
def gatherSyms (blob : @& ByteArray) (offs : @& Array Nat) (ix : @& ByteArray) :
    ByteArray × Array Nat :=
  let n := offs.size - 1
  let key (j : Nat) : ByteArray :=
    match gatherAt n ix j with
    | some i => blob.extract offs[i]! (offs[i + 1]! - 1)
    | none => ByteArray.empty
  (List.range (ix.size / 8)).foldl (init := (ByteArray.empty, #[0])) fun (b, o) j =>
    let k := key j
    ((b ++ k).push 0, o.push (b.size + k.size + 1))

/-- `gatherBytes` from an ALP column, which the C answers element by element where the index points
and never restores whole: the gather a `where` hands half a column to. -/
@[extern "qlean_alp_gather"]
def gatherAlp (fill : UInt64) (metadata pack a : @& ByteArray) (n : USize) (idx : @& ByteArray) :
    ByteArray :=
  let w : USize := if Column.alpF32 a then 4 else 8
  gatherBytes w fill (Coc.alpDecode w metadata pack a n) idx

/-- Whether every `long` of `idx`, read unsigned, is below `n`: a gather by it misses nowhere. In C
because the Lean fold was 11% of `select from t where k=5` on a table with an interned column. -/
@[extern "qlean_structural_all_below"]
def allBelow (n : USize) (idx : @& ByteArray) : Bool :=
  (idx.size / 8).all fun k _ => (Column.bitsAt idx (k * 8) 8).toNat < n.toNat

/-- q's `x@i` when a kernel claims it: `x` is `n` elements at `t` and `i` a `long` vector of `m`, which
is the answer's count. Measured — `type 1 2 3@0 2` is `7h` and `type 1 2 3@2` is `-7h`, so only the
*vector* index answers a vector and an atom index is one element, which `Enc.get` already serves
without materialising anything.

An empty index answers the empty vector at `t`: `1 2 3@0#0` is `` `long$() ``, and `(0#0)@0 1` is
`0N 0N`, so an empty *source* is not a decline either — every index simply misses. -/
def gatherColumn (t : QAtomicType) (n : USize) (e : Enc) (m : USize) (ie : Enc) : Option Enc :=
  -- both encoded is the representation's own case and reads neither operand into dense bytes; every
  -- other pairing brings the index to dense bytes and leaves the source where it is
  match denseWidth t, foRColumn t n e, foRColumn .long m ie with
  | some w, some (n, sm, sp), some (m, im, ip) =>
    some (.bytes (gatherFoRIdx w.toUSize ((nullBits t).getD 0) sm sp n im ip m))
  | _, _, _ =>
    -- the index decode is a thunk and every arm below opens it for itself: the source's payload is
    -- what decides whether there is an answer at all, and an index column is `long` and therefore
    -- always encoded, so opening it above the refusal writes eight megabytes for a `none`
    let idx (_ : Unit) : Option ByteArray := match Enc.bytesOf .long m ie with
      | some ix => if ix.size < m.toNat * 8 then none else some ix
      | none => none
    match t, e with
    | .boolean, .bits b => (idx ()).map fun ix => .bits (gatherBits n b ix)
    | .symbol, .syms blob offs =>
      (idx ()).map fun ix => let (nb, no) := gatherSyms blob offs ix; .syms nb no
    -- interned: `asc` is a grade and this gather, and the grade was already the ids' — leaving this
    -- on the blob is what made `asc xs` slower interned than not
    -- no rows name no symbol: an empty answer holding the source's dictionary would carry it into
    -- every `,` onto it, and a `,` from it extends that dictionary — forking its kept hash — for a
    -- value that is thrown away, as `upsert` types a record against its table's empty rows
    | .symbol, .enum dict dof ids =>
      if m == 0 then some (.syms .empty #[0]) else
      -- an index past `n`, negative or null reads as a `UInt64` at or past `n`
      let inRange (_ : Unit) : Bool := match idx () with
        | some ix => allBelow n ix
        | none => false
      let ans (gather : USize → USize → UInt64 → ByteArray) : Enc :=
        let (db, dbo, nids) := gatherIds dict dof inRange gather
        .enum db dbo nids
      match foRColumn .long m ie with
      | some (m, im, ip) => some (ans fun w wo e => gatherPackedFoR n w wo e ids im ip m)
      | none => (idx ()).map fun ix => ans fun w wo e => gatherPacked n w wo e ids ix
    | t, .alp md p a =>
      if !Column.alpEncodes t then none else
        (idx ()).map fun ix => .bytes (gatherAlp ((nullBits t).getD 0) md p a n ix)
    | t, e =>
      match rowWidth t, foRColumn t n e with
      | some w, some (n, sm, sp) =>
        (idx ()).map fun ix => .bytes (gatherFoR w.toUSize ((nullBits t).getD 0) sm sp n ix)
      | some w, none =>
        match Enc.bytesOf t n e with
        | some src => (idx ()).map fun ix => .bytes (gatherBytes w.toUSize ((nullBits t).getD 0) src ix)
        | none => none
      | none, _ => none

/-- The other direction: an index payload read back as row numbers. A gather composed with another,
`fby`'s buckets and a row delete all do this, and the `bitsAt` per element it replaces was eight
shifts and a `Array.range` of a million naturals. -/
@[extern "qlean_structural_rows_of"]
def longRows (b : @& ByteArray) : Array Nat :=
  (Array.range (b.size / 8)).map fun i => (Column.bitsAt b (8 * i) 8).toNat

/-- `enumIds` over the Frame-of-Reference column an enumerated column's indices arrive in — every
`long` column a file holds is encoded as it is read. The body is the specification: the dense
indices, then `enumIds`. `rust/src/structural.rs` packs a block at a time out of a 1024-element buffer and
never holds them dense, which is what reading a partition's symbol column comes down to. -/
@[extern "qlean_structural_enum_ids_for"]
def enumIdsFoR (n d nullId w : USize) (metadata pack : @& ByteArray) : ByteArray × USize :=
  enumIds n d nullId w (Coc.decode 8 metadata pack n)

end Rel.Kernel


namespace Rel.Kernel

/-- Eight bytes a count: a list built by `countBytes` holds exactly its array's counts, so no caller
checks `size = 8 * parts` where the parts are as many as the counts. -/
theorem countBytes_size (ns : Array USize) : (countBytes ns).size = 8 * ns.size := by
  suffices h : ∀ (l : List USize) (b : ByteArray),
      (l.foldl (fun acc n => Column.pushBits acc n.toUInt64 8) b).size = b.size + 8 * l.length by
    simpa [countBytes, ← Array.foldl_toList] using h ns.toList .empty
  intro l; induction l with
  | nil => simp
  | cons n l ih => intro b; simp [ih, Column.pushBits_size]; omega

/-- Whether a dense answer costs less than re-encoding `s` answer blocks, a dense answer costing the `n`
elements' `w` bytes and a re-encoded element what `k` of that move's dense bytes do; under 64 blocks
either is microseconds. `k` is the caller's because the dense answer's cost per byte is the move's own:
measured (`CLAUDE.md`, "A concat whose parts are mostly off the block grid answers dense") it is 5 at
Frame of Reference, and at ALP 8 for `,` and a slice and 16 for `reverse` and a shift, whose dense
answer is a decode and one byte move. At ALP `w` is 8 whatever the element type: the decode is a
divide in `double` at `real` too, so a `real`'s dense answer costs a `float`'s (measured, dense
`1_xr` 118 us against `1_xf` 53, re-encoded both 54). The one rule of every whole-column move the
writer re-encodes: `razeColumn`, `reverseColumn`, `shiftColumn` and `sliceColumn`. -/
def denseCheaper (k n w s : Nat) : Bool :=
  64 * 2 ^ Column.lgEnc ≤ n && (n + 2 ^ Column.lgEnc - 1) / 2 ^ Column.lgEnc * w < s * k

/-- The parts of a `,` the encoded form can serve, at a type the encoding is for: Frame of
Reference's `(meta, pack)` at a type `Column.encodes`, and ALP's `(meta, pack, alp)` at a float, the
`Bool` saying which and the `alp` blobs empty under Frame of Reference. Whether their
blocks line up is `concatFoR`'s and `concatALP`'s to decide — the parts that do are moved and the parts that do not are
re-encoded — so the counts travel with the payloads rather than being a condition here.

A part that is not encoded yet is encoded to meet the ones that are. `Enc.ofAtoms` still answers
dense bytes, so a one-cell part made from an atom used to send the whole join the other way: every
encoded part decoded to dense to meet it, which is what made `t upsert (1;2)` widen a million
elements to append one. Where no part is encoded there is nothing to meet, and the join stays where
it lies. -/
def encodedParts (t : QAtomicType) (cs : Array (USize × Enc)) :
    Option (Bool × Nat × Array USize × Array ByteArray × Array ByteArray × Array ByteArray) := do
  let alp := Column.alpEncodes t
  if !(alp || Column.encodes t) || !cs.any (fun c => match c.2 with | .foR .. => !alp | .alp .. => alp | _ => false) then none
  else
    let ps ← cs.mapM fun
      | (n, .foR m p) => if alp then none else some (n, m, p, ByteArray.empty)
      | (n, .alp m p a) => if alp then some (n, m, p, a) else none
      | (n, e) =>
        if alp then (match Enc.alpOf t n e with | some (.alp m p a) => some (n, m, p, a) | _ => none)
        else match Enc.encode t n e with | .foR m p => some (n, m, p, ByteArray.empty) | _ => none
    some (alp, ps.foldl (init := 0) (· + ·.1.toNat), ps.map (·.1), ps.map (·.2.1), ps.map (·.2.2.1),
      ps.map (·.2.2.2))

/-- The answer blocks of a `,` over parts of `ns` elements that no part supplies whole, and so are
re-encoded: a block moves only when it starts on its part's 1024-element grid and ends inside that
part, which is `cat_take`'s test in `rust/src/structural.rs`. -/
def straddles (ns : Array Nat) : Nat :=
  let total := ns.foldl (· + ·) 0
  let (_, moved) := ns.foldl (init := (0, 0)) fun (s, mv) n =>
    (s + n, if s % 2 ^ Column.lgEnc != 0 then mv
      else mv + if s + n == total then (n + 2 ^ Column.lgEnc - 1) / 2 ^ Column.lgEnc else n / 2 ^ Column.lgEnc)
  (total + 2 ^ Column.lgEnc - 1) / 2 ^ Column.lgEnc - moved

/-- q's `raze` at one element type, which by `~/q/q.k` line 19's `raze:,/` is also `x,y` at two
columns of that type. Measured — `raze (1 2;3 4)` is `1 2 3 4`, `raze (0#0;0#0)` is the empty long
vector, `raze enlist 1 2` is `1 2`, `raze (01b;10b)` is `0110b` and `` raze (`a`b;`c) `` is
`` `a`b`c ``.

No parts at all is declined: `raze ()` is the general empty list `()` at type `0h`, not a typed empty
vector, and there is no `t` in it to answer with. -/
def razeColumn (t : QAtomicType) (cs : Array (USize × Enc)) : Option QValue :=
  if cs.isEmpty then none
  else match t with
    | .boolean =>
      match cs.mapM (fun | (n, .bits b) => some (n, b) | _ => none) with
      | some ps => needSize (ps.foldl (init := 0) (fun s p => s + p.1.toNat)) "raze: booleans" (fun _ => none) fun c =>
        some (.vector .boolean c (.bits (concatBits (countBytes (ps.map (·.1))) (ps.map (·.2)))) none)
      | none => none
    | .symbol =>
      match cs.mapM (fun | (_, .syms b o) => some (b, o) | _ => none) with
      | some ps => some (concatSyms ps)
      | none =>
        -- a part that is not interned yet is interned to meet the ones that are, exactly as
        -- `encodedParts` encodes one to meet an encoded part; where **no** part is interned the arm
        -- above joins two blobs and interning them to join them would be the dearer answer. A part
        -- that is neither is not a symbol payload at all and is what the `none` below is for.
        match cs.mapM (fun (n, e) => match Column.intern e with
            | .enum dict offs ids => some (n, dict, offs, ids)
            | _ => none) with
        | some ps => some (concatEnum ps)
        | none => none
    | t =>
      let dense := fun (_ : Unit) => match t.width, cs.mapM fun (n, e) => Enc.bytesOf t n e with
        | some w, some ps =>
          if (cs.zip ps).any fun ((n, _), b) => b.size < n.toNat * w then none
          else needSize (cs.foldl (· + ·.1.toNat) 0) "raze: elements" (fun _ => none) fun c =>
            some (.vector t c (.bytes (concatBytes ps)) none)
        | _, _ => none
      match encodedParts t cs, t.width with
      | some (alp, n, ns, ms, ps, as), some w =>
        -- the straddling blocks are the ones re-encoded; every other block moves
        if denseCheaper (if alp then 8 else 5) n (if alp then 8 else w) (straddles (ns.map (·.toNat))) then dense ()
        else needSize n "raze: elements" (fun _ => none) fun c =>
        -- `countBytes_size` makes `nb` one count a part exactly where `ns` is; that is `encodedParts`' to hold
        let nb := countBytes ns
        need (ns.size = ms.size) (fun _ => s!"raze: {ns.size} counts for {ms.size} parts") (fun _ => none)
          fun _ =>
        if alp then
          match concatALP w.toUSize nb ms ps as with
          | (m, p, a) => some (.vector t c (Enc.answer t c (.alp m p a)) none)
        else
          match concatFoR w.toUSize nb ms ps with
          | (m, p) => some (.vector t c (Enc.answer t c (.foR m p)) none)
      | _, _ => dense ()

/-- The type a code column is read at by `keySource`, whether any code is negative, and the greatest
code. An interned column's ids are in `[0, d)` and pass as they lie, at any lane: the chain's
`Ew.eIds` stage reads them unsigned a tile at a time, so no lane is widened whole first. Measured at
1e7 rows, two lanes of 1, 2 or 4 bits: 1.3–2.3 ms a key, against 2.7–4.6 widening them by `remapIds`
first and 1.0–1.7 for the same codes already dense `u8`, the widening not counted. A bitmap is in
`[0, 1]` without a read.

A dense column is read by `overBytes`, a fold that skips its `nul` and seeds `min` with `~~~nul`.
So `min` skipping `-1` is negative exactly when a code other than `-1` is, and `min` skipping `-2`
when `-1` is — every null being negative, that is the null test too — and `max` skips
`Int64.minValue`, which is never the greatest of codes in a domain. An encoded column is read from
its metadata and patch list, no element at all. -/
def keyOperand (t : QAtomicType) (e : Enc) : Option (QAtomicType × Bool × Int) :=
  match e with
  | .enum _ offs _ => some (.symbol, false, ((offs.size - 1 : Nat) : Int) - 1)
  | .bits _ => if t == .boolean then some (t, false, 1) else none
  | .bytes b => do
    guard (t == .byte || t == .short || t == .int || t == .long)
    let cls ← clsOf t
    -- two passes for `min`, because at `long` every `nul` is some element: one skipping `-1` and
    -- one skipping `-2` together see every negative code, at every class
    some (t, overBytes .lesser cls (-1) b < 0 || overBytes .lesser cls (-2) b < 0,
      (overBytes .greater cls Int64.minValue b).toInt)
  | .foR md pk => do
    guard (t == .short || t == .int || t == .long)
    -- every block's extremes, and the patch list's values — a null or an outlier is held there and
    -- not in the extremes — read where `Column.foRExc` reads them, without its position search
    let e := Column.blockStart md (Column.nblk md)
    let nexc := if pk.size ≤ e then 0 else (Column.bitsAt pk e 8).toNat
    let esz := (Column.bitsAt pk (e + 8) 8).toNat % 256
    let s := (64 - 8 * esz).toUInt64
    let exc := (List.range nexc).map fun k =>
      let v := Column.bitsAt pk (e + 16 + k * esz) esz
      if esz == 1 then v.toInt64 else (v <<< s).toInt64 >>> s.toInt64
    let bs := List.range (Column.nblk md)
    let lo := (bs.map fun b => (Column.baseAt md b).toInt64) ++ exc
    let hi := (bs.map fun b => (Column.maxvAt md b).toInt64) ++ exc
    some (t, lo.any (· < 0), hi.foldl (init := -1) fun m x => max m x.toInt)
  | _ => none

/-- `operandSource` at `i64` for a `keyOperand` column of `n` elements, with an interned column's ids
read where they lie by an `Ew.eIds` stage: an id is a code here, and no class `operandSource` reads
names it. `none` where the payload holds fewer than `n` ids, which the C would read past. -/
def keySource (b : Ew.Build) (t : QAtomicType) (e : Enc) (n : USize) : Option (Ew.Build × UInt8) :=
  match e with
  | .enum _ offs ids =>
    let w := Column.idWidth offs
    if Column.idsCap ids w n.toNat != n.toNat then none else
      let (b, a) := b.input ids
      some (b.add { engine := Ew.eIds, cls := Ew.i64, shape := w.toUInt8, a })
  | e => operandSource b t n e Ew.i64 Int64.minValue Int64.minValue n

/-- The composite key `c₁·d₂ + c₂`, element `i` being `Column.idAt ids w i` at
`w = Column.idWidthOf (d₁ * d₂)` — the width a dictionary of `d₁·d₂` entries packs its ids at — so a
key reads where an id does.

One chain, one pass: each operand decoded and promoted to `long` a tile at a time by
`keySource`, whatever its layout — `u8`, `i16`, `i32`, a bitmap, Frame of Reference, an interned
id lane — then `*` by the atom, `+`, and an `Ew.ePack` stage writing the key at the lane `w`, sub-byte
lanes included. No operand, no intermediate and no answer at a wider lane is a whole column.
Measured at 1e7 rows, two bitmaps: 15.5 ms with the key cast to bytes and then narrowed by
`remapIds`, against 5.4 ms with that second pass gone.

`none` where the counts differ, `d₁·d₂ ≥ 2⁶³`, or a code is outside its domain — null, negative,
`c₁ ≥ d₁` or `c₂ ≥ d₂` — which `keyOperand`'s extremes decide before the chain runs. Inside the
domain no partial value leaves `[0, d₁·d₂)`, so nothing wraps and the key fits `w` bits. -/
def composeKey (t₁ : QAtomicType) (n : USize) (e₁ : Enc) (d₁ d₂ : Nat) (t₂ : QAtomicType) (n₂ : USize)
    (e₂ : Enc) : Option ByteArray := do
  let (u₁, neg₁, hi₁) ← keyOperand t₁ e₁
  let (u₂, neg₂, hi₂) ← keyOperand t₂ e₂
  guard (n₂ == n && d₁ * d₂ < 2 ^ 63 &&
    (n == 0 || (!neg₁ && hi₁ < d₁ && !neg₂ && hi₂ < d₂)))
  -- no code equals `Int64.minValue` inside the domain, so it is the null of every stage
  let nul := Int64.minValue
  let (bld, s₁) ← keySource {} u₁ e₁ n
  let (bld, k) := bld.input (atomBytes Ew.i64 d₂.toUInt64)
  let (bld, p) := bld.add
    { engine := Ew.eVal, op := Ew.mul, cls := Ew.i64, shape := Ew.va, a := s₁, b := k, nul }
  let (bld, s₂) ← keySource bld u₂ e₂ n
  let (bld, s) := bld.add
    { engine := Ew.eVal, op := Ew.add, cls := Ew.i64, shape := Ew.vv, a := p, b := s₂, nul }
  some (bld.run { engine := Ew.ePack, cls := Ew.i64, shape := (Column.idWidthOf (d₁ * d₂)).toUInt8, a := s }
    n)

end Rel.Kernel
