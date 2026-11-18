import Rel.Kernel.Value

/-! The part of `Rel.Kernel.Coc` the Rel kernels reach; `Rel.Kernel.Coc` imports it. -/


namespace Rel.Kernel.Coc

/-- What is added to a `w`-byte element to make unsigned comparison agree with q's order: half the
range, which is flipping the sign bit. One byte is the exception and biases by nothing, `byte` and
`char` being q's only unsigned fixed-width types — `boolean` is a `Column.bits` payload and never
reaches an encoder. -/
def bias (w : Nat) : Nat := if w = 1 then 0 else 2 ^ (8 * w - 1)

/-- Element `i` of a dense payload of `w`-byte elements, biased into unsigned order. -/
def keyAt (w : Nat) (x : ByteArray) (i : Nat) : Nat :=
  (Rel.Column.bitsAt x (i * w) w).toNat ^^^ bias w

/-- A key written back out as the `int64_t` a block minimum is stored as: the bias taken off again,
sign-extended to 64 bits. Adding `2 ^ 64 - bias w` is that sign extension — a non-negative element
comes back unchanged modulo `2 ^ 64`, and a negative one comes back as its two's complement in 64
bits rather than in `8 * w`. `Column.baseAt` reads these bits and adds the residual with `UInt64`
wrapping, so this is the form that makes the two agree. -/
def unbias (w k : Nat) : UInt64 := (k + (2 ^ 64 - bias w)).toUInt64

/-- The element a block's cached sum skips, as the raw bits `Column.foRBits` answers. q's null is the
bottom of a signed type's range, which is the key `0` written back out. One byte has none — `byte` and
`char` are q's unsigned pair — and takes `Int64.minValue`, which no zero-extended byte is; `COC_NUL`
in `rust/src/coc.rs` is the same choice for the same reason. -/
def sumNul (w : Nat) : UInt64 := if w = 1 then (2 ^ 63 : Nat).toUInt64 else unbias w 0

/-- Block `b`, of `B` elements, of a payload of `n` `w`-byte elements: its minimum key, its maximum key, the sum of the
elements that are not `sumNul w`, and the residual width the extremes' difference needs. The extreme
folds are seeded with the block's first element rather than with an identity, which is what makes them
total without a bound on `b` — an out-of-range block reads zeros through `bitsAt` and answers a width
of 0 instead of an empty minimum; the sum is seeded with `0`, which is what an empty block sums to.

The sum is here and not in a pass of its own because it is the same walk of the same block, which is
what makes it free in `rust/src/coc.rs`'s `encode_meta` too. -/
def blockOf (B w n b : Nat) (x : ByteArray) : Nat × Nat × UInt64 × Nat :=
  let lo := b * B
  let ks := (Array.range (min (lo + B) n - lo)).map fun j => keyAt w x (lo + j)
  let mn := ks.foldl min (keyAt w x lo)
  let mx := ks.foldl max (keyAt w x lo)
  let nul := sumNul w
  let s := ks.foldl (init := (0 : UInt64)) fun acc k =>
    let v := unbias w k
    if v == nul then acc else acc + v
  (mn, mx, s, Rel.Column.widthFor (mx - mn))

/-- One block's residual bytes from the residuals themselves, laid out the way `Column.resAt` reads
them back: residual `j`'s low `w` bits at bits `[j * w, j * w + w)` of a little-endian bit stream,
byte `k` being the OR of the residuals whose fields it overlaps, shifted into place.

A block of `B` elements always occupies `B * w / 8` bytes even when it holds fewer than `B`, so a block
start is a prefix sum of the widths and is always a multiple of eight. The elements past the count
are encoded as a residual of 0 — `rust/src/coc.rs` reaches the same bytes by leaving its zeroed buffer
alone. -/
def packRes (B w : Nat) (res : Nat → UInt64) : ByteArray :=
  if w = 0 then ByteArray.empty else
  Nat.fold (B * w / 8) (init := ByteArray.emptyWithCapacity (B * w / 8))
    fun k _ acc => acc.push <|
      (List.range' (8 * k / w) ((8 * k + 7) / w + 1 - 8 * k / w)).foldl (init := (0 : UInt8)) fun b j =>
        b ||| ((res j).toNat % 2 ^ w * 2 ^ (j * w) / 2 ^ (8 * k)).toUInt8

/-- The metadata of the blocks `(base, maxv, bsum, width)` describe, in the five sections and the
trailer `QLean/Value.lean` lays out. `off` is the prefix sum of `2 ^ lg * width / 8` rather than anything
carried over, because that is what `Column.blockStarts` recomputes — copying an argument's offsets
would let the metadata and the denotation drift. `rust/src/coc.rs`'s `coc_offsets` is the same prefix sum.

`nul`, `sumn` and `lg` are the trailer: the null the sums skipped, the count they were taken at and
the block size's logarithm, `2 ^ lg` elements a block. A caller
that has no sums to offer passes `0` and `0`, which is what every reader tests for. -/
def foRMeta (lg : Nat) (nul : UInt64) (sumn : Nat) (bs : Array (UInt64 × UInt64 × UInt64 × Nat)) : ByteArray :=
  (bs.foldl (init := ByteArray.empty) fun acc b => Rel.Column.pushBits acc b.1 8)
    ++ (bs.foldl (init := ByteArray.empty) fun acc b => Rel.Column.pushBits acc b.2.1 8)
    ++ (bs.foldl (init := (ByteArray.empty, 0)) fun (acc, pos) b =>
          (Rel.Column.pushBits acc pos.toUInt64 8, pos + 2 ^ lg * b.2.2.2 / 8)).1
    ++ (bs.foldl (init := ByteArray.empty) fun acc b => Rel.Column.pushBits acc b.2.2.1 8)
    ++ Rel.Column.pushBits (Rel.Column.pushBits (Rel.Column.pushBits ByteArray.empty nul 8) sumn.toUInt64 8)
        lg.toUInt64 8
    ++ bs.foldl (init := ByteArray.empty) fun acc b => acc.push b.2.2.2.toUInt8

/-- A section padded up to the multiple of eight the next one starts on. -/
private def alpPad (b : ByteArray) : ByteArray :=
  b ++ ⟨Array.replicate ((8 - b.size % 8) % 8) 0⟩

/-- The exception ladder `Column.alpSects` reads back, `rust/src/layout.rs`'s `exc_layout`: the header (the count of
`exc`, then `word`), `exc_raw` (element `i` of `x` at `w` bytes, each `i` of `exc`), `exc_off` (at each of the `nb + 1`
block starts, the exceptions before it), `exc_pos` (each one's place in its block of `B`) and `last`, each section
aligned. ALP's blob ends in its block exponents, a FoR patch list in its frames or in nothing. -/
def excBlob (word : UInt64) (B w nb : Nat) (x : ByteArray) (exc : Array Nat) (last : ByteArray) : ByteArray :=
  alpPad (Rel.Column.pushBits (Rel.Column.pushBits ByteArray.empty exc.size.toUInt64 8) word 8)
    ++ alpPad (exc.foldl (init := ByteArray.empty) fun acc i =>
         Rel.Column.pushBits acc (Rel.Column.bitsAt x (i * w) w) w)
    ++ alpPad ((Array.range (nb + 1)).foldl (init := ByteArray.empty) fun acc b =>
         Rel.Column.pushBits acc (exc.filter (· < b * B)).size.toUInt64 4)
    ++ alpPad (exc.foldl (init := ByteArray.empty) fun acc i =>
         Rel.Column.pushBits acc (i % B).toUInt64 2)
    ++ alpPad last

/-- Whether key `k` lies outside the `2 ^ d` keys from frame `f`, so that its block patches it. -/
def outside (f d k : Nat) : Bool := k < f || f + 2 ^ d ≤ k

/-- How many of the block's keys `ks` frame `f` at width `d` patches. -/
def npatch (ks : Array Nat) (f d : Nat) : Nat := (ks.filter (outside f d)).size

/-- The frame at width `d`: of `mn` and the keys, the one patching fewest, the lowest of those. -/
def frameAt (ks : Array Nat) (mn d : Nat) : Nat :=
  ks.foldl (init := mn) fun f k =>
    if npatch ks k d < npatch ks f d || (npatch ks k d == npatch ks f d && k < f) then k else f

/-- The bytes block `ks` costs at width `d`, at `w` bytes an element: its residual bits rounded up to bytes, and
`2 + w` a patch (its `u16` position and the element). -/
def cost (ks : Array Nat) (mn w d : Nat) : Nat := (ks.size * d + 7) / 8 + npatch ks (frameAt ks mn d) d * (2 + w)

/-- A block's frame key and residual width: the width of `0 .. W` that `cost` is least at, the narrower on a tie, and
its `frameAt`; `W`, the bit length of `mx - mn`, patches nothing, and a wider width only costs more. Where `patch` is
off — ALP's integers, whose exceptions are its own blob's — the width is `W` and the frame `mn`. -/
def planOf (patch : Bool) (ks : Array Nat) (mn mx w : Nat) : Nat × Nat :=
  if patch then
    -- the best width's cost rides in the accumulator: recomputing it is a `frameAt` search per width
    let d := ((List.range (Rel.Column.widthFor (mx - mn) + 1)).foldl (init := (0, cost ks mn w 0)) fun (d, cd) c =>
      let cc := cost ks mn w c
      if cc < cd then (c, cc) else (d, cd)).1
    (frameAt ks mn d, d)
  else (mn, Rel.Column.widthFor (mx - mn))

/-- Block `b` of `n` `w`-byte elements at blocks of `2 ^ lg`: `blockOf`'s extremes and sum, then `planOf`'s frame and
width for its keys. -/
def planBlock (lg w n : Nat) (patch : Bool) (x : ByteArray) (b : Nat) : Nat × Nat × UInt64 × Nat × Nat :=
  let (mn, mx, s, _) := blockOf (2 ^ lg) w n b x
  let lo := b * 2 ^ lg
  let (f, d) := planOf patch ((Array.range (min (lo + 2 ^ lg) n - lo)).map fun j => keyAt w x (lo + j)) mn mx w
  (mn, mx, s, f, d)

/-- `encode` at blocks of `2 ^ lg` elements: the model every theorem about the encoder is stated
over, at any `lg` the layout admits, `6 .. 16`. `encode` is this at `Column.lgEnc`.

Block `b` is `blockOf`'s extremes and sum with `planOf`'s frame `f` and width `d`: an element whose key `outside`
leaves is patched — its residual 0, its bits in the patch list `excBlob` lays after the residuals — and every other
is its key less `f` at `d` bits. The patch list exists where a block patches, its frames (`f - mn` a block) where
one is not its minimum; `rust/src/enc.rs`'s `for_blk` and `pack_exc_blk` write the same bytes. A column of `2 ^ 32`
elements or more patches nothing: the list's block offsets are `u32`. -/
def encodeAt (lg : Nat) (width : USize) (x : ByteArray) (patch : Bool := true) : ByteArray × ByteArray :=
  let w := width.toNat
  let n := x.size / w
  let blk := planBlock lg w n (patch && decide (n < 2 ^ 32)) x
  let bs := (Array.range ((n + 2 ^ lg - 1) / 2 ^ lg)).map blk
  -- every per-element read of a plan goes to `bs`, never `blk`: each `blk` call reruns the block's width search
  let pack := (bs.foldl (init := (ByteArray.empty, 0)) fun (acc, b) (_, _, _, f, d) =>
    let lo := b * 2 ^ lg
    (acc ++ packRes (2 ^ lg) d fun j =>
      (if lo + j < n && !outside f d (keyAt w x (lo + j)) then keyAt w x (lo + j) - f else 0).toUInt64, b + 1)).1
  let exc := (Array.range n).filter fun i =>
    outside (bs.getD (i / 2 ^ lg) default).2.2.2.1 (bs.getD (i / 2 ^ lg) default).2.2.2.2 (keyAt w x i)
  let fs := bs.map fun (mn, _, _, f, _) => (f - mn).toUInt64
  let frm := fs.any (· != 0)
  let tail := if exc.size = 0 then ByteArray.empty else
    excBlob (w.toUInt64 ||| if frm then 256 else 0) (2 ^ lg) w bs.size x exc
      (if frm then fs.foldl (init := ByteArray.empty) fun acc v => Rel.Column.pushBits acc v 8 else ByteArray.empty)
  (foRMeta lg (sumNul w) n (bs.map fun (mn, mx, s, _, d) => (unbias w mn, unbias w mx, s, d)), pack ++ tail)

/-- A dense payload of `width`-byte elements as `(metadata, pack)`.

The obligation is `Column.atoms t (.foR n metadata pack) = Column.atoms t (.bytes x)` — encoding is a
choice of representation and owes nothing else, which is why the C comment on `qlean_coc_encode_i64`
states the round trip and not the bytes.

`width` is `QAtomicType.width`, and only 1, 2, 4 and 8 are legal: the kernels are instantiated at
those four element types, `Column.encode` below refuses everything else, and the C aborts rather than
answering an empty pair, which would drop a column's contents silently. -/
@[extern "qlean_coc_encode"]
def encode (width : USize) (x : @& ByteArray) : ByteArray × ByteArray := encodeAt Rel.Column.lgEnc width x


/-- The bytes of the patch list whose header is at byte `e` of `pk`, for `nb` blocks: `rust/src/coc.rs`'s
`for_layout` of the header's count, element width and frame flag — the ladder `Column.alpSects` gives,
then a `u64` frame a block when bit 8 of the width word is set. `none` where that word is not one
`coc_attach` reads: an element width of 1, 2, 4 or 8 and no bit above the flag. -/
def foRTail (nb : Nat) (pk : ByteArray) (e : Nat) : Option Nat :=
  let f := (Rel.Column.bitsAt pk (e + 8) 8).toNat
  if [1, 2, 4, 8].contains (f % 256) && f < 512 then
    some ((Rel.Column.alpSects nb (Rel.Column.bitsAt pk e 8).toNat (f % 256)).2.2
      + if f < 256 then 0 else 8 * nb)
  else none

/-- Whether `(md, pk)` holds `n` elements in the form the writers lay out: one block per started `blk`
elements, a pack that ends where its last block's residuals do or, with a patch list, where the
layout its header declares does, `foRTail`, and no width past 64. A column mapped from a file or
built by hand can satisfy `Column.WF` without it, and a kernel that moves blocks or residuals whole
claims only where this holds: a block past the count would be carried into the answer, and a short
pack would put the next part's residuals in its place. A kernel that cannot carry a patch list
declines one on top of this. `Verify.foRStd_iff` is `Verify.FoRWF`, `Verify.foRWF_encode` that
`encode` establishes it, and `rust/src/coc.rs`'s `coc_std` is the same test. -/
def foRStd (n : USize) (md pk : ByteArray) : Bool :=
  Rel.Column.nblk md == (n.toNat + Rel.Column.blk md - 1) / Rel.Column.blk md
    && (pk.size == Rel.Column.blockStart md (Rel.Column.nblk md)
      || (foRTail (Rel.Column.nblk md) pk (Rel.Column.blockStart md (Rel.Column.nblk md))).map
          (Rel.Column.blockStart md (Rel.Column.nblk md) + ·) == some pk.size)
    && (List.range (Rel.Column.nblk md)).all fun b => Rel.Column.widthAt md b ≤ 64

/-- The elements as raw bits. Every specification below is a fold over this, `decode` included, so it
is the one place that mentions `base`, the block starts and the residual layout. `Ew.foRShift` is
stated over it too, for that reason, which is why it is not `private`. -/
def elems (metadata pack : ByteArray) (n : USize) : List UInt64 :=
  let starts := Rel.Column.blockStarts metadata
  (List.range n.toNat).map (Rel.Column.foRBits metadata pack starts)

/-- The dense payload an encoded column denotes: `n` little-endian `width`-byte elements, the `i`th
being `foRBits` truncated to that width. This is the inverse of `encode`, and the entry every kernel
family outside this file reaches a `.foR` column through — an elementwise or a sort or a search kernel
is written over dense bytes, and an encoded argument is decoded once and handed to it. Two whole-vector
C calls, which is what `PLAN.ckernel.md` §3.1 permits; what it bans is a per-element extern.

`Column.dense` does not go through this, and neither does the `roundTrips` guard in
`QLean/Kernel/Test.lean`. That guard exists to hold the C encoder against the *Lean* reader, and
routing it through a C decoder would turn it into C against C. -/
@[extern "qlean_coc_decode"]
def decode (width : USize) (metadata : @& ByteArray) (pack : @& ByteArray) (n : USize) : ByteArray :=
  (elems metadata pack n).foldl (init := ByteArray.empty) fun acc v =>
    Rel.Column.pushBits acc v width.toNat

/-- The six verbs, in the order `rust/src/coc.rs` switches on. A Lean enumeration is passed to C as a
`uint8_t` in constructor order, so this list and the one in `rust/src/coc.rs` are the same list and cannot be
reordered apart. -/
inductive Over
  | add | mul | lesser | greater | all | any
  deriving DecidableEq, Repr, Inhabited

/-- Whether the fold runs over `"b"$x` rather than over the elements themselves. This is also why
`all` and `any` are the two that do not skip `0N`: `"b"$0N` is `1b`, so the cast has already turned
the null into an ordinary `1` before the fold sees it, and there is nothing left to skip. -/
def Over.boolCast : Over → Bool
  | .all | .any => true
  | _ => false

/-- What q answers when the fold sees no element at all, at the element type `nul` is the null of.
`min` seeds with that type's `0W` and `max` with its `-0W`: measured, `min 0#0h` is `0Wh` and
`max 0#0h` is `-0Wh`, and the same at `int` and `long`. `~nul` is `0W` at every width — the null
being the minimum of the type, its complement is the maximum — and is written that way rather than
`-nul - 1`, which overflows at `long`. -/
def Over.seed (op : Over) (nul : Int64) : Int64 :=
  match op with
  | .add => 0
  | .mul => 1
  | .lesser => ~~~nul
  | .greater => nul + 1
  | .all => 1
  | .any => 0

/-- One step of the fold. `add` and `mul` wrap at 64 bits, which both paths have to do and agree on
where: on a timestamp column `1024 * base` overflows `Int64` on the very first block, so bit-exactness
is the right demand rather than an approximate one, and it is q's own semantics for a long sum. -/
def Over.step : Over → Int64 → Int64 → Int64
  | .add, acc, x => acc + x
  | .mul, acc, x => acc * x
  | .lesser, acc, x => if acc < x then acc else x
  | .greater, acc, x => if x < acc then acc else x
  | .all, acc, x => if x != 0 then acc else 0
  | .any, acc, x => if x != 0 then 1 else acc

/-- `nul` is the **element type's** null and not always `Int64.minValue`: the encoded form holds a
short column's elements sign-extended, so its null is `-32768` there and the fold has to skip that.
The block structure carries over unchanged — a block holds a null exactly when its minimum is one,
and inside such a block an element is null exactly when its residual is zero — because the null is
still the smallest value the type has. -/
@[extern "qlean_coc_over"]
def over (op : Over) (nul : Int64) (metadata : @& ByteArray) (pack : @& ByteArray)
    (n : USize) : Int64 :=
  (elems metadata pack n).foldl (init := op.seed nul) fun acc v =>
    let x := v.toInt64
    if !op.boolCast && x == nul then acc else op.step acc x

/-- `2 ^ 53`, the one bound in the float layer. Past it an integer is no longer exact as a double,
so "the value is the integer `d`" stops being true; it is also what keeps a block's integer sum
inside an `Int64` at `Column.blk` elements, and what leaves room to shift a whole block by a
constant. `rust/src/coc.rs`'s `ALP_P53`. -/
def alpP53 : Float := 9007199254740992.0

/-- q's in-band sentinels — `0n`, `0w` and `-0w` — are the patterns whose exponent field is all
ones. Tested on the raw bits and before any decimal test, so that a round trip returns the same NaN
and not merely some NaN. `rust/src/coc.rs`'s `COC_SENT` at each width. -/
def alpSentinel (f32 : Bool) (x : UInt64) : Bool :=
  if f32 then (x >>> 23) &&& 0xff == 0xff else (x >>> 52) &&& 0x7ff == 0x7ff

/-- The element as a `Float`. A four-byte element widens exactly and order-preservingly, which is
why the whole layer is type-erased into `Float` for the reason the integral one is type-erased into
`Int64`. This is never the path a value takes back to the user — it may canonicalise a NaN
payload — so an exception is copied as bits and only compared or added here. -/
def alpVal (f32 : Bool) (x : UInt64) : Float :=
  if f32 then (Float32.ofBits x.toUInt32).toFloat else Float.ofBits x

/-- Is `x` the decimal `d * 10 ^ -e`, and if so which `d` (as `Int64` bits)? Decided by decoding `d`
and comparing **bits**: comparing values would admit `-0.0`, which decodes as `+0.0`.

`Float.round` breaks a tie away from zero where `rust/src/coc.rs`'s `nearbyint` breaks it to even. Nothing
rests on that: the round trip is what accepts a `d`, so each side accepts only its own `d` and both
satisfy the specification `alpDecode (alpEncode x) = x`. -/
def alpDat (f32 : Bool) (x : UInt64) (e : Nat) : Option UInt64 :=
  let s := alpVal f32 x * Rel.Column.pow10 e
  if s.abs < alpP53 then
    let d := s.round.toInt64.toUInt64
    if Rel.Column.alpDec d e f32 == x then some d else none
  else none

/-- The smallest exponent at which `x` is a decimal, `none` for a sentinel or for a value that is a
decimal at no exponent at all. -/
def alpOwn (f32 : Bool) (x : UInt64) : Option Nat :=
  if alpSentinel f32 x then none
  else (List.range 19).find? fun e => (alpDat f32 x e).isSome

/-- Block `b`'s exponent and each of its elements' `d`, `none` at an exception. The exponent is the
largest any of the block's elements needs and then **every** element is re-verified at it: raising
it is not harmless, `x * 10 ^ e` running out of mantissa, so a value exact at its own exponent can
still fall out here. -/
def alpBlockOf (f32 : Bool) (B w n b : Nat) (x : ByteArray) (own : Array (Option Nat)) :
    Nat × Array (Option UInt64) :=
  let lo := b * B
  let js := Array.range (min (lo + B) n - lo)
  let e := js.foldl (init := 0) fun acc j => max acc ((own[lo + j]!).getD 0)
  (e, js.map fun j =>
    if (own[lo + j]!).isNone then none
    else alpDat f32 (Rel.Column.bitsAt x ((lo + j) * w) w) e)

/-- The alp blob: `excBlob` ending in each block's exponent, its flag word saying whether an element is four bytes.
`Column.alpSects` reads this ladder back and `rust/src/coc.rs`'s `alp_layout` is the C's one copy of it. -/
def alpBlob (f32 : Bool) (B w n : Nat) (x : ByteArray) (bs : Array (Nat × Array (Option UInt64))) :
    ByteArray :=
  excBlob (if f32 then 1 else 0) B w bs.size x ((Array.range n).filter fun i => ((bs[i / B]!).2[i % B]!).isNone)
    (bs.foldl (init := ByteArray.empty) fun acc be => acc.push be.1.toUInt8)

/-- A dense payload of `w`-byte floats as `(metadata, pack, alp)`. Three passes, the first of them
the expensive one — up to nineteen trial round trips an element — because a block's exponent is not
known until every one of its elements has been asked for its own.

Every exception is packed as its block's minimum, i.e. residual zero. It therefore cannot widen the
pack, and what it wrongly contributes to a reduction is a constant the layer below subtracts back
out; `encode` recomputes that same minimum from the integers handed to it. -/
def alpEncodeAt (f32 : Bool) (x : ByteArray) (lg : Nat := Rel.Column.lgEnc) :
    ByteArray × ByteArray × ByteArray :=
  let w := if f32 then 4 else 8
  let n := x.size / w
  let own := (Array.range n).map fun i => alpOwn f32 (Rel.Column.bitsAt x (i * w) w)
  let bs := (Array.range ((n + 2 ^ lg - 1) / 2 ^ lg)).map fun b =>
    alpBlockOf f32 (2 ^ lg) w n b x own
  let ds := bs.foldl (init := ByteArray.empty) fun acc be =>
    let mn := be.2.foldl (init := (none : Option Int)) fun m d => match d with
      | none => m
      | some v => some (match m with | none => v.toInt64.toInt | some a => min a v.toInt64.toInt)
    let base := (Int64.ofInt (mn.getD 0)).toUInt64
    be.2.foldl (init := acc) fun a d => Rel.Column.pushBits a (d.getD base) 8
  let (metadata, pack) := encodeAt lg 8 ds false
  (metadata, pack, alpBlob f32 (2 ^ lg) w n x bs)

/-- The obligation is `alpDecode (alpEncode x) = x`, **byte for byte**, NaN payloads included: `0n`
comes back as `0n`, a second NaN stays distinct from it, `0w` and `-0w` keep their signs and `-0.0`
does not come back as `+0.0`. That is stronger than value equality and is the whole reason exactness
is decided on the bits.

Two names and one specification: `rust/src/coc.rs` exports a kernel per element width, so there is a Lean
declaration per C symbol, and both carry `alpEncodeAt` at the width. `Coc.encode` takes its width as
an argument instead because the integral encoder is one C symbol; the shape here follows the C. -/
@[extern "qlean_alp_encode_f64"]
def alpEncode64 (x : @& ByteArray) : ByteArray × ByteArray × ByteArray := alpEncodeAt false x

@[extern "qlean_alp_encode_f32"]
def alpEncode32 (x : @& ByteArray) : ByteArray × ByteArray × ByteArray := alpEncodeAt true x

/-- `encode` when its parts are fewer bytes than the `x.size / width * width` dense ones. -/
@[extern "qlean_coc_encode_below"]
def encodeBelow (width : USize) (x : @& ByteArray) : Option (ByteArray × ByteArray) :=
  let (m, p) := encode width x
  if m.size + p.size < x.size / width.toNat * width.toNat then some (m, p) else none

/-- `alpEncode64` when its parts are fewer bytes than the dense ones. -/
@[extern "qlean_alp_encode_below_f64"]
def alpEncodeBelow64 (x : @& ByteArray) : Option (ByteArray × ByteArray × ByteArray) :=
  let (m, p, a) := alpEncode64 x
  if m.size + p.size + a.size < x.size / 8 * 8 then some (m, p, a) else none

/-- `alpEncode32` when its parts are fewer bytes than the dense ones. -/
@[extern "qlean_alp_encode_below_f32"]
def alpEncodeBelow32 (x : @& ByteArray) : Option (ByteArray × ByteArray × ByteArray) :=
  let (m, p, a) := alpEncode32 x
  if m.size + p.size + a.size < x.size / 4 * 4 then some (m, p, a) else none

/-- The elements as raw bits, `elems`' counterpart on this constructor and the one place the block
starts are hoisted out of the loop. Every specification below is a fold over it. -/
def alpElems (metadata pack a : ByteArray) (n : USize) : List UInt64 :=
  let starts := Rel.Column.blockStarts metadata
  (List.range n.toNat).map (Rel.Column.alpBits metadata pack a starts)

/-- The dense payload an ALP column denotes: `n` little-endian elements. This is the inverse of
`alpEncode64` and the entry every kernel family written over dense floats reaches an ALP column
through — `Column.bytesOf` is that call. -/
@[extern "qlean_alp_decode_f64"]
def alpDecode64 (metadata pack a : @& ByteArray) (n : USize) : ByteArray :=
  (alpElems metadata pack a n).foldl (init := ByteArray.empty) fun acc v =>
    Rel.Column.pushBits acc v 8

@[extern "qlean_alp_decode_f32"]
def alpDecode32 (metadata pack a : @& ByteArray) (n : USize) : ByteArray :=
  (alpElems metadata pack a n).foldl (init := ByteArray.empty) fun acc v =>
    Rel.Column.pushBits acc v 4

/-- `alpElems` as `w`-byte elements, the payload `Column.get` reads an ALP column as at any fixed
width: the two C decoders at the widths ALP is the encoding for, the fold they implement otherwise.
One reader, so `Column.bytesOf` never declines a column `Column.get` reads and `~`'s element
fallback never sees one `Kernel.columnHash` cannot key. -/
def alpDecode (w : USize) (metadata pack a : ByteArray) (n : USize) : ByteArray :=
  if w == 4 then alpDecode32 metadata pack a n else if w == 8 then alpDecode64 metadata pack a n
  else (alpElems metadata pack a n).foldl (init := ByteArray.empty) fun acc v =>
    Rel.Column.pushBits acc v w.toNat

end Rel.Kernel.Coc

namespace Rel.Column

/-- The types Frame of Reference is the encoding *for*. `CLAUDE.md` settles that the encoded form is
the representation rather than a fast path, so this is not a policy about when it pays — it is which
types it is the right encoding for at all. Every exclusion is measured or structural:

* `boolean` is `bits`, one bit per element, which is already eight times less than q spends;
* `byte` and `char` are one byte, so the residual width is already the type width and the metadata
  per block is a net loss — `tools/coc/note.md` §5 has them at 0.98–1.02x across the board, measured
  when a block cost 25 bytes and so a 2.4% loss; at 33 it is 3.2% and the exclusion only holds
  harder. `CLAUDE.md` grants them explicitly;
* `real`, `float` and `datetime` are floats. Frame of Reference over raw IEEE bit patterns is
  lossless and shrinks nothing, patterns not clustering the way the values do; their encoding is
  `alpEncodes`, below;
* `symbol` has no fixed width. -/
def encodes : QAtomicType → Bool
  | .short | .int | .month | .date | .minute | .second | .time
  | .long | .timestamp | .timespan => true
  | _ => false

/-- The types ALP is the encoding for: q's three float types and no others. `real` is four bytes and
goes through the `_f32` kernels, `float` and `datetime` are eight and go through the `_f64` ones —
`QAtomicType.width` is what chooses, so `datetime` needs no case of its own here or anywhere below.

`datetime` is a float in q and not a separate thing: its payload is a `double` count of days, which
is a decimal on a tick like any price, so nothing about it wants a different encoding. -/
def alpEncodes : QAtomicType → Bool
  | .real | .float | .datetime => true
  | _ => false

end Rel.Column

namespace Rel.Ext.Enc
open Column

/-- The payload as dense bytes, whatever constructor holds it, and `none` at a type whose payload is
not fixed-width bytes at all. This is the form every kernel family outside this file is written over,
and the one place an encoded column is decoded for them: `.bytes` already is it, and `.foR` and
`.alp` go through their C decoders.

Not `Column.dense`, which reads the payload back through `Column.atoms` and boxes every element on the
way. That one stays where it is used, because `QLean/Kernel/Test.lean`'s round trip holds the C
*encoder* against the *Lean* reader, and routing it through a C decoder would make it C against C. -/
def bytesOf (t : QAtomicType) (n : USize) (e : Ext.Enc X) : Option ByteArray :=
  match e, t with
  | .bytes b, _ => some b
  | .foR metadata pack, t => t.width.map fun w =>
    Rel.Kernel.Coc.decode w.toUSize metadata pack n
  -- at every width `Enc.get` reads it at, not only the float ones: a width this declined left
  -- `~` comparing elements while `Kernel.columnHash` keyed every element as 0
  | .alp metadata pack a, t => t.width.map fun w =>
    Rel.Kernel.Coc.alpDecode w.toUSize metadata pack a n
  | _, _ => none

/-- The same atoms in the Frame-of-Reference form, or the column unchanged at a type `encodes`
declines. The width comes from `QAtomicType.width` rather than from a second table, so there is one
place that says how wide a `date` is.

**This is what a *result* is handed back in, and it is deliberately not what a column that arrives
is put into.** `Column.admit` is the second, and the split is measured rather than tidy: encoding a
million longs is a min/max scan and a bit-pack, which `xl+xl` pays inside its own 12.7 µs, while the
ALP exponent search is per element and up to nineteen trial round trips — 6.6 ms a million doubles,
five hundred times what the add it would follow costs. So a float result stays dense here and a float
column takes its encoded form where it enters, which is where it is read many times over. -/
def encode (t : QAtomicType) (n : USize) (e : Ext.Enc X) : Ext.Enc X :=
  -- a general column has no width and so lands on `none`
  match t.width with
  | some w =>
    if encodes t then
      match bytesOf t n e with
      | some b =>
        let (metadata, pack) := Rel.Kernel.Coc.encode w.toUSize b
        .foR metadata pack
      | none => e
    else e
  | none => e

/-- Whether the encoded form is smaller than the `n * w` dense bytes it replaces: the one size rule
for both encodings, `CLAUDE.md`'s "nothing is encoded that the encoding does not shrink". -/
def shrinks (w : Nat) (n : USize) (e : Ext.Enc X) : Bool :=
  match e with
  | .foR metadata pack => metadata.size + pack.size < n.toNat * w
  | .alp metadata pack blob => metadata.size + pack.size + blob.size < n.toNat * w
  | _ => true

/-- The fewest elements a column is encoded at. Below it the encoding cannot pay for its pass: a
short answer is read once, by the `each` that made it, and freed. Measured in `answer`'s doc. -/
def encodeMin : USize := 64

/-- The form a column a kernel **writes** is handed back in, as `admit` is the form one that enters
takes: an encoded answer is kept exactly when it `shrinks` the dense bytes it replaces and is decoded
otherwise, and a dense one is encoded under the same test. Every producer of an answer goes through
this and none through `encode` or `alpOf`, which stay unconditional so that a test can still reach an
encoded kernel on a three-element column.

Per column and not per block: the constructors hold one form a column, and a block already takes the
narrowest residual width its range allows, so all a 64-bit block costs over dense is its metadata —
and only the whole column's total against `n * w` says whether the narrow blocks paid that back. -/
def answer (t : QAtomicType) (n : USize) (e : Ext.Enc X) : Ext.Enc X :=
  match t with
  -- a boolean has no dense bytes to decode to: its bitmap or `u1` `foR` is kept as it is
  | .general | .boolean => e
  | t => match t.width, e with
    | some w, .bytes b => if n < encodeMin then e else
    -- ALP first at a float, as on entry: a float answer encoded with `encode` alone stayed dense, so
    -- `(1000+N?100000)%100` was dense where the same doubles read back from a file were ALP
    -- `shrinks` of `alpOf`, else of `encode`, decided by the encoder after its first pass
      if alpEncodes t then
        match (if w == 4 then Rel.Kernel.Coc.alpEncodeBelow32 b else Rel.Kernel.Coc.alpEncodeBelow64 b) with
        | some (m, p, a) => .alp m p a
        | none => e
      else if encodes t then
        match Rel.Kernel.Coc.encodeBelow w.toUSize b with
        | some (m, p) => .foR m p
        | none => e
      else e
    | some w, _ =>
      if shrinks w n e && encodeMin ≤ n then e
      else match bytesOf t n e with | some b => .bytes b | none => e
    | none, _ => e

end Rel.Ext.Enc


namespace Rel.Kernel.Coc

end Rel.Kernel.Coc

namespace Rel.Column

end Rel.Column

namespace Rel.Ext.Enc
open Column

/-- The column in ALP form, whatever constructor holds it, and `none` at a type ALP is not the
encoding for. Unconditional: `admit` is where the decline lives, and `QLean/Eval/Test.lean` forces
this so that the corpus reaches shapes — an empty column, a block that is all exceptions — a policy
would keep it away from. -/
def alpOf (t : QAtomicType) (n : USize) (e : Ext.Enc X) : Option (Ext.Enc X) :=
  if !alpEncodes t then none else
  match t.width, bytesOf t n e with
  | some w, some b =>
    let (metadata, pack, a) :=
      if w == 4 then Rel.Kernel.Coc.alpEncode32 b else Rel.Kernel.Coc.alpEncode64 b
    some (.alp metadata pack a)
  | _, _ => none

end Rel.Ext.Enc
