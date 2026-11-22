import Rel.Kernel.Value

/-! The part of `Rel.Kernel.Coc` the Rel kernels reach; `Rel.Kernel.Coc` imports it. -/


namespace Rel.Kernel.Coc

/-- Element `i` of a dense payload of `w`-byte elements as the value q holds, `Column.sext` of its bits: the reading
`Column.foRExc` gives a patch, and `toUInt64` of it is the `int64_t` a block minimum is stored as. The encoder orders
and subtracts keys as `Int64`, so no key is a `Nat` past a machine word. -/
def keyAt (w : Nat) (x : ByteArray) (i : Nat) : Int64 := Rel.Column.sext w (Rel.Column.bitsAt x (i * w) w)

/-- The element a block's cached sum skips, as the raw bits `Column.foRBits` answers. q's null is the
bottom of a signed type's range: the `w`-byte pattern with only its top bit set, sign-extended. One byte has none —
`byte` and `char` are q's unsigned pair — and takes `Int64.minValue`, which no zero-extended byte is; `COC_NUL`
in `rust/src/coc.rs` is the same choice for the same reason. -/
def sumNul (w : Nat) : UInt64 :=
  if w = 1 then Int64.minValue.toUInt64 else (Rel.Column.sext w ((1 : UInt64) <<< (8 * w - 1).toUInt64)).toUInt64

/-- Block `b`, of `B` elements, of a payload of `n` `w`-byte elements: its minimum key, its maximum key, the sum of the
elements that are not `sumNul w`, and the residual width the extremes' difference needs. The extreme
folds are seeded with the block's first element rather than with an identity, which is what makes them
total without a bound on `b` — an out-of-range block reads zeros through `bitsAt` and answers a width
of 0 instead of an empty minimum; the sum is seeded with `0`, which is what an empty block sums to.

The sum is here and not in a pass of its own because it is the same walk of the same block, which is
what makes it free in `rust/src/coc.rs`'s `encode_meta` too. -/
def blockOf (B w n b : Nat) (x : ByteArray) : Int64 × Int64 × UInt64 × Nat :=
  let lo := b * B
  let ks := (Array.range (min (lo + B) n - lo)).map fun j => keyAt w x (lo + j)
  let mn := ks.foldl min (keyAt w x lo)
  let mx := ks.foldl max (keyAt w x lo)
  let nul := sumNul w
  let s := ks.foldl (init := (0 : UInt64)) fun acc k =>
    if k.toUInt64 == nul then acc else acc + k.toUInt64
  (mn, mx, s, Rel.Column.widthFor (mx - mn).toUInt64.toNat)

/-- One block's residual bytes from the residuals themselves, laid out the way `Column.resAt` reads
them back: residual `j`'s low `w` bits at bits `[j * w, j * w + w)` of a little-endian bit stream,
byte `k` being the OR of the residuals whose fields it overlaps, shifted into place.

A block of `B` elements always occupies `B * w / 8` bytes even when it holds fewer than `B`, so a block
start is a prefix sum of the widths and is always a multiple of eight. The elements past the count
are encoded as a residual of 0 — `rust/src/coc.rs` reaches the same bytes by leaving its zeroed buffer
alone.

The bytes are one mapped list made an array once, not `B * w / 8` pushes: a push is `List.concat` to `decide`, so
the kernel built a block's pack in quadratic terms — 8 GB for one block at width 16, whatever the element count. -/
def packRes (B w : Nat) (res : Nat → UInt64) : ByteArray :=
  if w = 0 then ByteArray.empty else
  ⟨((List.range (B * w / 8)).map fun k =>
    (List.range' (8 * k / w) ((8 * k + 7) / w + 1 - 8 * k / w)).foldl (init := (0 : UInt8)) fun b j =>
      b ||| ((res j).toNat % 2 ^ w * 2 ^ (j * w) / 2 ^ (8 * k)).toUInt8).toArray⟩

/-- What `packRes` runs as: field `j`'s bits `m` (cut by `Column.ones`) moved into byte `k` by one word shift, where the
spec's `2 ^ (j * w)` and `2 ^ (8 * k)` are GMP numbers from the eighth byte on. -/
private def packResImpl (B w : Nat) (res : Nat → UInt64) : ByteArray :=
  if w = 0 then ByteArray.empty else
  ⟨((List.range (B * w / 8)).map fun k =>
    (List.range' (8 * k / w) ((8 * k + 7) / w + 1 - 8 * k / w)).foldl (init := (0 : UInt8)) fun b j =>
      b ||| (let m := res j &&& Rel.Column.ones w; let s := j * w
        if 8 * k ≤ s then (if s - 8 * k < 8 then (m <<< (s - 8 * k).toUInt64).toUInt8 else 0)
        else if 8 * k - s < 64 then (m >>> (8 * k - s).toUInt64).toUInt8 else 0)).toArray⟩

private theorem fieldByte_eq (w s k : Nat) (v : UInt64) :
    (v.toNat % 2 ^ w * 2 ^ s / 2 ^ (8 * k)).toUInt8 =
      (let m := v &&& Rel.Column.ones w
       if 8 * k ≤ s then (if s - 8 * k < 8 then (m <<< (s - 8 * k).toUInt64).toUInt8 else 0)
       else if 8 * k - s < 64 then (m >>> (8 * k - s).toUInt64).toUInt8 else 0) := by
  have hm : (v &&& Rel.Column.ones w).toNat = v.toNat % 2 ^ w := by
    rw [UInt64.toNat_and, Rel.Column.ones_eq, Nat.toUInt64_eq, UInt64.toNat_ofNat']
    apply Nat.eq_of_testBit_eq; intro t
    simp only [Nat.testBit_and, Nat.testBit_mod_two_pow, Nat.testBit_two_pow_sub_one]
    by_cases ht : t < 64
    · simp [ht, Bool.and_comm]
    · have := Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le v.toNat_lt (Nat.pow_le_pow_right (by decide) (by omega : 64 ≤ t)))
      simp [this]
  have hlt : (v &&& Rel.Column.ones w).toNat < 2 ^ 64 := UInt64.toNat_lt _
  rw [← hm]
  generalize v &&& Rel.Column.ones w = m at hlt ⊢
  apply UInt8.toNat_inj.1
  simp only [Nat.toUInt8_eq, UInt8.toNat_ofNat']
  split
  · obtain ⟨d, rfl⟩ : ∃ d, s = 8 * k + d := ⟨s - 8 * k, by omega⟩
    rw [Nat.pow_add, ← Nat.mul_assoc, Nat.mul_comm _ (2 ^ (8 * k)), Nat.mul_assoc,
      Nat.mul_div_cancel_left _ (Nat.two_pow_pos _), Nat.add_sub_cancel_left]
    split
    · have hs : (d.toUInt64).toNat % 64 = d := by simp only [Nat.toUInt64_eq, UInt64.toNat_ofNat']; omega
      rw [UInt64.toNat_toUInt8, UInt64.toNat_shiftLeft, hs, Nat.shiftLeft_eq, Nat.mod_mod_of_dvd _ (by decide : 2 ^ 8 ∣ 2 ^ 64)]
    · obtain ⟨e, rfl⟩ : ∃ e, d = 8 + e := ⟨d - 8, by omega⟩
      rw [Nat.pow_add, ← Nat.mul_assoc, Nat.mul_comm, ← Nat.mul_assoc, Nat.mul_mod_left]; rfl
  · obtain ⟨d, hd⟩ : ∃ d, 8 * k = s + d := ⟨8 * k - s, by omega⟩
    rw [hd]
    rw [Nat.pow_add, ← Nat.div_div_eq_div_mul, Nat.mul_div_cancel _ (Nat.two_pow_pos _), Nat.add_sub_cancel_left]
    split
    · have hs : (d.toUInt64).toNat % 64 = d := by simp only [Nat.toUInt64_eq, UInt64.toNat_ofNat']; omega
      rw [UInt64.toNat_toUInt8, UInt64.toNat_shiftRight, hs, Nat.shiftRight_eq_div_pow]
    · rw [Nat.div_eq_of_lt (Nat.lt_of_lt_of_le hlt (Nat.pow_le_pow_right (by decide) (by omega)))]; rfl

@[csimp] private theorem packRes_eq_packResImpl : @packRes = @packResImpl := by
  funext B w res; unfold packRes packResImpl; simp only [fieldByte_eq]

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
          (Rel.Column.pushBits acc pos.toUInt64 8, pos + 2 ^ lg * (b.2.2.2 % 128) / 8)).1
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

/-- Whether key `k` lies outside the `2 ^ d` keys from frame `f`, so that its block patches it: below `f`, or `k - f`
read unsigned has a bit at `d` or above. A shift and not `2 ^ d`, which is a big `Nat` at `d = 64`. -/
def outside (f : Int64) (d : Nat) (k : Int64) : Bool := k < f || d < 64 && (k - f).toUInt64 >>> d.toUInt64 != 0

/-- Whether the writer patches key `k` of a block of frame `f` and width byte `d`: it lies `outside` the frame, or the
block holds a null (`d`'s bit 7) and `k` sits at the null's code, the top residual `ones (d % 128)`, which no value may
read as. `lst` is whether the column can carry a patch list at all (below `2 ^ 32` rows). -/
def patched (lst : Bool) (f : Int64) (d : Nat) (k : Int64) : Bool :=
  outside f d k || lst && decide (128 ≤ d) && (k - f).toUInt64 == Rel.Column.ones (d % 128)

/-- How many of the block's keys `ks` frame `f` at width `d` patches. -/
def npatch (ks : Array Int64) (f : Int64) (d : Nat) : Nat := (ks.filter (outside f d)).size

/-- The frame at width `d`: of `mn` and the keys, the one patching fewest, the lowest of those. The incumbent's count
rides in the accumulator, so each candidate costs one `npatch`, its own. -/
def frameAt (ks : Array Int64) (mn : Int64) (d : Nat) : Int64 :=
  (ks.foldl (init := (mn, npatch ks mn d)) fun (f, nf) k =>
    let nk := npatch ks k d
    if nk < nf || (nk == nf && k < f) then (k, nk) else (f, nf)).1

/-- The bytes block `ks` costs at width `d`, at `w` bytes an element: its residual bits rounded up to bytes, and
`2 + w` a patch (its `u16` position and the element). -/
def cost (ks : Array Int64) (mn : Int64) (w d : Nat) : Nat :=
  (ks.size * d + 7) / 8 + npatch ks (frameAt ks mn d) d * (2 + w)

/-- A block's frame key and residual width: the width of `0 .. W` that `cost` is least at, the narrower on a tie, and
its `frameAt`; `W`, the bit length of `mx - mn`, patches nothing, and a wider width only costs more. Where `patch` is
off — ALP's integers, whose exceptions are its own blob's — the width is `W` and the frame `mn`. -/
def planOf (patch : Bool) (ks : Array Int64) (mn mx : Int64) (w : Nat) : Int64 × Nat :=
  if patch then
    -- the best width's cost rides in the accumulator: recomputing it is a `frameAt` search per width
    let d := ((List.range (Rel.Column.widthFor (mx - mn).toUInt64.toNat + 1)).foldl (init := (0, cost ks mn w 0))
      fun (d, cd) c =>
        let cc := cost ks mn w c
        if cc < cd then (c, cc) else (d, cd)).1
    (frameAt ks mn d, d)
  else (mn, Rel.Column.widthFor (mx - mn).toUInt64.toNat)

/-- Block `b`, of `B` elements, of a nullable column (`atom+1`, owner decision K) where it holds a null: `x` its `n`
`w`-byte elements, row `i` the null where `Column.bitAt nul i`. Its base, maximum and `blockOf`'s sum are taken over the
rows that are not null (`0`, `0`, `0` where every row is); its width byte is the range's `widthFor`, one bit wider where
a value sits at the top residual `2 ^ d - 1` (so no value reads as the null), plus `nulAt`'s bit 7. A block whose range
is all `2 ^ 64` keys cannot widen: there `encodeAt` patches the value at the top residual (`patched`). -/
def nulBlock (B w n b : Nat) (x nul : ByteArray) : Int64 × Int64 × UInt64 × Nat :=
  let lo := b * B
  let ks := ((Array.range (min (lo + B) n - lo)).filter fun j => !Rel.Column.bitAt nul (lo + j)).map
    fun j => keyAt w x (lo + j)
  let mn := ks.foldl min (ks.getD 0 0)
  let mx := ks.foldl max (ks.getD 0 0)
  let s := ks.foldl (init := (0 : UInt64)) fun acc k => if k.toUInt64 == sumNul w then acc else acc + k.toUInt64
  let d := Rel.Column.widthFor (mx - mn).toUInt64.toNat
  (mn, mx, s, 128 + if !ks.isEmpty && d < 64 && (mx - mn).toUInt64 == Rel.Column.ones d then d + 1 else d)

/-- The writer's block step, block `b` of `n` `w`-byte elements at blocks of `2 ^ lg`, row `i` null where
`Column.bitAt nul i`: `(base, max, sum, frame, width byte)`. A block holding a null is `nulBlock`'s, its frame its base;
any other is `blockOf`'s extremes and sum with `planOf`'s frame and width. Which blocks reserve the null's top residual
is decided here and nowhere else. -/
def planBlock (lg w n : Nat) (patch : Bool) (x nul : ByteArray) (b : Nat) : Int64 × Int64 × UInt64 × Int64 × Nat :=
  let lo := b * 2 ^ lg
  if (Array.range (min (lo + 2 ^ lg) n - lo)).any fun j => Rel.Column.bitAt nul (lo + j) then
    let (mn, mx, s, d) := nulBlock (2 ^ lg) w n b x nul
    (mn, mx, s, mn, d)
  else
  let (mn, mx, s, _) := blockOf (2 ^ lg) w n b x
  let (f, d) := planOf patch ((Array.range (min (lo + 2 ^ lg) n - lo)).map fun j => keyAt w x (lo + j)) mn mx w
  (mn, mx, s, f, d)

/-- `encode` at blocks of `2 ^ lg` elements: the model every theorem about the encoder is stated
over, at any `lg` the layout admits, `6 .. 16`. `encode` is this at `Column.lgEnc`. The one writer of null and non-null
columns: `nul` the bitmap of the null rows (a bit past it is `0`), empty for a column with none.

Block `b` is `planBlock`'s base, frame `f` and width byte `d` (its residual width `d % 128`): an element `patched`
holds — outside the frame, or a value at the null's code in a block holding a null — is patched: its residual 0, its bits in the patch list `excBlob` lays after the residuals — a null row
takes the top residual `2 ^ d - 1`, so the null is tested on the block (`Column.foRNul`) and never decoded, and every
other is its key less `f` at `d` bits. The patch list exists where a block patches, its frames (`f - mn` a block) where
one is not its minimum; `rust/src/enc.rs`'s `for_blk`, `nul_meta` and `pack_exc_blk` write the same bytes. A column of
`2 ^ 32` elements or more patches nothing: the list's block offsets are `u32`. -/
def encodeAt (lg : Nat) (width : USize) (x : ByteArray) (patch : Bool := true) (nul : ByteArray := .empty) :
    ByteArray × ByteArray :=
  let w := width.toNat
  let n := x.size / w
  -- the block size once as a shift, not a `2 ^ lg` at every element
  let B := 1 <<< lg
  let blk := planBlock lg w n (patch && decide (n < 2 ^ 32)) x nul
  let bs := (Array.range ((n + B - 1) / B)).map blk
  -- every per-element read of a plan goes to `bs`, never `blk`: each `blk` call reruns the block's width search
  let pack := (bs.foldl (init := (ByteArray.empty, 0)) fun (acc, b) (_, _, _, f, d) =>
    let lo := b * B
    (acc ++ packRes B (d % 128) fun j =>
      if lo + j < n && Rel.Column.bitAt nul (lo + j) then Rel.Column.ones (d % 128) else
      (if lo + j < n && !patched (decide (n < 2 ^ 32)) f d (keyAt w x (lo + j)) then keyAt w x (lo + j) - f else 0).toUInt64,
      b + 1)).1
  let exc := (Array.range n).filter fun i =>
    !Rel.Column.bitAt nul i &&
      patched (decide (n < 2 ^ 32)) (bs.getD (i / B) default).2.2.2.1 (bs.getD (i / B) default).2.2.2.2 (keyAt w x i)
  let fs := bs.map fun (mn, _, _, f, _) => (f - mn).toUInt64
  let frm := fs.any (· != 0)
  let tail := if exc.size = 0 then ByteArray.empty else
    excBlob (w.toUInt64 ||| if frm then 256 else 0) B w bs.size x exc
      (if frm then fs.foldl (init := ByteArray.empty) fun acc v => Rel.Column.pushBits acc v 8 else ByteArray.empty)
  (foRMeta lg (sumNul w) n (bs.map fun (mn, mx, s, _, d) => (mn.toUInt64, mx.toUInt64, s, d)), pack ++ tail)

/-- A dense payload of `width`-byte elements as `(metadata, pack)`.

The obligation is `Column.atoms t (.foR n metadata pack) = Column.atoms t (.bytes x)` — encoding is a
choice of representation and owes nothing else, which is why the C comment on `qlean_coc_encode_i64`
states the round trip and not the bytes.

`width` is `QAtomicType.width`, and only 1, 2, 4 and 8 are legal: the kernels are instantiated at
those four element types, `Column.encode` below refuses everything else, and the C aborts rather than
answering an empty pair, which would drop a column's contents silently. `nul` is `encodeAt`'s: the bitmap of the
null rows, empty for a column with none. -/
@[extern "qlean_coc_encode"]
def encode (width : USize) (x : @& ByteArray) (nul : @& ByteArray := .empty) : ByteArray × ByteArray :=
  encodeAt Rel.Column.lgEnc width x true nul

/-- The `u1` Frame of Reference column of the `n` booleans `p`, the form every boolean writer answers: `encodeAt` of
their 0/1 bytes, unpatched, so a mixed block's residuals are its bitmap at width 1 and an all-0 or all-1 block is
width 0 at base 0 or 1 with no residual. `rust/src/ffi.rs`'s `Sink::bools` writes it a block at a time. -/
def bools (n : Nat) (p : Nat → Bool) : ByteArray × ByteArray :=
  encodeAt Rel.Column.lgEnc (USize.ofNat32 1 (by decide)) (Rel.Column.packIds 8 n fun i => (p i).toNat) false

/-- The first `n` bits of the bitmap `b` as the `u1` column `bools` lays out, a bit past `b` being `0`: the writer a
kernel whose answer is a bitmap hands it to, so no boolean answer is a bitmap `Enc`. -/
def boolsOf (n : USize) (b : @& ByteArray) : ByteArray × ByteArray := bools n.toNat (Rel.Column.bitAt b)


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
declines one on top of this. `Verify.foRStd_iff` is `Verify.FoRWF`, `Verify.foRWF_encodeAt` that
`encode` establishes it, and `rust/src/coc.rs`'s `coc_std` is the same test. -/
def foRStd (n : USize) (md pk : ByteArray) : Bool :=
  Rel.Column.nblk md == (n.toNat + Rel.Column.blk md - 1) / Rel.Column.blk md
    && (pk.size == Rel.Column.blockStart md (Rel.Column.nblk md)
      || (foRTail (Rel.Column.nblk md) pk (Rel.Column.blockStart md (Rel.Column.nblk md))).map
          (Rel.Column.blockStart md (Rel.Column.nblk md) + ·) == some pk.size)
    && (List.range (Rel.Column.nblk md)).all fun b => Rel.Column.widthAt md b ≤ 64

/-- The elements as raw bits. Every specification below is a fold over this, `decode` included, so it
is the one place that mentions `base`, the block starts and the residual layout. -/
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







/-- The elements as raw bits, `elems`' counterpart on this constructor and the one place the block
starts are hoisted out of the loop. Every specification below is a fold over it. -/
def alpElems (metadata pack a : ByteArray) (n : USize) : List UInt64 :=
  let starts := Rel.Column.blockStarts metadata
  (List.range n.toNat).map (Rel.Column.alpBits metadata pack a starts)

/-- The dense payload an ALP column denotes: `n` little-endian elements. This is the inverse of
`alpEncode64` and the entry every kernel family written over dense floats reaches an ALP column
through — `Column.bytesOf` is that call. -/
def alpDecode64 (metadata pack a : @& ByteArray) (n : USize) : ByteArray :=
  (alpElems metadata pack a n).foldl (init := ByteArray.empty) fun acc v =>
    Rel.Column.pushBits acc v 8

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



end Rel.Column

namespace Rel.Ext.Enc
open Column

/-- The payload as dense bytes, decoded once from its blocks, and `none` at a type whose payload is not fixed-width:
the form a kernel family outside this file that has not yet been rewritten over blocks reads. -/
def bytesOf (t : QAtomicType) (n : USize) (e : Ext.Enc X) : Option ByteArray :=
  match e, t with
  | .foR metadata pack, t => t.width.map fun w =>
    Rel.Kernel.Coc.decode w.toUSize metadata pack n
  -- a `pos` column is a long since `Enc.WF` admits it (decision M); this old layer reads it as its `n` positions
  | .pos, .i64 => some (((List.range n.toNat).map Nat.toUInt64).foldl (fun acc v => Column.pushBits acc v 8) .empty)
  | _, _ => none

/-- The `foR` column of the dense payload `b`, `w` bytes an element: where every producer of a fixed-width column
(a literal, `ofAtoms`, `blank`, a test) enters the one encoding. -/
def ofBytes (w : Nat) (b : ByteArray) : Ext.Enc X :=
  .foR (Rel.Kernel.Coc.encode w.toUSize b).1 (Rel.Kernel.Coc.encode w.toUSize b).2
end Rel.Ext.Enc

namespace Rel.Kernel

/-- `n` bits from `f`, packed LSB first with the tail of the last byte left zero, because
trailing set bits make two equal boolean vectors compare unequal under
`~`. One definition for the bit-payload kernels (four in `Structural`, `bitsOfFoR`
here), which differ only in `f`. -/
def packOf (n : Nat) (f : Nat → Bool) : ByteArray :=
  (List.range ((n + 7) / 8)).foldl (init := ByteArray.empty) fun acc k =>
    acc.push ((List.range 8).foldl (init := (0 : UInt8)) fun byte t =>
      if k * 8 + t < n && f (k * 8 + t) then byte ||| (1 <<< t.toUInt8) else byte)

/-- A boolean `foR` (`u1`) as a bitmap: bit `i` is element `i`'s low bit, which is what
`Enc.raw` reads at a boolean, and a row past the blocks is `0`. The C copies a width-1, frame-0 block's residual
words whole — they already are its bitmap — and builds any other block in one block of L1 scratch. -/
def bitsOfFoR (metadata pack : @& ByteArray) (n : USize) : ByteArray :=
  let starts := Column.blockStarts metadata
  packOf n.toNat fun i =>
    i < Column.blk metadata * Column.nblk metadata && (Column.foRBits metadata pack starts i).toNat % 2 == 1

/-- A boolean payload as its bitmap, whichever of the two forms `Enc.WF .u1` admits it is in (a `u1` `foR`
through `bitsOfFoR`); `none` at any other type or form. The one boolean read every bitmap consumer goes through,
here below `Elementwise` so that its operand readers take a boolean through it too. -/
def boolBits (t : QAtomicType) (n : USize) (e : Ext.Enc X) : Option ByteArray :=
  match t, e with
  | .u1, .foR m p => some (bitsOfFoR m p n)
  | _, _ => none

end Rel.Kernel

namespace Rel

namespace Ext.Enc
open Column

/-- `n` elements of `t`, all zero bits, for every `n`: the value a failed `need`'s model answers. It
needs no bound because a replicated array has the size asked for. Here, after `Coc.bools`, because a
boolean is a `u1` `foR`. -/
def blank (t : QAtomicType) (n : USize) : Ext.Enc X :=
  match t, t.width with
  | .general, _ => .gen (Array.replicate n.toNat default)
  | .u1, _ => .foR (Kernel.Coc.bools n.toNat fun _ => false).1 (Kernel.Coc.bools n.toNat fun _ => false).2
  | _, some w => ofBytes w ⟨Array.replicate (n.toNat * w) 0⟩
  | _, none => .gen #[]

/-- The payload holding exactly these atoms at `t`, count `as.size`, or `none` if one of them is not
at `t`. Only the payload, because the header is the caller's arguments: `.vector t as.size e none`.
The caller decides what a mismatch means — `Eval.vectorOf` answers with a general list, which is q's
own behaviour — so this never coerces. -/
def ofAtoms (t : QAtomicType) (as : Array QAtom) (h : t ≠ .general := by first | decide | assumption) :
    Option (Ext.Enc X) :=
  if as.all (·.type == t) then match t with
    | .general => absurd rfl h
    | .u1 => some (.foR (Kernel.Coc.bools as.size fun i => (as[i]?.map boolOf).getD false).1
        (Kernel.Coc.bools as.size fun i => (as[i]?.map boolOf).getD false).2)
    | t => match t.width with
      | some w =>
        some (ofBytes w (as.foldl (init := ByteArray.emptyWithCapacity (as.size * w))
          fun acc a => pushBits acc (bitsOf a) w))
      | none => none
  else none

end Ext.Enc

namespace Column
open Ext.Enc


end Column

namespace Ext.QValue



end Ext.QValue

end Rel
