module

public import Rel.Kernel.Need

-- exposed: every def body is a spec a downstream `rfl`/`decide`/`simp` may unfold (PLAN W.8)
@[expose] public section

/-! The part of `Rel.Value` the Rel kernels reach; `Rel.Value` imports it. -/


namespace Rel

/-- `Sum` equality decided through `Sum.elim`, whose motive does not mention the two sides. Core's derived
`instDecidableEqSum` matches on both with a motive `Decidable (a = b)`, and under `decide +kernel` over a kernel's answer
the kernel copies that motive with both answers inside it at every step: a scatter pair that reduces in 2 s ran 166 s and
failed (`expr_eq_fn` 48%, its hash cache 30%, `level ==` 19%). -/
instance (priority := high) instDecidableEqSumElim {α β : Type _} [DecidableEq α] [DecidableEq β] :
    DecidableEq (α ⊕ β) := fun a b =>
  decidable_of_iff (Sum.elim (fun x => Sum.elim (fun y => decide (x = y)) (fun _ => false) b)
    (fun x => Sum.elim (fun _ => false) (fun y => decide (x = y)) b) a = true) (by cases a <;> cases b <;> simp)

/-- The element type of a column. The constructor index is the tag the Rust kernels read: the fixed-width
types come first, so `u1`..`i8` (0..8) are `crate/src/key.rs`'s `SK_*` kinds, then `sym`, `date` (i32 days),
`datetime` (i64 ns) and `general`. `code` gives q's type code. `general` is q's type 0, a list of any values;
q has no type-0 atom, so `general` is a column type with no atom value: a function that reads or builds an
atom (`atomOfBits`, `Column.ofAtoms`) takes `t ≠ .general`. A general list's null is not a function of its
type either: it depends on the value (its first item's typed null, its empty vector, or `()`). -/
inductive QAtomicType
  | u1 | u8 | i16 | i32 | i64 | f32 | f64 | char | i8
  | sym | date | datetime
  | general
  deriving Repr, DecidableEq, Inhabited, Hashable

namespace QAtomicType

/-- Bytes per element **in the IPC wire format and in splayed column files** — deliberately not the
in-memory width. `boolean` is one byte on the wire and one *bit* in memory, so `Column` answers for
it before ever consulting this; anything reading a `Column` through `width` is a bug. A symbol is
its 8-byte id in its column's dictionary, and a general list's elements are values,
not bytes. -/
def width : QAtomicType → Option Nat
  | u1 | u8 | char | i8 => some 1
  | i16 => some 2
  | i32 | f32 | date => some 4
  | i64 | f64 | datetime | sym => some 8
  | general => none

end QAtomicType

namespace Bits

def f64IsNaN (b : UInt64) : Bool := (b >>> 52) &&& 0x7ff == 0x7ff && b &&& 0xfffffffffffff != 0
def f32IsNaN (b : UInt32) : Bool := (b >>> 23) &&& 0xff == 0xff && b &&& 0x7fffff != 0

end Bits

/-- A word of the atom `t` the language never holds (PLAN R7, decision G): at `f32`, `f64` a NaN or the negative
    zero, none at any other atom. Where a float word is produced it is normalised to one zero; a NaN has no row. -/
def QAtomicType.nonCanonical : QAtomicType → UInt64 → Bool
  | .f64, b => Bits.f64IsNaN b || b == 0x8000000000000000
  | .f32, b => Bits.f32IsNaN b.toUInt32 || b.toUInt32 == 0x80000000
  | _, _ => false

/-- A q atom. One constructor per atomic type so that no ill-typed atom is representable;
the payload is the raw wire value, including null and infinity sentinels. -/
inductive QAtom
  | u1 : Bool → QAtom
  | u8 : UInt8 → QAtom
  | i16 : Int16 → QAtom
  | i32 : Int32 → QAtom
  | i64 : Int64 → QAtom
  | f32 : UInt32 → QAtom
  | f64 : UInt64 → QAtom
  | char : UInt8 → QAtom
  | i8 : Int8 → QAtom
  /-- A symbol as its id: its position in the sorted, distinct dictionary beside its column (PLAN 8.3). -/
  | sym : UInt64 → QAtom
  | date : Int32 → QAtom
  | datetime : Int64 → QAtom
  deriving Repr, Inhabited

namespace QAtom

/-- q's comparison tolerance (code.kx.com/q/basics/precision): two floats are equal when they are
closer than `2^-43` of the smaller magnitude. Measured on q 4.1: `1f=1f+2 xexp -43` and
`(1f+2 xexp -43)=1f` are `0b`, `1f=1f-2 xexp -44` and `1f=(1f+2 xexp -43)-2 xexp -52` are `1b` —
the strict `<` and the smaller side, where the page's "does not exceed … the larger" answers `1b` to
the first. q's own test is an "efficient approximation" of this: on a million pairs drawn within
`2^-42` of each other it disagrees on 0.6%, every one within 0.1% of the threshold, and no closed
form of the two sizes, strict or not, reproduced it. Opposite signs, a NaN and an infinity all fail
the `<` by themselves, and zero equals only zero. -/
def tolerant (x y : Float) : Bool :=
  (x - y).abs < Float.ofBits 0x3D40000000000000 * (if x.abs < y.abs then x.abs else y.abs)

end QAtom

/-- The cell a marked value keeps its index in, built when the cell is made. In C because the
builder, `Kernel.Index.build`, sits above this module and is reached through the slot it registers
at initialisation; a cell made before that keeps its value and builds on its first lookup. -/
opaque IndexCell.Pointed : NonemptyType
def IndexCell : Type := IndexCell.Pointed.type

namespace Ext

mutual

/-- A q value, typed at run time as q's `K` is. `vector` carries its element type and its length in a
header as a q vector does: the payload is untyped bytes, the header's `t` is what says how wide an
element is and how to read it, and `Enc.atoms` is the only way back to atoms. An element of the wrong
type is not representable — `Column.atoms_type` proves it. What remains as an external condition is
that the payload's shape agrees with the header; `Enc.WF` states that, and `QValue.WFAt` on a value.

`vector` is every list, a general one included: a general list is `.vector .general xs.size (.gen xs)`,
which the pattern `QValue.general` names. One constructor, so a list has one representation; a header
the payload disagrees with is `Enc.mismatch`. -/
inductive QValue (X : Type)
  | atom : QAtom → QValue X
  /-- `t` and `n` are read, never inferred from the payload — `⌈n/8⌉` bytes, a block count or a pack
  at width `w` do not determine `n`. `attr` is the attribute, at the wire's code 1 to 4, and the cell
  holding the index q builds when it applies it, `none` for no attribute; a general list's mark is
  here too, and an enumeration's is on its indices. Set through `QValue.mark`, read through
  `QValue.attrCell`. -/
  | vector : (t : QAtomicType) → (n : USize) → (enc : Enc X) → (attr : Option (UInt8 × IndexCell)) → QValue X
  /-- The `Bool` is q's sorted dictionary, type 127: measured, it is not the key's `` `s `` —
  `` -8!(`s#`a`b)!1 2 `` writes 99, and `-9!` of a 127 over a bare key keeps the key bare. -/
  | dict : QValue X → QValue X → (sorted : Bool) → QValue X
  | table : QTable X → QValue X
  /-- A keyed table: a dictionary whose key and value are both tables. The implicit `IndexCell` holds
  the key-row index (`Index.keys`), built on the table's first lookup or append and kept and extended
  from then on; a construction goes through `QValue.key`. The `Bool` is `dict`'s: q's sorted
  dictionary, `` `s#kt ``, which no flag of either table says. -/
  | keyed : QTable X → QTable X → (sorted : Bool) → {_ix : IndexCell} → QValue X
  /-- A general list whose elements are all vectors of one type, laid out as **one** payload and
  the boundaries that cut it: `string`'s answer, `flip`'s rows, and every `each` over a string
  family. The fields are the whole payload's, its header the element type and the total element count;
  the elements it denotes are dense vectors over `.bytes <slice>`, and `slicesExpand` is what
  builds them where something insists on having them.

  It exists because a per-element **Lean loop** is the floor under all of those, not the objects
  the loop allocates. Measured on this machine at a million elements: `Array.push` of an unboxed
  `Nat` is 73ms, `ByteArray.push` 126ms, and a `QValue.vector` over one *shared* payload 99ms,
  against the 0.23ns an element a C kernel spends on `xf+xf`. So the answer has to stay one
  payload and the loop that would cut it into a million values has to not run. -/
  | slices : (t : QAtomicType) → (n : USize) → (enc : Enc X) → (attr : Option (UInt8 × IndexCell)) →
      Array Nat → QValue X
  /-- Functions and their relatives, wire types 100–112, kept as raw decoded components.
  The checker treats these as `dynamic` until the lambda's source can be re-parsed. -/
  | func : Int8 → Array (QValue X) → QValue X
  /-- A q error (wire type −128), carrying the error text without its leading backtick. -/
  | err : String → QValue X
  /-- An enumeration, q's types ±20: the global named `domain` indexed by `ix`, a `long` atom or a
  `long` vector. The name, not q's session code, is the identity (`Prim.Ty.enum`), and what an
  index denotes is read from the global at each use, because `` `d?x `` extends the domain in place
  under the enumerations already built over it.

  The indices are an ordinary `long` column and so encoded like one: they lie in `[0, count d)`,
  which frame-of-reference packs to the domain's bit width, where `int` would only halve it. -/
  | enum : String → QValue X → QValue X
  /-- A value of the extension `X`, atom or column, which rel knows nothing about: qlean's guid. Last, so the
  tags of the nine constructors before it and every field layout are unchanged. -/
  | ext : X → QValue X
  deriving Inhabited

/-- A q table: column names paired with equal-length column vectors, and the attribute byte q holds on
the table itself (`62 0N`: `0` none, then `` `s `` `` `u `` `` `p `` `` `g ``), which no column says:
`-9!` of `62 02` answers a table whose `attr` is `` `u `` with every column bare. -/
inductive QTable (X : Type)
  -- the byte is here, not on `QValue.table`, because `keyed` holds two tables and q marks either one
  -- (`` `s#kt `` the key, `asc kt` the value), so one field serves all three places a table sits
  | mk : Array String → Array (QValue X) → (attr : UInt8) → QTable X
  deriving Inhabited

/-- A vector's payload, one constructor per layout. No constructor stores the element count: it is
the header's `n` on `QValue.vector`, one source for it. -/
inductive Enc (X : Type)
  /-- Frame of Reference: the elements in blocks of `blk = 2 ^ lg` (64 .. 65536, `lg` read from the
  trailer), each block storing its minimum and the
  bit width of `x - base`, and the residuals bit-packed at that width. What it buys is not memory
  but that a reduction can run *on this form*: `min` and `max` read only the metadata, a predicate
  skips a block whose whole range falls on one side, and `x + k` shifts the metadata and leaves the
  residuals alone. `tools/coc/note.md` §5 measures all of it against q.

  `metadata` is 33 bytes per block and a 24-byte trailer -- `base : Int64[nblk]` at 0, `maxv` at
  `8 * nblk`, `off : UInt64[nblk]` at `16 * nblk`, `bsum : Int64[nblk]` at `24 * nblk`, then
  `sumnul : Int64` at `32 * nblk`, `sumn : UInt64` at `32 * nblk + 8`, `lg : UInt64` at `32 * nblk + 16` and
  `width : UInt8[nblk]` at `32 * nblk + 24` -- and it is a `ByteArray` rather than the `Array Nat` a symbol column's offsets
  use because the kernels in `rust/src/coc.rs` read it in place as `int64_t *` and `uint8_t *`. That is a
  different reason from the one `Array UInt64` was rejected for there, and it is the reason that
  applies: `offs` never crosses the FFI, `metadata` is defined by it.

  `maxv`, `off` and `bsum` are caches and the denotation never reads them. `maxv` is what lets a
  predicate decide a whole block, and `base + 2 ^ width - 1` cannot replace it, being only an upper
  bound; `off` is the prefix sum of `blk * width / 8`, since every block reserves room for a full `blk`
  residuals so that a block always starts on a multiple of 8 bytes. Keeping them out of `atoms`
  costs nothing and keeps the wrap that `off : UInt64` would reintroduce out of the round trip --
  the same reason a symbol column's offsets are `Nat`.

  `bsum` is the block's elements added up with `Int64` wrapping, skipping the ones equal to `sumnul`,
  and it is what makes `sum` O(nblk) where the residuals it would otherwise read make it O(n) -- 977
  adds at a million elements rather than a million, which puts `sum` where `min` and `max` already
  are. **A sum is only a sum relative to two things, and the trailer carries both.** The first is the
  null it skipped: this constructor does not know its element type, the same bytes are `long` or
  `int` or `short` depending on the tag the `QValue` around it carries, and each of those skips a
  different value, so `sumnul` names the one these sums used and a reduction at any other null
  recomputes. `0` is no type's null and marks metadata whose sums were never filled in, which is what
  a kernel that builds an encoded column and cannot cheaply maintain them leaves behind. The second
  is the count: `Kernel.Structural.appendFoR` answers a longer column with the metadata of a shorter
  one, so `sumn` says how many elements these sums covered and a column of any other length
  recomputes. A `float` never reaches either test: over a float this encoding is over raw IEEE bits,
  whose total is not the column's total in any domain, and a float is declined before the
  question is asked.

  The element count is the header's: `nblk` only bounds it to a multiple of `blk`. Every fixed-width
  type is held here and nowhere else (one encoding, doc/rel-architecture.zh.typ §4): a literal, a
  kernel's answer and a file's column alike, a `float` as its stored bits. -/
  | foR : (metadata : ByteArray) → (pack : ByteArray) → Enc X
  /-- A general list, q's type 0: its elements as values, under the header type
  `QAtomicType.general`: the pattern `QValue.general`. Under an atom type it is a mismatch,
  `Column.mismatch`, as a typed payload under `general` is. -/
  | gen : Array (QValue X) → Enc X
  /-- The row positions `0 … n-1` of an `i64` column, `n` the header's: element `i` is `i`, and nothing is stored, in
  memory or on disk (PLAN 6.13). A kernel reads it as its loop index, never as a materialised `til n`. A kernel's
  answer is `pos` only where its arguments' forms say so, never because the values happen to be positions. `WF`
  admits it at no type until no executable reader is left that needs a dense payload (6.13b).

  Nullary, so in Lean's ABI it is the scalar `lean_box(4)`, its tag, which `crate/src/blocks.rs`'s `POS` names. -/
  | pos : Enc X
  deriving Inhabited

end

end Ext

/-- rel's own values, at no extension: `Empty` has no value, so a `match` over them needs no `ext` arm. -/
abbrev QValue := Ext.QValue Empty
abbrev QTable := Ext.QTable Empty
abbrev Enc := Ext.Enc Empty

-- `Rel.QValue.atom` … as aliases of the family's constructors, so rel's code names them as before
export Ext (QValue.atom QValue.vector QValue.dict QValue.table QValue.keyed QValue.slices QValue.func QValue.err
  QValue.enum QValue.ext QTable.mk Enc.foR Enc.gen)

/-- What a rel function that recurses through `gen`, `dict` or `table` must do at an `ext`; a field is added when
another such function must. -/
class ValueExt (X : Type) where
  /-- q's `~` on two extension values. -/
  identical : X → X → Bool

instance : ValueExt Empty := ⟨nofun⟩

namespace Column

/-- What `bitsAt` runs as: the same bytes ORed at the same shifts, with the four widths a
`QAtomicType` actually has written out. What that buys is the per-byte `8 * w` and its
`Nat.toUInt64` -- two boxed-`Nat` calls of the twelve a byte costs -- becoming a literal, and the
loop's own `Nat.decEq` and `Nat.sub` going away entirely. The bounds test stays inside each byte,
so a short payload still reads `0` past its end exactly as the body says. Widths outside the four
take the general fold, which is the body's equation with the recursion turned into `Nat.fold`.

The element width is the parameter and the switch on it is hoisted out of the loop, which is
`rust/src/coc.rs`'s own shape for the same reason: each width becomes its own straight-line read. -/
def bitsAtImpl (b : ByteArray) (o w : Nat) : UInt64 :=
  let g := fun k => (if h : o + k < b.size then b[o + k] else 0).toUInt64
  match w with
  | 1 => g 0
  | 2 => g 0 ||| g 1 <<< 8
  | 4 => g 0 ||| g 1 <<< 8 ||| g 2 <<< 16 ||| g 3 <<< 24
  | 8 => g 0 ||| g 1 <<< 8 ||| g 2 <<< 16 ||| g 3 <<< 24 |||
         g 4 <<< 32 ||| g 5 <<< 40 ||| g 6 <<< 48 ||| g 7 <<< 56
  | w => Nat.fold w (init := 0) fun k _ acc => acc ||| g k <<< (8 * k).toUInt64

/-- `w` little-endian bytes at `o`, as raw bits. A read past the end answers `0` rather than
panicking: callers are bounded by `count`, and the decoders that build a `Column` validate lengths
before it ever gets here.

Recursion on `w` rather than a fold over `List.range w`, and a bounds test rather than `b[o + k]?`:
the two are the same equation, but the fold allocated a cons cell and a boxed `Option` per byte, and
this is the read every element of every column goes through. Measured on a profile of `key dd`,
`List.foldl` here was 8.2% of cycles and `List.range` under it a further 4.0%. -/
@[implemented_by bitsAtImpl]
def bitsAt (b : ByteArray) (o : Nat) : Nat → UInt64
  | 0 => 0
  | w + 1 =>
    bitsAt b o w ||| ((if h : o + w < b.size then b[o + w] else 0).toUInt64 <<< (8 * w).toUInt64)

/-- What `pushBits` runs as. Same bytes in the same order, and the same `(8 * k).toUInt64` shift, so
the two agree at every width including the ones past 8 where `UInt64.shiftRight` wraps modulo 64.

It exists because of *ownership*, not speed. Lean's borrow inference marks a parameter owned only
where something consumes it, and the recursion below consumes nothing: its base case hands `out`
straight back, so `out` is passed **borrowed**, the caller keeps its reference alive across the
call, and the first `ByteArray.push` therefore sees a shared buffer and copies the whole payload.
One full copy per element, which is what made `Column.ofAtoms` quadratic -- `-8!til 1000000` was
46 seconds, 96% of it in `memcpy`. Here the accumulator reaches `ByteArray.push` directly, which
owns it, so the pushes are in place. -/
def pushBitsImpl (out : ByteArray) (v : UInt64) (w : Nat) : ByteArray :=
  Nat.fold w (init := out) fun k _ acc => acc.push (v >>> (8 * k).toUInt64).toUInt8

/-- The low `w` bytes of `v`, little-endian. Recursion on `w` for the reason `bitsAt` gives. -/
@[implemented_by pushBitsImpl]
def pushBits (out : ByteArray) (v : UInt64) : Nat → ByteArray
  | 0 => out
  | w + 1 => (pushBits out v w).push (v >>> (8 * w).toUInt64).toUInt8

/-- Bit `i`, LSB first within a byte. Past the end reads `false`. -/
def bitAt (b : ByteArray) (i : Nat) : Bool :=
  ((b[i / 8]?.getD 0) >>> (i % 8).toUInt8) &&& 1 == 1

/-- Blocks in a Frame-of-Reference payload, from the 33 bytes each one contributes to `metadata`.
Exact rather than a floor even though the trailer follows the last block: the trailer is 24 bytes and
a block's share is 33, so it never reaches the next multiple. -/
def nblk (metadata : ByteArray) : Nat := metadata.size / 33

/-- The trailer's `lg` as stored: the block size's base-2 logarithm. -/
def lgAt (metadata : ByteArray) : Nat := (bitsAt metadata (32 * nblk metadata + 16) 8).toNat

/-- Whether the stored `lg` is one the layout admits, `6 ≤ lg ≤ 16`. `Enc.WF` requires it, which is
how a reader refuses any other: the model treats it as malformed as it treats a short metadata. -/
def lgOk (metadata : ByteArray) : Bool := 6 ≤ lgAt metadata && lgAt metadata ≤ 16

/-- The block size's logarithm every reader takes a block apart by, through `blk`. The stored
`lg` is clamped into `6 .. 16`, which changes nothing where `lgOk` holds and keeps a malformed
column's reads total and cheap — `2 ^ lg` at an arbitrary `UInt64` would not be — and every fact the
layout rests on (a positive block size, an 8-byte-aligned block start) unconditional. -/
def lgOf (metadata : ByteArray) : Nat := min 16 (max 6 (lgAt metadata))

/-- `2 ^ lgOf`, the elements a block holds. -/
def blk (metadata : ByteArray) : Nat := 2 ^ lgOf metadata

/-- A power of two as a word: `UInt64`'s `^` multiplies words, where `Nat`'s `^` and `<<<` run as `lean_nat_pow`,
`lean_nat_shiftl`, which build a GMP number even for a small result. -/
theorem toUInt64_pow (a k : Nat) : (a ^ k : Nat).toUInt64 = a.toUInt64 ^ k := by
  induction k with
  | zero => rfl
  | succ k ih => rw [Nat.pow_succ, UInt64.pow_succ, ← ih]; exact UInt64.ofNat_mul _ _

theorem toNat_pow {a k : Nat} (h : a ^ k < 2 ^ 64) : (a.toUInt64 ^ k).toNat = a ^ k := by
  rw [← toUInt64_pow]; exact Nat.mod_eq_of_lt h

/-- `2 ^ d` as a `UInt64`, `0` at `d ≥ 64`: one shift, where `UInt64`'s `^` multiplies once per bit of `d` and `Nat`'s
is a GMP number from `d = 63`. -/
def pow2 (d : Nat) : UInt64 := if d < 64 then 1 <<< d.toUInt64 else 0

theorem pow2_eq (d : Nat) : pow2 d = (2 ^ d : Nat).toUInt64 := by
  apply UInt64.toNat_inj.1
  unfold pow2; split
  · have hs : (d.toUInt64).toNat % 64 = d := by simp only [Nat.toUInt64_eq, UInt64.toNat_ofNat']; omega
    -- `Nat.pow_le_pow_right` to `2 ^ 63`, since `Nat.pow_lt_pow_right` brings `Classical.choice`
    have h2 : 2 ^ d < 2 ^ 64 := Nat.lt_of_le_of_lt (Nat.pow_le_pow_right (by decide) (by omega : d ≤ 63)) (by decide)
    rw [UInt64.toNat_shiftLeft, hs, UInt64.toNat_one, Nat.shiftLeft_eq, Nat.one_mul, Nat.mod_eq_of_lt h2,
      Nat.toUInt64_eq, UInt64.toNat_ofNat', Nat.mod_eq_of_lt h2]
  · obtain ⟨m, hm⟩ : ∃ m, 2 ^ d = 2 ^ 64 * m := ⟨2 ^ (d - 64), by rw [← Nat.pow_add]; congr 1; omega⟩
    rw [Nat.toUInt64_eq, UInt64.toNat_ofNat', hm, Nat.mul_mod_right]; rfl

/-- What `blk` runs as: `pow2`, since `foRBits` takes `blk` on every element it reads. -/
def blkImpl (metadata : ByteArray) : Nat := (pow2 (lgOf metadata)).toNat

@[csimp] theorem blk_eq_blkImpl : @blk = @blkImpl := by
  funext m; rw [blk, blkImpl, pow2_eq, Nat.toUInt64_eq, UInt64.toNat_ofNat']
  exact (Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by decide) (by unfold lgOf; omega))).symm

/-- The `lg` every encoder writes. -/
def lgEnc : Nat := 10

/-- Block `b`'s minimum, as raw bits: the value its residuals are measured from. -/
def baseAt (metadata : ByteArray) (b : Nat) : UInt64 := bitsAt metadata (b * 8) 8





/-- Block `b`'s width byte, as stored: its residual width (`widthAt`) and its null flag (`nulAt`). -/
def widthByte (metadata : ByteArray) (b : Nat) : Nat := (metadata[32 * nblk metadata + 24 + b]?.getD 0).toNat

/-- Block `b`'s residual bit width, `0 .. 64`: the width byte's low seven bits. Bit 7 is `nulAt`'s flag, free because a
width is at most 64, so every reader of a width reads it here and an unflagged block's byte is its width. -/
def widthAt (metadata : ByteArray) (b : Nat) : Nat := widthByte metadata b % 128

/-- Whether block `b` holds nulls in band: bit 7 of its width byte (`rust/src/coc.rs`'s `NUL_FLAG`). In a flagged
block the residual `2 ^ widthAt - 1` is the null (`foRNul`); an encoder flags a block only where it holds a null, and
widens it by one bit only where its values' range already reaches `2 ^ w - 1`. -/
def nulAt (metadata : ByteArray) (b : Nat) : Bool := 128 ≤ widthByte metadata b

/-- Where each block's residuals begin, as byte offsets into the pack. `metadata` stores this too, and
the kernels read it from there; recomputing it here is what keeps a fixed-width offset table's wrap
out of the denotation, for the reason a symbol column's offsets are `Nat`. -/
def blockStarts (metadata : ByteArray) : Array Nat :=
  (Nat.fold (nblk metadata) (init := ((#[0] : Array Nat), 0)) fun b _ s =>
    let pos := s.2 + blk metadata * widthAt metadata b / 8
    (s.1.push pos, pos)).1

/-- Where block `b`'s residuals begin, summing only the blocks before it and allocating nothing.
`Verify.blockStarts_get` is that this is entry `b` of the table above, so the two are one answer and
not two: a whole-column read hoists the table, a single-element read sums `b` widths and stops.

The body is the **specification** and stays the sum, which is what keeps that theorem true and keeps
a fixed-width offset table's wrap out of the denotation. The C reads the prefix sum the metadata
already carries, as every kernel does — `coc_offsets` writes exactly this fold and `rust/src/coc.rs`'s
`for_src` records that the stored offsets are trusted. The sum is what made `Column.get` linear in
the block index: `xl@i` cost 0.85us at `i = 0` and 3.25us at `i = 1M`, on a single element read. -/
def blockStart (metadata : @& ByteArray) (b : @& Nat) : Nat :=
  Nat.fold b (init := 0) fun c _ pos => pos + blk metadata * widthAt metadata c / 8

/-- What `resAt` runs as: one eight-byte read at the field's first byte, shifted down, and the ninth
byte only when the field straddles it. `rust/src/coc.rs`'s `res_get` is the same reading. -/
def resAtImpl (pack : ByteArray) (s w j : Nat) : UInt64 :=
  if w = 0 then 0 else
  let o := j * w
  let lo := bitsAt pack (s + o / 8) 8 >>> (o % 8).toUInt64
  let v := if o % 8 + w ≤ 64 then lo
    else lo ||| (pack[s + o / 8 + 8]?.getD 0).toUInt64 <<< (64 - o % 8).toUInt64
  if w = 64 then v else v &&& ((1 : UInt64) <<< w.toUInt64) - 1

/-- The `j`th residual of a block whose residuals begin at byte `s`, at width `w` (any of `0 .. 64`):
bits `[j * w, j * w + w)` of the little-endian bit stream from byte `s`, each byte `k` of the field's
contributing its bits shifted into place. At 1/2/4 that is `8 / w` fields to a byte, low field first,
and at 8/16/32/64 whole little-endian fields, so a power-of-two width reads the bytes it always did. -/
@[implemented_by resAtImpl]
def resAt (pack : ByteArray) (s w j : Nat) : UInt64 :=
  (List.range' (j * w / 8) ((j * w + w + 7) / 8 - j * w / 8)).foldl (init := 0) fun acc k =>
    acc ||| ((pack[s + k]?.getD 0).toNat * 2 ^ (8 * k) / 2 ^ (j * w) % 2 ^ w).toUInt64

/-- Where the exception ladder of `rust/src/coc.rs`'s `exc_layout` puts `exc_off`, `exc_pos` and, in an ALP
blob, `exp`; `exc_raw` is always at 16, after the u64 count and the u64 element width or flags. -/
def alpSects (nblk nexc esz : Nat) : Nat × Nat × Nat :=
  let o := (16 + nexc * esz + 7) / 8 * 8
  let p := o + (nblk + 1) * 8
  (o, p, (p + nexc * 2 + 7) / 8 * 8)

/-- A `w`-byte element's bits `v` as the value q holds: sign-extended from its `8 * w` bits by a shift up and an
arithmetic shift down, except one byte, q's unsigned pair, which is its bits zero-extended. -/
def sext (w : Nat) (v : UInt64) : Int64 :=
  if w == 1 then v.toInt64 else (v <<< (64 - 8 * w).toUInt64).toInt64 >>> (64 - 8 * w).toUInt64.toInt64

/-- Patch `k`'s value in the patch list at `e`, sign-extended from its stored width (`foRExc`). -/
def foRPatch (pack : ByteArray) (e k : Nat) : UInt64 :=
  let esz := (bitsAt pack (e + 8) 8).toNat % 256
  (sext esz (bitsAt pack (e + 16 + k * esz) esz)).toUInt64

/-- The patches block `b` owns, as indices into the patch list at `e`: `exc_off`'s entries `b` to `b + 1`. -/
def foRPatches (metadata pack : ByteArray) (e b : Nat) : List Nat :=
  let o := (alpSects (nblk metadata) (bitsAt pack e 8).toNat ((bitsAt pack (e + 8) 8).toNat % 256)).1
  let off (b : Nat) := (bitsAt pack (e + o + b * 8) 8).toNat
  List.range' (off b) (off (b + 1) - off b)

/-- Element `i`'s own bits when the pack's patch list holds it: the list `rust/src/coc.rs` lays after the
last block's residuals when some element is a null or an outlier, the ladder `alpSects` describes,
an element sign-extended from its stored width as `baseAt` is (one byte, q's unsigned pair, is not).
`e`, where the last block's residuals end, is `blockStart` at `nblk`; `foRBits` passes its hoisted table's last entry
(`Verify.blockStarts_get`), because the sum over every block on each element read is what made a column read quadratic. -/
def foRExc (metadata pack : ByteArray) (i : Nat) (e : Nat := blockStart metadata (nblk metadata)) : Option UInt64 :=
  if pack.size ≤ e then none else
  let p := (alpSects (nblk metadata) (bitsAt pack e 8).toNat ((bitsAt pack (e + 8) 8).toNat % 256)).2.1
  ((foRPatches metadata pack e (i / blk metadata)).find?
      fun k => (bitsAt pack (e + p + k * 2) 2).toNat == i % blk metadata).map (foRPatch pack e)

/-- How far block `b`'s frame, the value its residuals are measured from, lies above its minimum:
the `u64` the patch list keeps per block after `exc_pos` when bit 8 of its width word says so, and
`0` for a pack with no patch list or no frames. A
frame above the minimum is what lets a low outlier be patched as a high one is. `e` is `foRExc`'s. -/
def foRFrame (metadata pack : ByteArray) (b : Nat) (e : Nat := blockStart metadata (nblk metadata)) : UInt64 :=
  let f := (bitsAt pack (e + 8) 8).toNat
  if pack.size ≤ e || f / 256 % 2 == 0 then 0 else
  let (_, _, q) := alpSects (nblk metadata) (bitsAt pack e 8).toNat (f % 256)
  bitsAt pack (e + q + b * 8) 8

/-- The raw bits element `i` denotes: its block's frame plus its residual, added with `UInt64`
wrapping. This *is* the denotation of the encoding, and it is one definition rather than one inside
`atoms` and another inside each kernel specification, so a reduction proved against a kernel and the
atoms it is meant to agree with are reading the same expression.

`starts` is the hoisted prefix sum over every block: a whole-column read passes `blockStarts` once,
because recomputing it per element is the one way reading a column could become quadratic. A read
the table does not cover — a single element, which passes `#[]` — sums the blocks before `i` here
instead, `blockStarts_get` being that this is the same number. It is not `0`, which would answer
with the wrong element rather than decline. -/
def foRBits (metadata pack : ByteArray) (starts : Array Nat) (i : Nat) : UInt64 :=
  let b := i / blk metadata
  let e := match starts[nblk metadata]? with | some s => s | none => blockStart metadata (nblk metadata)
  match foRExc metadata pack i e with
  | some v => v
  | none => baseAt metadata b + foRFrame metadata pack b e +
    resAt pack (match starts[b]? with | some s => s | none => blockStart metadata b)
      (widthAt metadata b) (i % blk metadata)

/-- `2 ^ d - 1` as a `UInt64`, all ones at `d ≥ 64`: by a shift, since `2 ^ d` is a big `Nat` from `d = 63`. -/
def ones (d : Nat) : UInt64 := pow2 d - 1

theorem ones_eq (d : Nat) : ones d = (2 ^ d - 1).toUInt64 := by
  rw [ones, pow2_eq]; exact (UInt64.ofNat_sub Nat.one_le_two_pow).symm


/-- Whether element `i` is the null of a nullable column (`atom+1`), tested on the encoding and never decoded: its
block is flagged (`nulAt`), no patch holds it (`foRExc`), and its residual is the block's top one, `2 ^ w - 1`.
`starts` as in `foRBits`; the Rust test is `rust/src/cocops.rs`'s `in_band_null_is_the_flagged_top_residual`. -/
def foRNul (metadata pack : ByteArray) (starts : Array Nat) (i : Nat) : Bool :=
  let b := i / blk metadata
  let e := match starts[nblk metadata]? with | some s => s | none => blockStart metadata (nblk metadata)
  nulAt metadata b && (foRExc metadata pack i e).isNone &&
    resAt pack (match starts[b]? with | some s => s | none => blockStart metadata b) (widthAt metadata b)
      (i % blk metadata) == ones (widthAt metadata b)

/-- Element `i` of a nullable column, the denotation of `atom+1` in one column: `none` (the `1`) at its null
(`foRNul`), else the raw bits `foRBits` reads. A column with no flagged block reads `some` everywhere. -/
def foROpt (metadata pack : ByteArray) (starts : Array Nat) (i : Nat) : Option UInt64 :=
  if foRNul metadata pack starts i then none else some (foRBits metadata pack starts i)

/-- Whether every value a `foR` payload holds is below 2, decided per block from its metadata and patch list alone,
never per element (`Verify.u1Ok_bound`): an unpatched value is `baseAt + foRFrame + residual`, the residual at most
`ones (widthAt)` and, in a block `nulAt` flags, one less (the top one is the null), and a patched value is its patch.
Every `u1` column the encoder writes passes, since it picks the minimal width (`widthFor` of the block's range), so a
`0`/`1` block is base `0` width `1` or base `0`/`1` width `0`; a file whose `u1` block has a larger frame or width is
rejected, even where each of its values happens to be `0` or `1`. So is a `u1` block flagged for a null: the encoder
widens it to width 2 (residual 3 the null), whose metadata admits a residual 2; a nullable column (`Opt`) is
decided by `Enc.WF` itself. -/
def u1Ok (metadata pack : ByteArray) : Bool :=
  let e := blockStart metadata (nblk metadata)
  Nat.all (nblk metadata) fun b _ =>
    (baseAt metadata b).toNat + (foRFrame metadata pack b e).toNat + (ones (widthAt metadata b)).toNat <
      2 + (nulAt metadata b).toNat &&
    (pack.size ≤ e || (foRPatches metadata pack e b).all fun k => (foRPatch pack e k).toNat < 2)

/-- Exceptions stored out of line. Read out of the alp blob's header rather than derived, `exc_off`
being a prefix sum whose last entry is this. -/
def alpNexc (a : ByteArray) : Nat := (bitsAt a 0 8).toNat

/-- Whether an element is four bytes (q's `real`) rather than eight. Bit 0 of the header's flag
word. The tag says the same thing through `QAtomicType.width`; `Enc.WF` states that the two agree, and
every encoder keeps it by choosing the kernel by that width. -/
def alpF32 (a : ByteArray) : Bool := bitsAt a 8 8 &&& 1 == 1

/-- Bytes one element takes in `exc_raw`. -/
def alpEsz (a : ByteArray) : Nat := if alpF32 a then 4 else 8

/-- Where block `b`'s exceptions start in `exc_pos` and `exc_raw`, `b = nblk` giving `nexc`. -/
def alpExcOff (metadata a : ByteArray) (b : Nat) : Nat :=
  (bitsAt a ((alpSects (nblk metadata) (alpNexc a) (alpEsz a)).1 + b * 8) 8).toNat

/-- Exception `j`'s position **inside its own block**, which is why `Column.blk` fitting a `UInt16`
is what this layout rests on. -/
def alpExcPos (metadata a : ByteArray) (j : Nat) : Nat :=
  (bitsAt a ((alpSects (nblk metadata) (alpNexc a) (alpEsz a)).2.1 + j * 2) 2).toNat

/-- Exception `j`'s element, as the raw bits it was stored with. The only place the original
pattern survives, and it never passes through `Float`. `exc_raw` is first in the blob and so needs
no block count to find, which is why this one takes no metadata. -/
def alpExcRaw (a : ByteArray) (j : Nat) : UInt64 :=
  bitsAt a (16 + j * alpEsz a) (alpEsz a)

/-- Block `b`'s decimal exponent, `0 ≤ e ≤ 18`. Stored as an `int8_t`, and the encoder never writes
a negative one — a value needing no exponent takes `0` and one needing more than 18 is an
exception. -/
def alpExpAt (metadata a : ByteArray) (b : Nat) : Nat :=
  (a[(alpSects (nblk metadata) (alpNexc a) (alpEsz a)).2.2 + b]?.getD 0).toNat

/-- `10 ^ e` as the double `rust/src/coc.rs`'s `POW10` table holds. Exact at every `e ≤ 18`: `10 ^ 18` is
`2 ^ 18 * 5 ^ 18` and `5 ^ 18` is under `2 ^ 53`, so no entry is rounded and the two tables are the
same nineteen numbers. -/
def pow10 (e : Nat) : Float := Float.ofNat (10 ^ e)

/-- What `pow10` runs as: `e` multiplications of a small `Nat`, where `10 ^ e` runs as `lean_nat_pow` through GMP on
every `alp` element read. -/
def pow10Impl (e : Nat) : Float := Float.ofNat (Nat.fold e (init := 1) fun _ _ a => a * 10)

@[csimp] theorem pow10_eq_pow10Impl : @pow10 = @pow10Impl := by
  funext e; unfold pow10 pow10Impl; congr 1; symm
  induction e with
  | zero => simp [Nat.fold_zero]
  | succ e ih => simp only [Nat.fold_succ, ih, Nat.pow_succ]

/-- The value `d` denotes at exponent `e`, as raw bits: `d / 10 ^ e`, narrowed to four bytes for a
`real` column. `rust/src/coc.rs`'s `alp_dec` is this expression and the encoder verified its round trip
against exactly it.

A **division**, and not a multiplication by `10 ^ -e`. `10 ^ -e` is not representable, so the
product is off by an ulp from the quotient and the round trip the encoder checked would not be the
one performed here. -/
def alpDec (d : UInt64) (e : Nat) (f32 : Bool) : UInt64 :=
  let v := d.toInt64.toFloat / pow10 e
  if f32 then v.toFloat32.toBits.toUInt64 else v.toBits

/-- Which exception, if any, sits at position `j` of block `b`. A scan of that block's slice of
`exc_pos`, which is what the layout supports: the positions are in increasing order but no index
into them is stored, the C reading them the other way round — it walks the exceptions and overwrites
the elements they land on. -/
def alpExcAt (metadata a : ByteArray) (b j : Nat) : Option Nat :=
  (List.range' (alpExcOff metadata a b) (alpExcOff metadata a (b + 1) - alpExcOff metadata a b)).find?
    fun k => alpExcPos metadata a k == j

/-- The raw bits element `i` denotes, and so the denotation of the whole encoding: its exception's
stored pattern where it has one, and its block's integer scaled back where it has not. `starts` is
`foRBits`' hoisted prefix sum and means the same thing here.

An exception is never rebuilt through arithmetic, only copied, which is what makes the round trip
hold on the *bits*: `0n` comes back as `0n` rather than as some other NaN, `-0w` keeps its sign and
`-0.0` does not become `+0.0`. -/
def alpBits (metadata pack a : ByteArray) (starts : Array Nat) (i : Nat) : UInt64 :=
  match alpExcAt metadata a (i / blk metadata) (i % blk metadata) with
  | some k => alpExcRaw a k
  | none => alpDec (foRBits metadata pack starts i) (alpExpAt metadata a (i / blk metadata)) (alpF32 a)

/-- The residual bit width a range needs, exactly: its bit length, any of `0 .. 64` for a range under
`2 ^ 64`. `rust/src/coc.rs`'s `width_for`, a leading-zero count. -/
def widthFor (range : Nat) : Nat := if range = 0 then 0 else Nat.log2 range + 1

/-- The narrowest of 0/1/2/4/8/16/32/64 that holds `w` bits. An interned column's ids are packed at
it, and `rust/src/coc.rs`'s `coc_lanes` unpacks an odd-width block to it (at eight bits at least) so that
every kernel's width switch reads the lanes; `lane_width` there. -/
def laneWidth (w : Nat) : Nat :=
  if w ≤ 2 then w else if w ≤ 4 then 4 else if w ≤ 8 then 8
  else if w ≤ 16 then 16 else if w ≤ 32 then 32 else 64

/-- Bits one id takes where `nd` values are numbered `0 .. nd-1`: an interned column's dictionary
entries, or a grouping's groups (`Kernel.Order.groupIds`). `rust/src/ids.rs`'s `id_width`. -/
def idWidthOf (nd : Nat) : Nat := laneWidth (widthFor (nd - 1))

/-- Element `i`'s dictionary index, at `w = idWidth offs` bits. Past the end reads `0`, the
convention `bitsAt` sets, so a malformed column answers rather than panicking.

`w` is the parameter and not the offsets, because every caller that loops hoists it — recomputing
the ladder per element is the mistake `blockStarts` exists to avoid on the other constructor. -/
def idAt (ids : ByteArray) (w i : Nat) : Nat := (resAt ids 0 w i).toNat

/-- How many of the first `n` ids a payload at `w` bits holds: `rust/src/ids.rs`'s `ids_avail` clamp, which
rounds `⌈n·w/8⌉` back down. Every id is there at width `0`, which stores nothing. -/
def idsCap (ids : ByteArray) (w n : Nat) : Nat := if w = 0 then n else min n (ids.size * 8 / w)

/-- `n` ids at `w` bits, `f i` being id `i` — `idAt`'s inverse and the one place an id payload is
laid out. The bits past `n` in the last byte stay `0` so that two
columns holding the same symbols must hold the same bytes, or `~` and `atomIdenticalHash` call equal
columns different. -/
def packIds (w n : Nat) (f : Nat → Nat) : ByteArray :=
  if 8 ≤ w then
    Nat.fold n (init := ByteArray.emptyWithCapacity (n * (w / 8))) fun i _ acc =>
      pushBits acc (f i).toUInt64 (w / 8)
  else if w = 0 then ByteArray.empty
  else
    let per := 8 / w
    Nat.fold ((n + per - 1) / per) (init := ByteArray.emptyWithCapacity ((n + per - 1) / per))
      fun k _ acc =>
        acc.push (Nat.fold per (init := (0 : UInt8)) fun j _ b =>
          let i := k * per + j
          b ||| (if i < n then ((f i) % (2 ^ w)).toUInt8 <<< (j * w).toUInt8 else 0))

end Column

namespace Ext.Enc
open Column

/-- What the header promises about the payload: the layout is one `t` has, and it holds exactly `n`
elements. The conditions `count`, `admit` and `mismatch` used to encode between them, stated once;
every reader trusts the header, so a vector that fails this is a bug where it was built. Booleans are
a `u1` `foR` and never `bytes`; Frame of Reference takes every fixed-width type, a `boolean` one being `u1` (every
element but a null 0 or 1, read through `foROpt`, since a null row holds its block's top residual and no value); a `foR` payload's blocks cover its `n`, and a block flagged `nulAt` holds a null row (`foRNul`). A `sym` column is
its ids, positions in the sorted, distinct dictionary held beside it at the Rel level and never in the payload,
so id order is symbol order and every integer kernel reads it unchanged (PLAN 8.3). -/
def WF (t : QAtomicType) (n : USize) (e : Ext.Enc X) : Prop :=
  match t, e with
  | .general, .gen xs => xs.size = n.toNat
  | t, .foR metadata pack =>
    t.width.isSome ∧ (t = .u1 → ∀ i < n.toNat, ∀ v, foROpt metadata pack (blockStarts metadata) i = some v → v.toNat < 2) ∧
      n.toNat ≤ blk metadata * nblk metadata ∧ lgOk metadata ∧
      -- owner decision F: a block is flagged only where it holds a null, so a column's `hasNul` is its rows' flags
      ∀ b < nblk metadata, nulAt metadata b = true → ∃ j < blk metadata, b * blk metadata + j < n.toNat ∧
        foRNul metadata pack (blockStarts metadata) (b * blk metadata + j) = true
  -- owner decision M (PLAN): the encodings are `foR` and `pos`; `pos` holds the positions `0..n-1`, so it is a long
  | .i64, .pos => True
  | _, _ => False

/-- `atoms`' fixed-width branches before `atomOfBits`: the raw bits of each element, a boolean's as `0`/`1` and
a symbol column's as its ids (a symbol is its id, `QAtom.sym`). A theorem
about a numeric column is stated over this.

Every form reads an element of a `w`-byte type as its `8 * w` bits zero-extended, the dense payload's own reading, so
`raw` is a function of the column and not of its form: `foRBits` holds an element sign-extended to 64 bits
(`Verify.unbias_keyAt`), and its encoded forms are cut to the low `8 * w` here, a boolean's to its one bit. -/
def raw (t : QAtomicType) (n : USize) (e : Ext.Enc X) : Array UInt64 :=
  match t, e with
  | .u1, .foR metadata pack => let starts := blockStarts metadata
    (Array.range n.toNat).map fun i => UInt64.ofNat ((foRBits metadata pack starts i).toNat % 2)
  | t, .foR metadata pack => match t.width with
    | some w => let starts := blockStarts metadata
      (Array.range n.toNat).map fun i => UInt64.ofNat ((foRBits metadata pack starts i).toNat % 2 ^ (8 * w))
    | none => #[]
  -- a model read by proofs and kernel specifications; compiled kernels read `pos` as their loop index
  | .i64, .pos => (Array.range n.toNat).map UInt64.ofNat
  | _, _ => #[]

/-- The low `8 * w` bits of `v`, `0 < w`, by a shift up and down: `v.toNat % 2 ^ (8 * w)` builds a big `Nat` for a
sign-extended negative element and at `w = 8`. -/
def lowBytes (w : Nat) (v : UInt64) : UInt64 := if w < 8 then (v <<< (64 - 8 * w).toUInt64) >>> (64 - 8 * w).toUInt64 else v

-- through `omega` at each width: `Nat.and_two_pow_sub_one_eq_mod` carries `Classical.choice`
theorem lowBytes_toNat (w : Nat) (hw : 0 < w) (v : UInt64) : (lowBytes w v).toNat = v.toNat % 2 ^ (8 * w) := by
  have := UInt64.toNat_lt v
  unfold lowBytes; split
  · rw [UInt64.toNat_shiftRight, UInt64.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow]
    rcases (by omega : w = 1 ∨ w = 2 ∨ w = 3 ∨ w = 4 ∨ w = 5 ∨ w = 6 ∨ w = 7) with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [Nat.reduceMul, Nat.reduceSub, Nat.toUInt64_eq, UInt64.toNat_ofNat', Nat.reducePow, Nat.reduceMod] <;>
      omega
  · exact (Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le this (Nat.pow_le_pow_right (by decide) (by omega)))).symm

/-- `raw` as it runs: each `% 2 ^ (8 * w)` a `lowBytes` mask. -/
def rawImpl (t : QAtomicType) (n : USize) (e : Ext.Enc X) : Array UInt64 :=
  match t, e with
  | .u1, .foR metadata pack => let starts := blockStarts metadata
    (Array.range n.toNat).map fun i => (foRBits metadata pack starts i) &&& 1
  | t, .foR metadata pack => match t.width with
    | some w => let starts := blockStarts metadata
      (Array.range n.toNat).map fun i => lowBytes w (foRBits metadata pack starts i)
    | none => #[]
  | .i64, .pos => (Array.range n.toNat).map UInt64.ofNat
  | _, _ => #[]

@[csimp] theorem raw_eq_rawImpl : @raw = @rawImpl := by
  funext X t n e
  have h1 : ∀ v : UInt64, UInt64.ofNat (v.toNat % 2) = v &&& 1 := fun v => by
    apply UInt64.toNat_inj.1
    have := UInt64.toNat_lt v
    rw [UInt64.toNat_ofNat', UInt64.toNat_and, show (1 : UInt64).toNat = 2 ^ 1 - 1 from rfl,
      Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt (by omega)]
  have hw : ∀ w, 0 < w → ∀ v : UInt64, UInt64.ofNat (v.toNat % 2 ^ (8 * w)) = lowBytes w v := fun w hw v => by
    apply UInt64.toNat_inj.1
    rw [lowBytes_toNat w hw, UInt64.toNat_ofNat',
      Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.mod_le _ _) (UInt64.toNat_lt v))]
  cases e <;> cases t <;> simp [raw, rawImpl, QAtomicType.width, ← h1, ← hw]

end Ext.Enc

namespace Column
open Ext.Enc

/-- `push` grows the array by one byte. -/
theorem push_size (b : ByteArray) (x : UInt8) : (b.push x).size = b.size + 1 := by
  cases b
  simp [← ByteArray.size_data, ByteArray.push]

/-- Reading an existing byte after one push. -/
theorem push_getElem?_lt {b : ByteArray} {x : UInt8} {j : Nat} (hj : j < b.size) :
    (b.push x)[j]? = b[j]? := by
  rw [getElem?_pos (b.push x) j (by rw [push_size]; omega), getElem?_pos b j hj]
  congr 1
  rw [ByteArray.getElem_eq_getElem_data, ByteArray.getElem_eq_getElem_data]
  exact Array.getElem_push_lt (by simpa [← ByteArray.size_data] using hj)

/-- Reading the byte just pushed. -/
theorem push_getElem?_eq {b : ByteArray} {x : UInt8} :
    (b.push x)[b.size]? = some x := by
  rw [getElem?_pos (b.push x) b.size (by rw [push_size]; omega)]
  congr 1
  rw [ByteArray.getElem_eq_getElem_data]
  exact Array.getElem_push_eq

/-- One step of `pushBits`: append byte `w` of `v`. -/
theorem pushBits_succ (b : ByteArray) (v : UInt64) (w : Nat) :
    pushBits b v (w + 1) = (pushBits b v w).push (v >>> (8 * w).toUInt64).toUInt8 := rfl

/-- `pushBits` appends exactly `w` bytes. -/
theorem pushBits_size (b : ByteArray) (v : UInt64) (w : Nat) :
    (pushBits b v w).size = b.size + w := by
  induction w with
  | zero => simp [pushBits]
  | succ w ih =>
      rw [pushBits_succ, push_size, ih]
      omega

/-- What was already there is still there. -/
theorem pushBits_getElem?_lt (b : ByteArray) (v : UInt64) (w j : Nat) (hj : j < b.size) :
    (pushBits b v w)[j]? = b[j]? := by
  induction w generalizing j with
  | zero => simp [pushBits]
  | succ w ih =>
      rw [pushBits_succ]
      have hjp : j < (pushBits b v w).size := by
        rw [pushBits_size]
        omega
      rw [push_getElem?_lt (x := (v >>> (8 * w).toUInt64).toUInt8) hjp]
      exact ih j hj

/-- One step of `bitsAt`: OR in byte `w`. Stated in the `getElem?` spelling rather than the bounds
test the definition uses, because that is what the proofs below and `Verify.Encoding` read. -/
theorem bitsAt_succ (b : ByteArray) (o w : Nat) :
    bitsAt b o (w + 1) = bitsAt b o w ||| ((b[o + w]?.getD 0).toUInt64 <<< (8 * w).toUInt64) := by
  have hbyte : (if h : o + w < b.size then b[o + w] else 0) = b[o + w]?.getD 0 := by
    split
    · next h => rw [getElem?_pos b (o + w) h, Option.getD_some]
    · next h => rw [getElem?_neg b (o + w) h, Option.getD_none]
  rw [bitsAt, hbyte]

/-- `bitsAt` only reads bytes `o .. o + w - 1`. -/
theorem bitsAt_congr (b b' : ByteArray) (o w : Nat) (hagree : ∀ k < w, b'[o + k]? = b[o + k]?) :
    bitsAt b' o w = bitsAt b o w := by
  induction w with
  | zero => simp [bitsAt]
  | succ w ih =>
      rw [bitsAt_succ b' o w, bitsAt_succ b o w]
      rw [ih (fun k hk => hagree k (by omega))]
      rw [hagree w (by omega)]

/-- Splitting a remainder at the byte boundary `8 * w`. -/
private theorem mod_low8 (a w : Nat) :
    a % (2 ^ (8 * w) * 2 ^ 8) = a % 2 ^ (8 * w) + (a / 2 ^ (8 * w) % 2 ^ 8) * 2 ^ (8 * w) := by
  let m := 2 ^ (8 * w)
  change a % (m * 2 ^ 8) = a % m + (a / m % 2 ^ 8) * m
  rw [show m * 2 ^ 8 = 2 ^ 8 * m by rw [Nat.mul_comm]]
  have hm : 0 < m := Nat.pow_pos (by decide : 0 < 2)
  have hlow : a % m < m := Nat.mod_lt a hm
  have hd : a / m % 2 ^ 8 < 2 ^ 8 := Nat.mod_lt (a / m) (by decide : 0 < 2 ^ 8)
  have hlo : a % m + (a / m % 2 ^ 8) * m < 2 ^ 8 * m := by
    have h1 : a % m + (a / m % 2 ^ 8) * m < m + (a / m % 2 ^ 8) * m :=
      Nat.add_lt_add_right hlow ((a / m % 2 ^ 8) * m)
    have h2 : m + (a / m % 2 ^ 8) * m ≤ 2 ^ 8 * m := by
      rw [Nat.add_comm, ← Nat.succ_mul]
      exact Nat.mul_le_mul_right m (Nat.succ_le_of_lt hd)
    exact Nat.lt_of_lt_of_le h1 h2
  calc
    a % (2 ^ 8 * m) = (m * (a / m) + a % m) % (2 ^ 8 * m) := by
      conv => lhs; rw [← Nat.div_add_mod a m]
    _ = (m * (2 ^ 8 * (a / m / 2 ^ 8) + a / m % 2 ^ 8) + a % m) % (2 ^ 8 * m) := by
      conv => lhs; rw [← Nat.div_add_mod (a / m) (2 ^ 8)]
    _ = (m * 2 ^ 8 * (a / m / 2 ^ 8) + m * (a / m % 2 ^ 8) + a % m) % (2 ^ 8 * m) := by
      rw [Nat.mul_add, ← Nat.mul_assoc]
    _ = (a % m + (a / m % 2 ^ 8) * m) % (2 ^ 8 * m) := by
      rw [show m * 2 ^ 8 * (a / m / 2 ^ 8) + m * (a / m % 2 ^ 8) + a % m =
            a % m + (a / m % 2 ^ 8) * m + (2 ^ 8 * m) * (a / m / 2 ^ 8) by ac_rfl]
      rw [Nat.add_mul_mod_self_left (a % m + (a / m % 2 ^ 8) * m) (2 ^ 8 * m) (a / m / 2 ^ 8)]
    _ = a % m + (a / m % 2 ^ 8) * m := by
      rw [Nat.mod_eq_of_lt hlo]

/-- `pushBits` writes `v`'s low `w` bytes little-endian. -/
theorem bitsAt_pushBits (b : ByteArray) (v : UInt64) (w : Nat) (hw : w ≤ 8) :
    bitsAt (pushBits b v w) b.size w = UInt64.ofNat (v.toNat % 2 ^ (8 * w)) := by
  apply UInt64.toNat_inj.1
  induction w with
  | zero => simp [bitsAt, Nat.pow_zero, Nat.mod_one]
  | succ w ih =>
      let byte := (v >>> (8 * w).toUInt64).toUInt8
      rw [pushBits_succ, bitsAt_succ]
      have hagree : ∀ k < w, ((pushBits b v w).push byte)[b.size + k]? = (pushBits b v w)[b.size + k]? := by
        intro k hk
        have hjp : b.size + k < (pushBits b v w).size := by
          rw [pushBits_size]
          omega
        exact push_getElem?_lt hjp
      rw [bitsAt_congr (pushBits b v w) ((pushBits b v w).push byte) b.size w hagree]
      rw [UInt64.toNat_or]
      rw [ih (by omega)]
      have hget : ((pushBits b v w).push byte)[b.size + w]? = some byte := by
        rw [← pushBits_size]
        exact push_getElem?_eq
      rw [hget, show ((some byte).getD 0).toUInt64 = byte.toUInt64 by rfl]
      rw [UInt64.toNat_shiftLeft]
      have h8w : (8 * w).toUInt64.toNat = 8 * w := by
        rw [UInt64.toNat_ofNat']
        exact Nat.mod_eq_of_lt (Nat.lt_trans (by omega : 8 * w < 64) (by decide : 64 < 2 ^ 64))
      rw [h8w, Nat.mod_eq_of_lt (by omega : 8 * w < 64)]
      simp only [UInt64.toNat_ofNat']
      rw [Nat.mod_eq_of_lt
        (Nat.lt_of_lt_of_le (Nat.mod_lt v.toNat (Nat.pow_pos (by decide : 0 < 2)))
          (Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : 8 * w ≤ 64)))]
      rw [Nat.mod_eq_of_lt
        (Nat.lt_of_lt_of_le (Nat.mod_lt v.toNat (Nat.pow_pos (by decide : 0 < 2)))
          (Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : 8 * (w + 1) ≤ 64)))]
      let low := v.toNat % 2 ^ (8 * w)
      let bw := (v.toNat / 2 ^ (8 * w)) % 2 ^ 8
      have hbyte : byte.toUInt64.toNat = bw := by
        rw [show bw = (v.toNat / 2 ^ (8 * w)) % 2 ^ 8 by rfl]
        rw [UInt8.toNat_toUInt64, UInt64.toNat_toUInt8, UInt64.toNat_shiftRight, h8w,
          Nat.mod_eq_of_lt (by omega : 8 * w < 64), Nat.shiftRight_eq_div_pow]
      rw [hbyte]
      have hbw : bw < 2 ^ 8 := by simpa [bw] using (Nat.mod_lt (v.toNat / 2 ^ (8 * w)) (by decide : 0 < 2 ^ 8))
      have hsh : bw <<< (8 * w) < 2 ^ 64 := by
        rw [Nat.shiftLeft_eq]
        have h1 : bw * 2 ^ (8 * w) < 2 ^ 8 * 2 ^ (8 * w) :=
          -- not `Nat.mul_lt_mul_right`, which brings `Classical.choice`
          Nat.mul_lt_mul_of_lt_of_le hbw (Nat.le_refl _) (Nat.pow_pos (by decide : 0 < 2))
        have h2 : 2 ^ 8 * 2 ^ (8 * w) ≤ 2 ^ 64 := by
          rw [← Nat.pow_add]
          exact Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : 8 + 8 * w ≤ 64)
        exact Nat.lt_of_lt_of_le h1 h2
      rw [Nat.mod_eq_of_lt hsh]
      rw [Nat.shiftLeft_eq, Nat.or_comm, Nat.mul_comm]
      have hlow : low < 2 ^ (8 * w) := by simpa [low] using (Nat.mod_lt v.toNat (Nat.pow_pos (by decide : 0 < 2)))
      rw [← Nat.two_pow_add_eq_or_of_lt hlow bw]
      rw [show 8 * (w + 1) = 8 * w + 8 by omega, Nat.pow_add]
      rw [mod_low8 v.toNat w]
      rw [show 2 ^ (8 * w) * bw + low = low + bw * 2 ^ (8 * w) by
        conv => lhs; rw [Nat.add_comm, Nat.mul_comm]]

end Column

namespace QTable

end QTable

namespace QValue

end QValue

namespace QValue

end QValue

namespace QValue

end QValue



/-- q's `0n`. Arithmetic that produces a NaN produces exactly this pattern in q. -/
def nanBits : UInt64 := 0xfff8000000000000


def nanBits32 : UInt32 := 0xffc00000

end Rel


namespace Rel

namespace QAtomicType

/-- The q type code of the *vector* form; the atom form is its negation. Code 2 (guid, which Rel does not
carry) is unused, and code 0, the general list, has no atom form. `datetime` is q type 12 (timestamp, i64 ns since the
epoch) and `date` type 14 (i32 days); q types 13 and 15 to 19 are not carried. -/
def code : QAtomicType → Int8
  | general => 0
  | u1 => 1 | i8 => 3 | u8 => 4 | i16 => 5 | i32 => 6 | i64 => 7
  | f32 => 8 | f64 => 9 | char => 10 | sym => 11 | datetime => 12 | date => 14

/-- A type with a fixed width has atoms: how a reader that has matched `width` reaches a function
that takes `t ≠ .general`. -/
theorem ne_general_of_width {t : QAtomicType} {w : Nat} (h : t.width = some w) : t ≠ .general := by
  rintro rfl; cases h

end QAtomicType

namespace Bits

end Bits

namespace QAtom

def type : QAtom → QAtomicType
  | u1 _ => .u1 | u8 _ => .u8 | i16 _ => .i16
  | i32 _ => .i32 | i64 _ => .i64 | f32 _ => .f32 | f64 _ => .f64
  | char _ => .char | i8 _ => .i8 | sym _ => .sym
  | date _ => .date | datetime _ => .datetime


end QAtom

/-- A general list, q's type 0: the `general` column over `gen`, the one representation a list has.
A pattern too, written `.general xs _ _`: the count is the header's and `xs.size` is not a pattern, so
both a match and a construction name it; a construction from a Lean `Array` whose count is not in scope
goes through `QValue.ofArray`. The attribute is a parameter because a general list carries one in q
(`` `u#(1;`a) ``), and a pattern that pinned `none` would miss it; a construction defaults it to `none`. -/
@[match_pattern] abbrev Ext.QValue.general (xs : Array (Ext.QValue X)) (n : USize)
    (a : Option (UInt8 × IndexCell) := none) : Ext.QValue X :=
  .vector .general n (.gen xs) a


namespace Column

/-- The raw bits a fixed-width atom occupies, as q writes them.

Floats stay *bits*: `QAtom.float` already holds the wire pattern, and it must never pass through
`Float.ofBits`, which canonicalises `0xfff8000000000000` — q's `0n` — to `0x7ff8000000000000` and so
corrupts every float null. `symbol` is not a scalar and does not come through here. -/
def bitsOf : QAtom → UInt64
  | .u1 x => if x then 1 else 0
  | .u8 x | .char x => x.toUInt64
  | .i16 x => x.toUInt16.toUInt64
  | .i32 x | .date x => x.toUInt32.toUInt64
  | .i64 x | .datetime x => x.toUInt64
  | .i8 x => x.toUInt8.toUInt64
  | .f32 x => x.toUInt64
  | .f64 x => x
  | .sym x => x

/-- The atom of type `t` those raw bits denote. Total, and its type is `t` by construction, which is
what `atoms_type` turns into the invariant `QLean/Verify/` used to assume. `symbol` is
handled by `atoms` directly and answers its own null here. `general` has no atom. -/
def atomOfBits (t : QAtomicType) (v : UInt64) (h : t ≠ .general := by first | decide | assumption) :
    QAtom :=
  match t with
  | .general => absurd rfl h
  | .u1 => .u1 (v != 0)
  | .u8 => .u8 v.toUInt8
  | .char => .char v.toUInt8
  | .i16 => .i16 v.toUInt16.toInt16
  | .i32 => .i32 v.toUInt32.toInt32
  | .date => .date v.toUInt32.toInt32
  | .i8 => .i8 v.toUInt8.toInt8
  | .i64 => .i64 v.toInt64
  | .datetime => .datetime v.toInt64
  | .f32 => .f32 v.toUInt32
  | .f64 => .f64 v
  | .sym => .sym v


end Column

namespace Ext.Enc
open Column

instance (t : QAtomicType) (n : USize) (e : Ext.Enc X) : Decidable (WF t n e) := by
  unfold WF; split <;> (try split) <;> exact inferInstance


/-- One element, without materialising the rest. `first`, `last`, indexing and every binary search
belong here; calling `atoms` to read a single element is what this exists to prevent.

It reads through the same four element denotations `atoms` maps — `bitAt`, `foRBits`
and `bitsAt` under `atomOfBits` — so there is one statement of what element `i` is and this is not
a second one. What differs is only what is hoisted: `atoms` computes the block starts once for the
whole column, and here the table is empty, so `foRBits` sums the blocks before `i` and stops —
`i / 1024` steps and no allocation, against `count / 1024` for the whole table.

The body used to be `(atoms t c)[i]!`, which materialised the whole column to read one element of
it — 64 lookups on a vector of a million cost 64 million boxed atoms. It had no caller yet, so
nothing was slowed by it; `tools/bench-ts.lean` was the first and measured 3.4 µs per element
before this was fixed. -/
def get (t : QAtomicType) (n : USize) (e : Ext.Enc X) (i : Nat) (starts : Array Nat := #[]) : Option QAtom :=
  if i < n.toNat then
    match t, e with
    | t, .foR metadata pack =>
      -- `starts` is `#[]` (no hoisted table) for a single read: `foRBits` then sums the blocks before `i`, which
      -- `blockStarts_get` says is the start a whole-column reader passing `blockStarts metadata` reads out of it
      match hw : t.width with
      | some _ => some (atomOfBits t (foRBits metadata pack starts i) (QAtomicType.ne_general_of_width hw))
      | none => none
    | .i64, .pos => some (.i64 (Int64.ofNat i))
    | _, _ => none
  else none


end Ext.Enc

/-- `v` is a vector at `t` holding `n` elements laid out as its type has them. Where a proof needs a
typed vector it takes `{v : QValue // v.WFAt t n}`. -/
def Ext.QValue.WFAt (t : QAtomicType) (n : USize) : Ext.QValue X → Prop
  | .vector t' n' e _ => t' = t ∧ n' = n ∧ Enc.WF t n e
  | _ => False

namespace Column
open Ext.Enc



/-- The bit an atom contributes to a boolean column. -/
def boolOf (a : QAtom) : Bool := match a with | .u1 b => b | _ => false



end Column

namespace QTable

end QTable

end Rel
