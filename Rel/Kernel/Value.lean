import Rel.Kernel.Need

/-! The part of `Rel.Value` the Rel kernels reach; `Rel.Value` imports it. -/


namespace Rel

/-- The element type of a q list, q's list type codes 0 to 19, in type-code order. `general` is type 0,
a list of any values. q has no type-0 atom, so `general` is a column type with no atom value: a function
that reads or builds an atom (`atomOfBits`, `Column.ofAtoms`) takes `t ≠ .general`. A general list's
null is not a function of its type either: it depends on the value (its first item's typed null, its
empty vector, or `()`). -/
inductive QAtomicType
  | general
  | boolean | guid | byte | short | int | long | real | float | char | symbol
  | timestamp | month | date | datetime | timespan | minute | second | time
  deriving Repr, DecidableEq, Inhabited, Hashable

namespace QAtomicType

/-- Bytes per element **in the IPC wire format and in splayed column files** — deliberately not the
in-memory width. `boolean` is one byte on the wire and one *bit* in memory, so `Column` answers for
it before ever consulting this; anything reading a `Column` through `width` is a bug. Symbols are
variable width (NUL-terminated) and so have no fixed size, and a general list's elements are values,
not bytes. -/
def width : QAtomicType → Option Nat
  | boolean | byte | char => some 1
  | short => some 2
  | int | real | month | date | minute | second | time => some 4
  | long | float | timestamp | datetime | timespan => some 8
  | guid => some 16
  | symbol | general => none

end QAtomicType

/-- A 16-byte GUID. -/
abbrev Guid := Vector UInt8 16

namespace Bits

def f64IsNaN (b : UInt64) : Bool := (b >>> 52) &&& 0x7ff == 0x7ff && b &&& 0xfffffffffffff != 0
def f32IsNaN (b : UInt32) : Bool := (b >>> 23) &&& 0xff == 0xff && b &&& 0x7fffff != 0

end Bits

/-- A q atom. One constructor per atomic type so that no ill-typed atom is representable;
the payload is the raw wire value, including null and infinity sentinels. -/
inductive QAtom
  | boolean : Bool → QAtom
  | guid : Guid → QAtom
  | byte : UInt8 → QAtom
  | short : Int16 → QAtom
  | int : Int32 → QAtom
  | long : Int64 → QAtom
  | real : UInt32 → QAtom
  | float : UInt64 → QAtom
  | char : UInt8 → QAtom
  | symbol : String → QAtom
  | timestamp : Int64 → QAtom
  | month : Int32 → QAtom
  | date : Int32 → QAtom
  | datetime : UInt64 → QAtom
  | timespan : Int64 → QAtom
  | minute : Int32 → QAtom
  | second : Int32 → QAtom
  | time : Int32 → QAtom
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

mutual

/-- A q value, typed at run time as q's `K` is. `vector` carries its element type and its length in a
header as a q vector does: the payload is untyped bytes, the header's `t` is what says how wide an
element is and how to read it, and `Enc.atoms` is the only way back to atoms. An element of the wrong
type is not representable — `Column.atoms_type` proves it. What remains as an external condition is
that the payload's shape agrees with the header; `Enc.WF` states that, and `QValue.WFAt` on a value.

`vector` is every list, a general one included: a general list is `.vector .general xs.size (.gen xs)`,
which the pattern `QValue.general` names. One constructor, so a list has one representation; a header
the payload disagrees with is `Enc.mismatch`. -/
inductive QValue
  | atom : QAtom → QValue
  /-- `t` and `n` are read, never inferred from the payload — `⌈n/8⌉` bytes, a block count or a pack
  at width `w` do not determine `n`. `attr` is the attribute, at the wire's code 1 to 4, and the cell
  holding the index q builds when it applies it, `none` for no attribute; a general list's mark is
  here too, and an enumeration's is on its indices. Set through `QValue.mark`, read through
  `QValue.attrCell`. -/
  | vector : (t : QAtomicType) → (n : USize) → (enc : Enc) → (attr : Option (UInt8 × IndexCell)) → QValue
  /-- The `Bool` is q's sorted dictionary, type 127: measured, it is not the key's `` `s `` —
  `` -8!(`s#`a`b)!1 2 `` writes 99, and `-9!` of a 127 over a bare key keeps the key bare. -/
  | dict : QValue → QValue → (sorted : Bool) → QValue
  | table : QTable → QValue
  /-- A keyed table: a dictionary whose key and value are both tables. The implicit `IndexCell` holds
  the key-row index (`Index.keys`), built on the table's first lookup or append and kept and extended
  from then on; a construction goes through `QValue.key`. The `Bool` is `dict`'s: q's sorted
  dictionary, `` `s#kt ``, which no flag of either table says. -/
  | keyed : QTable → QTable → (sorted : Bool) → {ix : IndexCell} → QValue
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
  | slices : (t : QAtomicType) → (n : USize) → (enc : Enc) → (attr : Option (UInt8 × IndexCell)) →
      Array Nat → QValue
  /-- Functions and their relatives, wire types 100–112, kept as raw decoded components.
  The checker treats these as `dynamic` until the lambda's source can be re-parsed. -/
  | func : Int8 → Array QValue → QValue
  /-- A q error (wire type −128), carrying the error text without its leading backtick. -/
  | err : String → QValue
  /-- An enumeration, q's types ±20: the global named `domain` indexed by `ix`, a `long` atom or a
  `long` vector. The name, not q's session code, is the identity (`Prim.Ty.enum`), and what an
  index denotes is read from the global at each use, because `` `d?x `` extends the domain in place
  under the enumerations already built over it.

  The indices are an ordinary `long` column and so encoded like one: they lie in `[0, count d)`,
  which frame-of-reference packs to the domain's bit width, where `int` would only halve it. -/
  | enum : String → QValue → QValue
  deriving Inhabited

/-- A q table: column names paired with equal-length column vectors, and the attribute byte q holds on
the table itself (`62 0N`: `0` none, then `` `s `` `` `u `` `` `p `` `` `g ``), which no column says:
`-9!` of `62 02` answers a table whose `attr` is `` `u `` with every column bare. -/
inductive QTable
  -- the byte is here, not on `QValue.table`, because `keyed` holds two tables and q marks either one
  -- (`` `s#kt `` the key, `asc kt` the value), so one field serves all three places a table sits
  | mk : Array String → Array QValue → (attr : UInt8) → QTable
  deriving Inhabited

/-- A vector's payload, one constructor per layout. No constructor stores the element count: it is
the header's `n` on `QValue.vector`, one source for it. -/
inductive Enc
  /-- Fixed-width types other than boolean, guid's 16 bytes included: q's own layout, little-endian,
  byte for byte the same as the IPC wire format and a splayed column file. Booleans are `bits`, not
  this. -/
  | bytes : ByteArray → Enc
  /-- Booleans, one *bit* each, LSB first within a byte. q spends a byte per boolean; a bit is
  eight times less memory, and it is also the shape every comparison wants — a predicate over 100M
  elements writes 12.5 MB here against q's 100 MB.

  `⌈n/8⌉` is not invertible — a 3-byte payload holds between 17 and 24 booleans — which is why the
  count is the header's. This is the one type whose in-memory width differs from its wire width, so
  `QLean/Wire/` and `QLean/Db/` expand and contract it instead of copying. -/
  | bits : ByteArray → Enc
  /-- Symbols. `blob` is each symbol's UTF-8 bytes *followed by its NUL*, concatenated — byte for
  byte the IPC payload and the splayed `sym` file, so sending it is a memcpy. `offs` holds the n+1
  starts, `offs[0] = 0` and `offs[n] = blob.size`; symbol `i` is `blob[offs[i] .. offs[i+1] - 1]`,
  without that trailing NUL. `offs` never crosses the wire, it is rebuilt by scanning for NULs.

  `Nat` offsets, not fixed-width entries packed into a `ByteArray`. Any fixed width wraps: at four
  bytes a blob reaching `2 ^ 32` makes the last offset come back smaller than the first, `symBytes`'
  `hi > lo` guard fail, and the column read back as empty symbols — silent corruption. Widening to
  eight only moves the counterexample to `2 ^ 64`; `Nat` ends the family, and that is what lets the
  round-trip theorem hold with no size hypothesis. Refusing to encode an oversized blob instead
  would cost more: `ofAtoms_isSome` is what makes `QLean/Dep/Val.lean`'s pack total, so a symbol
  column that can fail would put an `Option` back into the indexed world.

  This costs nothing at run time. A `Nat` below `2 ^ 63` is a tagged scalar in the `lean_object*`
  slot, so the table is one word per entry and allocates nothing — the boxing that rules out an
  `Array UInt64` here does not apply to `Nat`. -/
  | syms : (blob : ByteArray) → (offs : Array Nat) → Enc
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
  whose total is not the column's total in any domain, and `Coc.nullOf` declines a float before the
  question is asked.

  The element count is the header's for the reason `bits`' is: `nblk` only bounds it to a multiple
  of `blk`. Only fixed-width types other than `boolean` and `guid` can be encoded (`Column.WF`). A
  `float` column is legal here and lossless, but it is Frame of Reference over raw IEEE *bit
  patterns*, which compresses nothing -- the encoding that does is ALP, and it is a separate
  constructor. -/
  | foR : (metadata : ByteArray) → (pack : ByteArray) → Enc
  /-- ALP: a float column as the decimal integers `d = round (x * 10 ^ e)`, one exponent `e` per
  block, `d` carried by `foR`'s own `metadata` and `pack`, and everything that is not a decimal at
  its block's `e` — q's `0n`, `0w` and `-0w` among them — set aside raw in `alp`. Decoding
  **divides**: `x = d / 10 ^ e`. `rust/src/coc.rs`'s section on ALP states the four rules that make that
  lossless and `tools/coc/note.md` §8 measures it; `Column.alpBits` is the denotation.

  **A constructor of its own, not a sixth metadata section inside `foR`.** The exports in `rust/src/coc.rs`
  already say so — `qlean_alp_encode_f64` answers three `ByteArray`s where `qlean_coc_encode`
  answers two — and the reason they do is that the exponents, the exception offsets, the exception
  positions and the raw exceptions are read by *no* integral kernel. Folding them into `foR`'s
  metadata would put four sections and a header on every `long` column that will never look at them,
  and would make `Column.nblk`'s `metadata.size / 33` — the one place the block count comes from —
  depend on which type the tag carries.

  `alp` is 16 header bytes, `nexc : UInt64` then a flag word whose bit 0 is set for a four-byte
  element, followed by `exc_raw` at 16, `exc_off : UInt32[nblk+1]`, `exc_pos : UInt16[nexc]` and
  `exp : Int8[nblk]`, each section starting on a multiple of eight. `Column.alpSects` is that ladder
  and `rust/src/coc.rs`'s `alp_layout` is the same one written once for its reader and its writer.

  An exception's slot in the pack holds the block minimum, i.e. residual zero, so it can never widen
  the pack and what it wrongly contributes to a reduction is a known constant the kernels subtract
  back out. That is what keeps every reduction on the shared integral kernels.

  Only `real`, `float` and `datetime` reach here; `Column.alpEncodes` is that list, and
  `Column.admit` is where a column takes this form and where a column the decimal hypothesis fails
  on is left dense instead. -/
  | alp : (metadata : ByteArray) → (pack : ByteArray) → (alp : ByteArray) → Enc
  /-- Symbols interned: `dict` and `offs` are the *distinct* symbols in `syms` layout, and `ids` is
  the header's `n` dictionary indices **bit-packed at `idWidth`**, which is the residual packing `foR` uses
  and not a width of its own. `=`, `asc`, `distinct`, `group`, `in` and `?` then become integer work
  on a payload the kernels are already written for, and the blob is touched only when a symbol has
  to be printed or sent. This is to `syms` what `foR` is to `bytes`.

  **The id space is the column's own, so its width is the dictionary's and not four bytes.** An
  `Int32` id spends 4 MB on a million elements over three symbols where two bits an element spend
  250 KB, and these lines are memory-traffic bound: `asc`, `group` and `in` over a symbol column
  read the ids and nothing else. `d` is `offs.size - 1` and needs no field; the count is the
  header's — `⌈n·w/8⌉` is not invertible, and at `w = 0` the pack is empty for every `n`.

  **The dictionary is the column's own, not a process-wide table.** q interns into a global symbol
  table and compares pointers; a `Column` that meant nothing without that ambient state could not
  round-trip, could not be serialised on its own and could not carry its own theorems, so the id
  space is per column. What that costs is the one thing a shared table would have given free: two
  columns do not agree on ids, so a cross-column verb maps one dictionary onto the other first —
  `Kernel.symTranslate`, d₁+d₂ symbol comparisons, and then n integer ones. -/
  | enum : (dict : ByteArray) → (offs : Array Nat) → (ids : ByteArray) → Enc
  /-- A general list, q's type 0: its elements as values, under the header type
  `QAtomicType.general`: the pattern `QValue.general`. Under an atom type it is a mismatch,
  `Column.mismatch`, as a typed payload under `general` is.

  Last, so the constructor tags of the six before it are unchanged: `rust/src/structural.rs` builds a
  `bytes` payload as constructor 0 with one field. -/
  | gen : Array QValue → Enc
  deriving Inhabited

end

namespace Column

/-- What `bitsAt` runs as: the same bytes ORed at the same shifts, with the four widths a
`QAtomicType` actually has written out. What that buys is the per-byte `8 * w` and its
`Nat.toUInt64` -- two boxed-`Nat` calls of the twelve a byte costs -- becoming a literal, and the
loop's own `Nat.decEq` and `Nat.sub` going away entirely. The bounds test stays inside each byte,
so a short payload still reads `0` past its end exactly as the body says. Widths outside the four
take the general fold, which is the body's equation with the recursion turned into `Nat.fold`.

The element width is the parameter and the switch on it is hoisted out of the loop, which is
`rust/src/coc.rs`'s own shape for the same reason: each width becomes its own straight-line read. -/
private def bitsAtImpl (b : ByteArray) (o w : Nat) : UInt64 :=
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
private def pushBitsImpl (out : ByteArray) (v : UInt64) (w : Nat) : ByteArray :=
  Nat.fold w (init := out) fun k _ acc => acc.push (v >>> (8 * k).toUInt64).toUInt8

/-- The low `w` bytes of `v`, little-endian. Recursion on `w` for the reason `bitsAt` gives. -/
@[implemented_by pushBitsImpl]
def pushBits (out : ByteArray) (v : UInt64) : Nat → ByteArray
  | 0 => out
  | w + 1 => (pushBits out v w).push (v >>> (8 * w).toUInt64).toUInt8

/-- Bit `i`, LSB first within a byte. Past the end reads `false`. -/
def bitAt (b : ByteArray) (i : Nat) : Bool :=
  ((b[i / 8]?.getD 0) >>> (i % 8).toUInt8) &&& 1 == 1

/-- The `i`th symbol's bytes, as `(start, length)` into `blob`, with the stored NUL excluded. The
comparisons, sorts and hashes in `QLean/Eval/` go through this rather than `atoms`, because building
a `String` per symbol is exactly the allocation this layout removes. Past the table it is `(0, 0)`, the
empty symbol an id past the dictionary denotes, by the guard and not by `!`'s panicking default. -/
def symBytes (offs : Array Nat) (i : Nat) : Nat × Nat :=
  if i + 1 < offs.size then
    let lo := offs[i]!
    let hi := offs[i + 1]!
    (lo, if hi > lo then hi - lo - 1 else 0)
  else (0, 0)

/-- The `i`th symbol's bytes, without its stored NUL — the form every comparison reads. -/
def symKey (blob : ByteArray) (offs : Array Nat) (i : Nat) : ByteArray :=
  let (lo, len) := symBytes offs i
  blob.extract lo (lo + len)

/-- q's order on two symbols' bytes: the first byte they differ at, unsigned, and their lengths when
neither is a prefix of the other. Measured — `` iasc `$("ab";"a";"aa";"") `` is `3 1 2 0` and
`` iasc `$("é";"z";"a") `` is `2 1 0`. Here rather than in a kernel because three of them read it —
the sort, the search and the element-wise comparisons — and none imports the others. -/
def symCmp (x y : ByteArray) : Ordering :=
  match (List.range (min x.size y.size)).find? fun i => x[i]?.getD 0 != y[i]?.getD 0 with
  | some i => compare (x[i]?.getD 0) (y[i]?.getD 0)
  | none => compare x.size y.size

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

/-- The `lg` every encoder writes. -/
def lgEnc : Nat := 10

/-- Block `b`'s minimum, as raw bits: the value its residuals are measured from. -/
def baseAt (metadata : ByteArray) (b : Nat) : UInt64 := bitsAt metadata (b * 8) 8

/-- Block `b`'s maximum, as raw bits. The denotation below never reads it — `foRBits` needs only the
minimum and the residual — but it is one of the sections and the kernels that answer `max` and that
move a block whole read it, so it is stated here beside the section it neighbours. -/
def maxvAt (metadata : ByteArray) (b : Nat) : UInt64 :=
  bitsAt metadata (8 * nblk metadata + b * 8) 8

/-- Block `b`'s cached sum, as raw bits. A cache like `maxv`, and read by even less: the denotation
never touches it and neither does any Lean body here, `Coc.over`'s being the fold over the elements
that the C answers from this instead. `sumNulAt` is the condition under which it may. -/
def bsumAt (metadata : ByteArray) (b : Nat) : UInt64 :=
  bitsAt metadata (24 * nblk metadata + b * 8) 8

/-- The null `bsumAt` skipped, and `0` — no type's null — for metadata that carries no sums. -/
def sumNulAt (metadata : ByteArray) : Int64 := (bitsAt metadata (32 * nblk metadata) 8).toInt64

/-- The element count `bsumAt` was taken at. It is not `count`: `Column.appendFoR` answers a longer
column with the metadata of a shorter one, and this is what says the sums are that shorter one's. -/
def sumCountAt (metadata : ByteArray) : Nat := (bitsAt metadata (32 * nblk metadata + 8) 8).toNat

/-- Block `b`'s residual bit width, one of 0/1/2/4/8/16/32/64. -/
def widthAt (metadata : ByteArray) (b : Nat) : Nat :=
  (metadata[32 * nblk metadata + 24 + b]?.getD 0).toNat

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
@[extern "qlean_coc_block_start"]
def blockStart (metadata : @& ByteArray) (b : @& Nat) : Nat :=
  Nat.fold b (init := 0) fun c _ pos => pos + blk metadata * widthAt metadata c / 8

/-- What `resAt` runs as: one eight-byte read at the field's first byte, shifted down, and the ninth
byte only when the field straddles it. `rust/src/coc.rs`'s `res_get` is the same reading. -/
private def resAtImpl (pack : ByteArray) (s w j : Nat) : UInt64 :=
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
  let p := (o + (nblk + 1) * 4 + 7) / 8 * 8
  (o, p, (p + nexc * 2 + 7) / 8 * 8)

/-- Element `i`'s own bits when the pack's patch list holds it: the list `rust/src/coc.rs` lays after the
last block's residuals when some element is a null or an outlier, the ladder `alpSects` describes,
an element sign-extended from its stored width as `baseAt` is (one byte, q's unsigned pair, is not). -/
def foRExc (metadata pack : ByteArray) (i : Nat) : Option UInt64 :=
  let e := blockStart metadata (nblk metadata)
  if pack.size ≤ e then none else
  let esz := (bitsAt pack (e + 8) 8).toNat % 256
  let (o, p, _) := alpSects (nblk metadata) (bitsAt pack e 8).toNat esz
  let off (b : Nat) := (bitsAt pack (e + o + b * 4) 4).toNat
  let b := i / blk metadata
  ((List.range' (off b) (off (b + 1) - off b)).find?
      fun k => (bitsAt pack (e + p + k * 2) 2).toNat == i % blk metadata).map fun k =>
    let v := bitsAt pack (e + 16 + k * esz) esz
    let s := (64 - 8 * esz).toUInt64
    if esz == 1 then v else ((v <<< s).toInt64 >>> s.toInt64).toUInt64

/-- How far block `b`'s frame, the value its residuals are measured from, lies above its minimum:
the `u64` the patch list keeps per block after `exc_pos` when bit 8 of its width word says so, and
`0` for a pack with no patch list or no frames. A
frame above the minimum is what lets a low outlier be patched as a high one is. -/
def foRFrame (metadata pack : ByteArray) (b : Nat) : UInt64 :=
  let e := blockStart metadata (nblk metadata)
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
  match foRExc metadata pack i with
  | some v => v
  | none => baseAt metadata b + foRFrame metadata pack b +
    resAt pack (match starts[b]? with | some s => s | none => blockStart metadata b)
      (widthAt metadata b) (i % blk metadata)

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
  (bitsAt a ((alpSects (nblk metadata) (alpNexc a) (alpEsz a)).1 + b * 4) 4).toNat

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

/-- Bits one id takes in a column whose dictionary is `offs`: the ids run `0 .. d-1` for
`d = offs.size - 1`, so the range they span is `d - 1`.

`0` at `d ≤ 1` and that is the answer, not a floor to step over: a dictionary of one symbol has one
id, so a zero-width pack storing nothing at all denotes the right column once `count` is stored —
`resAt` already answers `0` at width `0`. `d = 0` lands there too and every read is then an id past
the dictionary, which is the empty symbol, the same convention a malformed payload has always had.

Derived and never stored: a stored width could disagree with the dictionary, and every kernel that
rebuilds a dictionary — the gather that appends the empty symbol, the symbol maps that re-intern —
would have to keep it in step. -/
def idWidth (offs : Array Nat) : Nat := idWidthOf (offs.size - 1)

/-- Element `i`'s dictionary index, at `w = idWidth offs` bits. Past the end reads `0`, the
convention `bitsAt` sets, so a malformed column answers rather than panicking.

`w` is the parameter and not the offsets, because every caller that loops hoists it — recomputing
the ladder per element is the mistake `blockStarts` exists to avoid on the other constructor. -/
def idAt (ids : ByteArray) (w i : Nat) : Nat := (resAt ids 0 w i).toNat

/-- How many of the first `n` ids a payload at `w` bits holds: `rust/src/ids.rs`'s `ids_avail` clamp, which
rounds `⌈n·w/8⌉` back down. Every id is there at width `0`, which stores nothing. -/
def idsCap (ids : ByteArray) (w n : Nat) : Nat := if w = 0 then n else min n (ids.size * 8 / w)

/-- `n` ids at `w` bits, `f i` being id `i` — `idAt`'s inverse and the one place an id payload is
laid out. The bits past `n` in the last byte stay `0` for the reason `packBits` clears its tail: two
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

/-- A `syms` payload as every writer of one lays it out: at least one start, the first `0`, the last the blob's
size, none past the blob, and none before the one ahead of it. `concatSyms` reads part `p`'s entries back only from
parts that hold this, and a cycling `sliceSyms` rebuilds the starts as a running total that matches its blob only
where they do not decrease. -/
structure SymsWF (b : ByteArray) (o : Array Nat) : Prop where
  pos : 0 < o.size
  first : o[(0 : Nat)]! = 0
  last : o[o.size - 1]! = b.size
  le : ∀ k < o.size, o[k]! ≤ b.size
  mono : ∀ k < o.size - 1, o[k]! ≤ o[k + 1]!

namespace Enc
open Column

/-- What the header promises about the payload: the layout is one `t` has, and it holds exactly `n`
elements. The conditions `count`, `admit` and `mismatch` used to encode between them, stated once;
every reader trusts the header, so a vector that fails this is a bug where it was built. Booleans are
`bits` and never `bytes`; Frame of Reference takes every fixed-width type but `boolean` and `guid`,
ALP the three float layouts; a `foR` or `alp` payload's blocks cover its `n`, and an `enum` payload's
pack holds its `n` ids and its dictionary's offsets end at its blob with none past it, so a symbol
appended to the dictionary leaves every entry before it reading as it did, and no entry is there twice,
so two ids name the same symbol only where they are equal. -/
def WF (t : QAtomicType) (n : USize) (e : Enc) : Prop :=
  match t, e with
  | .general, .gen xs => xs.size = n.toNat
  | .boolean, .bits b => b.size = (n.toNat + 7) / 8
  | .symbol, .syms blob offs => offs.size = n.toNat + 1 ∧ SymsWF blob offs ∧
    ∀ i < n.toNat, (symKey blob offs i).IsValidUTF8
  | .symbol, .enum dict offs ids => ids.size = (n.toNat * idWidth offs + 7) / 8 ∧ SymsWF dict offs ∧
    (∀ i < n.toNat, idAt ids (idWidth offs) i < offs.size - 1) ∧ ((List.range (offs.size - 1)).map fun i => (symKey dict offs i).data.toList).Nodup ∧
    ∀ i < offs.size - 1, (symKey dict offs i).IsValidUTF8
  | .boolean, .bytes _ => False
  | t, .bytes b => match t.width with
    | some w => b.size = n.toNat * w
    | none => False
  | t, .foR metadata _ =>
    t.width.isSome ∧ t ≠ .boolean ∧ t ≠ .guid ∧ n.toNat ≤ blk metadata * nblk metadata ∧ lgOk metadata
  | t, .alp metadata _ a =>
    (t = .real ∨ t = .float ∨ t = .datetime) ∧ n.toNat ≤ blk metadata * nblk metadata ∧ lgOk metadata ∧ alpF32 a = (t.width == some 4)
  | _, _ => False

/-- `atoms`' fixed-width branches before `atomOfBits`: the raw bits of each element. A theorem about a
numeric column is stated over this, because `atoms`' symbol branch brings `Classical.choice` with it. -/
def raw (t : QAtomicType) (n : USize) (e : Enc) : Array UInt64 :=
  match t, e with
  | .boolean, .bytes _ | .guid, .bytes _ | .boolean, .foR _ _
  | .guid, .foR _ _ => #[]
  | .boolean, .alp _ _ _ | .guid, .alp _ _ _ => #[]
  | t, .bytes b => match t.width with
    | some w => (Array.range n.toNat).map fun i => bitsAt b (i * w) w
    | none => #[]
  | t, .foR metadata pack => match t.width with
    | some _ =>
      let starts := blockStarts metadata; (Array.range n.toNat).map (foRBits metadata pack starts)
    | none => #[]
  | t, .alp metadata pack a => match t.width with
    | some _ =>
      let starts := blockStarts metadata; (Array.range n.toNat).map (alpBits metadata pack a starts)
    | none => #[]
  | _, _ => #[]

end Enc

namespace Column
open Enc

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

/-- Days from 2000.01.01 to the first of `y`-`m`, which is the month payload's own anchor: q's
`` `date$1999.12m `` is `1999.12.01`. Here and not in `Eval` because the kernels' unit conversion
(`Kernel.Ew.tickStep`) reads a month through it too. -/
def daysOfFirst (y m : Int) : Int :=
  let y := if m ≤ 2 then y - 1 else y
  let era := (if y ≥ 0 then y else y - 399) / 400
  let yoe := y - era * 400
  let doy := (153 * ((m + 9) % 12) + 2) / 5
  era * 146097 + (yoe * 365 + yoe / 4 - yoe / 100 + doy) - 730425
end Rel


namespace Rel

namespace QAtomicType

/-- The q type code of the *vector* form; the atom form is its negation. Code 3 is unused, and code 0,
the general list, has no atom form. -/
def code : QAtomicType → Int8
  | general => 0
  | boolean => 1 | guid => 2 | byte => 4 | short => 5 | int => 6 | long => 7
  | real => 8 | float => 9 | char => 10 | symbol => 11 | timestamp => 12
  | month => 13 | date => 14 | datetime => 15 | timespan => 16 | minute => 17
  | second => 18 | time => 19

/-- A type with a fixed width has atoms: how a reader that has matched `width` reaches a function
that takes `t ≠ .general`. -/
theorem ne_general_of_width {t : QAtomicType} {w : Nat} (h : t.width = some w) : t ≠ .general := by
  rintro rfl; cases h

end QAtomicType

namespace Bits

end Bits

namespace QAtom

def type : QAtom → QAtomicType
  | boolean _ => .boolean | guid _ => .guid | byte _ => .byte | short _ => .short
  | int _ => .int | long _ => .long | real _ => .real | float _ => .float
  | char _ => .char | symbol _ => .symbol | timestamp _ => .timestamp
  | month _ => .month | date _ => .date | datetime _ => .datetime
  | timespan _ => .timespan | minute _ => .minute | second _ => .second | time _ => .time

/-- q's `~` on atoms: bit-pattern identity, so a null matches a null. -/
def identical : QAtom → QAtom → Bool
  | boolean a, boolean b => a == b
  | guid a, guid b => a.toArray == b.toArray
  | byte a, byte b | char a, char b => a == b
  | short a, short b => a == b
  | int a, int b | month a, month b | date a, date b
  | minute a, minute b | second a, second b | time a, time b => a == b
  | long a, long b | timestamp a, timestamp b | timespan a, timespan b => a == b
  -- the two zeros are one value to `~` even though their bit patterns differ: measured,
  -- `-0.0~0.0` and `-0.0e~0.0e` are both `1b`, and `distinct -0.0 0.0` is the single `,-0f`.
  -- Everything else stays bit equality, which is what keeps `0n~0n` true.
  | real a, real b => a == b || (a &&& 0x7fffffff == 0 && b &&& 0x7fffffff == 0)
  | float a, float b | datetime a, datetime b =>
    a == b || (a &&& 0x7fffffffffffffff == 0 && b &&& 0x7fffffffffffffff == 0)
  | symbol a, symbol b => a == b
  | _, _ => false

end QAtom

/-- A general list, q's type 0: the `general` column over `gen`, the one representation a list has.
A pattern too, written `.general xs _ _`: the count is the header's and `xs.size` is not a pattern, so
both a match and a construction name it; a construction from a Lean `Array` whose count is not in scope
goes through `QValue.ofArray`. The attribute is a parameter because a general list carries one in q
(`` `u#(1;`a) ``), and a pattern that pinned `none` would miss it; a construction defaults it to `none`. -/
@[match_pattern] abbrev QValue.general (xs : Array QValue) (n : USize)
    (a : Option (UInt8 × IndexCell) := none) : QValue :=
  .vector .general n (.gen xs) a

/-- A general list over `xs`, its count `xs.size`: the one place a Lean `Array`'s size becomes a
`USize` count, under the proof that it fits. -/
def QValue.ofArray (xs : Array QValue) : QValue :=
  Kernel.needSize xs.size "ofArray: elements" (fun _ => .general #[] 0) fun n => .general xs n

namespace Column

/-- The raw bits a fixed-width atom occupies, as q writes them.

Floats stay *bits*: `QAtom.float` already holds the wire pattern, and it must never pass through
`Float.ofBits`, which canonicalises `0xfff8000000000000` — q's `0n` — to `0x7ff8000000000000` and so
corrupts every float null. `guid` and `symbol` are not scalars and do not come through here. -/
def bitsOf : QAtom → UInt64
  | .boolean x => if x then 1 else 0
  | .byte x | .char x => x.toUInt64
  | .short x => x.toUInt16.toUInt64
  | .int x | .month x | .date x | .minute x | .second x | .time x => x.toUInt32.toUInt64
  | .long x | .timestamp x | .timespan x => x.toUInt64
  | .real x => x.toUInt64
  | .float x | .datetime x => x
  | .guid _ | .symbol _ => 0

/-- The atom of type `t` those raw bits denote. Total, and its type is `t` by construction, which is
what `atoms_type` turns into the invariant `QLean/Verify/` used to assume. `guid` and `symbol` are
handled by `atoms` directly and answer their own null here. `general` has no atom. -/
def atomOfBits (t : QAtomicType) (v : UInt64) (h : t ≠ .general := by first | decide | assumption) :
    QAtom :=
  match t with
  | .general => absurd rfl h
  | .boolean => .boolean (v != 0)
  | .byte => .byte v.toUInt8
  | .char => .char v.toUInt8
  | .short => .short v.toUInt16.toInt16
  | .int => .int v.toUInt32.toInt32
  | .month => .month v.toUInt32.toInt32
  | .date => .date v.toUInt32.toInt32
  | .minute => .minute v.toUInt32.toInt32
  | .second => .second v.toUInt32.toInt32
  | .time => .time v.toUInt32.toInt32
  | .long => .long v.toInt64
  | .timestamp => .timestamp v.toInt64
  | .timespan => .timespan v.toInt64
  | .real => .real v.toUInt32
  | .float => .float v
  | .datetime => .datetime v
  | .guid => .guid (Vector.replicate 16 0)
  | .symbol => .symbol ""

/-- Booleans packed eight to a byte, LSB first. The unused tail bits of the last byte stay `0`, so
two columns holding the same booleans hold the same bytes — `~` and `atomIdenticalHash` compare
payloads, and trailing garbage would make equal vectors compare unequal. -/
def packBits (as : Array QAtom) : ByteArray := Id.run do
  let mut out := ByteArray.emptyWithCapacity ((as.size + 7) / 8)
  let mut cur : UInt8 := 0
  for i in [0 : as.size] do
    if (match as[i]! with | .boolean b => b | _ => false) then
      cur := cur ||| (1 <<< (i % 8).toUInt8)
    if i % 8 == 7 then
      out := out.push cur
      cur := 0
  if as.size % 8 != 0 then out := out.push cur
  return out

/-- A payload of exactly `⌈n·w/8⌉` bytes, the size every writer lays out, holds all `n` ids. -/
theorem idsCap_of_size {ids : ByteArray} {w n : Nat} (h : ids.size = (n * w + 7) / 8) : idsCap ids w n = n := by
  unfold idsCap; split
  · rfl
  · rw [h]; refine Nat.min_eq_left ((Nat.le_div_iff_mul_le (by omega)).2 ?_); generalize n * w = k; omega

end Column

instance (b : ByteArray) (o : Array Nat) : Decidable (SymsWF b o) :=
  decidable_of_iff (0 < o.size ∧ o[(0 : Nat)]! = 0 ∧ o[o.size - 1]! = b.size ∧ (∀ k < o.size, o[k]! ≤ b.size) ∧
      ∀ k < o.size - 1, o[k]! ≤ o[k + 1]!)
    ⟨fun h => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩, fun h => ⟨h.pos, h.first, h.last, h.le, h.mono⟩⟩

namespace Enc
open Column

instance (t : QAtomicType) (n : USize) (e : Enc) : Decidable (WF t n e) := by
  unfold WF; split <;> (try split) <;> exact inferInstance

/-- `n` elements of `t`, all zero bits, for every `n`: the value a failed `need`'s model answers. It
needs no bound because a replicated array has the size asked for. -/
def blank (t : QAtomicType) (n : USize) : Enc :=
  match t, t.width with
  | .general, _ => .gen (Array.replicate n.toNat default)
  | .boolean, _ => .bits ⟨Array.replicate ((n.toNat + 7) / 8) 0⟩
  | .symbol, _ => .syms .empty (Array.replicate (n.toNat + 1) 0)
  | _, some w => .bytes ⟨Array.replicate (n.toNat * w) 0⟩
  | _, none => .gen #[]

theorem blank_WF (t : QAtomicType) (n : USize) : WF t n (blank t n) := by
  cases t
  case symbol =>
    have h0 : ∀ k, (Array.replicate (n.toNat + 1) 0)[k]! = 0 := fun k => by
      by_cases hk : k < n.toNat + 1
      · rw [getElem!_pos _ k (by simpa using hk)]; simp
      · rw [getElem!_neg _ k (by simpa using hk)]; rfl
    show (Array.replicate (n.toNat + 1) 0).size = n.toNat + 1 ∧ SymsWF ByteArray.empty (Array.replicate (n.toNat + 1) 0) ∧
      ∀ i < n.toNat, (symKey ByteArray.empty (Array.replicate (n.toNat + 1) 0) i).IsValidUTF8
    -- every entry is the empty bytes, which are valid
    exact ⟨by simp, ⟨by simp, h0 0, by rw [h0]; rfl, fun k _ => by rw [h0]; exact Nat.zero_le _,
      fun k _ => by rw [h0, h0]; exact Nat.le_refl _⟩, fun i _ => by simp only [symKey, symBytes, h0]; split <;> decide⟩
  all_goals simp [blank, WF, QAtomicType.width, ByteArray.size]

/-- One element, without materialising the rest. `first`, `last`, indexing and every binary search
belong here; calling `atoms` to read a single element is what this exists to prevent.

It reads through the same four element denotations `atoms` maps — `bitAt`, `symBytes`, `foRBits`
and `bitsAt` under `atomOfBits` — so there is one statement of what element `i` is and this is not
a second one. What differs is only what is hoisted: `atoms` computes the block starts once for the
whole column, and here the table is empty, so `foRBits` sums the blocks before `i` and stops —
`i / 1024` steps and no allocation, against `count / 1024` for the whole table.

The body used to be `(atoms t c)[i]!`, which materialised the whole column to read one element of
it — 64 lookups on a vector of a million cost 64 million boxed atoms. It had no caller yet, so
nothing was slowed by it; `tools/bench-ts.lean` was the first and measured 3.4 µs per element
before this was fixed. -/
def get (t : QAtomicType) (n : USize) (e : Enc) (i : Nat) : Option QAtom :=
  if i < n.toNat then
    match t, e with
    | .boolean, .bits b => some (.boolean (bitAt b i))
    | .symbol, .syms blob offs =>
      let (lo, len) := symBytes offs i
      some (.symbol ((String.fromUTF8? (blob.extract lo (lo + len))).getD ""))
    | .symbol, .enum dict offs ids =>
      let (lo, len) := symBytes offs (idAt ids (idWidth offs) i)
      some (.symbol ((String.fromUTF8? (dict.extract lo (lo + len))).getD ""))
    | .guid, .bytes b =>
      some (.guid (Vector.ofFn fun k : Fin 16 => (b[i * 16 + k.val]?).getD 0))
    | t, .bytes b => match hw : t.width with
      | some w => some (atomOfBits t (bitsAt b (i * w) w) (QAtomicType.ne_general_of_width hw))
      | none => none
    | t, .foR metadata pack =>
      -- `#[]` is "no hoisted table": `foRBits` then sums the blocks before `i` rather than all of
      -- them, which `blockStarts_get` says is the same start `atoms` reads out of the table
      match hw : t.width with
      | some _ => some (atomOfBits t (foRBits metadata pack #[] i) (QAtomicType.ne_general_of_width hw))
      | none => none
    | t, .alp metadata pack a =>
      match hw : t.width with
      | some _ => some (atomOfBits t (alpBits metadata pack a #[] i) (QAtomicType.ne_general_of_width hw))
      | none => none
    | _, _ => none
  else none

/-- Symbols as `blob` plus its offset table. -/
def symsOf (as : Array QAtom) : Enc :=
  let bs := as.map fun | .symbol s => s.toUTF8 | _ => ByteArray.empty
  let offs := bs.foldl (init := (#[0], 0)) fun (o, pos) s =>
    (o.push (pos + s.size + 1), pos + s.size + 1)
  let blob := bs.foldl (init := ByteArray.empty) fun acc s => (acc ++ s).push 0
  .syms blob offs.1

/-- The payload holding exactly these atoms at `t`, count `as.size`, or `none` if one of them is not
at `t`. Only the payload, because the header is the caller's arguments: `.vector t as.size e none`.
The caller decides what a mismatch means — `Eval.vectorOf` answers with a general list, which is q's
own behaviour — so this never coerces. -/
def ofAtoms (t : QAtomicType) (as : Array QAtom) (h : t ≠ .general := by first | decide | assumption) :
    Option Enc :=
  if as.all (·.type == t) then match t with
    | .general => absurd rfl h
    | .boolean => some (.bits (packBits as))
    | .symbol => some (symsOf as)
    | .guid =>
      some (.bytes (as.foldl (init := ByteArray.emptyWithCapacity (as.size * 16))
        fun acc a => match a with
          | .guid g => g.toArray.foldl ByteArray.push acc
          | _ => acc))
    | t => match t.width with
      | some w =>
        some (.bytes (as.foldl (init := ByteArray.emptyWithCapacity (as.size * w))
          fun acc a => pushBits acc (bitsOf a) w))
      | none => none
  else none

end Enc

/-- `v` is a vector at `t` holding `n` elements laid out as its type has them. Where a proof needs a
typed vector it takes `{v : QValue // v.WFAt t n}`. -/
def QValue.WFAt (t : QAtomicType) (n : USize) : QValue → Prop
  | .vector t' n' e _ => t' = t ∧ n' = n ∧ Enc.WF t n e
  | _ => False

namespace Column
open Enc

/-- `ofAtoms` fails on exactly one condition, so a caller that already knows its atoms are at `t`
gets a payload back. Every assembler in `QLean/Eval/` establishes that condition by filtering or
testing before it commits to a vector, which is what makes its announced type honest. -/
theorem ofAtoms_isSome {t : QAtomicType} {as : Array QAtom} (hn : t ≠ .general)
    (h : ∀ a ∈ as, a.type = t) : (ofAtoms t as).isSome := by
  unfold ofAtoms
  rw [if_pos (Array.all_eq_true'.mpr fun x hx => by simp [h x hx])]
  cases t <;> first | contradiction | simp [QAtomicType.width]

/-- The fold appends `w` bytes per element. -/
private theorem foldl_pushBits_size {w : Nat} (b : ByteArray) (as : List QAtom) :
    (as.foldl (fun acc a => pushBits acc (bitsOf a) w) b).size = b.size + as.length * w := by
  induction as generalizing b with
  | nil => simp
  | cons a as ih => rw [List.foldl_cons, ih, pushBits_size]; simp [Nat.succ_mul]; omega

/-- The bit an atom contributes to a boolean column. -/
def boolOf (a : QAtom) : Bool := match a with | .boolean b => b | _ => false

/-- Bit `j` of a byte, LSB first: what `bitAt` reads once it has located the byte. -/
def byteBit (x : UInt8) (j : Nat) : Bool := (x >>> j.toUInt8) &&& 1 == 1

/-- One iteration of `packBits`' loop on the `(cur, out)` pair its `do` block threads. The pair is
an `MProd`, not a `Prod`: that is how the `do` elaborator bundles two `mut` variables. -/
def packStep (as : Array QAtom) (r : MProd UInt8 ByteArray) (i : Nat) :
    MProd UInt8 ByteArray :=
  if boolOf as[i]! = true then
    if (i % 8 == 7) = true then ⟨0, r.2.push (r.1 ||| 1 <<< (i % 8).toUInt8)⟩
    else ⟨r.1 ||| 1 <<< (i % 8).toUInt8, r.2⟩
  else if (i % 8 == 7) = true then ⟨0, r.2.push r.1⟩ else ⟨r.1, r.2⟩

/-- Folds with pointwise equal steps agree. `packBits`' body elaborates to its own `match`
auxiliary, which is not the one `boolOf` builds, so the two step functions have to be compared
element by element rather than by `rfl`. -/
private theorem foldl_ext {α β : Type} {f g : β → α → β} (init : β) (l : List α)
    (h : ∀ b a, f b a = g b a) : l.foldl f init = l.foldl g init := by
  induction l generalizing init with
  | nil => rfl
  | cons a l ih => rw [List.foldl_cons, List.foldl_cons, h, ih]

/-- Both arms of the loop body yield, so the `if` can be pulled out of the monad and the loop
collapses to a `foldl`. -/
private theorem ite_pure_yield {β : Type} (c : Prop) [Decidable c] (a b : β) :
    (if c then (pure (ForInStep.yield a) : Id (ForInStep β)) else pure (ForInStep.yield b))
      = pure (ForInStep.yield (if c then a else b)) := by
  split <;> rfl

/-- `packBits` as a fold over the loop's index list, plus the flush of the last partial byte. -/
theorem packBits_eq (as : Array QAtom) (r : MProd UInt8 ByteArray)
    (hr : r = (List.range' 0 as.size).foldl (packStep as)
      ⟨0, ByteArray.emptyWithCapacity ((as.size + 7) / 8)⟩) :
    packBits as = if as.size % 8 = 0 then r.2 else r.2.push r.1 := by
  subst hr
  simp only [packBits, Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    ite_pure_yield, List.forIn_pure_yield_eq_foldl, pure_bind, bne_iff_ne, ne_eq,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one]
  by_cases hm : as.size % 8 = 0
  · rw [if_neg fun hn => hn hm, if_pos hm]
    simp only [Id.run_pure]
    apply congrArg MProd.snd
    apply foldl_ext
    intro b a
    cases hx : as[a]! <;> simp [packStep, boolOf, hx]
  · rw [if_pos hm, if_neg hm]
    simp only [Id.run_pure]
    apply congrArg fun r : MProd UInt8 ByteArray => r.2.push r.1
    apply foldl_ext
    intro b a
    cases hx : as[a]! <;> simp [packStep, boolOf, hx]

/-- A read inside the prefix is untouched by a push. -/
theorem bitAt_push_lt (b : ByteArray) (x : UInt8) (i : Nat) (h : i / 8 < b.size) :
    bitAt (b.push x) i = bitAt b i := by
  simp only [bitAt, push_getElem?_lt (b := b) (x := x) (j := i / 8) h]

/-- A read in the byte just pushed. -/
theorem bitAt_push_eq (b : ByteArray) (x : UInt8) (i : Nat) (h : i / 8 = b.size) :
    bitAt (b.push x) i = byteBit x (i % 8) := by
  simp only [bitAt, byteBit, h, push_getElem?_eq, Option.getD_some]

/-- `byteBit` is `Nat.testBit` on the byte's value, which is what makes the `|||` in `packStep`
tractable: setting one bit is an `or` with a power of two. -/
theorem byteBit_eq_testBit (x : UInt8) (j : Nat) (hj : j < 8) :
    byteBit x j = x.toNat.testBit j := by
  have hj8 : j.toUInt8.toNat % 8 = j := by
    have hjn : j.toUInt8.toNat = j := by
      simp only [Nat.toUInt8, UInt8.toNat_ofNat']
      omega
    omega
  have key : ((x >>> j.toUInt8) &&& 1).toNat = x.toNat / 2 ^ j % 2 := by
    rw [UInt8.toNat_and, UInt8.toNat_shiftRight, hj8, UInt8.toNat_one, Nat.and_one_is_mod,
      Nat.shiftRight_eq_div_pow]
  rw [byteBit, Nat.testBit_eq_decide_div_mod_eq, ← key]
  apply Bool.eq_iff_iff.mpr
  simp only [beq_iff_eq, decide_eq_true_eq, ← UInt8.toNat_inj, UInt8.toNat_one]

/-- Setting bit `j` of a byte is an `or` with `2 ^ j`. -/
private theorem toNat_or_bit (c : UInt8) (j : Nat) (hj : j < 8) :
    (c ||| 1 <<< j.toUInt8).toNat = c.toNat ||| 2 ^ j := by
  have hj8 : j.toUInt8.toNat % 8 = j := by
    have hjn : j.toUInt8.toNat = j := by
      simp only [Nat.toUInt8, UInt8.toNat_ofNat']
      omega
    omega
  rw [UInt8.toNat_or, UInt8.toNat_shiftLeft, hj8, UInt8.toNat_one, Nat.shiftLeft_eq, Nat.one_mul,
    Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by decide : 1 < 2) hj)]

/-- The loop invariant: after `n` steps `out` holds the `n / 8` bytes already full, and `cur` the
`n % 8` bits of the byte in progress with its remaining bits still `0`. -/
theorem packStep_loop (as : Array QAtom) (n : Nat) (r : MProd UInt8 ByteArray)
    (hr : r = (List.range' 0 n).foldl (packStep as)
      ⟨0, ByteArray.emptyWithCapacity ((as.size + 7) / 8)⟩) :
    r.2.size = n / 8 ∧ (∀ i < 8 * (n / 8), bitAt r.2 i = boolOf as[i]!)
      ∧ ∀ j < 8, r.1.toNat.testBit j = (decide (j < n % 8) && boolOf as[8 * (n / 8) + j]!) := by
  subst hr
  induction n with
  | zero =>
    refine ⟨ByteArray.size_eq_zero_iff.mpr rfl, fun i hi => absurd hi (by omega), fun j _ => ?_⟩
    simp
  | succ n ih =>
    obtain ⟨hsize, hbits, hcur⟩ := ih
    rw [List.range'_concat]
    simp only [List.foldl_append, List.foldl_cons, List.foldl_nil, Nat.zero_add, Nat.one_mul]
    revert hsize hbits hcur
    generalize (List.range' 0 n).foldl (packStep as)
      (⟨0, ByteArray.emptyWithCapacity ((as.size + 7) / 8)⟩ : MProd UInt8 ByteArray) = p
    intro hsize hbits hcur
    -- the byte in progress after this element, whichever branch `packStep` takes
    have hbit : ∀ j < 8, (if boolOf as[n]! = true then p.1 ||| 1 <<< (n % 8).toUInt8
        else p.1).toNat.testBit j
          = (p.1.toNat.testBit j || (decide (n % 8 = j) && boolOf as[n]!)) := by
      intro j hj
      by_cases hb : boolOf as[n]! = true
      · rw [if_pos hb, toNat_or_bit _ _ (by omega), Nat.testBit_or, Nat.testBit_two_pow, hb]
        simp
      · rw [if_neg hb]
        simp [Bool.of_not_eq_true hb]
    have hn : 8 * (n / 8) + n % 8 = n := by omega
    by_cases h7 : n % 8 = 7
    · have hq : (n + 1) / 8 = n / 8 + 1 := by omega
      have hm : (n + 1) % 8 = 0 := by omega
      rw [show packStep as p n = ⟨0, p.2.push (if boolOf as[n]! = true
          then p.1 ||| 1 <<< (n % 8).toUInt8 else p.1)⟩ by
        simp only [packStep, h7]; split <;> simp]
      refine ⟨by rw [push_size, hsize, hq], fun i hi => ?_, fun j _ => by simp [hm]⟩
      by_cases hlt : i / 8 < p.2.size
      · rw [bitAt_push_lt _ _ _ hlt]
        exact hbits i (by rw [hsize] at hlt; omega)
      · have hik : i / 8 = p.2.size := by rw [hsize] at hlt ⊢; omega
        rw [bitAt_push_eq _ _ _ hik, byteBit_eq_testBit _ _ (by omega), hbit _ (by omega), hcur _
          (by omega)]
        have hi8 : 8 * (n / 8) + i % 8 = i := by rw [hsize] at hik; omega
        by_cases he : i % 8 = 7
        · have : i = n := by omega
          subst this
          simp [he]
        · have hlt7 : i % 8 < 7 := by omega
          simp [h7, hi8, hlt7, Ne.symm he]
    · have hq : (n + 1) / 8 = n / 8 := by omega
      have hm : (n + 1) % 8 = n % 8 + 1 := by omega
      rw [show packStep as p n = ⟨if boolOf as[n]! = true
          then p.1 ||| 1 <<< (n % 8).toUInt8 else p.1, p.2⟩ by
        simp only [packStep]; split <;> simp [h7]]
      refine ⟨by rw [hsize, hq], fun i hi => hbits i (by omega), fun j hj => ?_⟩
      rw [hbit _ hj, hcur _ hj, hq, hm]
      by_cases he : n % 8 = j
      · subst he
        simp [hn]
      · by_cases hj' : j < n % 8
        · simp [he, hj', Nat.lt_succ_of_lt hj']
        · simp [he, hj', show ¬j < n % 8 + 1 by omega]

/-- Pushing a list of bytes appends exactly that many. -/
theorem foldl_push_size (b : ByteArray) (xs : List UInt8) :
    (xs.foldl ByteArray.push b).size = b.size + xs.length := by
  induction xs generalizing b with
  | nil => simp
  | cons x xs ih => rw [List.foldl_cons, ih, push_size]; simp only [List.length_cons]; omega

/-- The guid fold appends sixteen bytes per element. -/
private theorem foldl_guid_size (b : ByteArray) (as : List QAtom)
    (h : ∀ a ∈ as, a.type = .guid) :
    (as.foldl (fun acc a => match a with
        | .guid g => g.toArray.foldl ByteArray.push acc
        | _ => acc) b).size = b.size + as.length * 16 := by
  induction as generalizing b with
  | nil => simp
  | cons a as ih =>
    obtain ⟨g, rfl⟩ : ∃ g, a = .guid g := by
      have ha := h a List.mem_cons_self
      cases a <;> first | exact ⟨_, rfl⟩ | simp [QAtom.type] at ha
    simp only [List.foldl_cons]
    rw [ih _ fun x hx => h x (List.mem_cons_of_mem _ hx), ← Array.foldl_toList, foldl_push_size]
    simp [Nat.succ_mul]
    omega

/-- The bytes a symbol contributes. The NUL that follows them is `blobStep`'s, not this. -/
def utf8Of : QAtom → ByteArray
  | .symbol s => s.toUTF8
  | _ => ByteArray.empty

/-- One step of the `offs` fold: record where the *next* symbol starts. -/
def offStep (p : Array Nat × Nat) (s : ByteArray) : Array Nat × Nat :=
  (p.1.push (p.2 + s.size + 1), p.2 + s.size + 1)

/-- One step of the `blob` fold: a symbol's bytes, then its NUL. -/
def blobStep (acc s : ByteArray) : ByteArray := (acc ++ s).push 0

/-- Where symbol `i` starts in the blob: every earlier symbol's bytes, each plus its NUL. The
recursion is on the index rather than on the list, so that `symStart bs 0 = 0` holds for a variable
`bs` — offset `0` is read before the list is ever taken apart. -/
private def symStart (bs : List ByteArray) : Nat → Nat
  | 0 => 0
  | i + 1 => symStart bs i + bs[i]!.size + 1

/-- Dropping the first symbol shifts every start by its bytes and its NUL. This is the form the
folds' induction step needs, where the list, not the index, is what shrinks. -/
private theorem symStart_cons (s : ByteArray) (bs : List ByteArray) (i : Nat) :
    symStart (s :: bs) (i + 1) = s.size + 1 + symStart bs i := by
  induction i with
  | zero => simp [symStart]
  | succ i ih => rw [symStart, ih, symStart, List.getElem!_cons_succ]; omega

/-- Starts grow with the index, which is what puts symbol `i`'s bytes inside the blob. -/
private theorem symStart_le (bs : List ByteArray) {i j : Nat} (hij : i ≤ j) :
    symStart bs i ≤ symStart bs j := by
  obtain ⟨d, rfl⟩ : ∃ d, j = i + d := ⟨j - i, by omega⟩
  induction d with
  | zero => exact Nat.le_refl _
  | succ d ih =>
    exact Nat.le_trans (ih (by omega))
      (by rw [show i + (d + 1) = (i + d) + 1 from by omega, symStart]; omega)

/-- An offset that was already in the table is still there after another is appended. -/
private theorem offs_push_getElem!_lt (o : Array Nat) (v j : Nat) (hj : j < o.size) :
    (o.push v)[j]! = o[j]! := by
  rw [getElem!_pos (o.push v) j (by rw [Array.size_push]; omega), getElem!_pos o j hj,
    Array.getElem_push_lt hj]

/-- The offset just appended. -/
private theorem offs_push_getElem!_eq (o : Array Nat) (v : Nat) : (o.push v)[o.size]! = v := by
  rw [getElem!_pos (o.push v) o.size (by rw [Array.size_push]; omega), Array.getElem_push_eq]

/-- The offs fold appends one start per symbol. -/
private theorem foldl_offStep_size (o : Array Nat) (pos : Nat) (bs : List ByteArray) :
    (bs.foldl offStep (o, pos)).1.size = o.size + bs.length := by
  induction bs generalizing o pos with
  | nil => simp
  | cons s bs ih =>
    rw [List.foldl_cons,
      show offStep (o, pos) s = (o.push (pos + s.size + 1), pos + s.size + 1) from rfl,
      ih (o.push (pos + s.size + 1)) (pos + s.size + 1), Array.size_push, List.length_cons]
    omega

/-- Appending never disturbs a start already recorded, so a read inside the initial table survives
the rest of the fold. -/
private theorem foldl_offStep_lt (o : Array Nat) (pos : Nat) (bs : List ByteArray) (j : Nat)
    (hj : j < o.size) : (bs.foldl offStep (o, pos)).1[j]! = o[j]! := by
  induction bs generalizing o pos with
  | nil => rfl
  | cons s bs ih =>
    rw [List.foldl_cons,
      show offStep (o, pos) s = (o.push (pos + s.size + 1), pos + s.size + 1) from rfl,
      ih (o.push (pos + s.size + 1)) (pos + s.size + 1) (by rw [Array.size_push]; omega),
      offs_push_getElem!_lt o (pos + s.size + 1) j hj]

/-- Symbol `i`'s successor start is where the fold wrote it. -/
private theorem foldl_offStep_get (o : Array Nat) (pos : Nat) (bs : List ByteArray) (i : Nat)
    (hi : i < bs.length) :
    (bs.foldl offStep (o, pos)).1[o.size + i]! = pos + symStart bs (i + 1) := by
  induction bs generalizing o pos i with
  | nil => simp at hi
  | cons s bs ih =>
    rw [List.foldl_cons,
      show offStep (o, pos) s = (o.push (pos + s.size + 1), pos + s.size + 1) from rfl]
    match i with
    | 0 =>
      rw [show o.size + 0 = o.size from by omega,
        foldl_offStep_lt (o.push (pos + s.size + 1)) (pos + s.size + 1) bs o.size
          (by rw [Array.size_push]; omega),
        offs_push_getElem!_eq o (pos + s.size + 1), symStart_cons, symStart]
      omega
    | i + 1 =>
      rw [show o.size + (i + 1) = (o.push (pos + s.size + 1)).size + i from by
        rw [Array.size_push]; omega,
        ih (o.push (pos + s.size + 1)) (pos + s.size + 1) i (by simpa using hi), symStart_cons]
      omega

/-- The blob fold appends each symbol's bytes and its NUL, which is what `symStart` counts. -/
private theorem foldl_blobStep_size (acc : ByteArray) (bs : List ByteArray) :
    (bs.foldl blobStep acc).size = acc.size + symStart bs bs.length := by
  induction bs generalizing acc with
  | nil => simp [symStart]
  | cons s bs ih =>
    rw [List.foldl_cons, ih (blobStep acc s),
      show (blobStep acc s).size = acc.size + s.size + 1 from by
        rw [blobStep, push_size, ByteArray.size_append],
      List.length_cons, symStart_cons]
    omega

/-- Appending never disturbs a byte already written, so a read inside the prefix survives the rest
of the fold. -/
private theorem foldl_blobStep_lt (acc : ByteArray) (bs : List ByteArray) (j : Nat)
    (hj : j < acc.size) : (bs.foldl blobStep acc)[j]? = acc[j]? := by
  induction bs generalizing acc with
  | nil => rfl
  | cons s bs ih =>
    rw [List.foldl_cons,
      ih (blobStep acc s) (by rw [blobStep, push_size, ByteArray.size_append]; omega), blobStep,
      push_getElem?_lt (x := 0) (by rw [ByteArray.size_append]; omega),
      getElem?_pos (acc ++ s) j (by rw [ByteArray.size_append]; omega), getElem?_pos acc j hj,
      ByteArray.getElem_append_left hj]

/-- Byte `k` of symbol `i` reads back where the fold wrote it. -/
private theorem foldl_blobStep_get (acc : ByteArray) (bs : List ByteArray) (i : Nat)
    (hi : i < bs.length) (k : Nat) (hk : k < bs[i]!.size) :
    (bs.foldl blobStep acc)[acc.size + symStart bs i + k]? = bs[i]![k]? := by
  induction bs generalizing acc i with
  | nil => simp at hi
  | cons s bs ih =>
    have hstep : (blobStep acc s).size = acc.size + s.size + 1 := by
      rw [blobStep, push_size, ByteArray.size_append]
    rw [List.foldl_cons]
    match i with
    | 0 =>
      rw [List.getElem!_cons_zero] at hk ⊢
      rw [show acc.size + symStart (s :: bs) 0 + k = acc.size + k from by rw [symStart]; omega,
        foldl_blobStep_lt (blobStep acc s) bs (acc.size + k) (by omega), blobStep,
        push_getElem?_lt (x := 0) (j := acc.size + k) (by rw [ByteArray.size_append]; omega),
        getElem?_pos (acc ++ s) (acc.size + k) (by rw [ByteArray.size_append]; omega),
        getElem?_pos s k hk, ByteArray.getElem_append_right (by omega)]
      simp
    | i + 1 =>
      rw [List.getElem!_cons_succ] at hk ⊢
      rw [show acc.size + symStart (s :: bs) (i + 1) + k
            = (blobStep acc s).size + symStart bs i + k from by rw [symStart_cons, hstep]; omega]
      exact ih (blobStep acc s) i (by simpa using hi) hk

/-- Same size and same bytes is the same payload. `atoms` reads the blob with `extract`, so the
byte-level facts above have to be lifted through it, which is the move `bitsAt_congr` makes for the
fixed-width branch. -/
private theorem bytes_ext {a b : ByteArray} (hs : a.size = b.size)
    (h : ∀ k, k < b.size → a[k]? = b[k]?) : a = b := by
  apply ByteArray.ext
  apply Array.ext
  · rw [ByteArray.size_data, ByteArray.size_data, hs]
  · intro k h1 h2
    have ha : k < a.size := by rw [← ByteArray.size_data]; exact h1
    have hb : k < b.size := by rw [← ByteArray.size_data]; exact h2
    have hk := h k hb
    rw [getElem?_pos a k ha, getElem?_pos b k hb, Option.some.injEq,
      ByteArray.getElem_eq_getElem_data, ByteArray.getElem_eq_getElem_data] at hk
    exact hk

/-- Symbol `i` comes back out of the blob exactly as it went in. -/
private theorem extract_blobStep (bs : List ByteArray) (i : Nat) (hi : i < bs.length) :
    (bs.foldl blobStep ByteArray.empty).extract (symStart bs i) (symStart bs i + bs[i]!.size)
      = bs[i]! := by
  have hsize : (bs.foldl blobStep ByteArray.empty).size = symStart bs bs.length := by
    rw [foldl_blobStep_size, ByteArray.size_empty, Nat.zero_add]
  -- symbol `i` ends before symbol `i + 1` starts, and that start is at most the blob's size
  have hbound : symStart bs i + bs[i]!.size + 1 ≤ symStart bs bs.length := by
    have hle := symStart_le bs (show i + 1 ≤ bs.length from hi)
    rw [symStart] at hle
    omega
  apply bytes_ext
  · rw [ByteArray.size_extract, hsize]; omega
  · intro k hk
    rw [getElem?_pos _ k (by rw [ByteArray.size_extract, hsize]; omega),
      ByteArray.getElem_extract, ← getElem?_pos _ _ (by rw [hsize]; omega),
      show symStart bs i + k = ByteArray.empty.size + symStart bs i + k from by
        rw [ByteArray.size_empty]; omega]
    exact foldl_blobStep_get ByteArray.empty bs i hi k hk

/-- Offset `j` of the fold is symbol `j`'s start: entry `0` is the initial table's, the others the fold's. -/
private theorem offStep_start (bs : List ByteArray) (j : Nat) (hj : j ≤ bs.length) :
    (bs.foldl offStep (#[0], 0)).1[j]! = symStart bs j := by
  match j with
  | 0 => rw [foldl_offStep_lt #[0] 0 bs 0 (by simp)]; rfl
  | i + 1 => simpa [Nat.add_comm] using foldl_offStep_get #[0] 0 bs i (by omega)

/-- The two folds read back entry `i` as `bs[i]`: the `hi > lo` guard of `symBytes` holds outright,
because the next start is one past this symbol's last byte. -/
theorem symKey_folds (bs : List ByteArray) (i : Nat) (hi : i < bs.length) :
    symKey (bs.foldl blobStep ByteArray.empty) (bs.foldl offStep (#[0], 0)).1 i = bs[i]! := by
  have hpair : symBytes (bs.foldl offStep (#[0], 0)).1 i = (symStart bs i, bs[i]!.size) := by
    have hs : i + 1 < (bs.foldl offStep (#[0], 0)).1.size := by
      rw [foldl_offStep_size]; show i + 1 < 1 + bs.length; omega
    simp only [symBytes, if_pos hs, offStep_start bs i (by omega), offStep_start bs (i + 1) (by omega), symStart]
    rw [if_pos (by omega)]
    congr 1
    omega
  unfold symKey
  rw [hpair]
  exact extract_blobStep bs i hi

/-- The bytes `packBits` writes: one per eight booleans, the last one partial. -/
theorem packBits_size (as : Array QAtom) : (packBits as).size = (as.size + 7) / 8 := by
  obtain ⟨hsize, -, -⟩ := packStep_loop as as.size _ rfl
  rw [packBits_eq as _ rfl]
  revert hsize
  generalize (List.range' 0 as.size).foldl (packStep as)
    (⟨0, ByteArray.emptyWithCapacity ((as.size + 7) / 8)⟩ : MProd UInt8 ByteArray) = p
  intro hsize
  by_cases hm : as.size % 8 = 0
  · rw [if_pos hm]; omega
  · rw [if_neg hm, push_size]; omega

/-- The two folds lay their symbols out as `SymsWF` says: start `j` is `symStart j`, which grows with
`j` and ends at the blob's size. -/
private theorem symsWF_folds (bs : List ByteArray) :
    SymsWF (bs.foldl blobStep ByteArray.empty) (bs.foldl offStep (#[0], 0)).1 := by
  have hs : (bs.foldl offStep (#[0], 0)).1.size = bs.length + 1 := by
    rw [foldl_offStep_size]; show 1 + bs.length = bs.length + 1; omega
  have hO : ∀ j, j ≤ bs.length → (bs.foldl offStep (#[0], 0)).1[j]! = symStart bs j := offStep_start bs
  have hb : (bs.foldl blobStep ByteArray.empty).size = symStart bs bs.length := by
    rw [foldl_blobStep_size, show ByteArray.empty.size = 0 from rfl, Nat.zero_add]
  refine ⟨by omega, hO 0 (Nat.zero_le _), by rw [hs, Nat.add_sub_cancel, hO _ (Nat.le_refl _), hb],
    fun k hk => ?_, fun k hk => ?_⟩
  · rw [hO k (by omega), hb]; exact symStart_le bs (by omega)
  · rw [hO k (by omega), hO (k + 1) (by omega)]; exact symStart_le bs (Nat.le_succ k)

/-- What `ofAtoms` builds is well formed: its header is the atoms' type and count, and each layout
holds exactly that many. -/
theorem ofAtoms_WF {t : QAtomicType} {as : Array QAtom} {e : Enc} {hn : t ≠ .general}
    (h : ∀ a ∈ as, a.type = t) (hc : ofAtoms t as hn = some e) (hs : as.size < USize.size) :
    WF t as.size.toUSize e := by
  unfold WF; rw [USize.toNat_ofNat_of_lt' hs]
  unfold ofAtoms at hc
  rw [if_pos (Array.all_eq_true'.mpr fun x hx => by simp [h x hx])] at hc
  have h0 : ∀ k, (ByteArray.emptyWithCapacity k).size = 0 := fun _ =>
    ByteArray.size_eq_zero_iff.mpr rfl
  match t, hn, h, hc with
  | .general, hn, _, _ => exact absurd rfl hn
  | .boolean, _, _, hc => cases hc; exact packBits_size as
  | .symbol, _, _, hc =>
    cases hc
    show ((as.map utf8Of).foldl offStep (#[0], 0)).1.size = as.size + 1 ∧
      SymsWF ((as.map utf8Of).foldl blobStep ByteArray.empty) ((as.map utf8Of).foldl offStep (#[0], 0)).1 ∧
      ∀ i < as.size, (symKey ((as.map utf8Of).foldl blobStep ByteArray.empty)
        ((as.map utf8Of).foldl offStep (#[0], 0)).1 i).IsValidUTF8
    rw [← Array.foldl_toList blobStep, ← Array.foldl_toList offStep]
    refine ⟨by rw [foldl_offStep_size]; simp <;> omega, symsWF_folds _, fun i hi => ?_⟩
    -- every entry is a `String`'s `toUTF8`, or the empty bytes for a non-symbol
    rw [symKey_folds _ i (by simpa using hi), getElem!_pos _ i (by simpa using hi), Array.getElem_toList,
      Array.getElem_map]
    cases as[i] <;> first | exact String.isValidUTF8 _ | exact (by decide : ByteArray.empty.IsValidUTF8)
  | .guid, _, h, hc =>
    cases hc
    show _ = as.size * 16
    rw [← Array.foldl_toList, foldl_guid_size _ _ fun a ha => h a (by simpa using ha), h0]; simp
  | .byte, _, _, hc | .char, _, _, hc | .short, _, _, hc | .int, _, _, hc | .long, _, _, hc
  | .real, _, _, hc | .float, _, _, hc | .timestamp, _, _, hc | .month, _, _, hc | .date, _, _, hc
  | .datetime, _, _, hc | .timespan, _, _, hc | .minute, _, _, hc | .second, _, _, hc
  | .time, _, _, hc =>
    cases hc
    simp only [WF, QAtomicType.width]
    rw [← Array.foldl_toList, foldl_pushBits_size, h0]; simp <;> omega

end Column

namespace QTable

end QTable

namespace QValue

/-- The attribute a value carries, `0` for none, and the value under it. Every reader but
`attr`, `meta` and the encoder wants the second half alone. -/
def marking : QValue → UInt8 × QValue
  | vector t n e (some (a, _)) => (a, vector t n e none)
  | enum d (vector t n e (some (a, _))) => (a, enum d (vector t n e none))
  -- a table holds q's whole byte (`62 0N`); a dictionary or a keyed table carries only `` `s ``,
  -- type 127
  | table (.mk ns cs a) => (a, table (.mk ns cs 0))
  | dict k v true => (1, dict k v false)
  | @keyed k v true ix => (1, @keyed k v false ix)
  | v => (0, v)

end QValue

namespace QValue

/-- The `i`th slice of a `slices` value, as the vector it denotes. Reading one is a copy of its
bytes and nothing else; reading them all is the loop the constructor exists to avoid, which is why
this is by index and there is no `toArray`.

**The slice stays dense, and that is measured rather than conceded.** `CLAUDE.md`'s "the encoded form
is the representation" is about a column that *enters* and is then read many times; a slice is read
once, by the `each` that asked for it, so encoding it spends a whole extra pass to save part of one.
Interleaved against the same binary with the encode spliced in, a million longs in a thousand pieces:
`count each value group xg` 1.32x, `min each value group xg` 1.18x, `sums each value group xg` 1.12x,
`{x+x} each value group xg` and `{x+x} each flip mxl` 1.05x — against the same pieces held as a
general list, `{x+x} each mxl` at 1.00x and `sums each mxl` at 1.04x. Every shape is a loss.

There is no boxing on the other side of that trade, which is what would have paid for the pass.
`Kernel.overColumn` folds a dense payload at every integral type and a `.bits` one at `boolean`, and
the elementwise and scan families have their own dense paths: measured, `min each mxf` is 341ns per
thousand elements and `{x+x} each mxl` 1.0µs, where `Column.atoms` alone would be 64µs. The decline
`CLAUDE.md` warns about is real at a column that arrives, not at a slice of one.

Two things anyone re-proposing the one-liner needs: `Column.encode` lives in `QLean/Kernel/Coc.lean`,
which *imports* this file, so it cannot be called from here at all; and it answers a float column
unchanged (`Coc.encodes` is false there — ALP is the float encoding and reaches columns through
`Column.admit`), so it would be a no-op at the one type it was wanted for.

The second case rests on every producer — `group`, `flip`, `string`, `vs`, `cross` — sharing a
`.bytes` payload. A payload that is not dense has no per-piece cut here and answers the whole column,
so a producer over an encoded column must cut it where it is built, the way `Kernel.cutFoR` does. -/
def sliceAt (t : QAtomicType) (n : USize) (e : Enc) (attr : Option (UInt8 × IndexCell))
    (offs : Array Nat) (i : Nat) : QValue :=
  match e with
  -- `offs` are byte offsets, so the slice's count is its bytes over the element width; a type with
  -- no width has no `bytes` layout (`Enc.WF`)
  | .bytes blob =>
    let c := (offs[i + 1]! - offs[i]!) / (t.width.getD 1)
    Kernel.needSize c "sliceAt: count" (fun _ => .vector t 0 (.blank t 0) none)
      fun c => .vector t c (.bytes (blob.extract offs[i]! offs[i + 1]!)) none
  | _ => .vector t n e attr

/-- Every element of a `slices` value, which is the million-value loop it exists to avoid. Only
where something genuinely needs them all — `~` against a general list, the wire encoder — and the
count is small, or the cost is the one the constructor was avoiding. -/
def slicesExpand (t : QAtomicType) (n : USize) (e : Enc) (attr : Option (UInt8 × IndexCell))
    (offs : Array Nat) : Array QValue :=
  if offs.isEmpty then #[]
  else (Array.range (offs.size - 1)).map (sliceAt t n e attr offs)

end QValue

namespace QValue

end QValue
end Rel
