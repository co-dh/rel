/-! The part of `QLean.Value` the Rel kernels reach; `QLean.Value` imports it. -/


namespace QLean

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
end QLean
