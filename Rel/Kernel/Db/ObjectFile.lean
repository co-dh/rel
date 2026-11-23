module

-- exposed: every def body is a spec a downstream `rfl`/`decide`/`simp` may unfold (PLAN W.8)
@[expose] public section

/-! The part of `Rel.Db.ObjectFile` the Rel kernels reach; `Rel.Db.ObjectFile` imports it.

The own-format column file both ways: `ownWrite` writes a column's parts under a header, `ownMap` maps the file and
answers them in place. Each is one `@[extern]` def whose body is its specification over the file's bytes, `ownImage`
and `ownParse`, the layout `crate/src/own.rs` documents; `Rel.KernelSpec.Own` proves `ownParse ∘ ownImage` the
identity on every column the writer accepts. -/


namespace Rel.Db

open Rel

/-- A column as `ownWrite` takes it and `ownMap` answers it: the header's fields and the constructor's parts. -/
structure OwnFile where
  code : UInt8
  kind : UInt8
  count : USize
  parts : Array ByteArray

/-- `own.rs`'s `OWN_NPARTS`: the part count of each constructor kind (2 foR, 5 a side of `1`: its count and no part),
`none` for a number that is no kind: 0 `bytes` and 3 `alp` were removed in version 5, 4 `enum` with `Enc.enum` (PLAN
8.3), 1 was the bitmap; the others keep their numbers. -/
def ownNParts : List (Option Nat) := [none, none, some 2, none, none, some 0]

/-- The kinds with their part counts as both refusals name them, `2:2 or 5:0` (`own.rs`'s `Kinds`). -/
def ownKinds : String :=
  match (ownNParts.zipIdx.filterMap fun (n, k) => n.map (s!"{k}:{·}")).reverse with
  | [] => ""
  | [l] => l
  | l :: ks => ", ".intercalate ks.reverse ++ " or " ++ l

/-- The file's first 8 bytes, `qleancol`. -/
def ownMagic : ByteArray := ⟨#[0x71, 0x6c, 0x65, 0x61, 0x6e, 0x63, 0x6f, 0x6c]⟩

/-- Byte 8, the format version, `own.rs`'s `OWN_VERSION`: 7 since the header holds no attribute and no domain name. -/
def ownVersion : UInt8 := 7

/-- The low `w` bytes of `v`, little-endian. -/
def leBytes (v w : Nat) : ByteArray := ⟨.ofFn (n := w) fun k => (v / 256 ^ k.val).toUInt8⟩

/-- The `w`-byte little-endian number at byte `o` of `b`, a byte past the end read as 0 (`own::le`). -/
def leAt (b : ByteArray) (o : Nat) : Nat → Nat
  | 0 => 0
  | w + 1 => leAt b o w + (b.data[o + w]?.getD 0).toNat * 256 ^ w

/-- Where a part starts after `a` bytes: past 32 zero bytes (`OWN_ROOM`, where a mapped part's `ByteArray` header
goes), rounded up to a multiple of 8 (`write_head`). -/
def ownOff (a : Nat) : Nat := (a + 32 + 7) / 8 * 8

/-- The `k` parts of `ps` from part `i` laid out from byte `a`: their part table entries (offset, length) and the
bytes from `a` on, each part after zeros up to `ownOff`, then 32 zero bytes. Counted like `ownSpans`, which reads it. -/
def ownLayout (ps : Array ByteArray) (a i : Nat) : Nat → ByteArray × ByteArray
  | 0 => (.empty, ⟨.replicate 32 0⟩)
  | k + 1 =>
    let p := ps[i]?.getD .empty
    let r := ownLayout ps (ownOff a + p.size) (i + 1) k
    (leBytes (ownOff a) 8 ++ leBytes p.size 8 ++ r.1, ⟨.replicate (ownOff a - a) 0⟩ ++ p ++ r.2)

/-- The file `ownWrite` writes for `f`, or `own::write`'s refusal: bytes 0..8 `qleancol`, the version `ownVersion`, code,
kind, the part count (1 byte), 4 zero bytes, the element count (8 bytes), the part table, then `ownLayout`. -/
def ownImage (f : OwnFile) : Except String ByteArray :=
  let np := f.parts.size
  if ownNParts[f.kind.toNat]?.join != some np then
    .error s!"a column of kind and part count {ownKinds}, given kind {f.kind} with {np} parts"
  else
    let r := ownLayout f.parts (24 + 16 * np) 0 np
    .ok (ownMagic ++ ⟨#[ownVersion, f.code, f.kind]⟩ ++ leBytes np 1 ++ leBytes 0 4 ++ leBytes f.count.toNat 8 ++
      r.1 ++ r.2)

/-- The one column writer: `parts` are a `Column` constructor's `ByteArray`s, written as they lie (`ownImage`). The
extern writes a temporary beside `path` and renames it over `path`, so a mapping of the old file keeps its pages. Missing parent directories are created. -/
@[extern "qlean_own_write"]
def ownWrite (path : @& String) (code kind : UInt8) (count : USize) (parts : @& Array ByteArray) : IO Unit := do
  if let some d := (System.FilePath.mk path).parent then IO.FS.createDirAll d
  IO.FS.writeBinFile path (← IO.ofExcept (ownImage ⟨code, kind, count, parts⟩))

/-- `own::head`'s loop: the `k` parts from part `i`, whose table entry is at `24 + 16 * i`, the bytes before it ending
at `e`. -/
def ownSpans (b : ByteArray) (i e : Nat) : Nat → Except String (List ByteArray)
  | 0 => .ok []
  | k + 1 =>
    let a := 24 + 16 * i
    let off := leAt b a 8
    let l := leAt b (a + 8) 8
    if off % 8 != 0 then .error s!"part {i} at byte {a}: a data offset that is a multiple of 8, found {off}"
    else if off < e + 32 then
      .error s!"part {i} at byte {a}: 32 reserved bytes after byte {e} before its data, found offset {off}"
    else if off > b.size || l > b.size - off then
      .error s!"part {i} at byte {a}: {l} bytes from byte {off}, the file is {b.size} bytes"
    else (b.extract off (off + l) :: ·) <$> ownSpans b (i + 1) (off + l) k

/-- The column file `b` holds, or `own::map`'s refusal, test for test and word for word: the header, the part table,
each part inside the file after its reserved bytes. -/
def ownParse (b : ByteArray) : Except String OwnFile :=
  let byte (o : Nat) : UInt8 := b.data[o]?.getD 0
  let kind := leAt b 10 1
  let np := leAt b 11 1
  let v := leAt b 8 1
  if b.size < 24 then .error s!"a 24-byte own-format header, the file is {b.size} bytes"
  else if b.extract 0 8 ≠ ownMagic then .error "byte 0: the magic `qleancol`"
  else if v != ownVersion.toNat then
    .error s!"byte 8: format version {ownVersion}, found {v}; a file before version {ownVersion} is rewritten by `set` from the data it was made from: version 7 removed the attribute byte and the domain name, version 6 widened the patch list's block offsets to u64, and version 5 removed the dense `bytes` (kind 0) and `alp` (kind 3) forms"
  else if ownNParts[kind]?.join != some np then
    .error s!"byte 10: a constructor kind and part count {ownKinds}, found kind {kind} with {np} parts"
  else if 24 + 16 * np > b.size then
    .error s!"byte 24: a part table ending at byte {24 + 16 * np}, the file is {b.size} bytes"
  else do
    let parts ← ownSpans b 0 (24 + 16 * np) np
    .ok ⟨byte 9, kind.toUInt8, (leAt b 16 8).toUSize, parts.toArray⟩

/-- An own-format column file **mapped**, not read: `ownParse` of its bytes, each part a `ByteArray` lying in the
mapping (`crate/src/own.rs`), so no byte of a part is copied or decoded. The parts are persistent objects (rc 0): an update copies first, and the mapping is `MAP_PRIVATE`, so the
file is never written through them. The extern also refuses a part the Rust kernels could read outside of
(`own::check`: Frame of Reference block widths and offsets, patch lists, ALP sections, symbol ids),
which this body does not model. -/
@[extern "qlean_own_map"]
def ownMap (path : @& String) : IO OwnFile := do
  IO.ofExcept (ownParse (← IO.FS.readBinFile path))

/-- `ownWrite`'s `parts` grown by one computed buffer: `Array.push` at `ByteArray`, so a plan register can name it
(`kernel%` reads a monomorphic signature). The symbol is the toolchain's; a native run gets it from `crate/rt`. -/
@[extern "lean_array_push"]
def pushPart (parts : Array ByteArray) (b : ByteArray) : Array ByteArray := parts.push b


end Rel.Db
