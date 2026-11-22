import Rel.Kernel.Db.Own
import Rel.Kernel.Coc

/-! `ownMap` beside its body, as `decide` beside `#guard` for a pure kernel: every file is read twice, by the extern
(which maps it) and by the body (`ownParse` of its bytes). A column written by `ownWrite` must come back from both as
the column written; a file broken in one place must be refused by both with the same text, one file per refusal of
`own::map`. The one place the two differ by design is `own::check`, which the body does not model: its test pins the
extern refusing and the body accepting. -/

namespace Rel.Db.OwnTest
open Rel

/-- `xs` as 8-byte elements. -/
def dense (xs : List UInt64) : ByteArray := xs.foldl (init := .empty) fun acc w => Column.pushBits acc w 8

/-- What an `OwnFile` is compared by. -/
def key (f : OwnFile) : UInt8 × UInt8 × UInt8 × USize × String × List (List UInt8) :=
  (f.code, f.attr, f.kind, f.count, f.domain, f.parts.toList.map (·.data.toList))

/-- An `IO` answer as text: `ok` and the column's kind and part sizes, or the error. -/
def say (r : Except IO.Error OwnFile) : String :=
  match r with
  | .ok f => s!"ok kind {f.kind} count {f.count} domain `{f.domain}` part sizes {f.parts.toList.map (·.size)}"
  | .error e => toString e

/-- The file at `p` read by the extern and by the body. -/
def both (p : System.FilePath) : IO (Except IO.Error OwnFile × Except IO.Error OwnFile) :=
  return (← (ownMap p.toString).toBaseIO,
          ← (do IO.ofExcept (ownParse (← IO.FS.readBinFile p)) : IO OwnFile).toBaseIO)

/-- `f` written by `ownWrite` into a fresh file, then read by `both`: each must answer `f`; the extern's answer is
printed. A part of the extern's answer is a `ByteArray` in the mapping, compared here byte for byte. -/
def roundTrip (f : OwnFile) : IO OwnFile := do
  let (h, p) ← IO.FS.createTempFile
  h.flush
  ownWrite p.toString f.code f.attr f.kind f.count f.domain f.parts
  let (m, s) ← both p
  IO.FS.removeFile p
  for r in [m, s] do
    match r with
    | .ok g => unless key g == key f do throw (IO.userError s!"{p}: read back as {say r}")
    | .error e => throw e
  IO.println (say m)
  IO.ofExcept m

/-- The column `v` is written as (`ownFile`), round-tripped, and its `Enc` rebuilt from the mapped parts. -/
def column (v : QValue) : IO Unit := do
  let some f ← IO.ofExcept (ownFile v) | throw (IO.userError "positions, which have no file")
  let g ← roundTrip f
  match ownEnc (X := Empty) g.kind g.parts with
  | some (.foR m p) => IO.println s!"foR: metadata {m.size} bytes, pack {p.size} bytes"
  | some _ => IO.println "another constructor"
  | none => throw (IO.userError s!"ownEnc: no constructor of kind {g.kind}")

-- 64 longs 0..62 and one outlier: Frame of Reference, one block of 1024 at 6 bits (768 residual bytes) and a 40-byte
-- patch list holding the outlier
/--
info: ok kind 2 count 64 domain `` part sizes [57, 808]
foR: metadata 57 bytes, pack 808 bytes
-/
#guard_msgs in
#eval column (.vector .i64 64 (Ext.Enc.ofBytes 8 (dense ((List.range 63).map (·.toUInt64) ++ [1000000000000]))) none)

/--
info: ok kind 2 count 0 domain `` part sizes [24, 0]
foR: metadata 24 bytes, pack 0 bytes
-/
#guard_msgs in
#eval column (.vector .i64 0 (Ext.Enc.ofBytes 8 .empty) none)

/--
info: ok kind 2 count 3 domain `dom` part sizes [57, 256]
foR: metadata 57 bytes, pack 256 bytes
-/
#guard_msgs in
#eval column (.enum "dom" (.vector .i64 3 (Ext.Enc.ofBytes 8 (dense [2, 0, 1])) none))

-- positions are never written (PLAN 6.13): `ownFile` answers no file; a symbol column is refused (no writer of the
-- sorted dictionary yet); and the writer refuses kind 5, a number that is no kind
/-- info: (Except.ok none,
 Except.error "a `syms` column, which the own format does not hold: a symbol column is stored as `foR` ids into a sorted dictionary (doc/rel-architecture.zh.typ §4), and no writer builds that yet") -/
#guard_msgs in
#eval ((ownFile (X := Empty) (.vector .i64 5 .pos none)).map (·.map key),
  (ownFile (X := Empty) (.vector .sym 1 (.syms (ByteArray.mk #[97, 0]) #[0, 2]) none)).map (·.map key))
/--
info: ("error: a column of kind and part count 2:2 or 4:2 and a domain name under 65536 bytes, given kind 5 with 0 parts and a 0-byte name",
 "error: a column of kind and part count 2:2 or 4:2 and a domain name under 65536 bytes, given kind 5 with 0 parts and a 0-byte name")
-/
#guard_msgs in
#eval show IO _ from do
  let (_, p) ← IO.FS.createTempFile
  let w ← (ownWrite p.toString 7 0 5 5 "" #[]).toBaseIO
  IO.FS.removeFile p
  return (match w with | .ok () => "ok" | .error e => s!"error: {e}",
          match ownImage ⟨7, 0, 5, 5, "", #[]⟩ with | .ok _ => "ok" | .error e => s!"error: {e}")

/-- A good kind-2 file: 2 longs Frame-of-Reference encoded, domain `ab` after the two parts' table entries. -/
def good : ByteArray :=
  match ownImage ⟨QAtomicType.i64.code.toUInt8, 0, 2, 2, "ab", #[(Kernel.Coc.encode 8 (dense [5, 6])).1, (Kernel.Coc.encode 8 (dense [5, 6])).2]⟩ with | .ok b => b | .error _ => .empty

-- header 24, part table 24..56, domain 56..58, part 0 (57 bytes) at `ownOff 58 = 96`, part 1 (128 bytes) at
-- `ownOff 153 = 192`, 32 trailing zeros
#guard good.size == 352

/-- `b` with byte `i` set to `v` for each `(i, v)`. -/
def mutate (b : ByteArray) (edits : List (Nat × UInt8)) : ByteArray :=
  ⟨(edits.foldl (fun l (i, v) => l.set i v) b.data.toList).toArray⟩

/-- The bytes `b` as a file, read by the extern then by the body. -/
def readBoth (b : ByteArray) : IO Unit := do
  let (h, p) ← IO.FS.createTempFile
  h.write b
  h.flush
  let (m, s) ← both p
  IO.FS.removeFile p
  IO.println s!"extern: {say m}\nbody:   {say s}"

/--
info: extern: ok kind 2 count 2 domain `ab` part sizes [57, 128]
body:   ok kind 2 count 2 domain `ab` part sizes [57, 128]
-/
#guard_msgs in #eval readBoth good

/--
info: extern: a 24-byte own-format header, the file is 8 bytes
body:   a 24-byte own-format header, the file is 8 bytes
-/
#guard_msgs in #eval readBoth (good.extract 0 8)

/--
info: extern: byte 0: the magic `qleancol`
body:   byte 0: the magic `qleancol`
-/
#guard_msgs in #eval readBoth (mutate good [(0, 120)])

/--
info: extern: byte 8: format version 5, found 2; a file before version 5 may hold the dense `bytes` (kind 0) or `alp` (kind 3) form, which version 5 removed (one encoding, foR), and is rewritten by `set` from the data it was made from
body:   byte 8: format version 5, found 2; a file before version 5 may hold the dense `bytes` (kind 0) or `alp` (kind 3) form, which version 5 removed (one encoding, foR), and is rewritten by `set` from the data it was made from
-/
#guard_msgs in #eval readBoth (mutate good [(8, 2)])

-- a kind at a part count not its own
/--
info: extern: byte 11: a constructor kind and part count 2:2 or 4:2, found kind 2 with 1 parts
body:   byte 11: a constructor kind and part count 2:2 or 4:2, found kind 2 with 1 parts
-/
#guard_msgs in #eval readBoth (mutate good [(12, 1)])

-- kinds 0 (`bytes`), 1 (the bitmap) and 3 (`alp`) are gone, each refused at its old part count
/--
info: extern: byte 11: a constructor kind and part count 2:2 or 4:2, found kind 0 with 1 parts
body:   byte 11: a constructor kind and part count 2:2 or 4:2, found kind 0 with 1 parts
-/
#guard_msgs in #eval readBoth (mutate good [(11, 0), (12, 1)])

/--
info: extern: byte 11: a constructor kind and part count 2:2 or 4:2, found kind 1 with 1 parts
body:   byte 11: a constructor kind and part count 2:2 or 4:2, found kind 1 with 1 parts
-/
#guard_msgs in #eval readBoth (mutate good [(11, 1), (12, 1)])

/--
info: extern: byte 11: a constructor kind and part count 2:2 or 4:2, found kind 3 with 3 parts
body:   byte 11: a constructor kind and part count 2:2 or 4:2, found kind 3 with 3 parts
-/
#guard_msgs in #eval readBoth (mutate good [(11, 3), (12, 3)])

-- the writer refuses kind 1 too
/--
info: ("error: a column of kind and part count 2:2 or 4:2 and a domain name under 65536 bytes, given kind 1 with 1 parts and a 0-byte name",
 "error: a column of kind and part count 2:2 or 4:2 and a domain name under 65536 bytes, given kind 1 with 1 parts and a 0-byte name")
-/
#guard_msgs in
#eval show IO _ from do
  let (_, p) ← IO.FS.createTempFile
  let w ← (ownWrite p.toString 7 0 1 5 "" #[.empty]).toBaseIO
  IO.FS.removeFile p
  return (match w with | .ok () => "ok" | .error e => s!"error: {e}",
          match ownImage ⟨7, 0, 1, 5, "", #[.empty]⟩ with | .ok _ => "ok" | .error e => s!"error: {e}")

-- the worst kind and part count a header can hold, refused whole by both
/--
info: extern: byte 11: a constructor kind and part count 2:2 or 4:2, found kind 255 with 65535 parts
body:   byte 11: a constructor kind and part count 2:2 or 4:2, found kind 255 with 65535 parts
-/
#guard_msgs in #eval readBoth (mutate good [(11, 255), (12, 255), (13, 255)])

-- a domain name of 2 + 512 bytes
/--
info: extern: byte 24: a part table and domain name ending at byte 570, the file is 352 bytes
body:   byte 24: a part table and domain name ending at byte 570, the file is 352 bytes
-/
#guard_msgs in #eval readBoth (mutate good [(15, 2)])

/--
info: extern: part 0 at byte 24: a data offset that is a multiple of 8, found 81
body:   part 0 at byte 24: a data offset that is a multiple of 8, found 81
-/
#guard_msgs in #eval readBoth (mutate good [(24, 81)])

/--
info: extern: part 0 at byte 24: 32 reserved bytes after byte 58 before its data, found offset 72
body:   part 0 at byte 24: 32 reserved bytes after byte 58 before its data, found offset 72
-/
#guard_msgs in #eval readBoth (mutate good [(24, 72)])

-- part 0's length 57 + 256
/--
info: extern: part 0 at byte 24: 313 bytes from byte 96, the file is 352 bytes
body:   part 0 at byte 24: 313 bytes from byte 96, the file is 352 bytes
-/
#guard_msgs in #eval readBoth (mutate good [(33, 1)])

-- part 1 too close after part 0, which ends at byte 153
/--
info: extern: part 1 at byte 40: 32 reserved bytes after byte 153 before its data, found offset 160
body:   part 1 at byte 40: 32 reserved bytes after byte 153 before its data, found offset 160
-/
#guard_msgs in #eval readBoth (mutate good [(40, 160)])

/--
info: extern: byte 56: a domain name of 2 bytes in UTF-8 with no NUL
body:   byte 56: a domain name of 2 bytes in UTF-8 with no NUL
-/
#guard_msgs in #eval readBoth (mutate good [(56, 0xff)])

/--
info: extern: byte 56: a domain name of 2 bytes in UTF-8 with no NUL
body:   byte 56: a domain name of 2 bytes in UTF-8 with no NUL
-/
#guard_msgs in #eval readBoth (mutate good [(57, 0)])

-- `own::check`, which the body does not model: Frame of Reference metadata of 20 bytes is no whole block
/--
info: extern: part 0: Frame of Reference metadata of 33 bytes a block and a 24-byte trailer, found 20 bytes
body:   ok kind 2 count 0 domain `` part sizes [20, 0]
-/
#guard_msgs in
#eval readBoth (match ownImage ⟨QAtomicType.i64.code.toUInt8, 0, 2, 0, "", #[⟨.replicate 20 0⟩, .empty]⟩ with
  | .ok b => b | .error _ => .empty)

/--
info: extern: no such file or directory (error code: 2)
  file: own-absent/x
body:   no such file or directory (error code: 2)
  file: own-absent/x
-/
#guard_msgs in #eval do let (m, s) ← both "own-absent/x"; IO.println s!"extern: {say m}\nbody:   {say s}"

/--
info: extern: inappropriate type (error code: 21, is a directory)
  file: .
body:   inappropriate type (error code: 21, is a directory)
-/
#guard_msgs in #eval do let (m, s) ← both "."; IO.println s!"extern: {say m}\nbody:   {say s}"

-- the writer's own refusal: a NUL in the domain name, which `lean_mk_string` would cut the name at
/--
info: ("error: a domain name with no NUL byte, found one at byte 1",
 "error: a domain name with no NUL byte, found one at byte 1")
-/
#guard_msgs in
#eval show IO _ from do
  let (_, p) ← IO.FS.createTempFile
  let w ← (ownWrite p.toString 7 0 2 0 "a\x00b" #[.empty, .empty]).toBaseIO
  IO.FS.removeFile p
  return (match w with | .ok () => "ok" | .error e => s!"error: {e}",
          match ownImage ⟨7, 0, 2, 0, "a\x00b", #[.empty, .empty]⟩ with | .ok _ => "ok" | .error e => s!"error: {e}")

end Rel.Db.OwnTest
