/-! The part of `Rel.Db.ObjectFile` the Rel kernels reach; `Rel.Db.ObjectFile` imports it. -/


namespace Rel.Db

open Rel

/-- The one column writer: `parts` are a `Column` constructor's `ByteArray`s, written as they lie
under the header `rust/src/own.rs` documents, to a temporary beside `path` that is then renamed over it. -/
@[extern "qlean_own_write"]
opaque ownWrite (path : @& String) (code attr kind : UInt8) (count : USize) (domain : @& String)
    (parts : @& Array ByteArray) : IO Unit

/-- An own-format column file **mapped**, not read (`crate/src/own.rs`, which has the layout): element 0 is the
header, part table and domain name copied out, and each element after it is one part of the `Column`, a
`ByteArray` lying in the mapping. The parts are persistent objects, so an update copies first and the file is
never written through them. A file the header or part checks refuse is an error naming the byte and the rule. -/
@[extern "qlean_own_map"]
opaque fileMap (path : @& String) : IO (Array ByteArray)

/-- `ownWrite`'s `parts` grown by one computed buffer: `Array.push` at `ByteArray`, so a plan register can name it
(`kernel%` reads a monomorphic signature). The symbol is the toolchain's; a native run gets it from `crate/rt`. -/
@[extern "lean_array_push"]
def pushPart (parts : Array ByteArray) (b : ByteArray) : Array ByteArray := parts.push b


end Rel.Db
