/-! The part of `Rel.Db.ObjectFile` the Rel kernels reach; `Rel.Db.ObjectFile` imports it. -/


namespace Rel.Db

open Rel

/-- The one column writer: `parts` are a `Column` constructor's `ByteArray`s, written as they lie
under the header `rust/src/own.rs` documents, to a temporary beside `path` that is then renamed over it. -/
@[extern "qlean_own_write"]
opaque ownWrite (path : @& String) (code attr kind : UInt8) (count : USize) (domain : @& String)
    (parts : @& Array ByteArray) : IO Unit


end Rel.Db
