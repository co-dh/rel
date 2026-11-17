import Rel.Kernel.Sort
import Rel.Kernel.Value

/-! The part of `Rel.Db.Own` the Rel kernels reach; `Rel.Db.Own` imports it. -/


namespace Rel.Db

open Rel

/-- A column as `ownWrite` takes it: the header's fields and the constructor's parts. -/
structure OwnFile where
  code : UInt8
  attr : UInt8
  kind : UInt8
  count : USize
  /-- Enumeration domain, empty when the column is not a q enumeration. -/
  domain : String
  parts : Array ByteArray

/-- A column's constructor kind and its parts, `rust/src/own.rs`'s numbering. A `syms` column is interned
first: its `offs` is an `Array Nat` with no bytes to write, where an interned column's per-element
payload is `ids`. The `syms` arm is what `intern` never answers, and the writer refuses its no
parts. -/
def ownParts (e : Enc) : UInt8 × Array ByteArray :=
  match Column.intern e with
  | .bytes b => (0, #[b])
  | .bits b => (1, #[b])
  | .foR metadata pack => (2, #[metadata, pack])
  | .alp metadata pack alp => (3, #[metadata, pack, alp])
  | .enum dict _ ids => (4, #[dict, ids])
  | .syms _ _ => (4, #[])
  -- `ownFile` sends a general column to the serialized-object form, whose encoder names it
  | .gen _ => (5, #[])

/-- The file a value is written as when it is a column: a vector, an enumeration's indices under
their domain's name, and either wearing an attribute. `none` is every other value, which keeps the
serialized-object form. -/
def ownFile (v : QValue) : Option OwnFile :=
  let (attr, w) := v.marking
  let column (t : QAtomicType) (n : USize) (e : Enc) (domain : String) : OwnFile :=
    let (kind, parts) := ownParts e
    { code := t.code.toUInt8, attr, kind, count := n, domain, parts }
  match w with
  | .enum d (.vector .long n e _) => if d.isEmpty then none else some (column .long n e d)
  | .vector _ _ (.gen _) _ => none
  | .vector t n e _ => if t == .general then none else some (column t n e "")
  | _ => none


end Rel.Db
