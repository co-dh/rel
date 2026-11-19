import Rel.Kernel.Db.ObjectFile
import Rel.Kernel.Sort
import Rel.Kernel.Value

/-! The part of `Rel.Db.Own` the Rel kernels reach; `Rel.Db.Own` imports it. -/


namespace Rel.Db

open Rel

/-- A column's constructor kind and its parts, `rust/src/own.rs`'s numbering. A `syms` column is interned
first: its `offs` is an `Array Nat` with no bytes to write, where an interned column's per-element
payload is `ids`. The `syms` arm is what `intern` never answers, and the writer refuses its no
parts. -/
def ownParts (e : Ext.Enc X) : UInt8 × Array ByteArray :=
  match Column.intern e with
  | .bytes b => (0, #[b])
  | .foR metadata pack => (2, #[metadata, pack])
  | .alp metadata pack alp => (3, #[metadata, pack, alp])
  | .enum dict _ ids => (4, #[dict, ids])
  | .syms _ _ => (4, #[])
  -- `ownFile` sends a general column to the serialized-object form, whose encoder names it
  | .gen _ => (5, #[])
  -- `ownFile` answers `none` for it: positions are never written, `n` is the other side's (PLAN 6.13)
  | .pos => (5, #[])

/-- The `offs` of a dictionary blob, one entry past each NUL after the leading `0`: the field a file cannot hold. -/
def dictOffs (dict : ByteArray) : Array Nat :=
  dict.data.foldl (init := (#[0], 0)) (fun (o, i) z => (if z == 0 then o.push (i + 1) else o, i + 1)) |>.1

/-- The constructor `ownParts` took apart, from the kind and the parts `ownMap` answers: each `ByteArray` is taken as
it is, so a mapped part stays in the mapping; an `enum`'s `offs` is `dictOffs`, one pass over the dictionary. -/
def ownEnc (kind : UInt8) (parts : Array ByteArray) : Option (Ext.Enc X) :=
  match kind, parts.toList with
  | 0, [b] => some (.bytes b)
  | 1, [b] => some (.bits b)
  | 2, [metadata, pack] => some (.foR metadata pack)
  | 3, [metadata, pack, alp] => some (.alp metadata pack alp)
  | 4, [dict, ids] => some (.enum dict (dictOffs dict) ids)
  | _, _ => none

/-- The file a value is written as when it is a column: a vector, an enumeration's indices under
their domain's name, and either wearing an attribute. `none` is every other value, which keeps the
serialized-object form. -/
def ownFile (v : Ext.QValue X) : Option OwnFile :=
  let (attr, w) := v.marking
  let column (t : QAtomicType) (n : USize) (e : Ext.Enc X) (domain : String) : OwnFile :=
    let (kind, parts) := ownParts e
    { code := t.code.toUInt8, attr, kind, count := n, domain, parts }
  match w with
  | .enum d (.vector .i64 n e _) => if d.isEmpty then none else some (column .i64 n e d)
  | .vector _ _ (.gen _) _ => none
  | .vector _ _ .pos _ => none
  | .vector t n e _ => if t == .general then none else some (column t n e "")
  | _ => none


end Rel.Db
