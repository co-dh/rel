import Rel.Kernel.Db.ObjectFile
import Rel.Kernel.Value

/-! The part of `Rel.Db.Own` the Rel kernels reach; `Rel.Db.Own` imports it. -/


namespace Rel.Db

open Rel

/-- A column's constructor kind and its parts, numbered as `ownNParts` (`crate/src/own.rs`'s `OWN_NPARTS`) gives each
kind its part count; there is no kind 1, a boolean being a `u1` `foR`. A form with a field that is no buffer has no
parts and is refused, naming the form. Positions are `none`: no file, `n` is the other side's (PLAN 6.13). -/
def ownParts : Ext.Enc X → Except String (Option (UInt8 × Array ByteArray))
  | .foR metadata pack => pure (some (2, #[metadata, pack]))
  | .pos => pure none
  | .syms _ _ => throw "a `syms` column, which the own format does not hold: a symbol column is stored as `foR` ids \
      into a sorted dictionary (doc/rel-architecture.zh.typ §4), and no writer builds that yet"
  | .enum _ _ _ => throw "an `enum` column, which the own format does not hold: a symbol column is stored as `foR` ids \
      into a sorted dictionary (doc/rel-architecture.zh.typ §4), and no writer builds that yet"
  | .gen _ => throw "a general list, which qlean's own column format does not hold"

/-- The constructor `ownParts` took apart, from the kind and the parts `ownMap` answers: each `ByteArray` is taken as
it is, so a mapped part stays in the mapping. -/
def ownEnc (kind : UInt8) (parts : Array ByteArray) : Option (Ext.Enc X) :=
  match kind, parts.toList with
  | 2, [metadata, pack] => some (.foR metadata pack)
  | _, _ => none

/-- The file a value is written as when it is a column: a vector, or an enumeration's indices under their domain's
name, either wearing an attribute; `none` for positions, which have no file (`ownParts`). Every other value is refused,
naming what it is. -/
def ownFile (v : Ext.QValue X) : Except String (Option OwnFile) :=
  let (attr, w) := v.marking
  let column (t : QAtomicType) (n : USize) (e : Ext.Enc X) (domain : String) : Except String (Option OwnFile) :=
    return (← ownParts e).map fun (kind, parts) => { code := t.code.toUInt8, attr, kind, count := n, domain, parts }
  match w with
  | .enum d (.vector .i64 n e _) =>
    if d.isEmpty then throw "an enumeration with an empty domain name" else column .i64 n e d
  | .vector t n e _ =>
    if t == .general then throw "a general list, which qlean's own column format does not hold" else column t n e ""
  | _ => throw "not a column: neither a vector nor an enumeration of longs"


end Rel.Db
