module

public import Rel.Kernel.Db.ObjectFile
public import Rel.Kernel.Value

-- exposed: every def body is a spec a downstream `rfl`/`decide`/`simp` may unfold (PLAN W.8)
@[expose] public section

/-! The part of `Rel.Db.Own` the Rel kernels reach; `Rel.Db.Own` imports it. -/


namespace Rel.Db

open Rel

/-- A column's constructor kind and its parts, numbered as `ownNParts` (`crate/src/own.rs`'s `OWN_NPARTS`) gives each
kind its part count; there is no kind 1, a boolean being a `u1` `foR`. A form with a field that is no buffer has no
parts and is refused, naming the form. Positions are `none`: no file, `n` is the other side's (PLAN 6.13). -/
def ownParts : Enc → Except String (Option (UInt8 × Array ByteArray))
  | .foR metadata pack => pure (some (2, #[metadata, pack]))
  | .pos => pure none

/-- The constructor `ownParts` took apart, from the kind and the parts `ownMap` answers: each `ByteArray` is taken as
it is, so a mapped part stays in the mapping. -/
def ownEnc (kind : UInt8) (parts : Array ByteArray) : Option (Enc) :=
  match kind, parts with
  | 2, #[metadata, pack] => some (.foR metadata pack)
  | _, _ => none

/-- The file the column `e` of `n` elements of `t` is written as; `none` for positions, which have no file
(`ownParts`). A general list is refused. -/
def ownFile (t : QAtomicType) (n : USize) (e : Enc) : Except String (Option OwnFile) := do
  if t == .general then throw "a general list, which qlean's own column format does not hold"
  return (← ownParts e).map fun (kind, parts) =>
    { code := t.code.toUInt8, kind, count := n, parts }


end Rel.Db
