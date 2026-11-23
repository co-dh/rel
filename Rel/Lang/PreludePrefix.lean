module

public import Rel.Lang.PreludeRows
public import Rel.Programs.Prelude

@[expose] public section

/-! `prefix : [α] ⟶ [α] ≜ cat° π₁` (`Programs/Prelude.lean`) means the row `prefix`'s `rowDens` term, `ys <+: xs`
    (B10b): the definition's term is built here, `cat°` as the row `uncat` its `conv` names. -/

namespace Rel.Lang

open Rel.Core.Rel hiding id comp recip inter union zero le inl inr junc

/-- The prelude's `prefix = cat° π₁` at `[B] ⟶ [B]`. -/
def Tm.prefixDef (B : Obj) : Tm (.arr B) (.arr B) := .comp (B := .prod (.arr B) (.arr B)) (.prim (rowOf "uncat")) .outl

end Rel.Lang
