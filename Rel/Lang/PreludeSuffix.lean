module

public import Rel.Lang.PreludeRows
public import Rel.Programs.Prelude

@[expose] public section

/-! `suffix : [α] ⟶ [α] ≜ cat° π₂` (`Programs/Prelude.lean`) means the row `suffix`'s `rowDens` term, `ys <:+ xs`
    (B10b): the definition's term is built here, `cat°` as the row `uncat` its `conv` names. -/

namespace Rel.Lang

open Rel.Core.Rel hiding id comp recip inter union zero le inl inr junc

/-- The prelude's `suffix = cat° π₂` at `[B] ⟶ [B]`. -/
def Tm.suffixDef (B : Obj) : Tm (.arr B) (.arr B) := .comp (B := .prod (.arr B) (.arr B)) (.prim (rowOf "uncat")) .outr

end Rel.Lang
