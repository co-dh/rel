module

public import Rel.Lang.PreludeRows

@[expose] public section

/-! `suffix : [α] ⟶ [α] ≜ cat° π₂` (`Programs/Prelude.lean`) means the row `suffix`'s `rowDens` term, `ys <:+ xs`
    (B10b): the definition's term is built here, `cat°` as the row `uncat` its `conv` names. -/

namespace Rel.Lang

open Rel.Core.Rel hiding id comp recip inter union zero le inl inr junc

/-- The prelude's `suffix = cat° π₂` at `[B] ⟶ [B]`. -/
def Tm.suffixDef (B : Obj) : Tm (.arr B) (.arr B) := .comp (B := .prod (.arr B) (.arr B)) (.prim (rowOf "uncat")) .outr

/-- **The definition of `suffix` means the row**: `ys` is the second half of a split of `xs`. -/
theorem Tm.suffixDef_den (ρ : Val) {B : Obj} (xs ys : Obj.El (.arr B)) :
    (Tm.suffixDef B).den ρ xs ys ↔ Prim.den (rowOf "suffix") (.arr B) (.arr B) [] xs ys := by
  have hs : (rowOf "suffix").sig = ([], .list (.var {} "B"), .list (.var {} "B")) := rfl
  have ho : (rowOf "suffix").objs (.arr B) (.arr B) [] = some [B] := by
    simp [Prim.objs, Prim.vars, hs, Option.orElse, OExp.unify, OExp.vars, List.eraseDups, List.eraseDupsBy,
      List.eraseDupsBy.loop, List.lookup]
  have hf : rowDens.find? (·.1.sym == (rowOf "suffix").sym) = some ⟨RowCode.suffix, fun _ _ xs ys => ys <:+ xs⟩ := rfl
  have hr : Prim.den (rowOf "suffix") (.arr B) (.arr B) [] xs ys = (ys <:+ xs) := by
    unfold Prim.den; simp only [List.map_nil]
    rw [hf, ho]; dsimp only; rw [dif_pos ⟨rfl, rfl⟩]
  rw [hr]
  simp only [Tm.suffixDef, Tm.den, Prim.den_uncat, Core.Rel.comp, Core.Rel.graph]
  constructor
  · rintro ⟨p, hp, rfl⟩; exact ⟨p.1, hp.symm⟩
  · rintro ⟨t, ht⟩; exact ⟨(t, ys), ht.symm, rfl⟩

end Rel.Lang
