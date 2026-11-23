module

public import Rel.Lang.PreludeRows

@[expose] public section

/-! `prefix : [α] ⟶ [α] ≜ cat° π₁` (`Programs/Prelude.lean`) means the row `prefix`'s `rowDens` term, `ys <+: xs`
    (B10b): the definition's term is built here, `cat°` as the row `uncat` its `conv` names. -/

namespace Rel.Lang

open Rel.Core.Rel hiding id comp recip inter union zero le inl inr junc

/-- The prelude's `prefix = cat° π₁` at `[B] ⟶ [B]`. -/
def Tm.prefixDef (B : Obj) : Tm (.arr B) (.arr B) := .comp (B := .prod (.arr B) (.arr B)) (.prim (rowOf "uncat")) .outl

/-- **The definition of `prefix` means the row**: `ys` is the first half of a split of `xs`. -/
theorem Tm.prefixDef_den (ρ : Val) {B : Obj} (xs ys : Obj.El (.arr B)) :
    (Tm.prefixDef B).den ρ xs ys ↔ Prim.den (rowOf "prefix") (.arr B) (.arr B) [] xs ys := by
  have hs : (rowOf "prefix").sig = ([], .list (.var {} "B"), .list (.var {} "B")) := rfl
  have ho : (rowOf "prefix").objs (.arr B) (.arr B) [] = some [B] := by
    simp [Prim.objs, Prim.vars, hs, Option.orElse, OExp.unify, OExp.vars, List.eraseDups, List.eraseDupsBy,
      List.eraseDupsBy.loop, List.lookup]
  have hf : rowDens.find? (·.1.sym == (rowOf "prefix").sym) = some ⟨RowCode.prefix, fun _ _ xs ys => ys <+: xs⟩ := rfl
  have hr : Prim.den (rowOf "prefix") (.arr B) (.arr B) [] xs ys = (ys <+: xs) := by
    unfold Prim.den; simp only [List.map_nil]
    rw [hf, ho]; dsimp only; rw [dif_pos ⟨rfl, rfl⟩]
  rw [hr]
  simp only [Tm.prefixDef, Tm.den, Prim.den_uncat, Core.Rel.comp, Core.Rel.graph]
  constructor
  · rintro ⟨p, hp, rfl⟩; exact ⟨p.2, hp.symm⟩
  · rintro ⟨t, ht⟩; exact ⟨(ys, t), ht.symm, rfl⟩

end Rel.Lang
