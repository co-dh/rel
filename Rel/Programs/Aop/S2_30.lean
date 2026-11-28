import Rel.Programs.Prelude
import Rel.Lang.Laws.AopS2_30

/-! # Division laws of freyd §2.30 (`Freyd/S2_30.lean`), in Rel

Each theorem is named after the last component of its freyd declaration, with the declaration and the companion
position (chapter file : line) beside it. `R/S` and `R\S` read their operands whole, within the identity universes
(`Rel/Lang/Laws/AopS2_30.lean`: `ldivDen_id`, `rdivDen_id`). -/

namespace Rel.Programs

open Rel.Programs.prelude in
rel_program aopS2_30 where
    theorem divCompLe(R : α ⟶ γ, S : β ⟶ γ) : (R / S) S ⊑ R by Rel.Lang.Tm.div_comp_le_den  -- Freyd.Alg.DivisionAllegory.div_comp_le, 00-laws.typ:311
    theorem divComp(X : α ⟶ δ, S : β ⟶ δ, W : γ ⟶ δ) : (X / S) (S / W) ⊑ X / W by Rel.Lang.Tm.div_comp_den  -- Freyd.Alg.div_comp, 00-laws.typ:334
    theorem divCompAssoc(X : α ⟶ δ, S₁ : β ⟶ γ, S₂ : γ ⟶ δ) : X / (S₁ S₂) = (X / S₂) / S₁ by Rel.Lang.Tm.div_comp_assoc_den  -- Freyd.Alg.div_comp_assoc, 00-laws.typ:105
    theorem divInterEq(R : α ⟶ γ, R' : α ⟶ γ, S : β ⟶ γ) : (R ∩ R') / S = (R / S) ∩ (R' / S) by Rel.Lang.Tm.div_inter_eq_den  -- Freyd.Alg.div_inter_eq, 00-laws.typ:54
    theorem divSelfComp(X : α ⟶ β) : (X / X) X = X by Rel.Lang.Tm.div_self_comp_den  -- Freyd.Alg.div_self_comp, 00-laws.typ:346
    theorem divSelfCompSelf(X : α ⟶ β) : (X / X) (X / X) = X / X by Rel.Lang.Tm.div_self_comp_self_den  -- Freyd.Alg.div_self_comp_self, 00-laws.typ:342
    theorem divUnion(X : α ⟶ γ, S₁ : β ⟶ γ, S₂ : β ⟶ γ) : X / (S₁ ∪ S₂) = (X / S₁) ∩ (X / S₂) by Rel.Lang.Tm.div_union_den  -- Freyd.Alg.div_union, 00-laws.typ:352
    theorem leftDivComp(S₁ : α ⟶ β, S₂ : β ⟶ γ, X : α ⟶ δ) : (S₁ S₂) \ X = S₂ \ (S₁ \ X) by Rel.Lang.Tm.left_div_comp_den  -- Freyd.Alg.leftDiv_comp, 00-laws.typ:117
    theorem leftDivCompLe(S : α ⟶ β, X : α ⟶ γ) : S (S \ X) ⊑ X by Rel.Lang.Tm.left_div_comp_le_den  -- Freyd.Alg.leftDiv_comp_le, 00-laws.typ:314
    theorem leftDivDiv(S : α ⟶ β, X : α ⟶ δ, W : γ ⟶ δ) : S \ (X / W) = (S \ X) / W by Rel.Lang.Tm.left_div_div_den  -- Freyd.Alg.leftDiv_div, 00-laws.typ:107
    theorem leftDivInter(S : α ⟶ β, R : α ⟶ γ, R' : α ⟶ γ) : S \ (R ∩ R') = (S \ R) ∩ (S \ R') by Rel.Lang.Tm.left_div_inter_den  -- Freyd.Alg.leftDiv_inter, 00-laws.typ:61
    theorem oneLeDivSelf(X : α ⟶ β) : 𝟙 ⊑ X / X by Rel.Lang.Tm.one_le_div_self_den  -- Freyd.Alg.one_le_div_self, 00-laws.typ:338

-- not ported: divOne (Freyd.Alg.div_one): `R / 𝟙` does not elaborate ("a term that needs keys where none are supplied"): the operand `𝟙` of `/` is read whole, which needs a universe the abstract object β has not

end Rel.Programs
