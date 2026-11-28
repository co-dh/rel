import Rel.Programs.Prelude
import Rel.Lang.Laws.AopA6_7

/-! # Closure laws of freyd §6.7 (`AOP/A6_7.lean`), in Rel

Each theorem is named after the last component of its freyd declaration, with the declaration and the companion
position (chapter file : line) beside it. `star(R)` is the prelude's `μX : 𝟙 ∪ (R X)` (`Rel/Lang/Laws/AopA6_7.lean`). -/

namespace Rel.Programs

open Rel.Programs.prelude in
rel_program aopA6_7 where
    theorem idLeStar(R : α ⟶ α) : 𝟙 ⊑ star(R) by Rel.Lang.Tm.id_le_star_den  -- Freyd.Alg.id_le_star, 06-recursive.typ:495
    theorem leStar(R : α ⟶ α) : R ⊑ star(R) by Rel.Lang.Tm.le_star_den  -- Freyd.Alg.le_star, 06-recursive.typ:504
    theorem starTrans(R : α ⟶ α) : star(R) star(R) ⊑ star(R) by Rel.Lang.Tm.star_trans_den  -- Freyd.Alg.star_trans, 06-recursive.typ:519
    theorem preorderPrefixed(R : α ⟶ α, X : α ⟶ α) if 𝟙 ⊑ X, X X ⊑ X, R ⊑ X : 𝟙 ∪ (R X) ⊑ X by Rel.Lang.Tm.preorder_prefixed_den  -- Freyd.Alg.preorder_prefixed, 06-recursive.typ:527
    theorem starLeOfPreorder(R : α ⟶ α, X : α ⟶ α) if 𝟙 ⊑ X, X X ⊑ X, R ⊑ X : star(R) ⊑ X by Rel.Lang.Tm.star_le_of_preorder_den  -- Freyd.Alg.star_le_of_preorder, 06-recursive.typ:531
    theorem starSimulationStep(A : β ⟶ β, B : α ⟶ β, C : α ⟶ α) if B A ⊑ C B : (star(C) B) A ⊑ star(C) B by Rel.Lang.Tm.star_simulation_step_den  -- Freyd.Alg.star_simulation_step, 09-dynamic.typ:450
    theorem starSimulation(A : β ⟶ β, B : α ⟶ β, C : α ⟶ α) if B A ⊑ C B : B star(A) ⊑ star(C) B by Rel.Lang.Tm.star_simulation_den  -- Freyd.Alg.star_simulation, 09-dynamic.typ:450
    theorem compStarBodyLe(A : β ⟶ β, B : α ⟶ β, C : α ⟶ α, Z : β ⟶ β) if B A ⊑ C B : B (𝟙 ∪ (A Z)) ⊑ B ∪ (C (B Z)) by Rel.Lang.Tm.comp_star_body_le_den  -- Freyd.Alg.comp_star_body_le, 10-appendix.typ:470
    -- `θ(P,Q) = P ∪ (μX : Q ∪ (X R − P))`, written out; freyd's `theta` is not a prelude definition
    theorem thetaZeroLeft(R : α ⟶ α, S : β ⟶ α) : 𝟘 ∪ (μX : S ∪ ((X R) − 𝟘)) = S star(R) by Rel.Lang.Tm.theta_zero_left_den  -- Freyd.Alg.theta_zero_left, 06-recursive.typ:586
    theorem thetaZeroRight(R : α ⟶ α, P : β ⟶ α) : P ∪ (μX : 𝟘 ∪ ((X R) − P)) = P by Rel.Lang.Tm.theta_zero_right_den  -- Freyd.Alg.theta_zero_right, 06-recursive.typ:595

-- not ported: Λ_star (Freyd.Alg.Λ_star, 06-recursive.typ:540): `cup` (the union of two sets) is not in the prelude
-- not ported: star_simulation_by_fusion (Freyd.Alg.star_simulation_by_fusion, 10-appendix.typ:471): the statement is `starSimulation`'s, proved there by fusion instead
-- not ported: star_div_prefixed (Freyd.Alg.star_div_prefixed, 06-recursive.typ:515): a step of freyd's division proof of `starTrans`; `starTrans` is proved directly
end Rel.Programs
