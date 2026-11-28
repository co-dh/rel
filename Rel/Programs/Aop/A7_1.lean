import Rel.Programs.Prelude
import Rel.Lang.Laws.AopA7_1

/-! # Laws of AOP `A7_1.lean` (companion `07-optimisation.typ`), in Rel

Each theorem is named after its freyd declaration's last component, with the declaration and the companion position
(chapter file : line) beside it. `τ` is freyd's `singletonMap`; `Λ(S)` has a sorted list at every point where the
premise `dom(Λ(S)) = 𝟙` holds. -/

namespace Rel.Programs

open Rel.Programs.prelude in
rel_program aopA7_1 where
    theorem singletonMapCompLb(R : α ⟶ α) : τ (∋°\R) = R by Rel.Lang.Tm.singletonMapCompLb_den  -- Freyd.Alg.singletonMap_comp_lb, 07-optimisation.typ:61
    theorem lamCompLb(S : β ⟶ α, R : α ⟶ γ) if dom(Λ(S)) = 𝟙 : Λ(S) (∋°\R) = S°\R by Rel.Lang.Tm.lamCompLb_den  -- Freyd.Alg.Λ_comp_lb, 07-optimisation.typ:81
    theorem memLeftDivEq(Z : α ⟶ γ) if dom(Λ(Z°)) = 𝟙 : ∋°\Z = (∋°\∋°) (Λ(Z°))° by Rel.Lang.Tm.memLeftDivEq_den  -- Freyd.Alg.mem_leftDiv_eq, 00-laws.typ:453

    theorem lamCompEst(S : β ⟶ α, Q : α ⟶ α) if dom(Λ(S)) = 𝟙 : Λ(S) est(Q) = S ∩ (S°\(Q° ∪ ran(S))) by Rel.Lang.Tm.lamCompEst_den  -- Freyd.Alg.Λ_comp_est, 07-optimisation.typ:29
    theorem lamCompEstContext(S : β ⟶ α, Q : α ⟶ α) if dom(Λ(S)) = 𝟙 : Λ(S) est((Q ∪ 𝟙) ∩ (S°S)) = Λ(S) est(Q) by Rel.Lang.Tm.lamCompEstContext_den  -- Freyd.Alg.Λ_comp_est_context, 07-optimisation.typ:30
    theorem singletonMapCompEst(Q : α ⟶ α) : τ est(Q) = 𝟙 ∩ (Q ∪ 𝟙)° by Rel.Lang.Tm.singletonMapCompEst_den  -- Freyd.Alg.singletonMap_comp_est, 07-optimisation.typ:27
    theorem powerRelMapCompEst(f : α ⟶ β, Q : β ⟶ β) if dom(f) = 𝟙, f°f ⊑ 𝟙, dom(E(f)) = 𝟙 : E(f) est(Q) = est(f (Q ∪ 𝟙) f°) f by Rel.Lang.Tm.powerRelMapCompEst_den  -- Freyd.Alg.powerRel_map_comp_est, 07-optimisation.typ:33 (`P(f) = E(f)` for a map `f`, `powerRel_map`)

-- not ported: powerRel_comp_est_le (Freyd.Alg.powerRel_comp_est_le, 07-optimisation.typ:196), powerRel_est_eq_bigUnion (07-optimisation.typ:39, 10-appendix.typ:85), powerRel_est_le_bigUnion (07-optimisation.typ:212): `powerRel` has no closed Rel term (A5_4: `∋°` under `\` needs keys where none are supplied), and the last two also need `union`, which has no prelude row
-- not ported: bigUnion_comp_lb: not attempted past a trial where `Λ(∋ ∋)` over `[[α]]` did not elaborate at the statement's type; `union` has no prelude row

end Rel.Programs
