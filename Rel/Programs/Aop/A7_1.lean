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

-- not ported: Λ_comp_est, Λ_comp_est_context, singletonMap_comp_est, powerRel_comp_est_le, powerRel_map_comp_est, powerRel_est_eq_bigUnion (both rows), powerRel_est_le_bigUnion: freyd's `est R = ∋ ∩ (∈\R°)` is the extreme under `R` alone; the prelude's `est(Q)` is the extreme under `Q ∪ 𝟙` (`estDen_iff`), so a statement about a non-reflexive `R` is not the prelude row's, and no other `est` exists to state it with
-- not ported: bigUnion_comp_lb: not attempted past a trial where `Λ(∋ ∋)` over `[[α]]` did not elaborate at the statement's type; `union` has no prelude row

end Rel.Programs
