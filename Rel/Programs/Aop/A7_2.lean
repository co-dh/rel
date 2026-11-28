import Rel.Programs.Prelude
import Rel.Lang.Laws.AopA7_2

namespace Rel.Programs

open Rel.Programs.prelude in
rel_program aopA7_2 where
    theorem greedy(e : 1 ⟶ β, S : α×β ⟶ β, Q : β ⟶ β) if (Q ∪ 𝟙)(Q ∪ 𝟙) ⊑ Q ∪ 𝟙, ⟨π₁, π₂|(Q ∪ 𝟙)⟩ S ⊑ S (Q ∪ 𝟙), dom(Λ(⦇[e, S]⦈ʳ)) = 𝟙 : ⦇[(𝟙÷∋)E(e)est(Q), (𝟙÷∋)E(S)est(Q)]⦈ʳ ⊑ (𝟙÷∋)E(⦇[e, S]⦈ʳ)est(Q) by Rel.Lang.Tm.greedy_den  -- Freyd.Alg.greedy, 07-optimisation.typ:360
    theorem fmapEstCompLeFmapEpsComp(f : [β] ⟶ γ, Q : β ⟶ β) : F(est(Q)) f ⊑ F(∋) f by Rel.Lang.Tm.fmapEstCompLeFmapEpsComp_den  -- Freyd.Alg.Fmap_est_comp_le_Fmap_eps_comp, 07-optimisation.typ:340
    theorem distributesOfPres(f : [β] ⟶ β, Q : β ⟶ β) if f°f ⊑ 𝟙, F((Q ∪ 𝟙)°) f ⊑ f (Q ∪ 𝟙)°, dom(Λ(F(∋) f)) = 𝟙 : F(est(Q)) f ⊑ Λ(F(∋) f) est(Q) by Rel.Lang.Tm.distributesOfPres_den  -- Freyd.Alg.distributes_of_pres, 07-optimisation.typ:331

-- not ported: pres_of_distributes (Freyd.Alg.pres_of_distributes, 07-optimisation.typ:333): states cleanly at the list relator, but its proof builds from `ys' F(R°) ys` the list of two-element sets `[{ys'[t], ys[t]}]` and reads `est` off each; not attempted
-- not ported: mon_thm71_step2, mon_thm71_step3, mon_thm71_step4, pres_iff_conj, pres_iff_distributes, pres_recip_iff (Freyd.Alg.*): `↔` between two inequations; a theorem states one relation formula, and each direction is a rewrite of `F.map` for an arbitrary relator
-- not ported: graph_conj_le_iff_monotone, graph_pres_iff_conj, existsImage_apply, powrel_reading_closed, powrel_reading_reached, powrel_reading_reaches, powerRel_reading (Freyd.Alg.RelSet.*): element quantifiers or `↔` over the RelSet model
-- not ported: plus_distributes_le (Freyd.Alg.RelSet.plus_distributes_le): `Plus` of the RelSet model, no prelude row
-- not ported: powerRel_comp_est (Freyd.Alg.RelSet.powerRel_comp_est): `powerRel` does not elaborate (A5_4)

end Rel.Programs
