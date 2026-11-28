import Rel.Programs.Prelude
import Rel.Lang.Laws.EstMap
import Rel.Lang.Laws.AopA7_7_MSS

/-! # Laws of freyd §7.7 (`AOP/A7_7_MSS.lean`, Ex 7.40 the maximum segment sum), in Rel

The program `mss` (`Rel/Programs/Mss.lean`) has the concrete `zero`, `plus`, `≥` on the bounded numbers `N`; here each row
is stated at an arbitrary seed `e : 1 ⟶ β`, step `P` and order `R` (the stronger form: `zero`, `⊤zero ∪ plus`, `≥` are instances),
because `sum`/`plus` at a type variable do not elaborate and at `N` the sums overflow (`mss` guards them with `safe`). -/

namespace Rel.Programs

open Rel.Programs.prelude in
rel_program aopA7_7_MSS where
    -- Freyd.Alg.RelSet.MSS.mss_mono, 07-optimisation.typ:787: F(R)[e, ⊤e ∪ P] ⊑ [e, ⊤e ∪ P] R, F(R)[e,S] = [e, ⟨π₁,π₂R⟩ S];
    -- the premises are R reflexive on e's values and P monotone (`mss`: `geqRefl`, `plus` monotone)
    theorem mssMono(e : 1 ⟶ β, P : δ×β ⟶ β, R : β ⟶ β) if e ⊑ e R, ⟨π₁,π₂R⟩ P ⊑ P R : [e, ⟨π₁,π₂R⟩ (⊤e ∪ P)] ⊑ [e, ⊤e ∪ P] R by Rel.Lang.Tm.mssMono_den
    -- Freyd.Alg.RelSet.MSS.mss_step_plus, 07-optimisation.typ:737: Λ(P) est(Q) = P for the map P = plus (the prelude's `estMap`; est(Q) is est(Q ∪ 𝟙))
    theorem mssStepPlus(P : δ×β ⟶ β, Q : β ⟶ β) if P°P ⊑ 𝟙 : Λ(P) est(Q) = P by Rel.Lang.Tm.estMap_den
    -- Freyd.Alg.RelSet.MSS.mss_step, 07-optimisation.typ:810: Λ([zero, S]) est(≥) = [zero, Λ(S) est(≥)]; S = ⊤zero ∪ plus gives ⊕ = Λ(S) est(≥)
    theorem mssStep(e : 1 ⟶ β, S : δ×β ⟶ β, Q : β ⟶ β) if e°e ⊑ 𝟙 : Λ([e, S]) est(Q) = [e, Λ(S) est(Q)] by Rel.Lang.Tm.mssStep_den
    -- Freyd.Alg.RelSet.MSS.cons_comp_sum, 07-optimisation.typ:732: cons sum = (𝟙×sum) plus, at the right fold sum = ⦇[e, P]⦈ʳ
    -- (the prelude's left-fold `sum` agrees with it only where the bounded sums do not overflow)
    theorem consCompSum(e : 1 ⟶ β, P : α×β ⟶ β) : cons ⦇[e, P]⦈ʳ = ⟨π₁,π₂⦇[e, P]⦈ʳ⟩ P by Rel.Lang.Tm.consCompSum_den
    -- Freyd.Alg.RelSet.MSS.prefAlg_comp_sum, 07-optimisation.typ:748: [nil, ⊤nil ∪ cons] sum = F(sum) [zero, ⊤zero ∪ plus],
    -- F(X)[e,S] = [e, ⟨π₁,π₂X⟩ S]; for any entire X with sum's two equations nil X = e and cons X = ⟨π₁,π₂X⟩ P
    theorem prefAlgCompSum(X : [α] ⟶ β, e : 1 ⟶ β, P : α×β ⟶ β) if nil X = e, cons X = ⟨π₁,π₂X⟩ P, dom(X) = 𝟙 : [nil, ⊤nil ∪ cons] X = [e, ⟨π₁,π₂X⟩ (⊤e ∪ P)] by Rel.Lang.Tm.prefAlgCompSum_den

-- ported by `Rel/Programs/Mss.lean`: mss_shape (07-optimisation.typ:699) is `mss.proof.toShape`; mss_greedy (:833) is `mss.proof.greedyFold`; mss_prefix_sum (:756) is `mss.proof.toFused`
-- not ported: mss_eq_scan (07-optimisation.typ:682): `语法缺` in freyd; it is `mss.toScan`, owed to Mss.lean (proved there by another agent)
-- not ported: mss_mono_fork (07-optimisation.typ:794): `语法缺` in freyd; its step (composition distributes over ∪) is inside the proof of `mssMono`
-- not ported: scan_pair_comm (07-optimisation.typ:840): the cata-defining equation of `⟨g, Λ(suffix)E(g)⟩` at the scan algebra `k` is `mss.toScan` (Rel/Programs/Mss.lean, Rel/Lang/Laws/MssGreedy.lean), proved there by another agent

end Rel.Programs
