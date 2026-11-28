import Rel.Programs.Prelude
import Rel.Lang.Laws.AopA10_1

namespace Rel.Programs

open Rel.Programs.prelude in
rel_program aopA10_1 where
    -- Freyd.Alg.greedy_dp_lower, 10-greedy.typ:39. Stronger form: `H : α ⟶ β` replaces `⦇h⦈ ⦇T⦈°` (the list relator `F(R)` for freyd's `F`, `T : [α] ⟶ α`), with only `T° F(H) h ⊑ H`; `est(R)` is freyd's `est(R ∪ 𝟙)`
    theorem greedyDpLower(T : [α] ⟶ α, h : [β] ⟶ β, H : α ⟶ β, Q : [α] ⟶ [α], R : β ⟶ β) if T° F(H) h ⊑ H : Λ(T°) est(Q) F(Λ(H) est(R)) h ⊑ H by Rel.Lang.Tm.greedyDpLower_den
    -- Freyd.Alg.greedy_dp_upper, 10-greedy.typ:40. Stronger form: `H ⊑ T° F(H) h` for any `H`, `h` simple (freyd: a map), and freyd's `≤`, `Q` are `R ∪ 𝟙`, `Q ∪ 𝟙` (the prelude's `est`); the goal is freyd's `≤°` = `R° ∪ 𝟙`
    theorem greedyDpUpper(T : [α] ⟶ α, h : [β] ⟶ β, H : α ⟶ β, Q : [α] ⟶ [α], R : β ⟶ β) if H ⊑ T° F(H) h, h° h ⊑ 𝟙, F(R ∪ 𝟙) h ⊑ h (R ∪ 𝟙), (R ∪ 𝟙)(R ∪ 𝟙) ⊑ R ∪ 𝟙, (Q ∪ 𝟙) F(H) h ⊑ F(H) h (R ∪ 𝟙) : H° Λ(T°) est(Q) F(Λ(H) est(R)) h ⊑ R° ∪ 𝟙 by Rel.Lang.Tm.greedyDpUpper_den
    -- Freyd.Alg.RelSet.greedy_disjoint_ranges, 10-greedy.typ:47; `Q₁ + Q₂` is `[Q₁ inl, Q₂ inr]`, `[V₁,V₂]°` elaborates to `V₁° inl ∪ V₂° inr`
    theorem greedyDisjointRanges(V₁ : α ⟶ γ, V₂ : β ⟶ γ, U₁ : α ⟶ δ, U₂ : β ⟶ δ, Q₁ : α ⟶ α, Q₂ : β ⟶ β) if V₂ V₁° = 𝟘 : Λ([V₁, V₂]°) est([Q₁ inl, Q₂ inr]) [U₁, U₂] = (ran(V₁) Λ(V₁°) est(Q₁) U₁) ∪ (ran(V₂) Λ(V₂°) est(Q₂) U₂) by Rel.Lang.Tm.greedyDisjointRanges_den


-- not ported: greedy_dp, greedy_dp_prefixed, greedy_dp_step1 (Freyd.Alg, 10-greedy.typ:16): `mu (fun X : A ⟶ B => Λ(T°) est(Q) F.map X h)` and `M T h ≤` need the initial algebra of a base functor (`⦇T⦈`, `⦇h⦈`, `hylo_fixed`), not the list relator, and `mu` over a Lean function; the two halves greedyDpLower, greedyDpUpper above are the content
-- not ported: greedy_dp_of_birelator (Freyd.Alg, 10-greedy.typ): over a variable `BiRelator G`; no relator parameter exists
-- not ported: est_le_eps, powerRel_inl_est, powerRel_inr_est, est_ran_split, union_le, union_mono (Freyd.Alg, 10-greedy.typ): `est_le_eps` is `estP_iff`'s first conjunct (inlined in greedyDpLower_core); `powerRel` has no closed Rel term (A5_4); `est_ran_split` is the left-to-right half of greedyDisjointRanges' proof; `union_le`/`union_mono` are `RelSet` lattice facts
-- not ported: greedy_dp_arms (Freyd.Alg.RelSet.SL, 10-greedy.typ): the snoc-list functor `F L E` with `arm₁`, `arm₂`, `armQ₁`, `armQ₂` and `rprodMap`, and `mu` over `Λ(…) est(…)` of the model objects

end Rel.Programs
