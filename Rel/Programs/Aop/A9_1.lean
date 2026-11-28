import Rel.Programs.Prelude
import Rel.Lang.Laws.AopA9_1

/-! # Laws of AOP `A9_1.lean` (companion `09-dynamic.typ`), in Rel

Each theorem is named after its freyd declaration's last component, with the declaration and the companion position
(chapter file : line) beside it (`Rel/Lang/Laws/AopA9_1.lean`). freyd's generic relator `F` is read as the list relator
`F(R)`, and `Alg F A` as a relation `[A] ⟶ A`. -/

namespace Rel.Programs

open Rel.Programs.prelude in
rel_program aopA9_1 where
    -- the order `≤ = cost ≼ cost°` is written out, so freyd's premise `hR : ≤ = cost ≼ cost°` is substituted
    theorem presOfCost(h : [α] ⟶ α, cost : α ⟶ γ, k : [γ] ⟶ γ, S : γ ⟶ γ) if dom(cost) = 𝟙, cost°cost ⊑ 𝟙, h cost = F(cost) k, F(S) k ⊑ k S : F(cost S cost°) h ⊑ h (cost S cost°) by Rel.Lang.Tm.presOfCost_den  -- Freyd.Alg.pres_of_cost, 09-dynamic.typ:81
    -- `S×𝟙` is written ⟨π₁ S, π₂⟩ (the product's guard does not enter), `Simple H°` is `H H° ⊑ 𝟙`
    theorem presInContext(h : [α] ⟶ α, cost : α ⟶ γ, H : β ⟶ α, k : [γ×β] ⟶ γ, S : γ ⟶ γ) if dom(cost) = 𝟙, cost°cost ⊑ 𝟙, H H° ⊑ 𝟙, h cost = F(⟨cost, H°⟩) k, F(⟨π₁ S, π₂⟩) k ⊑ k S : F((cost S cost°) ∩ (H° H)) h ⊑ h (cost S cost°) by Rel.Lang.Tm.presInContext_den  -- Freyd.Alg.pres_in_context, 09-dynamic.typ:82

-- not ported: concat_length_hom, sum_mono, pres_concat_length (Freyd.Alg.RelSet.ListRel, 09-dynamic.typ:269, 271, 273): `length` at a generic result object does not elaborate (`ran` at `length`'s seed 0, "an object variable its constant is generic over"), and at a numeric object the statements need the den of the fold-defined `concat`, `length`, `sum` (through `cat`/`loop`), for which no lemma exists; pres_concat_length is `presOfCost` at these three
-- not ported: dynamic_programming_lower, dynamic_programming_upper_head, dynamic_programming_upper_tail, dynamic_programming_upper, dynamic_programming_thin_lower, dynamic_programming_thin_upper, dynamic_programming_thin_prefixed (Freyd.Alg, 09-dynamic.typ:74-79, 167): `H T h = ⦇T⦈°⦇h⦈` and `M T h ≤ = Λ(H) est(≤)` need an initial algebra of a base functor `F` (not the list relator `F(R)`: a list algebra `[B] ⟶ B` has no cata), `powerRel` and `thinRel` are not prelude rows, and freyd's `est(≤)` is the prelude's `est(≤ ∪ 𝟙)`; stating them is a fold-level port of Theorem 9.1 with `hylo_fixed`, not attempted
-- not ported: dynamic_programming, dynamic_programming_thin (Freyd.Alg, 09-dynamic.typ:61, 162): the `mu (fun X => Λ(T°) powerRel(F.map X ≫ h) est ≤) ⊑ M T h ≤` form on the same `H`, `M`, `powerRel`, `thinRel`, base functor `F`
-- not ported: birelator_thin_condition (Freyd.Alg, 09-dynamic.typ:80): a statement over a variable binary relator `G` (`BiRelator`); no relator parameter exists (the ×/+ instances are A5_2 rows)
-- not ported: dp_disjoint_branch, dp_disjoint_ranges (Freyd.Alg.RelSet, 09-dynamic.typ:83, 84): over `thinRel`, `powerRel` and `sumMap`, none a prelude row, and `est R` of a non-reflexive `R`
-- not ported: est_arm₂_le, est_summand_le (Freyd.Alg.RelSet.SL, 10-greedy.typ:30, 31): element quantifiers over `Q ≤`-arms of the snoc-list `F L W`, with `thinRel`/`est` of the same kind as the rows above
-- not ported: Stairs.F_obj, Stairs.T_cata, Stairs.dynamic_programming_lower, Stairs.dynamic_programming_upper_tail (09-dynamic.typ:38, 44, 43, 146): `F_obj` is an equation of objects; the rest are the Stairs instance (types `N2`, `⦇T⦈ = ι′ concat`) of the generic rows above, and `N2` is a subtype of `[ℕ]` with no Rel object

end Rel.Programs
