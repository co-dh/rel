import Rel.Programs.Prelude
import Rel.Lang.Laws.AopA8_4_Knapsack

/-! # Laws of freyd §8.4 (`AOP/A8_4_Knapsack.lean`), in Rel

Packings are lists of (value, weight) pairs, so `val` and `wt` are `π₁` and `π₂` (`value ≜ sum list(val)`, as in
`Rel/Programs/Knapsack.lean`). The step algebra is on snoc lists: its dropping arm `[nil,π₂]` is `π₁ : [α]×α ⟶ [α]`. -/

namespace Rel.Programs

open Rel.Programs.prelude in
rel_program aopA8_4_Knapsack where
    obj N = 0…60                                  -- values, weights and their totals

    value : [α×β] ⟶ α ≜ F(π₁)sum                  -- value ≜ sum list(val): the total value of a packing
    weight : [α×β] ⟶ β ≜ F(π₂)sum                 -- weight ≜ sum list(wt): its total weight
    R : [N×α] ⟶ [N×β] ≜ value ≥ value°           -- more valuable
    Q : [N×N] ⟶ [N×N] ≜ R ∩ (weight ≤ weight°)    -- more valuable and no heavier

    -- Freyd.Alg.RelSet.Knapsack.knap_mono_drop, 08-thinning.typ:686: `(Q×𝟙) π₁ ⊑ π₁ Q`, dropping the head cannot undo `Q`
    theorem knapMonoDrop : ⟨π₁Q,π₂⟩π₁ ⊑ π₁Q by Rel.Lang.Tm.knapMonoDrop_den
    -- Freyd.Alg.RelSet.Knapsack.knap_sort_drop, 08-thinning.typ:692: `(R×𝟙) π₁ ⊑ π₁ R`, the same law at `R`
    theorem knapSortDrop : ⟨π₁R,π₂⟩π₁ ⊑ π₁R by Rel.Lang.Tm.knapMonoDrop_den

-- not ported: value_eq (Freyd.Alg.RelSet.Knapsack.value_eq, 08-thinning.typ:634), weight_eq (637): `value ≜ F(π₁)sum` is the definition above, so the statement is a syntactic identity
-- not ported: R_eq (…R_eq, 08-thinning.typ:649), Q_eq (652): `R` and `Q` are defined above by the relational form the two laws prove equal to freyd's pointwise `R`, `Q`: a syntactic identity
-- not ported: con_eq_junc (…con_eq_junc, 08-thinning.typ:639): `con` is the initial algebra of the host `ConsList`; rel has no `ConsList`/`Alg F` object, `[nil,cons]` is the list fold's own algebra
-- not ported: knap_mono_cons (…, 08-thinning.typ:686), knap_sort_cons (692): `(Q×𝟙) snoc within(w) ⊑ snoc within(w) Q` needs `value(snoc x a) = value x + val a` and plus monotone on `N`; the prelude has no law of `sum`/`plus` over fixed-width atoms (they wrap), so the statement is not provable at a type variable and no bounded-range lemma exists
-- not ported: knap_body (…, 08-thinning.typ:737): the fold-body split needs `cpL`, `cpr`, `h₁`, `g₁` and the thinL/merge laws (`τ_le_dup_cat_thinL`, `dup_cat_le_merge`, `corefl_τ_le_filter`), none of which is a law in rel yet, plus the same `sum` arithmetic for `τ_within`

end Rel.Programs
