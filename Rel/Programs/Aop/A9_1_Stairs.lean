/-! # Min Cost Climbing Stairs as `H ≜ ⦇T⦈°⦇h⦈`, B&dM §9.1 (`AOP/A9_1_Stairs.lean`), in Rel: no row ported

The instance lives on `N2 ≜ {xs ∈ [ℕ] | length xs ∈ {1,2}}`, a subtype of `[ℕ]` with no Rel object, and on the generic
rows of `A9_1` (`H T h`, `M T h ≤`, `powerRel`, base functor `F`), none of which is a Rel term. -/


-- not ported: F_obj (Freyd.Alg.RelSet.Stairs.F_obj, 09-dynamic.typ:38): an equation of carriers `𝟏 ⊕ N2×X`, `rfl`; no object `N2` and no base functor in Rel
-- not ported: T_cata (Freyd.Alg.RelSet.Stairs.T_cata, 09-dynamic.typ:44): `⦇T⦈ = ι′ concat` over the subtype `N2` of `[ℕ]` (no Rel object) and the fold-defined `concat`, whose den has no lemma (A9_1)
-- not ported: dynamic_programming_lower (Freyd.Alg.RelSet.Stairs.dynamic_programming_lower, 09-dynamic.typ:43): the Stairs instance of A9_1's `dynamic_programming_lower`, which needs `H T h`, `M T h ≤`, `powerRel` and an initial algebra of the base functor
-- not ported: dynamic_programming_upper_tail (Freyd.Alg.RelSet.Stairs.dynamic_programming_upper_tail, 09-dynamic.typ:146): same blockers, plus `(∋ F)° \ …` at the base functor object

