/-! # Paths in a layered network, B&dM §8.2 (`AOP/A8_2.lean`), in Rel: no row ported

Every 可写 row of the file needs one of: the power relator `powerRel` (no closed Rel term, see `A5_4`), the abstract
bifunctor `F : BiRelator` (Obj is closed, no relator parameter), or the structure field of freyd's `sumCop` (in Rel the
coproduct injection is the primitive `inl`, so `u₁ = graph inl` is a syntactic identity). The rows with `↔` or host
`List`/`Nat` in the statement were not 可写 to begin with. -/

-- not ported: sumCop_u₁_eq (Freyd.Alg.Paths.sumCop_u₁_eq, 08-thinning.typ:281): `(sumCop B C).u₁ = graph inl` is a structure field of freyd's coproduct; in Rel `inl` is the primitive, the equation is a syntactic identity
-- not ported: sumCop_u₂_eq (Freyd.Alg.Paths.sumCop_u₂_eq, 08-thinning.typ:284): same as sumCop_u₁_eq, for `inr`
-- not ported: Λ_F_map_eps_id (Freyd.Alg.Paths.Λ_F_map_eps_id, 08-thinning.typ:293): the right side is `[𝟙 P(inl), cpl P(inr)]` with `P` = powerRel, which has no closed Rel term (A5_4); `cpl` is also a `cpMap` of a relator
-- not ported: Λ_F_map_id_eps (Freyd.Alg.Paths.Λ_F_map_id_eps, 08-thinning.typ:296): the right side uses `singletonMap ≫ P(inl)` and `cpr ≫ P(inr)`, `P` = powerRel (A5_4)
-- not ported: thinning_paths_alg (Freyd.Alg.thinning_paths_alg, 08-thinning.typ:363): states `P(Λ(...) est R)` and `Λ(F(∋,∋)α) thin(Q)` at an abstract `BiRelator F` and algebra `α`: powerRel (A5_4), the inline thin of A8_1 needs keys, and a relator parameter is out of scope
-- not ported: consw_apply (08-thinning.typ:264), wrapz_apply (306): host `List`/`Nat`/`Decidable` in the statement
-- not ported: sumCop_u₁_apply (08-thinning.typ:282), sumCop_u₂_apply (285): `↔` of points, a pointwise restatement of the (unported) injection equations
-- not ported: cpMap_comp_powerRel_alphaR_comp_est_eq_junc (08-thinning.typ:373), pathAlg_monotonic (340): structure parameter `[Class A]`, Rel has no parameterised structures
