/-! # The cons-list datatype of B&dM §6 (`AOP/A6_ConsList.lean`), in Rel: no row ported

freyd defines `ConsList L E` and its base functor `F X = L + (E × X)` as a Lean structure. Rel has no such declaration to
state laws about: the list relator `F(R)` is already spelled `[𝟙 inl, (𝟙×R) inr]` (`1+(X×-)`, as `foldUP` writes it) in the
fold laws, so each row below is an identity of notation or an object-level `rfl`, with no relation-level content. -/

-- not ported: F_obj (05-datatypes.typ:434): `(F L E).obj X = Fobj L E X` is `rfl` on carriers; Rel has no object-level functor, only the sum/product objects
-- not ported: F_obj (08-thinning.typ:625): same declaration as above (a citation of the carrier `L ⊕ E × X`); no relation statement
-- not ported: Fmap_eq_sumMap (09-dynamic.typ:101): `F(R) = 𝟙 + 𝟙×R` is the definition of `F(R)` in Rel (the base functor is written with `+`/`×`), a syntactic identity
-- not ported: F_eq_sum_prod (A6_ConsList.lean:154, cited by the same rows): `F` equals `const L + (const E × id)`; Rel has no separate `F`, so the equation is a syntactic identity
