/-! # Tree/tip datatype of B&dM §6 (`AOP/A6_TreeTip.lean`), in Rel: no row ported

The unit folds over the host inductive `Tree A` (`tip a | bin t t`); Rel has no recursive datatype other than the array
`[α]`, so `cataTreeFold` and every equation about it have no term. -/

-- not ported: cataTreeFold_tip (Freyd.Alg.RelSet.TT.cataTreeFold_tip, 03-applications.typ:170): `cataTreeFold f (tip a) r = f (inl a) r` is a computation rule of the host `Tree` fold; no `Tree A` object
-- not ported: cataTreeFold_bin (…TT.cataTreeFold_bin, 03-applications.typ:171): element quantifier over the subtrees' values, and the same missing `Tree A`
