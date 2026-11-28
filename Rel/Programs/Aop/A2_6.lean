/-! # The natural numbers as an initial algebra (`AOP/A2_6.lean`), in Rel: no row ported

`nat_fold_spec` says, for an initial algebra `I` of `F X = 1 + X` in an arbitrary unitary allegory,
`α h = F(h) [c, f] ↔ zero h = c ∧ succ h = h f`. Rel has no initial algebra to quantify over: it has the list fold
`⦇[e,S]⦈` and its universal property `foldUP`, and no `Nat` object with `zero`, `succ` as constructors (the number
objects are fixed-width atoms, A10_3). The row is an `↔` over an arbitrary `h`, with the algebra `I` a parameter. -/

-- not ported: nat_fold_spec (Freyd.Alg.Nat.nat_fold_spec, 02-categories.typ:49): the initial algebra `I` of `1 + X` is a parameter; Rel has no `Nat` object, only the list fold (`foldUP` is its list instance)
-- not ported: nat_fold_spec_step5_zero (Freyd.Alg.Nat.nat_fold_spec_step5_zero, 02-categories.typ:69): a step of `nat_fold_spec`, same blocker (`zero ≫ h = c` read off an equation of `junc` over `I`)
-- not ported: nat_fold_spec_step5_succ (Freyd.Alg.Nat.nat_fold_spec_step5_succ, 02-categories.typ:70): a step of `nat_fold_spec`, same blocker
