/-! # Shortest paths on a cylinder, B&dM §7.4 (`AOP/A7_4_Cylinder.lean`), in Rel: no row ported

Every row is stated over the abstract setting of the file: a base BIFUNCTOR `F`, the `n`-tuple relator `N`, two initial
algebras `I`, `J` of its partial applications, and the abstract arrows `moves`, `trans`, `zip`, `setify` carried with
`LaxNatural` hypotheses. Rel has no relator parameter (Obj is closed), no `N`-tuple relator, no `laxNatural_*`
statement, and no closed term for the Egli-Milner `powerRel` (`A5_4`) that (7.11) needs. So the 可写 rows cannot be
stated even at the list instance: `gen`, `Q`, `paths` all contain `N(…)`, `moves`, `trans`, `zip`. -/

-- not ported: cyl_cp (10-appendix.typ:233): `cpMap (F.appl A) I.t = Λ(F(𝟙,∋))` is `rfl`, the definition of `cpMap` at a relator parameter; a syntactic identity
-- not ported: cyl_cp_prod (10-appendix.typ:234): `rfl` on the definition of `cpMap` at `A×−`, with `prodMap`/`relProd` of freyd's Relator structure; a syntactic identity
-- not ported: cyl_cp_const (10-appendix.typ:235): `cpMap (const A) B = Λ(𝟙)` is `rfl`; a syntactic identity
-- not ported: gen_cata_comm (10-appendix.typ:316): `α⦇gen⦈ = F(𝟙,⦇gen⦈) gen` is `relCata_cancel` at `gen`, whose body `F(𝟙,moves trans N(∪)) zip N(cp P(α))` needs the tuple relator `N` and abstract `moves`/`trans`/`zip`; the list-level cancellation law is `foldCancel` (A5_5)
-- not ported: cyl_step (10-appendix.typ:374): equation `Q = [N(wrap),(𝟙×moves trans N(est R)) zip' N(cons)]` between composites that contain `N(…)`, `moves`, `trans`, `zip` over an abstract coproduct `C` and bifunctor `F`; no `N` in Rel
-- not ported: cyl_7_13 (10-appendix.typ:463), cyl_fusion (437), cyl_laws (366): already `rel ✓` in the classification (A7_2's Theorem 7.1 `distributes_of_monotonicAlg`/`greedyLe_den` at the list instance); the `Cylinder` statements need `N`, `LaxNatural` and `powerRel`
