/-! # The cylinder on `Vec` as relations of freyd §7.4 (`AOP/A7_4_CylinderVecRel.lean`), in Rel: no row ported

Every bead is the `graph` of a `Vec` function (`A7_4_CylinderVec`) and every law is stated over the tuple relator
`tupleP n`, so the rows need the fixed-length tuple object `Vec n A = dTuple n A` and a relator parameter, neither of
which Rel has (its objects are closed and its lists are arrays of unfixed length). `est_eq` (`est S = ∋ ∩ (∋° \ S°)`
at `dTuple k A`) is, at lists, the definition of `est` in the prelude up to `Q ∪ 𝟙` (bridge `Tm.estPairTest_den`, `Laws/AopA7_1`). -/

-- not ported: Q_run (Freyd.Alg.Vec.Rel.Q_run, 07-optimisation.typ:1607): the greedy algebra `Q` is a Lean function used as a relation (graph) on `Vec`
-- not ported: Qfold_le_genFold (Freyd.Alg.Vec.Rel.Qfold_le_genFold, 07-optimisation.typ:1634): `⦇Q⦈ ⊑ ⦇gen⦈ est` over the tuple object `Vec (m+1) (Vec n A)` and the relator `tupleP`; no `Vec` object
-- not ported: cyl_7_13 (Freyd.Alg.Vec.Rel.cyl_7_13, 07-optimisation.typ:1653): the cons/gen square (7.13) over `Vec` and `tupleP`; no `Vec` object
-- not ported: cyl_fusion (Freyd.Alg.Vec.Rel.cyl_fusion, 07-optimisation.typ:1644): fusion of `⦇Q⦈` with `paths` over `Vec` and `tupleP`; no `Vec` object
-- not ported: cyl_laws (Freyd.Alg.Vec.Rel.cyl_laws, 07-optimisation.typ:1610): the three laws of the cylinder derivation over `Vec` and `tupleP`; no `Vec` object
-- not ported: est_concat (Freyd.Alg.Vec.Rel.est_concat, 07-optimisation.typ:1628): `est` commuting with `concat` over `Vec (j*p)` and `tupleP`; no `Vec` object
-- not ported: est_eq (Freyd.Alg.Vec.Rel.est_eq, 07-optimisation.typ:1466): `est S = ∋ ∩ (∋° \ S°)` at the tuple object `dTuple k A`; Rel has no fixed-length tuple object, and at `[α]` the same law is the prelude `est` bridge (`Tm.estPairTest_den`, A7_1)
-- not ported: run_cyl (Freyd.Alg.Vec.Rel.run_cyl, 07-optimisation.typ:1670): `#eval`-style check on host `List`/`Nat` data, no relation statement
-- not ported: run_input (Freyd.Alg.Vec.Rel.run_input, 07-optimisation.typ:1663): `#eval`-style check on host `List`/`Nat` data, no relation statement
-- not ported: run_kept (Freyd.Alg.Vec.Rel.run_kept, 07-optimisation.typ:1666): `#eval`-style check on host `List`/`Nat` data, no relation statement
