/-! # The cylinder beads on `Vec` of freyd §7.4 (`AOP/A7_4_CylinderVec.lean`), in Rel: no row ported

freyd's `Vec n : X ↦ (Fin n → X)` is a host functor on `Type`, and `moves`, `trans`, `concat`, `zip`, `cp`, `gen`,
`genFold` are Lean functions on it indexed by `n`, `m`, `3^m`. Rel has no fixed-length tuple object, so there is no
relation to state laws about; the one row that is an equation is `rfl` on those functions. -/

-- not ported: cons_genFold (Freyd.Alg.Vec.cons_genFold, 07-optimisation.typ:1543): an equation of the host functions `cons ≫ genFold (m+1)` and `Prod.map id (genFold m) ≫ gen` on `Fin n → X`, proved by `rfl` (definitional unfolding of `genFold`); no `Vec` object in Rel
-- not ported: gen_run (Freyd.Alg.Vec.gen_run, 07-optimisation.typ:1540): `#eval`-style check of the Lean function `gen` on host `Fin`-indexed data (graph of a function)
-- not ported: genFold_run (Freyd.Alg.Vec.genFold_run, 07-optimisation.typ:1568): `#eval`-style check of the Lean function `genFold` on host `Fin`-indexed data (graph of a function)
