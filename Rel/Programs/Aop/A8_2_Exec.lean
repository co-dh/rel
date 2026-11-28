/-! # Executable paths in a layered network, B&dM §8.2d (`AOP/A8_2_Exec.lean`), in Rel: no row ported

The 可写 rows are about freyd's abstract bifunctor `F : BiRelator` and its initial algebra `pathInit`; the 语法缺 rows
are host `List`/`Nat`/`Decidable` statements or a structure parameter `[Class A]`. The executable code
(`minPath`, `cpl`, `pathsExec`, `mcp`) is Lean host code, not a Rel statement. -/


-- not ported: F_obj (Freyd.Alg.Paths.F_obj, 08-thinning.typ:255): an equation of objects `F.obj B X = ⟨B ⊕ B×X⟩`, `rfl`; the base functor is not a Rel term (Obj is closed, no relator parameter)
-- not ported: alphaR_F (Freyd.Alg.Paths.alphaR_F, 08-thinning.typ:257): `alphaR = graph con` at the object `F.obj (dE A) (dCL A A)`; a syntactic identity once `F` is spelled `A + A×X`, and `con` is a host constructor
-- not ported: relCata_F_eps_eq_nelist (Freyd.Alg.Paths.relCata_F_eps_eq_nelist, 08-thinning.typ:273): a fold over `pathInit A`, an initial algebra of the bifunctor `F(PV,-)`, equal to `nelistRelator.map ∋`; needs a relator parameter and `powerRel` (A5_4)
-- not ported: minpath_spec (Freyd.Alg.Paths.minpath_spec, 08-thinning.typ:276): structure parameter `[Paths A]`, Rel has no parameterised structures
-- not ported: thinning_paths (Freyd.Alg.Paths.thinning_paths, 08-thinning.typ:348): structure parameter `[Paths A]`
-- not ported: run_cheapest, run_kept (Freyd.Alg.Paths.run_cheapest, run_kept, 08-thinning.typ:401, 404): host `List`/`Nat`/`Decidable` in the statement

