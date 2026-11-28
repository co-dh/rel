/-! # The knapsack program (`AOP/A8_4_KnapsackProgram.lean`), in Rel: no row ported

`run_knap` and `run_kept` are `#eval`-style runs of the thinning knapsack on one host `List (Nat × Nat)` input, with a
host `Nat` capacity: the rows are statements about the output of a host computation, not about a relation. The laws the
program rests on are `Rel/Programs/Aop/A8_4_Knapsack.lean` (`knapMonoDrop`) and `A8_3`/`A8_1` (thinning); a Rel run is
a `check`, which takes no proof term (A10_2). -/

-- not ported: run_knap (Freyd.Alg.RelSet.Knapsack.run_knap, 08-thinning.typ:750): a run on a host `List`/`Nat` input (`List`, `Nat` in the statement); in Rel a run is a `check`, not a theorem, and the value/weight order laws are blocked (A8_4: `sum` over fixed-width atoms has no additive law)
-- not ported: run_kept (Freyd.Alg.RelSet.Knapsack.run_kept, 08-thinning.typ:754): same, the kept items of that run
