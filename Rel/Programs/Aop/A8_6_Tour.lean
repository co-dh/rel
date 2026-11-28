/-! # Bitonic tours of B&dM §8.6 (`AOP/A8_6_Tour.lean`), in Rel: no row ported

Every row is about the host datatype `Tour City = Journey × Journey`, a pair of cons-lists of length at least two
(`ConsList (City × City) City`), with `head`, `next`, `tail`, `replaceHead`, `dropl`, `dropr` as host functions and
`tc : City × City → Int` as a class field. Rel has no recursive datatype and no `Journey`, and the prelude has no
`Int` minus or times (so `cost`/`cost_dropl` arithmetic cannot be stated). The two identities `R_eq` and `Q_eq` are
the definitions of `R` and `Q` there, so they are syntactic identities in Rel, not laws. -/

-- not ported: Q_apply (Freyd.Alg.RelSet.Tour.Q_apply, 08-thinning.typ:1038): pointwise ↔ restatement of the host `Q`, no relation statement
-- not ported: Q_eq (Freyd.Alg.RelSet.Tour.Q_eq, 08-thinning.typ:1010): `Q ≜ R ∩ (next₂ next₂°) ∩ (head₂ head₂°)` is the definition of `Q` once stated over relations (syntactic identity); `next`/`head` need the host `Journey`
-- not ported: R_apply (Freyd.Alg.RelSet.Tour.R_apply, 08-thinning.typ:1034): pointwise ↔ restatement of the host `R`, no relation statement
-- not ported: R_eq (Freyd.Alg.RelSet.Tour.R_eq, 08-thinning.typ:1001): `R ≜ cost ≤ cost°` is the definition of `R` (syntactic identity); `cost` is `outcost`/`incost` folds over the host `Journey` with `Int` addition
-- not ported: replaceHead_eq (Freyd.Alg.RelSet.Tour.replaceHead_eq, 08-thinning.typ:971): `graph` of a host function on `Journey`/`NEList`; no such objects in Rel
-- not ported: run_kept (Freyd.Alg.RelSet.Tour.run_kept, 08-thinning.typ:1100): host `List`/`Int` evaluation by `rfl`, no relation statement
-- not ported: run_tour (Freyd.Alg.RelSet.Tour.run_tour, 08-thinning.typ:1097): host `List`/`Int` evaluation by `rfl`, no relation statement
-- not ported: tour_laws (Freyd.Alg.RelSet.Tour.tour_laws, 08-thinning.typ:1067): Theorem 8.2 at `[start,dropl]`, `[start,dropr]` needs `Journey`, `cpL`, `minL`, `merge`, `thinL Q` over `Tour` (A8_3 found `cpL`/`merge` absent from the prelude) and the monotonicity rows below
-- not ported: tour_laws_defn (Freyd.Alg.RelSet.Tour.tour_laws_defn, 08-thinning.typ:1077): `rfl` unfolding of `tour` over the host `Tour` algebra `[start,dropl ∪ dropr]`; no `Journey` to fold over
-- not ported: tour_mono_dropl (Freyd.Alg.RelSet.Tour.tour_mono_dropl, 08-thinning.typ:1050): `dropl` and `cost_dropl` (`cost + tc(a,next x) − tc(head x,next x) + tc(head y,a)`) need the host `Journey` and `Int` subtraction
-- not ported: tour_mono_dropr (Freyd.Alg.RelSet.Tour.tour_mono_dropr, 08-thinning.typ:1050): same as `tour_mono_dropl` for `dropr`
-- not ported: tour_sort_dropl (Freyd.Alg.RelSet.Tour.tour_sort_dropl, 08-thinning.typ:1057): `Pres (graph droplAlgFn) ⊤` over the host `Tour` algebra; no `Journey`
-- not ported: tour_sort_dropr (Freyd.Alg.RelSet.Tour.tour_sort_dropr, 08-thinning.typ:1057): same as `tour_sort_dropl` for `dropr`
