/-! # Strictness of `choose` monotonicity of freyd §7.3 (`AOP/A7_3_ChooseStrict.lean`), in Rel: no row ported

The one row is a NEGATION, `(R×R) choose ≠ choose R`, witnessed by the partial relation `R = {(false,false)}` on `Bool`
in `Rel(Set)`. A `rel_program` theorem states only `⊑` and `=` between relations (with `if` premises): there is no `≠`
or `¬` form, and a concrete relation constant on `Bool` is not a closed term. The inclusion `(R×R) choose ⊑ choose R`
it refines is `choose_monotonic` of `A7_3_Party`; freyd's equality case for entire `R` is not a listed row. -/

-- not ported: choose_monotonic_strict (Freyd.Alg.choose_monotonic_strict, 07-optimisation.typ:1350): `≠` between `(R×R) choose` and `choose R` at the concrete `Rel(Set)` witness on `Bool`; rel_program theorems state only `⊑`/`=`, and a stronger parameter form of a negation (`R` not entire) is not statable either
