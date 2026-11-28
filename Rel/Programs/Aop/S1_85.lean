/-! # Exponentials (`Freyd/S1_85.lean`), in Rel: no row ported

`curry_eq_iff` is the universal property of the exponential `B ^^ A` of a cartesian closed category:
`g = curry f ↔ (A × g) eval = f`. Rel has no exponential object (`Obj` is closed under `×`, `+`, `[ ]`) and the statement
is an `↔` between two equations, not a single relation equation or inclusion. -/

-- not ported: curry_eq_iff (Freyd.curry_eq_iff, 05-datatypes.typ:138): `↔` over the exponential `B ^^ A` with `curry` and `eval`; Rel has no exponential object
