/-! # The power relator of B&dM §5.4 (`AOP/A5_4_PowerRel.lean`), in Rel: no row ported

`powerRel R = (∋° \ (R ∋°)) ∩ ((∋ R) / ∋)` does not elaborate as a closed term (see `Rel/Programs/Aop/A5_4.lean`:
"a term that needs keys where none are supplied" at `∋°` under `\`), so the one theorem `powerRel_map` has no statement.
Its right side `existsImage f = E(f)` is already ported (`A4_6`), and the left side is what is missing. -/

-- not ported: powerRel_map (Freyd.Alg.powerRel_map, 05-datatypes.typ:346): `P(f) = E(f)` for a map `f`; `P(f)` has no closed Rel term
-- not ported: powerRel_map (Freyd.Alg.powerRel_map, 07-optimisation.typ:727): the same declaration cited again; `P(f)` has no closed Rel term
