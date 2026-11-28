/-! # The power relator of B&dM §5.4 (`AOP/A5_4.lean`), in Rel: no row ported

`powerRel R = (∋° \ (R ∋°)) ∩ ((∋ R) / ∋)` does not elaborate as a closed term: `rel_program` answers
"internal: a term that needs keys where none are supplied" at `∋°` under `\`, because the divisions are taken over the
whole object universe (`Pre.rdivWhole`) and `∋°` runs only on demand. On arrays (lists, not sets) `P(𝟙)` is also the
same-elements relation, not `𝟙`. -/

-- not ported: powerRel_mono (Freyd.Alg.powerRel_mono, 05-datatypes.typ:339): `powerRel` has no closed Rel term (see above)
-- not ported: powerRel_id (Freyd.Alg.powerRel_id, 05-datatypes.typ:341): no closed term; on arrays `P(𝟙)` is the same-elements relation, `𝟙` only on sets
-- not ported: powerRel_comp (Freyd.Alg.powerRel_comp, 05-datatypes.typ:353): no closed term; freyd's proof needs tabularity (its "hard direction")
