/-! # Tabulations (`AOP/A4_3.lean`), in Rel: no row ported

`tabulation_incl_iff` is the universal property of a tabulation `(f, g)` of `R` through an object `C`: an inclusion
`k° h ⊑ R` holds iff there is a unique map `m : D ⟶ C` with `m f = h`, `m g = k`. `Tabulates` is a structure over an
arbitrary tabular allegory with an existential over the object `C`; Rel's objects are fixed, so there is no `C` to
quantify over. -/

-- not ported: tabulation_incl_iff (Freyd.Alg.tabulation_incl_iff, 04-relations.typ:25): `k° h ⊑ R ↔ ∃ m : D ⟶ C, Map m ∧ …` quantifies over the object `D` and the map `m` into a tabulation object `C`, and states uniqueness over all maps `m'`; no relation-level statement
