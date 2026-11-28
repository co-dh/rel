/-! # §7.2 `+` distributes over `≤` and the power-relator readings (`AOP/A7_2_RelSet.lean`), in Rel: no row ported

The rows are the `Rel(Set)` model of §7.2: element quantifiers over the sets `pow Nat` and `powerRel`, which has no closed
term (see `A5_4`). The one relation-level row, `plus_distributes_le`, is blocked by wrapping atoms. -/

-- not ported: plus_distributes_le (Freyd.Alg.RelSet.plus_distributes_le, 07-optimisation.typ:307): `(est(≤)×est(≤)) plus ⊑ Λ((∋×∋) plus) est(≤)` needs `min(x+y) = min x + min y`, i.e. `plus` monotone, which fails on the prelude's fixed-width wrapping `plus` (no bounded-range law exists, as for `A8_4` knap_mono_cons)
-- not ported: powerRel_comp_est (Freyd.Alg.RelSet.powerRel_comp_est, 10-appendix.typ:16): `P(S) est(R) = (∋S) ∩ (∈\(S R°))` has `powerRel S` on the left, which has no closed term
-- not ported: existsImage_apply (…, 05-datatypes.typ:278): element quantifier `∃ s, P s ∧ T s w`; `E(T)` itself is ported in `A4_6`
-- not ported: graph_conj_le_iff_monotone (…, 07-optimisation.typ:272): `↔` with an element quantifier (monotone as a pointwise implication)
-- not ported: graph_pres_iff_conj (…, 07-optimisation.typ:264): `↔` between two pointwise statements
-- not ported: powrel_reading_closed (…, 05-datatypes.typ:273): element quantifier over members of sets, about `powerRel`
-- not ported: powrel_reading_reached (…, 05-datatypes.typ:268): element quantifier over members of sets, about `powerRel`
-- not ported: powrel_reading_reaches (…, 05-datatypes.typ:283): element quantifier over members of sets, about `powerRel`
-- not ported: powerRel_reading (…, 05-datatypes.typ:288): element quantifier over members of sets, about `powerRel`
