/-! # The paragraph problem of B&dM §8.5 (`AOP/A8_5_Paragraph.lean`), in Rel: no row ported

The unit builds the paragraph problem on a host `Paragraph` structure (a type-class `[Class A]` of word widths, `Nat`
line widths, `List` of words) and states the laws pointwise (`R_apply`, `Q_apply`, `fits_apply`, `ok_apply` are `↔`
over elements; the others quantify over elements). Rel has no parameterised structure or type class, no fixed-length
`Nat` arithmetic with `≤` laws at a type variable (A10_3: no minus, times, max; A9_2: `length ≤` is not statable), and
no `Tour`/`Tree`-like host datatype (A8_6, A9_3). `R_eq`, `Q_eq` are the definitions of `R`, `Q` read back, a syntactic
identity in Rel (A6_ConsList, A8_6). -/

-- not ported: R_eq (Freyd.Alg.RelSet.Paragraph.R_eq, 08-thinning.typ:810): `[Class A]` structure parameter; and `R` is defined by this equation, so it is a syntactic identity in Rel
-- not ported: Q_eq (Freyd.Alg.RelSet.Paragraph.Q_eq, 08-thinning.typ:813): `[Class A]` structure parameter; a syntactic identity (the definition of `Q`)
-- not ported: fits_apply (Freyd.Alg.RelSet.Paragraph.fits_apply, 08-thinning.typ:836): an `↔` over elements of a host `List`/`Nat` width test
-- not ported: ok_apply (Freyd.Alg.RelSet.Paragraph.ok_apply, 08-thinning.typ:837): an `↔` over elements, same
-- not ported: R_apply (Freyd.Alg.RelSet.Paragraph.R_apply, 08-thinning.typ:838): an `↔` over elements, same
-- not ported: Q_apply (Freyd.Alg.RelSet.Paragraph.Q_apply, 08-thinning.typ:839): an `↔` over elements, same
-- not ported: para_mono_glue (Freyd.Alg.RelSet.Paragraph.para_mono_glue, 08-thinning.typ:852): `∀` over elements of a host line-length order; the width order has no law at a type variable (A8_4, A10_3)
-- not ported: para_mono_new (Freyd.Alg.RelSet.Paragraph.para_mono_new, 08-thinning.typ:852): host `List`/`Nat`, same
-- not ported: para_sort_glue (Freyd.Alg.RelSet.Paragraph.para_sort_glue, 08-thinning.typ:861): host `List`/`Nat`, same
-- not ported: para_sort_new (Freyd.Alg.RelSet.Paragraph.para_sort_new, 08-thinning.typ:861): host `List`/`Nat`, same
-- not ported: para_laws (Freyd.Alg.RelSet.Paragraph.para_laws, 08-thinning.typ:873): `∀` over elements; conjunction of the four above
-- not ported: para_alg_fusion (Freyd.Alg.RelSet.Paragraph.para_alg_fusion, 08-thinning.typ:889): `∀` over elements of the paragraph algebra
-- not ported: para_laws_split (Freyd.Alg.RelSet.Paragraph.para_laws_split, 08-thinning.typ:892): host `List`/`Nat`
-- not ported: para_spec (Freyd.Alg.RelSet.Paragraph.para_spec, 08-thinning.typ:896): `∀` over elements of the specification
-- not ported: para_body_split (Freyd.Alg.RelSet.Paragraph.para_body_split, 08-thinning.typ:914): `∀` over elements of the fold body
-- not ported: run_paragraph (Freyd.Alg.RelSet.Paragraph.run_paragraph, 08-thinning.typ:928): a run on a host `List`/`Nat` input; a Rel run is a `check`
-- not ported: run_kept (Freyd.Alg.RelSet.Paragraph.run_kept, 08-thinning.typ:932): a run on a host `List`/`Nat` input, same
