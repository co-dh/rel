/-! # `diag/CB_Allegory.lean` in Rel: nothing new to port

`diag/CB_Allegory.lean` derives the allegory laws of an arbitrary cartesian bicategory of relations. The one row marked
可写, `semidistrib_of_lax`, is `R (S ∩ T) ⊑ R S ∩ R T`, which Rel already states as `aopA4_1.compInterLe`
(`Rel/Programs/Aop/A4_1.lean`, `Tm.comp_inter_le_den`), so it is cited, not restated. -/

-- not ported: semidistrib_of_lax (Freyd.Diag.semidistrib_of_lax, 00-laws.typ:253): same statement as `compInterLe` in Rel/Programs/Aop/A4_1.lean (Rel.Lang.Tm.comp_inter_le_den): R (S ∩ T) ⊑ (R S) ∩ (R T)
