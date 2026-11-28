import Rel.Programs.Prelude
import Rel.Lang.Laws.AopA8_1

/-! # Laws of freyd §8.1 (`AOP/A8_1.lean`), in Rel

Each theorem is named after the last component of its freyd declaration, with the declaration and the companion
position (chapter file : line) beside it. `thin(Q) = (∋/∋) ∩ (∋° \ (Q° ∋°))` (freyd `thinRel Q`, with `∋/∋` written
`(∋° \ ∋°)°`) is not a definition of the program: its `∋°` runs only after a relation that supplies the keys of the
elements, so a body without one is refused (`the converse of ∋ does not run on demand`). Each statement therefore
writes it inline after a relation `X : β ⟶ [α]`, which is the stronger form (`X = 𝟙` is the freyd statement). -/

namespace Rel.Programs

open Rel.Programs.prelude in
rel_program aopA8_1 where
    theorem singletonMapCompEps : τ ∋ = 𝟙 by Rel.Lang.Tm.singleton_comp_eps_den  -- Freyd.Alg.singletonMap_comp_eps, 00-laws.typ:442
    theorem recipCompLamLeRecipEps(T : β ⟶ α) : T° Λ(T) ⊑ ∋° by Rel.Lang.Tm.recip_comp_lam_le_den  -- Freyd.Alg.recip_comp_Λ_le_recip_eps, 00-laws.typ:428
    theorem thinRelCompEpsLe(X : β ⟶ [α], Q : α ⟶ α) : X ((∋° \ ∋°)° ∩ (∋° \ (Q° ∋°))) ∋ ⊑ X ∋ by Rel.Lang.Tm.thin_comp_eps_le_den  -- Freyd.Alg.thinRel_comp_eps_le, 08-thinning.typ:35
    theorem thinRelMono(X : β ⟶ [α], Q : α ⟶ α, R : α ⟶ α) if Q ⊑ R : X ((∋° \ ∋°)° ∩ (∋° \ (Q° ∋°))) ⊑ X ((∋° \ ∋°)° ∩ (∋° \ (R° ∋°))) by Rel.Lang.Tm.thin_mono_den  -- Freyd.Alg.thinRel_mono, 08-thinning.typ:41
    theorem idLeThinRel(X : β ⟶ [α], Q : α ⟶ α) if 𝟙 ⊑ Q : X ⊑ X ((∋° \ ∋°)° ∩ (∋° \ (Q° ∋°))) by Rel.Lang.Tm.refl_le_thin_den  -- Freyd.Alg.id_le_thinRel, 08-thinning.typ:43

-- not ported: le_Λ_comp_thinRel_iff (Freyd.Alg.le_Λ_comp_thinRel_iff, 08-thinning.typ:33): an `↔` of two conjunctions; its halves need Λ(S) thin(Q), whose `∋/∋` is refused without keys of β (S supplies none for `S / ∋`)
-- not ported: recip_thinRel_comp_eps_le (08-thinning.typ:38): `thin(Q)° ∋ ⊑ ∋ Q` starts at the bare `[α]`, which has no universe to run `∋°` on; the form `X thin(Q)° ∋` is not a statement of the row
-- not ported: thinRel_trans (08-thinning.typ:43): two thin(Q) in sequence, the proof needs `recip_eps_comp_thinRel_le` (`∋° thin(Q) ⊑ Q° ∋°`), stated at the bare `∋°`
-- not ported: thinRel_comp_est, _cond1, _cond2 (08-thinning.typ:47,89,112; 09-dynamic.typ:175), est_comp_singletonMap_{cond1,cond2,le_thinRel} (08-thinning.typ:121,122,52), Λ_comp_est_comp_singletonMap_{cond1,cond2,le_thinRel} (08-thinning.typ:123,124,150): need `est` of a non-reflexive R (prelude est(Q) = freyd est(Q ∪ 𝟙)) together with the inline thin; not attempted
-- not ported: thinning, thinning_cond1, thinning_cond2, thinning_fusion, thinning_prefixed, thinning_est (08-thinning.typ:170,175,180,125,126,218): about an abstract relator F, `Alg F`, `InitialAlgebra F`
-- not ported: powerRel_thinRel_comp_bigUnion_{cond1,cond2,le} (08-thinning.typ:231,232,58): `powerRel` does not elaborate (A5_4: needs keys where none are supplied)

end Rel.Programs
