import Rel.Programs.Prelude
import Rel.Lang.Laws.AopA5_6_ListCombinators

/-! # List-combinator laws of freyd `AOP/A5_6_ListCombinators.lean`, in Rel

Each theorem is named after the last component of its freyd declaration, with the declaration and the companion
position (chapter file : line) beside it (`Rel/Lang/Laws/AopA5_6_ListCombinators.lean`). -/

namespace Rel.Programs

open Rel.Programs.prelude in
rel_program aopA5_6_ListCombinators where
    theorem lamProdNiCons(R : α ⟶ β, S : β ⟶ γ) if dom(Λ(R)) = 𝟙 : Λ(R S) = Λ(R)E(S) by Rel.Lang.Tm.lamE_den  -- Freyd.Alg.RelSet.ListRel.Λ_prod_ni_cons (R = 𝟙×∋, S = cons), 05-datatypes.typ:648
    theorem lamNilSingleton : nil Λ(𝟙) = Λ(nil) by Rel.Lang.Tm.lamNilSingletonPre_den  -- Freyd.Alg.RelSet.ListRel.Λ_nil_singleton (nil : 1 ⟶ [α], singletonMap = Λ(𝟙)), 05-datatypes.typ:695
    theorem prodNiUnionDist : ⟨π₁, π₂ ∋⟩ (cons ∪ π₂) = (⟨π₁, π₂ ∋⟩ cons) ∪ (⟨π₁, π₂ ∋⟩ π₂) by Rel.Lang.Tm.compJoin_den  -- Freyd.Alg.RelSet.ListRel.prod_ni_union_dist (𝟙×∋ written ⟨π₁, π₂ ∋⟩), 05-datatypes.typ:647
    theorem prodNiProjSlide : ⟨π₁, π₂ ∋⟩ π₂ = π₂ ∋ by Rel.Lang.Tm.pairOutr_den  -- Freyd.Alg.RelSet.ListRel.prod_ni_proj_slide, 05-datatypes.typ:701
    theorem prodNiUnionSlide : (⟨π₁, π₂ ∋⟩ cons) ∪ (⟨π₁, π₂ ∋⟩ π₂) = (⟨π₁, π₂ ∋⟩ cons) ∪ (π₂ ∋) by Rel.Lang.Tm.joinSlideOutr_den  -- Freyd.Alg.RelSet.ListRel.prod_ni_union_slide, 05-datatypes.typ:656
    theorem lamProjNi : Λ(π₂ ∋) = π₂ Λ(∋) by Rel.Lang.Tm.lamOutr_den  -- Freyd.Alg.RelSet.ListRel.Λ_proj_ni, STRONGER FORM: Λ(∋) = setify is not 𝟙 on an array that is not a set, so the right side keeps Λ(∋), 05-datatypes.typ:657
    theorem lamProdNiProj : Λ(⟨π₁, π₂ ∋⟩ π₂) = π₂ Λ(∋) by Rel.Lang.Tm.lamPairOutr_den  -- Freyd.Alg.RelSet.ListRel.Λ_prod_ni_proj, STRONGER FORM as lamProjNi, 05-datatypes.typ:653
    theorem sumMapJunc(R : α ⟶ β, S : α' ⟶ β', P : β ⟶ γ, Q : β' ⟶ γ) : [R inl, S inr] [P, Q] = [R P, S Q] by Rel.Lang.Tm.sumMapJunc_den  -- Freyd.Alg.RelSet.ListRel.subseq_alg_sum_map and subseq_alg_sum_junc (F(∋) is the sum map 𝟙+(𝟙×∋)), STRONGER FORM: R S P Q any relations, 05-datatypes.typ:675,679
    theorem subseqAlgLam : Λ([𝟙 inl, ⟨π₁, π₂ ∋⟩ inr] [nil, cons ∪ π₂]) = [nil Λ(𝟙), Λ(⟨π₁, π₂ ∋⟩ (cons ∪ π₂))] by Rel.Lang.Tm.subseqAlgLam_den  -- Freyd.Alg.RelSet.ListRel.subseq_alg_Λ (F(∋) = 𝟙+(𝟙×∋), via sumMapJunc), 05-datatypes.typ:660
    theorem subseqAlgLamNil(T : β ⟶ [[α]]) : [Λ(nil), Λ(T)] = [nil Λ(𝟙), Λ(T)] by Rel.Lang.Tm.lamNilJunc_den

-- ported: Λ_nil_singleton (05-datatypes.typ:695), Λ_prod_ni_cons (05:648), prod_ni_union_dist (05:647), prod_ni_proj_slide (05:701), prod_ni_union_slide (05:656), Λ_proj_ni (05:657, stronger), Λ_prod_ni_proj (05:653, stronger), subseq_alg_sum_map (05:679), subseq_alg_sum_junc (05:675), subseq_alg_Λ (05:660), subseq_alg_Λ_nil (05:693)
-- not ported: alphaR_eq_junc (07-optimisation.typ:443): the initial algebra `[nil, cons]` is the fold's own seed pair, a syntactic identity
-- not ported: concat_cata (05-datatypes.typ:568), sum_cata_nat (03-applications.typ:21): the prelude defines `concat`, `sum` as these folds, so the statement is a syntactic identity
-- not ported: list_cata (05-datatypes.typ:542), cplist_cata (05:603), cp_list (05:598), cp_list_alg (05:598): `list(R)` and `cpMap listRelator` are definitions as the very fold `⦇[nil,(R×𝟙)cons]⦈`; `cp` is a relator-indexed family and `cp_list` needs `powerRel`
-- not ported: setify_cpl (05:587), setify_cpp (05:587), setify_cpr (05:588): need `cpl`/`cpp`/`cpr` (not in the prelude) defined as list-level folds and a Cartesian-product-of-lists induction (freyd inlistP_cpp/cpl/cpr); opus-sized proof, the one open item of this unit
-- not ported: setify_ni_iff (08-thinning.typ:421): `↔` of pointwise membership (inlistP), a statement about elements not a relation law
-- not ported: partition_concat (05:563), concat_glue (05:611): `partition`, `glue` are not in the prelude and freyd defines them by `∃` over the split; stating them means defining them as these very folds
-- not ported: segment_eq (07:708): `mss.segment` is defined as `suffix prefix` in Rel/Programs/Mss.lean, so the statement is a syntactic identity
-- not ported: suffix_cat (05:558): `suffix` is defined as `cat° π₂` in the prelude (Prelude.lean:71), a syntactic identity
-- not ported: prefix_cat (05:553, 07:508), prefix_cata (05:552, 07:457): `prefix` is the prelude fold, already stated in Rel/Programs/Prefix.lean (prefixRow / prefixFold)
-- not ported: prefix_cancel (07:481): `α prefix = F(prefix) prefAlg` needs `prefAlg` defined, and it is `foldCancel` (Laws/AopA5_5) at the prefix fold, whose algebra is freyd's alone
-- not ported: prefixP_iff_append (07:489): `∀`/`∃` over elements with `++`, a pointwise iff, not a relation law
-- not ported: length_cata (03:26), pair_sum_length_cata (03:49): prelude length/sum at a generic result object do not elaborate (lessons A9_1), and `length` is a Lean function used as a relation
-- not ported: total_eq (08:628): `graph (total f) = list(graph f) sum` with a Lean function `f : A → Int` as a relation and `sum` at Int; needs `list(R)` defined and a numeric object
-- not ported: listRelator_obj (03:17, 05:537): an equation of objects (`listRelator.obj A = dList A`), no relation
-- not ported: subseq_cata (05:547, 07:909, 08:631): `subseq = ⦇[nil, cons ∪ π₂]⦈ʳ` states the cons fold against the prelude `subseq`, a snoc fold (Prelude.lean:75) read through a call node; needs a Sublist induction on both folds and a call-node den lemma (lessons A6_6b); A7_7_Filter defines `subseqC` as the cons fold
-- not ported: subseq_alg_Λ_junc (05:688): `Λ([R,S]) = [Λ(R), Λ(S)]` is the theorem `lamJunc` of Rel/Programs/Aop/A5_3.lean, cited not restated
-- not ported: subseq_alg_join (05:704), Λ_prod_ni_union (05:725), subseq_alg_transpose (05:737), Λ_subseq (05:634): the right side uses the power-object union `cup` and `powerRel`/`Λ_relCata`, neither has a closed term (lessons A5_4, A7_1est)

end Rel.Programs
