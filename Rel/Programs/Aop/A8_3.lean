import Rel.Programs.Prelude
import Rel.Lang.Laws.AopA8_3

namespace Rel.Programs

open Rel.Programs.prelude in
rel_program aopA8_3 where
    theorem sortCompMinLLe(C : [α] ⟶ [α], Q : α ⟶ α) if C ⊑ 𝟙 : Λ(∋)° C Λ(∋) est(Q) ⊑ est(Q) by Rel.Lang.Tm.sortCompMinLLe_den
    theorem sortCompThinLLe(X : β ⟶ [α], C : [α] ⟶ [α], S : [α] ⟶ [α], Q : α ⟶ α) if C ⊑ 𝟙, C S ⊑ S C : X Λ(∋)° C ((Λ(∋) ((∋° \ ∋°)° ∩ (∋° \ (Q° ∋°))) Λ(∋)°) ∩ S) ⊑ X ((∋° \ ∋°)° ∩ (∋° \ (Q° ∋°))) Λ(∋)° C by Rel.Lang.Tm.sortCompThinLLe_den

-- Forms: `sort(≼) = Λ(∋)° ordered(≼)` (`setify` is `Λ(∋)`, which sorts and drops repeats on an array). The prelude has no
-- `ordered`, `subseq`, `minL`, `thinL`: the two ported rows state the stronger form, `ordered(≼)` any coreflexive `C`,
-- `subseq` any `S` with `C S ⊑ S C` (freyd's `ordered_comp_subseq_le`), `thin(Q)` inline after `X : β ⟶ [α]` (A8_1).
-- not ported: bumpFold_eq_singleton_minL (08-thinning.typ:477): `∀`/`∃` over elements, no relation equation
-- not ported: bumpRel_wrap, bumpRel_cons (08-thinning.typ:440): `bump(Q)` is defined by `match` on the host list; stating it means defining `bump` as a fold of cases, and these two are its defining equations
-- not ported: le_thinL_iff (08-thinning.typ:446): an `↔` of two conjunctions-- not ported: bumpFold_le_thinL (08-thinning.typ:449): needs `bump(Q)` and `subseq` defined and the covering proof by list induction (`bumpFold_covers`, `subseqP_of_bumpFold`); no list-level fold proof in rel yet
-- not ported: sort_comp_filter_le (08-thinning.typ:485): needs `filter(p)` as the longest passing subsequence (`inlistP_of_longest`) and `ordered`, `subseq` as definitions
-- not ported: sort_comp_list_le (08-thinning.typ:483): `ordered(g≼g°) list(g) ⊑ list(g) ordered(≼)` is a property of `ordered`'s definition; `ordered` is not in the prelude and `powerRel(g)` does not elaborate (A5_4)
-- not ported: merge_top, prodMap_sort_comp_merge_le (08-thinning.typ:858,488): `merge(≼)` is an inductive host relation on pairs of lists, a recursion on two arguments that a plain fold `⦇[e,S]⦈` does not state; `P×P` needs `powerRel`
-- not ported: Fmap_sort_comp_cpL_le (ListRel and Poly), Fmap_sort_comp_cpL_list_filter_le, sortedAlg_fusion, thinningList (08-thinning.typ:490,492,127,608,574): `cpL` over a polynomial relator `F` (relator-indexed family), `Alg F`, `InitialAlgebra`; rel has no relator parameter

end Rel.Programs
