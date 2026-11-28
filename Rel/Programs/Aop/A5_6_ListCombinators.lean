import Rel.Programs.Prelude
import Rel.Lang.Laws.AopA5_6_ListCombinators

/-! # List-combinator laws of freyd `AOP/A5_6_ListCombinators.lean`, in Rel

Each theorem is named after the last component of its freyd declaration, with the declaration and the companion
position (chapter file : line) beside it (`Rel/Lang/Laws/AopA5_6_ListCombinators.lean`). -/

namespace Rel.Programs

open Rel.Programs.prelude in
rel_program aopA5_6_ListCombinators where
    theorem lamProdNiCons(R : α ⟶ β, S : β ⟶ γ) if dom(Λ(R)) = 𝟙 : Λ(R S) = Λ(R)E(S) by Rel.Lang.Tm.lamE_den  -- Freyd.Alg.RelSet.ListRel.Λ_prod_ni_cons (R = 𝟙×∋, S = cons), 05-datatypes.typ:648

-- not ported: alphaR_eq_junc (alphaR_eq_junc): the initial algebra `[nil, cons]` of `⦇ ⦈` is the fold's own seed pair, no relation law
-- not ported: concat_cata, sum_cata_nat: the prelude defines `concat`, `sum` as these folds, so the statement is a syntactic identity
-- not ported: list_cata, total_eq, cplist_cata, cp_list, cp_list_alg, setify_cpl, setify_cpp, setify_cpr, partition_concat, concat_glue, segment_eq, prefix_cancel, pair_sum_length_cata: rel has no `list(R)`, `cp*`, `partition`, `glue`, `segment`, `prefAlg`; stating them means defining them as these very folds or compositions (a trivial theorem), and the pointwise freyd definitions take `∃`
-- not ported: Λ_nil_singleton: `nil` is a prelude call whose `den` no generic lemma unfolds; needs `Λ(f) = f τ` for a map `f` plus `nil` a map, not proved here
-- not ported: listRelator_obj: an equation of objects (`listRelator.obj A = dList A`), no relation

end Rel.Programs
