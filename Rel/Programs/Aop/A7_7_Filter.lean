import Rel.Programs.Prelude
import Rel.Lang.Laws.AopA7_7_Filter

namespace Rel.Programs

open Rel.Programs.prelude in
rel_program aopA7_7_Filter where
    subseqC : [α] ⟶ [α] ≜ ⦇[nil, cons ∪ π₂]⦈ʳ   -- freyd's `subseq` on cons lists (the prelude's `subseq` is the same relation, a snoc fold)
    -- Stronger form of filter_alg_comm / filter_alg: `p` is any relation, not only a coreflexive (`pcons p` is `⟨π₁ p, π₂⟩cons`)
    theorem filterAlgComm(p : α ⟶ α) : subseqC F(p) = nil°nil ∪ (cons°(𝟙×(subseqC F(p)))(⟨π₁ p, π₂⟩cons ∪ π₂)) by Rel.Lang.Tm.filterAlgComm_den  -- Freyd.Alg.RelSet.Filter.filter_alg_comm, 07-optimisation.typ:538
    theorem filterAlg(p : α ⟶ α) : subseqC F(p) = ⦇[nil, ⟨π₁ p, π₂⟩cons ∪ π₂]⦈ʳ by Rel.Lang.Tm.filterAlg_den  -- Freyd.Alg.RelSet.Filter.filter_alg, 07-optimisation.typ:539
    theorem filterMono(p : α ⟶ α, Q : [α] ⟶ [α]) if ⟨π₁, π₂ Q⟩cons ⊑ cons Q : ⟨π₁, π₂ Q⟩(⟨π₁ p, π₂⟩cons ∪ π₂) ⊑ (⟨π₁ p, π₂⟩cons ∪ π₂) Q by Rel.Lang.Tm.filterMono_den  -- Freyd.Alg.RelSet.Filter.filter_mono, 07-optimisation.typ:926
    -- filterMono is the cons arm of `F(R°) S ⊑ S R°` with `R°` any `Q` such that cons commutes past it (stronger form; `Q = R°`, `R = length ≤ length°`, is an instance); the nil arm `nil ⊑ nil Q` is that same premise at `Q`

-- not ported: filter_cata_le (Freyd.Alg.RelSet.Filter.filter_cata_le, 07-optimisation.typ:1000): host types List/Nat/Decidable in the statement
-- not ported: filter_entire (07-optimisation.typ:1014), filter_eq_cata (07-optimisation.typ:880), filter_simple (07-optimisation.typ:1015), filter_step (07-optimisation.typ:955): host types List/Nat/Decidable in the statement, and `filter` needs `R = length ≤ length°` which has no universe at `[α]`
-- not ported: filter_mono_cons (07-optimisation.typ:946), id_le_pi2_lenLE_cons (07-optimisation.typ:919): a Lean function `fun q => q.2` as a relation, and the length preorder `R`

end Rel.Programs
