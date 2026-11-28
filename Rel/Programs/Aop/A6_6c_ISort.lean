import Rel.Programs.Prelude
import Rel.Lang.Laws.AopA6_6c_ISort

namespace Rel.Programs

open Rel.Programs.prelude in
rel_program aopA6_6c_ISort where
    add : [α]×α ⟶ [α] ≜ (cat°×𝟙)⟨⟨π₁π₁,π₂⟩snoc,π₁π₂⟩cat
    -- Stronger form of Freyd.Alg.RelSet.ISort.insertion_sort (06-recursive.typ:455): the sorted-ness relation `ordered R` is
    -- any `O : [α] ⟶ [α]` (`ordered(Q)` is an instance); freyd proves `nil ⊑ nil ordered R` (`wrap_ordered`), here it is a premise.
    theorem insertionSort(ins : [α]×α ⟶ [α], O : [α] ⟶ [α]) if nil ⊑ nil O, (O×𝟙) ins ⊑ add O : ⦇[nil, ins]⦈ ⊑ perm O by Rel.Lang.Tm.insertionSort_den

-- not ported: Freyd.Alg.RelSet.ISort.insert_add (06-recursive.typ:466): about the concrete `insert` of the file (a fold-defined `insertR` on a connected transitive preorder) and the prelude `ordered(Q)`, a call node with no `_den` lemma; needs list-level proofs of `insert` and of `ordered`

end Rel.Programs
