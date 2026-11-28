import Rel.Programs.Prelude
import Rel.Lang.Laws.AopA6_6b_SortConcrete

/-! # Selection sort, fully concrete (freyd `AOP/A6_6b_SortConcrete.lean`, B&dM §6.6)

The prelude folds over `snoc`, so freyd's `ok cons` is `K snoc` with `K : [α]×α ⟶ [α]×α` (the book's `ok`, "the element
is below every element of the array"), and `perm` is a parameter `P` with the two facts the proof reads of it: `K` commutes
with `P×𝟙` (Ex 6.22) and `snoc P = (P×𝟙) snoc P` (the snoc branch of `perm`'s fold). This is the stronger form of the rows,
`P = perm`, `K = ok` an instance, and `select` any `S : [α] ⟶ [α]×α`. The seed is any `e : 1 ⟶ [α]`, `nil` an instance. -/

namespace Rel.Programs

open Rel.Programs.prelude in
rel_program aopA6_6b_SortConcrete where
    theorem selectProviso(P : [α] ⟶ [α], K : [α]×α ⟶ [α]×α, S : [α] ⟶ [α]×α) if K (P×𝟙) = (P×𝟙) K, snoc P = ((P×𝟙) snoc) P, S° ⊑ (K snoc) P : (P×𝟙) S° ⊑ (K snoc) P by Rel.Lang.Tm.selectProviso_den  -- Freyd.Alg.RelSet.Sort.select_proviso, 06-recursive.typ:317
    theorem selectionSort(P : [α] ⟶ [α], O : [α] ⟶ [α], K : [α]×α ⟶ [α]×α, S : [α] ⟶ [α]×α, e : 1 ⟶ [α]) if P° = P, O ⊑ 𝟙, O = ⦇[e, K snoc]⦈, K (P×𝟙) = (P×𝟙) K, snoc P = ((P×𝟙) snoc) P, e ⊑ e P, S° ⊑ (K snoc) P : ⦇[e, S°]⦈° ⊑ P O by Rel.Lang.Tm.selectionSort_den  -- Freyd.Alg.RelSet.Sort.selection_sort, 06-recursive.typ:308
    theorem sortRec(S : [α] ⟶ [α]×α, e : 1 ⟶ [α]) : ⦇[e, S°]⦈° = e° nil ∪ ((S (⦇[e, S°]⦈°×𝟙)) snoc) by Rel.Lang.Tm.sortRec_den  -- Freyd.Alg.RelSet.Sort.sort_rec, 06-recursive.typ:330

-- not ported: ordered_cata (Freyd.Alg.RelSet.Sort.ordered_cata, 06-recursive.typ:295): `ordered(Q)` at a relation variable `Q` elaborates (a `Tm.arg (Tm.call …) Q` node, checked), but rel has no `Tm.orderedDef_den`: it needs the pointwise meaning of the body `𝟙 − dom(tails ∋ ⟨at(0),tail⟩(π₁∼Q ∩ (π₂∋)))` (tails, `at(0)` literal with its cast, `∼`) and the book's `ok Q` needs `Q/∋` at a variable (`a term that needs keys`, as in A6_6e check'); a proof-sized unit for an opus agent. selectionSort takes `O = ⦇[e, K snoc]⦈` as a premise instead

end Rel.Programs
