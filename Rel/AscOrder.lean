import Rel.ObjOrder
import Rel.KernelSpec.Asc

/-! The row `asc`'s meaning (dataframe §3.1's `σ`): the stable sort permutation of a list in `Obj.lt`, and the law that
makes it a function, not a refinement: a permutation sorted stably by a total preorder is unique. -/

namespace Rel
open Rel.Kernel Rel.Verify

/-- **A stable sort is unique**: two orderings of the same indices, each by `le` with ties in index order, are one. -/
theorem stable_unique {le : Nat → Nat → Bool} {l l' : List Nat} (hp : l.Perm l')
    (h : l.Pairwise fun i j => le i j = true ∧ (le j i = true → i < j))
    (h' : l'.Pairwise fun i j => le i j = true ∧ (le j i = true → i < j)) : l = l' :=
  hp.eq_of_pairwise (fun a _ _ _ h1 h2 => absurd (Nat.lt_trans (h1.2 h2.1) (h2.2 h1.1)) (Nat.lt_irrefl a)) h h'

/-- `ascIns`' grade by any total preorder `le`: a permutation of `til m`, ordered by `le` with ties in index order. -/
theorem ascIns_grade {le : Nat → Nat → Bool} (trans : ∀ a b c, le a b = true → le b c = true → le a c = true)
    (total : ∀ a b, (le a b || le b a) = true) (m : Nat) :
    ((List.range m).foldl (fun acc x => ascIns le x acc) []).Perm (List.range m) ∧
      ((List.range m).foldl (fun acc x => ascIns le x acc) []).Pairwise
        fun i j => le i j = true ∧ (le j i = true → i < j) := by
  induction m with
  | zero => exact ⟨by simp, by simp⟩
  | succ m ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    obtain ⟨hp, hs⟩ := ih
    exact ⟨((ascIns_perm _ m _).trans (hp.cons m)).trans (List.perm_append_singleton m (List.range m)).symm,
      ascIns_pairwise trans total m _ (fun y hy => List.mem_range.1 (hp.mem_iff.1 hy)) hs⟩

/-- Position `i` of `xs` no later than `j` by value alone: `j`'s element is not below `i`'s (`Obj.lt`). -/
def ascLe (A : Obj) (xs : List A.El) (i j : Nat) : Bool := !decide (A.lt (xs[j]?.getD A.dflt) (xs[i]?.getD A.dflt))

/-- **The stable sort permutation** of `xs`, dataframe §3.1's `σ = (dom(x) ≫ rank(>ₐ))°`: its positions ordered by
`Obj.lt` of their elements, ties by position; `kasc`'s insertion sort (`ascIns`) run on `ascLe`. -/
def ascL (A : Obj) (xs : List A.El) : List Nat := (List.range xs.length).foldl (fun acc x => ascIns (ascLe A xs) x acc) []

theorem ascLe_total (A : Obj) (xs : List A.El) (i j : Nat) : (ascLe A xs i j || ascLe A xs j i) = true := by
  simp only [ascLe, Bool.or_eq_true, Bool.not_eq_true', decide_eq_false_iff_not]
  by_cases h : A.lt (xs[j]?.getD A.dflt) (xs[i]?.getD A.dflt)
  · exact .inr (Obj.lt_asymm A h)
  · exact .inl h

theorem ascLe_trans (A : Obj) (xs : List A.El) (a b c : Nat) :
    ascLe A xs a b = true → ascLe A xs b c = true → ascLe A xs a c = true := by
  simp only [ascLe, Bool.not_eq_true', decide_eq_false_iff_not]
  intro h1 h2 h3
  rcases Obj.lt_trichotomy A (xs[c]?.getD A.dflt) (xs[b]?.getD A.dflt) with h | h | h
  · exact h2 h
  · exact h1 (by unfold Obj.lt at h3 ⊢; rw [← h]; exact h3)
  · exact h1 (Obj.lt_trans A h h3)

/-- `ascL` is a stable sort of the positions of `xs` by `ascLe`; with `stable_unique`, the only one. -/
theorem ascL_spec (A : Obj) (xs : List A.El) : (ascL A xs).Perm (List.range xs.length) ∧
    (ascL A xs).Pairwise fun i j => ascLe A xs i j = true ∧ (ascLe A xs j i = true → i < j) :=
  ascIns_grade (ascLe_trans A xs) (ascLe_total A xs) xs.length

-- `B A B` (`A < B` as symbols): position 1 first, then the two `B`s in input order
#guard ascL (.atom .sym) ["B", "A", "B"] = [1, 0, 2]

end Rel
