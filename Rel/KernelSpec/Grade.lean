import Rel.KernelSpec.Group
import Rel.Kernel.Sort
import Rel.Kernel.Coc
import Rel.Kernel.Scan
import Rel.Kernel.Value

/-! The part of `Rel.Verify.Grade` the Rel kernels reach; `Rel.Verify.Grade` imports it. -/


namespace Rel.Verify

open Rel Rel.Kernel
open Rel.Kernel.Scan (Kind)
open List.MergeSort.Internal

/-- `merge` reads its comparator only at a pair of one element from each side. -/
theorem merge_congr {s t : Nat → Nat → Bool} :
    ∀ (xs ys : List Nat), (∀ x ∈ xs, ∀ y ∈ ys, s x y = t x y) → List.merge xs ys s = List.merge xs ys t
  | [], ys, _ => by simp only [List.merge]
  | x :: xs, [], _ => by simp only [List.merge]
  | x :: xs, y :: ys, h => by
    rw [List.cons_merge_cons, List.cons_merge_cons, h x (List.mem_cons_self ..) y (List.mem_cons_self ..)]
    cases t x y
    · rw [if_neg Bool.false_ne_true, if_neg Bool.false_ne_true,
        merge_congr (x :: xs) ys fun a ha b hb => h a ha b (List.mem_cons_of_mem _ hb)]
    · rw [if_pos rfl, if_pos rfl, merge_congr xs (y :: ys) fun a ha b hb => h a (List.mem_cons_of_mem _ ha) b hb]
termination_by xs ys => xs.length + ys.length

/-- **Stability.** Sorting indices that start ascending answers them ordered by `le` with ties broken by
index: `zipIdxLE` of each index paired with itself. -/
theorem pairwise_lex_mergeSort {le : Nat → Nat → Bool} (trans : ∀ a b c, le a b → le b c → le a c)
    (total : ∀ a b, le a b || le b a) :
    ∀ l : List Nat, l.Pairwise (· < ·) → (l.mergeSort le).Pairwise fun i j => List.zipIdxLE le (i, i) (j, j)
  | [], _ => by rw [List.mergeSort_nil]; exact List.Pairwise.nil
  | [a], _ => by rw [List.mergeSort_singleton]; exact List.pairwise_singleton _ _
  | a :: b :: xs, h => by
    rw [List.mergeSort]
    have : (splitInTwo ⟨a :: b :: xs, rfl⟩).1.1.length < xs.length + 1 + 1 := by simp [splitInTwo_fst]; omega
    have : (splitInTwo ⟨a :: b :: xs, rfl⟩).2.1.length < xs.length + 1 + 1 := by simp [splitInTwo_snd]; omega
    have hlt := splitInTwo_fst_le_splitInTwo_snd (l := ⟨a :: b :: xs, rfl⟩) h
    rw [merge_congr (t := fun i j => List.zipIdxLE le (i, i) (j, j)) _ _ fun x hx y hy => by
      have hxy := Nat.le_of_lt (hlt x y (List.mem_mergeSort.1 hx) (List.mem_mergeSort.1 hy))
      unfold List.zipIdxLE
      cases e1 : le x y <;> cases e2 : le y x <;> simp only [e1, e2, hxy, decide_true, Bool.false_eq_true, ↓reduceIte]]
    exact List.pairwise_merge (fun x y z => List.zipIdxLE_trans trans (x, x) (y, y) (z, z))
      (fun x y => List.zipIdxLE_total total (x, x) (y, y)) _ _
      (pairwise_lex_mergeSort trans total _ (splitInTwo_fst_pairwise _ h))
      (pairwise_lex_mergeSort trans total _ (splitInTwo_snd_pairwise _ h))
termination_by l => l.length

/-- Sorting `til m` answers a permutation of it in which an index comes before a later one only when `le`
puts it first, and before a tie only when it is the smaller. -/
theorem range_mergeSort {le : Nat → Nat → Bool} (trans : ∀ a b c, le a b → le b c → le a c)
    (total : ∀ a b, le a b || le b a) (m : Nat) :
    ((List.range m).mergeSort le).Perm (List.range m) ∧
      ((List.range m).mergeSort le).Pairwise fun i j => le i j ∧ (le j i → i < j) := by
  have hp := List.mergeSort_perm (List.range m) le
  refine ⟨hp, ((pairwise_lex_mergeSort trans total _ (pairwise_range m)).and
    (hp.nodup_iff.2 ((pairwise_range m).imp Nat.ne_of_lt))).imp fun {i j} ⟨h, hne⟩ => ?_⟩
  unfold List.zipIdxLE at h
  cases hij : le i j <;> cases hji : le j i <;> simp only [hij, hji, Bool.false_eq_true, ↓reduceIte,
    decide_eq_true_eq] at h
  · exact ⟨rfl, fun e => absurd e Bool.false_ne_true⟩
  · exact ⟨rfl, fun _ => Nat.lt_of_le_of_ne h hne⟩

/-- `x` comes no later than `y`: ascending, or descending at `desc`. -/
def keyOrd (desc : Bool) (x y : UInt64) : Prop := if desc then y ≤ x else x ≤ y




end Rel.Verify

#print axioms Rel.Verify.merge_congr
#print axioms Rel.Verify.pairwise_lex_mergeSort
#print axioms Rel.Verify.range_mergeSort
