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

/-- **`grade` answers a stable sort of `til m`**, `m` the elements it reads: the long it writes at each
position is an index, every index once, each before every later one with a key `keyOrd` puts after it
and before every later tie. So `idesc` is not `iasc` reversed: ties keep index order both ways round. -/
theorem grade_spec (k : Kind) (desc : Bool) (n : USize) (b : ByteArray) :
    (ids (Order.grade k desc n b)).Perm (List.range (min n.toNat (k.avail b))) ∧
      (ids (Order.grade k desc n b)).Pairwise fun i j => keyOrd desc (Order.keyAt k b i) (Order.keyAt k b j) ∧
        (keyOrd desc (Order.keyAt k b j) (Order.keyAt k b i) → i < j) := by
  have hm : min n.toNat (k.avail b) < 2 ^ 64 := Nat.lt_of_le_of_lt (Nat.min_le_left _ _) (usize_lt n)
  have hd : ∀ i j, (if desc then decide (Order.keyAt k b j ≤ Order.keyAt k b i)
      else decide (Order.keyAt k b i ≤ Order.keyAt k b j)) = true ↔
        keyOrd desc (Order.keyAt k b i) (Order.keyAt k b j) := fun i j => by
    cases desc <;> exact decide_eq_true_iff
  have trans : ∀ a c e, (if desc then decide (Order.keyAt k b c ≤ Order.keyAt k b a)
      else decide (Order.keyAt k b a ≤ Order.keyAt k b c)) = true →
      (if desc then decide (Order.keyAt k b e ≤ Order.keyAt k b c)
        else decide (Order.keyAt k b c ≤ Order.keyAt k b e)) = true →
      (if desc then decide (Order.keyAt k b e ≤ Order.keyAt k b a)
        else decide (Order.keyAt k b a ≤ Order.keyAt k b e)) = true := fun a c e h1 h2 => by
    cases desc
    · exact decide_eq_true (UInt64.le_trans (of_decide_eq_true h1) (of_decide_eq_true h2))
    · exact decide_eq_true (UInt64.le_trans (of_decide_eq_true h2) (of_decide_eq_true h1))
  have total : ∀ a c, ((if desc then decide (Order.keyAt k b c ≤ Order.keyAt k b a)
      else decide (Order.keyAt k b a ≤ Order.keyAt k b c)) ||
      (if desc then decide (Order.keyAt k b a ≤ Order.keyAt k b c)
        else decide (Order.keyAt k b c ≤ Order.keyAt k b a))) = true := fun a c => by
    cases desc <;> cases UInt64.le_total (Order.keyAt k b a) (Order.keyAt k b c) with
      | inl h => simp only [h, decide_true, Bool.true_or, Bool.or_true, Bool.false_eq_true, ↓reduceIte]
      | inr h => simp only [h, decide_true, Bool.true_or, Bool.or_true, Bool.false_eq_true, ↓reduceIte]
  obtain ⟨hp, hs⟩ := range_mergeSort trans total (min n.toNat (k.avail b))
  rw [Order.grade, ids_indices _ fun i hi => Nat.lt_trans (List.mem_range.1 (hp.mem_iff.1 hi)) hm]
  exact ⟨hp, hs.imp fun ⟨h1, h2⟩ => ⟨(hd _ _).1 h1, fun h => h2 ((hd _ _).2 h)⟩⟩

/-- **`gradeFoR` answers `grade_spec` over the decoded elements**: a stable sort of all `n` indices by
`foRKey`. -/
theorem gradeFoR_spec (k : Kind) (hk : k ≠ .bit) (desc : Bool) (n : USize) (md pk : ByteArray) :
    (ids (Order.gradeFoR k desc n md pk)).Perm (List.range n.toNat) ∧
      (ids (Order.gradeFoR k desc n md pk)).Pairwise fun i j => keyOrd desc (foRKey k md pk i) (foRKey k md pk j) ∧
        (keyOrd desc (foRKey k md pk j) (foRKey k md pk i) → i < j) := by
  obtain ⟨hav, hkey⟩ := decode_keyAt k hk n md pk
  obtain ⟨hp, hs⟩ := grade_spec k desc n (Coc.decode k.width.toUSize md pk n)
  rw [hav, Nat.min_self] at hp
  have hlt : ∀ {i}, i ∈ ids (Order.gradeFoR k desc n md pk) → i < n.toNat := fun hi => List.mem_range.1 (hp.mem_iff.1 hi)
  exact ⟨hp, hs.imp_of_mem fun hi hj h => by rw [← hkey _ (hlt hi), ← hkey _ (hlt hj)]; exact h⟩

/-- **`gradeLane` answers a stable sort of the ids it reads**, `grade_spec`'s statement with `idAt` at
the lane for the key: every index below `idsCap` once, each before every later one whose id `desc`
puts after it and before every later tie. -/
theorem gradeLane_spec (desc : Bool) (n w : USize) (ids' : ByteArray) :
    (ids (Order.gradeLane desc n w ids')).Perm (List.range (Column.idsCap ids' w.toNat n.toNat)) ∧
      (ids (Order.gradeLane desc n w ids')).Pairwise fun i j =>
        (if desc then Column.idAt ids' w.toNat j ≤ Column.idAt ids' w.toNat i
          else Column.idAt ids' w.toNat i ≤ Column.idAt ids' w.toNat j) ∧
        ((if desc then Column.idAt ids' w.toNat i ≤ Column.idAt ids' w.toNat j
          else Column.idAt ids' w.toNat j ≤ Column.idAt ids' w.toNat i) → i < j) := by
  have hm : Column.idsCap ids' w.toNat n.toNat < 2 ^ 64 := by
    unfold Column.idsCap; split
    · exact usize_lt n
    · exact Nat.lt_of_le_of_lt (Nat.min_le_left _ _) (usize_lt n)
  have trans : ∀ a c e, (if desc then decide (Column.idAt ids' w.toNat c ≤ Column.idAt ids' w.toNat a)
      else decide (Column.idAt ids' w.toNat a ≤ Column.idAt ids' w.toNat c)) = true →
      (if desc then decide (Column.idAt ids' w.toNat e ≤ Column.idAt ids' w.toNat c)
        else decide (Column.idAt ids' w.toNat c ≤ Column.idAt ids' w.toNat e)) = true →
      (if desc then decide (Column.idAt ids' w.toNat e ≤ Column.idAt ids' w.toNat a)
        else decide (Column.idAt ids' w.toNat a ≤ Column.idAt ids' w.toNat e)) = true := fun a c e h1 h2 => by
    cases desc <;> simp only [Bool.false_eq_true, ↓reduceIte, decide_eq_true_eq] at h1 h2 ⊢ <;> omega
  have total : ∀ a c, ((if desc then decide (Column.idAt ids' w.toNat c ≤ Column.idAt ids' w.toNat a)
      else decide (Column.idAt ids' w.toNat a ≤ Column.idAt ids' w.toNat c)) ||
      (if desc then decide (Column.idAt ids' w.toNat a ≤ Column.idAt ids' w.toNat c)
        else decide (Column.idAt ids' w.toNat c ≤ Column.idAt ids' w.toNat a))) = true := fun a c => by
    cases desc <;> simp only [Bool.false_eq_true, ↓reduceIte, Bool.or_eq_true, decide_eq_true_eq] <;> omega
  obtain ⟨hp, hs⟩ := range_mergeSort trans total (Column.idsCap ids' w.toNat n.toNat)
  rw [Order.gradeLane, ids_indices _ fun i hi => Nat.lt_trans (List.mem_range.1 (hp.mem_iff.1 hi)) hm]
  exact ⟨hp, hs.imp fun ⟨h1, h2⟩ => ⟨by cases desc <;> simpa using h1,
    fun h => h2 (by cases desc <;> simpa using h)⟩⟩

end Rel.Verify

/-- info: 'Rel.Verify.gradeLane_spec' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Rel.Verify.gradeLane_spec

#print axioms Rel.Verify.merge_congr
#print axioms Rel.Verify.pairwise_lex_mergeSort
#print axioms Rel.Verify.range_mergeSort
#print axioms Rel.Verify.grade_spec
#print axioms Rel.Verify.gradeFoR_spec
#print axioms Rel.Verify.decode_keyAt
#print axioms Rel.Verify.groupIdsFoR_spec
