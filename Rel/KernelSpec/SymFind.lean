import Rel.KernelSpec.FindMember
import Rel.KernelSpec.Encoding
import Rel.KernelSpec.Group
import Rel.Kernel.Sort
import Rel.KernelSpec.Codes
import Rel.Kernel.Value
import Rel.Kernel.Search
import Rel.KernelSpec.Assign
import Rel.Kernel.Need
import Rel.Kernel.Structural

/-! The part of `Rel.Verify.SymFind` the Rel kernels reach; `Rel.Verify.SymFind` imports it. -/


namespace Rel.Verify
open Rel Rel.Kernel
theorem bget (x : ByteArray) (i : Nat) : x[i]? = x.data.toList[i]? := by
  rw [Array.getElem?_toList]
  by_cases h : i < x.size
  · rw [getElem?_pos x i h, getElem?_pos x.data i h]; rfl
  · rw [getElem?_neg x i h, getElem?_neg x.data i h]

theorem extract_toList (b : ByteArray) (s e : Nat) :
    (b.extract s e).data.toList = (b.data.toList.drop s).take (e - s) :=
  copySlice_end b ByteArray.empty s (e - s)

theorem getElem_idxOf' {α : Type} [BEq α] [LawfulBEq α] (l : List α) (k : α) (h : l.idxOf k < l.length) :
    l[l.idxOf k] = k := by
  induction l with
  | nil => exact absurd h (Nat.not_lt_zero _)
  | cons a l ih =>
    -- split on `==`, not `=`: `α` has no `DecidableEq`, and `by_cases` on `a = k` would be classical
    cases hb : a == k
    · simp only [List.idxOf_cons, hb, cond_false, List.length_cons] at h ⊢
      exact ih (by omega)
    · simp only [List.idxOf_cons, hb, cond_true, List.getElem_cons_zero]; exact eq_of_beq hb

/-- Array `==` is equality, through `isEqv` because core's `Array.instLawfulBEq` is classical. -/
theorem arr_beq_iff (a b : Array UInt8) : (a == b) = true ↔ a = b := by
  show a.isEqv b (· == ·) = true ↔ _
  rw [Array.isEqv_iff_rel]
  constructor
  · rintro ⟨hs, h⟩; exact Array.ext hs fun i h1 _ => eq_of_beq (h i h1)
  -- not `beq_self_eq_true`: its `ReflBEq UInt8` is found through `UInt8.instLawfulEqOrd`, which is classical
  · rintro rfl; exact ⟨rfl, fun i _ => decide_eq_true rfl⟩

/-- **The values at the first occurrences, in order, are the list with its repeats erased.** -/
theorem firstsOf_eraseDups {α : Type} [DecidableEq α] [BEq α] [LawfulBEq α] (g : Nat → α) (m : Nat) :
    (firstsOf g m).map g = ((List.range m).map g).eraseDups := by
  induction m with
  | zero => rfl
  | succ m ih =>
    have hs : firstsOf g (m + 1) = firstsOf g m ++
        [m].filter (fun i => (List.range i).all fun j => !decide (g j = g i)) := by
      simp only [firstsOf, List.range_succ, List.filter_append]
    rw [hs, List.map_append, ih, List.range_succ, List.map_append, List.eraseDups_append]
    congr 1
    by_cases hm : g m ∈ (List.range m).map g
    · obtain ⟨j, hj, e⟩ := List.mem_map.1 hm
      have hp : ((List.range m).all fun j => !decide (g j = g m)) = false := by
        cases hc : (List.range m).all fun j => !decide (g j = g m)
        · rfl
        · have := (List.all_eq_true.1 hc) j hj; simp [e] at this
      simp only [List.filter_cons, hp, Bool.false_eq_true, if_false, List.filter_nil, List.map_cons, List.map_nil, List.removeAll,
        List.elem_eq_mem, hm, decide_true, Bool.not_true]
      rfl
    · have hp : ((List.range m).all fun j => !decide (g j = g m)) = true :=
        List.all_eq_true.2 fun j hj => by simp only [Bool.not_eq_true', decide_eq_false_iff_not]; exact fun e => hm (List.mem_map.2 ⟨j, hj, e⟩)
      simp only [List.filter_cons, hp, if_true, List.filter_nil, List.map_cons, List.map_nil, List.removeAll,
        List.elem_eq_mem, hm, decide_false, Bool.not_false]
      rfl

theorem list_rev_ind {motive : List Nat → Prop} (nil : motive []) (append_singleton : ∀ l i, motive l → motive (l ++ [i]))
    (l : List Nat) : motive l := by
  rw [← List.reverse_reverse l]
  induction l.reverse with
  | nil => exact nil
  | cons a r ih => rw [List.reverse_cons]; exact append_singleton _ _ ih

theorem append_push_toList (a k : ByteArray) :
    ((a ++ k).push 0).data.toList = a.data.toList ++ (k.data.toList ++ [0]) := by
  show ((a ++ k).data.push 0).toList = _
  rw [Array.toList_push, ByteArray.data_append, Array.toList_append, List.append_assoc]

/-- **An id below the dictionary's count reads back from `packIds` at that count's width.** -/
theorem idAt_packIds_idWidthOf {nd n i : Nat} {f : Nat → Nat} (hnd : nd ≤ 2 ^ 64) (hi : i < n) (hf : f i < nd) :
    Column.idAt (Column.packIds (Column.idWidthOf nd) n f) (Column.idWidthOf nd) i = f i :=
  idAt_packIds (laneWidth_cases _) hi (lt_idWidthOf hf hnd)

/-- Every value of `g` below `m` is its value at a first occurrence. -/
theorem mem_firstsOf {α : Type} [DecidableEq α] (g : Nat → α) {m i : Nat} (hi : i < m) :
    g i ∈ (firstsOf g m).map g := by
  induction i using Nat.strongRecOn with
  | _ i ih =>
    cases hc : (List.range i).all fun j => !decide (g j = g i)
    -- not `List.all_eq_false`, which is classical
    · have ex : ∀ l : List Nat, (l.all fun j => !decide (g j = g i)) = false → ∃ j ∈ l, g j = g i := by
        intro l
        induction l with
        | nil => intro h; cases h
        | cons a l ih =>
          intro h
          by_cases ea : g a = g i
          · exact ⟨a, List.mem_cons_self .., ea⟩
          · simp only [List.all_cons, ea, decide_false, Bool.not_false, Bool.true_and] at h
            obtain ⟨j, hj, e⟩ := ih h
            exact ⟨j, List.mem_cons_of_mem _ hj, e⟩
      obtain ⟨j, hj, e⟩ := ex _ hc
      rw [← e]; exact ih j (List.mem_range.1 hj) (by have := List.mem_range.1 hj; omega)
    · exact List.mem_map.2 ⟨i, List.mem_filter.2 ⟨List.mem_range.2 hi, hc⟩, rfl⟩

/-- A member's first index is inside the list; not `List.idxOf_lt_length_of_mem`, which is classical at
`List UInt8`. -/
theorem idxOf_lt_of_mem {α : Type} [BEq α] [LawfulBEq α] {l : List α} {k : α} (h : k ∈ l) :
    l.idxOf k < l.length := by
  induction l with
  | nil => cases h
  | cons a l ih =>
    cases hb : a == k
    · simp only [List.idxOf_cons, hb, cond_false, List.length_cons]
      have hl : k ∈ l := by
        cases h with
        | head => exact absurd (beq_iff_eq.2 rfl) (by rw [hb]; decide)
        | tail _ h => exact h
      exact Nat.succ_lt_succ (ih hl)
    · simp only [List.idxOf_cons, hb, cond_true, List.length_cons]; exact Nat.succ_pos _

/-- info: 'Rel.Verify.idAt_packIds_idWidthOf' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms idAt_packIds_idWidthOf

end Rel.Verify


namespace Rel.Verify
open Rel Rel.Kernel

theorem toUSize_toNat {n : Nat} (h : n < USize.size) : n.toUSize.toNat = n := USize.toNat_ofNat_of_lt' h

/-- Through a distinct dictionary `(range d).map f`, the first element whose entry is `k` is the first
whose id is `k`'s index in the dictionary. -/
theorem map_range_inj {α : Type} {f : Nat → α} {d : Nat} (hD : ((List.range d).map f).Nodup) {i j : Nat}
    (hi : i < d) (hj : j < d) (e : f i = f j) : i = j := by
  have hp := List.pairwise_iff_getElem.1 hD
  rcases Nat.lt_trichotomy i j with h | h | h
  · exact (hp i j (by simpa) (by simpa) h (by simp only [List.getElem_map, List.getElem_range]; exact e)).elim
  · exact h
  · exact (hp j i (by simpa) (by simpa) h (by simp only [List.getElem_map, List.getElem_range]; exact e.symm)).elim

/-- Eight bytes a value, pushed onto an empty array and read back. -/
theorem bitsAt_foldl8 (m : Nat) (g : Nat → UInt64) (a : ByteArray) (ha : a.size = 0) :
    ((List.range m).foldl (fun acc j => Column.pushBits acc (g j) 8) a).size = 8 * m ∧
    ∀ j < m, (Column.bitsAt ((List.range m).foldl (fun acc j => Column.pushBits acc (g j) 8) a) (j * 8) 8).toNat =
      (g j).toNat := by
  obtain ⟨hs, -, hb⟩ := foldl_pushBits g 8 (by decide) (List.range m) a
  refine ⟨by simpa [ha] using hs, fun j hj => ?_⟩
  have := hb j (by simpa using hj)
  simp only [ha, Nat.zero_add, List.getElem_range] at this
  rw [Nat.mul_comm, this, UInt64.toNat_ofNat', Nat.mod_mod, Nat.mod_eq_of_lt (UInt64.toNat_lt _)]


end Rel.Verify
