import Rel.KernelSpec.Encoding
import Rel.Kernel.Sort
import Rel.Kernel.Coc
import Rel.Kernel.Scan
import Rel.Kernel.Value
import Rel.KernelSpec.Raw
import Rel.Kernel.Elementwise

/-! The part of `Rel.Verify.Group` the Rel kernels reach; `Rel.Verify.Group` imports it. -/


namespace Rel.Verify

open Rel Rel.Kernel
open Rel.Kernel.Scan (Kind)

section Firsts

variable {α : Type} [DecidableEq α] (g : Nat → α) (m : Nat)

/-- The indices below `m` where `g` takes a value for the first time, ascending. -/
def firstsOf : List Nat := (List.range m).filter fun i => (List.range i).all fun j => !decide (g j = g i)

/-- The indices below `m` where `g` takes `g f`, ascending. -/
def bucketOf (f : Nat) : List Nat := (List.range m).filter fun i => decide (g i = g f)

/-- The group of index `i`: the position in `firstsOf` of the first index holding `g i`. -/
def groupOf (i : Nat) : Nat := (firstsOf g m).findIdx fun f => decide (g f = g i)

-- core's `List.all_eq_false` and `List.pairwise_lt_range` carry `Classical.choice`; these two do not.
omit [DecidableEq α] in
theorem exists_of_all_false {l : List Nat} {p : Nat → Bool} (h : l.all p = false) : ∃ j ∈ l, p j = false := by
  induction l with
  | nil => cases h
  | cons a l ih =>
    cases ha : p a
    · exact ⟨a, List.mem_cons.2 (Or.inl rfl), ha⟩
    · rw [List.all_cons, ha, Bool.true_and] at h
      obtain ⟨j, hj, e⟩ := ih h
      exact ⟨j, List.mem_cons.2 (Or.inr hj), e⟩

omit [DecidableEq α] in
theorem pairwise_range (n : Nat) : (List.range n).Pairwise (· < ·) := by
  induction n with
  | zero => exact List.Pairwise.nil
  | succ n ih =>
    rw [List.range_succ, List.pairwise_append]
    exact ⟨ih, List.pairwise_singleton _ _, fun a ha b hb => by
      rw [List.mem_singleton.1 hb]; exact List.mem_range.1 ha⟩

variable {g m} in
theorem exists_first {i : Nat} (hi : i < m) : ∃ f ∈ firstsOf g m, g f = g i := by
  induction i using Nat.strongRecOn with
  | _ i ih =>
    cases hb : (List.range i).all fun j => !decide (g j = g i) with
    | true => exact ⟨i, List.mem_filter.2 ⟨List.mem_range.2 hi, hb⟩, rfl⟩
    | false =>
      obtain ⟨j, hj, e⟩ := exists_of_all_false hb
      have hj := List.mem_range.1 hj
      obtain ⟨f, hf, e'⟩ := ih j hj (by omega)
      refine ⟨f, hf, e'.trans ?_⟩
      cases hd : decide (g j = g i)
      · rw [hd] at e; cases e
      · exact of_decide_eq_true hd

/-- No value twice: a first occurrence differs from every earlier one. -/
theorem nodup_firsts : ((firstsOf g m).map g).Nodup := by
  refine List.pairwise_map.2 (((pairwise_range m).filter _).imp_of_mem fun {i j} _ hj hij e => ?_)
  have := List.all_eq_true.1 (List.mem_filter.1 hj).2 i (List.mem_range.2 hij)
  rw [decide_eq_true e] at this
  exact Bool.false_ne_true this

theorem firsts_lt {f : Nat} (hf : f ∈ firstsOf g m) : f < m := List.mem_range.1 (List.mem_filter.1 hf).1

variable {g m} in
theorem groupOf_lt {i : Nat} (hi : i < m) : groupOf g m i < (firstsOf g m).length :=
  let ⟨f, hf, e⟩ := exists_first hi
  List.findIdx_lt_length_of_exists ⟨f, hf, decide_eq_true e⟩

variable {g m} in
theorem groupOf_get {i : Nat} (hi : i < m) : g ((firstsOf g m)[groupOf g m i]'(groupOf_lt hi)) = g i :=
  of_decide_eq_true (List.findIdx_getElem (w := groupOf_lt hi))

variable {g m} in
theorem firsts_inj {j j' : Nat} (hj : j < (firstsOf g m).length) (hj' : j' < (firstsOf g m).length)
    (e : g (firstsOf g m)[j] = g (firstsOf g m)[j']) : j = j' := by
  have hp := List.pairwise_iff_getElem.1 (nodup_firsts g m)
  have ne : ∀ a b (ha : a < (firstsOf g m).length) (hb : b < (firstsOf g m).length), a < b →
      g (firstsOf g m)[a] ≠ g (firstsOf g m)[b] := fun a b ha hb hab => by
    have := hp a b (by rw [List.length_map]; exact ha) (by rw [List.length_map]; exact hb) hab
    rwa [List.getElem_map, List.getElem_map] at this
  rcases Nat.lt_trichotomy j j' with h | h | h
  · exact absurd e (ne j j' hj hj' h)
  · exact h
  · exact absurd e.symm (ne j' j hj' hj h)

variable {g m} in
/-- **`i` is in group `j` exactly when it holds the `j`-th first value.** -/
theorem groupOf_eq_iff {i j : Nat} (hi : i < m) (hj : j < (firstsOf g m).length) :
    groupOf g m i = j ↔ g i = g (firstsOf g m)[j] :=
  ⟨fun h => by subst h; exact (groupOf_get hi).symm,
   fun e => firsts_inj (groupOf_lt hi) hj ((groupOf_get hi).trans e)⟩

/-- **The rows of group `j` are the `j`-th bucket**, ascending. -/
theorem rows_groupOf {j : Nat} (hj : j < (firstsOf g m).length) :
    (List.range m).filter (fun i => groupOf g m i == j) = bucketOf g m (firstsOf g m)[j] :=
  List.filter_congr fun i hi => Bool.eq_iff_iff.2 (by
    rw [beq_iff_eq, decide_eq_true_iff]; exact groupOf_eq_iff (List.mem_range.1 hi) hj)

/-- **Only which keys agree counts**: two keys that agree on the same pairs below `m` group alike. -/
theorem groups_congr {β : Type} [DecidableEq β] {g' : Nat → β}
    (h : ∀ i < m, ∀ j < m, (g i = g j ↔ g' i = g' j)) :
    firstsOf g m = firstsOf g' m ∧ (∀ f < m, bucketOf g m f = bucketOf g' m f) ∧
      ∀ i < m, groupOf g m i = groupOf g' m i := by
  have hf : firstsOf g m = firstsOf g' m := List.filter_congr fun i hi => by
    have hi := List.mem_range.1 hi
    apply Bool.eq_iff_iff.2
    simp only [List.all_eq_true, List.mem_range, Bool.not_eq_true', decide_eq_false_iff_not]
    exact ⟨fun H j hj e => H j hj ((h j (by omega) i hi).2 e), fun H j hj e => H j hj ((h j (by omega) i hi).1 e)⟩
  refine ⟨hf, fun f hfm => List.filter_congr fun i hi => decide_eq_decide.2 (h i (List.mem_range.1 hi) f hfm),
    fun i hi => ?_⟩
  have hj' := groupOf_lt (g := g') hi
  have hj : groupOf g' m i < (firstsOf g m).length := by rw [hf]; exact hj'
  refine (groupOf_eq_iff hi hj).2 ?_
  rw [List.getElem_of_eq hf hj]
  exact (h i hi _ (firsts_lt g' m (List.getElem_mem hj'))).2 (groupOf_get hi).symm

end Firsts

/-- An eight-byte payload read back as the numbers it holds, as `overGroups` reads its ids. -/
def ids (b : ByteArray) : List Nat := (List.range (b.size / 8)).map fun i => (Column.bitsAt b (i * 8) 8).toNat


theorem usize_lt (n : USize) : n.toNat < 2 ^ 64 := Nat.lt_of_lt_of_le n.toNat_lt_size USize.size_le





section Over

variable (op : Coc.Over) (cls : UInt8) (nul : Int64) (ng w n : USize) (gid b : ByteArray)

/-- Row `i`'s group id and element, as `overGroups` reads them. -/
def gidAt (i : Nat) : Nat := Column.idAt gid w.toNat i
def valAt (i : Nat) : Int64 := Ew.signed cls (Ew.elem cls b i)


/-- `overGroups`' step, which `overGroups_eq` checks is the body's. -/
def overStep : Array Int64 × Array Int64 → Nat → Array Int64 × Array Int64 := fun (fold, live) i =>
  let g := Column.idAt gid w.toNat i
  let x := Ew.signed cls (Ew.elem cls b i)
  if g ≥ ng.toNat || (!op.boolCast && x == nul) then (fold, live)
  else (fold.set! g (op.step fold[g]! x), live.set! g (live[g]! + 1))

/-- `overGroups`' answer: the folds then the counts, eight bytes a slot. -/
def slots (fold live : Array Int64) : ByteArray :=
  (fold ++ live).foldl (init := ByteArray.empty) fun acc v => Column.pushBits acc v.toUInt64 8

theorem set!_get! (a : Array Int64) (g j : Nat) (v : Int64) (hj : j < a.size) :
    (a.set! g v)[j]! = if g = j then v else a[j]! := by
  rw [getElem!_pos (a.set! g v) j (by rw [Array.set!_eq_setIfInBounds, Array.size_setIfInBounds]; exact hj),
    getElem!_pos a j hj]
  simp only [Array.set!_eq_setIfInBounds, Array.getElem_setIfInBounds hj]



/-- `laneWidth` answers one of the eight lanes. -/
theorem laneWidth_cases (x : Nat) : Column.laneWidth x = 0 ∨ Column.laneWidth x = 1 ∨
    Column.laneWidth x = 2 ∨ Column.laneWidth x = 4 ∨ Column.laneWidth x = 8 ∨ Column.laneWidth x = 16 ∨
    Column.laneWidth x = 32 ∨ Column.laneWidth x = 64 := by
  unfold Column.laneWidth
  repeat' split
  all_goals omega

/-- **`packIds` at a lane holds all `m` of its ids**: `idsCap` reads back `m`, so neither a zero-width
payload nor the last byte's padding is read past them. -/
theorem idsCap_packIds {W : Nat} (m : Nat) (f : Nat → Nat)
    (hW : W = 0 ∨ W = 1 ∨ W = 2 ∨ W = 4 ∨ W = 8 ∨ W = 16 ∨ W = 32 ∨ W = 64) :
    Column.idsCap (Column.packIds W m f) W m = m := by
  have hpush : ∀ (g : Nat → UInt8) (l : List Nat) (a : ByteArray),
      (l.foldl (fun acc k => acc.push (g k)) a).size = a.size + l.length := fun g l => by
    induction l with
    | nil => intro a; rfl
    | cons x l ih =>
      intro a
      have hs : (a.push (g x)).size = a.size + 1 := by cases a; exact Array.size_push ..
      rw [List.foldl_cons, ih, hs, List.length_cons]; omega
  have hnar : ∀ W, 1 ≤ W → W < 8 → (Column.packIds W m f).size = (m + 8 / W - 1) / (8 / W) := fun W h1 h8 => by
    unfold Column.packIds
    rw [if_neg (by omega), if_neg (by omega)]
    dsimp only
    rw [fold_eq_foldl_range, hpush, List.length_range]
    exact Nat.zero_add _
  have hwide : ∀ W, 8 ≤ W → W ≤ 64 → (Column.packIds W m f).size = W / 8 * m := fun W h8 h64 => by
    unfold Column.packIds
    rw [if_pos h8, fold_eq_foldl_range (g := fun i acc => Column.pushBits acc (f i).toUInt64 (W / 8)),
      (foldl_pushBits (fun i => (f i).toUInt64) (W / 8) (by omega) (List.range m) _).1, List.length_range]
    exact Nat.zero_add _
  unfold Column.idsCap
  rcases hW with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rfl
  all_goals first
    | rw [if_neg (by decide), hnar _ (by decide) (by decide)]; omega
    | rw [if_neg (by decide), hwide _ (by decide) (by decide)]; omega

end Over



section Segs

variable (op : Coc.Over) (cls : UInt8) (nul : Int64) (offs b : ByteArray)

end Segs

#print axioms groupOf_eq_iff
#print axioms rows_groupOf
#print axioms groups_congr
/-- info: 'Rel.Verify.idsCap_packIds' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms idsCap_packIds

end Rel.Verify


namespace Rel.Verify

open Rel Rel.Kernel
open Rel.Kernel.Scan (Kind)

section Firsts

variable {α : Type} [DecidableEq α] (g : Nat → α) (m : Nat)

end Firsts

/-- Long `j` of an id payload is entry `j` of the ids it reads back as. -/
theorem ids_get {b : ByteArray} {l : List Nat} (h : ids b = l) {j : Nat} (hj : j < l.length) :
    (Column.bitsAt b (j * 8) 8).toNat = l[j] := by
  have hl : j < b.size / 8 := by
    have := congrArg List.length h; rw [ids, List.length_map, List.length_range] at this; omega
  have := congrArg (·[j]?) h
  simp only [ids, List.getElem?_map, List.getElem?_range hl, Option.map_some, List.getElem?_eq_getElem hj,
    Option.some.injEq] at this
  exact this


section Over

variable (op : Coc.Over) (cls : UInt8) (nul : Int64) (ng w n : USize) (gid b : ByteArray)

end Over

section Segs

variable (op : Coc.Over) (cls : UInt8) (nul : Int64) (offs b : ByteArray)

end Segs
#print axioms ids_get

end Rel.Verify
