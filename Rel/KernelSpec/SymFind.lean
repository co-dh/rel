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

/-- Symbol `i` of a blob as the kernels compare it: its bytes without the stored NUL. -/
def symAt (b : ByteArray) (o : Array Nat) (i : Nat) : List UInt8 := (Column.symKey b o i).data.toList

/-- The symbols of a symbol payload in element order: a blob's own, an interned column's dictionary
entry at each id. -/
def symsOf (n : Nat) : Ext.Enc X → List (List UInt8)
  | .syms b o => (List.range (o.size - 1)).map (symAt b o)
  | .enum d o ids => (List.range n).map fun i => symAt d o (Column.idAt ids (Column.idWidth o) i)
  | _ => []

theorem bget (x : ByteArray) (i : Nat) : x[i]? = x.data.toList[i]? := by
  rw [Array.getElem?_toList]
  by_cases h : i < x.size
  · rw [getElem?_pos x i h, getElem?_pos x.data i h]; rfl
  · rw [getElem?_neg x i h, getElem?_neg x.data i h]

theorem extract_toList (b : ByteArray) (s e : Nat) :
    (b.extract s e).data.toList = (b.data.toList.drop s).take (e - s) :=
  copySlice_end b ByteArray.empty s (e - s)

/-- A symbol whose end lies inside its blob is its `symBytes` without the last byte, the NUL. -/
theorem symAt_eq_dropLast (b : ByteArray) (o : Array Nat) (i : Nat) (h : o[i + 1]! ≤ b.size) :
    symAt b o i = (symBytes b o i).dropLast := by
  unfold symAt symBytes Column.symKey Column.symBytes
  simp only
  split
  · rw [extract_toList, List.dropLast_eq_take, List.length_take, List.length_drop, Array.length_toList,
      List.take_take]
    congr 1
    split <;> simp only [ByteArray.size] at h <;> omega
  · rename_i hn
    rw [getElem!_neg o (i + 1) hn, extract_toList]
    simp

/-- `symCmp` answers `.eq` exactly when the two byte strings are one. -/
theorem symCmp_eq_iff (x y : ByteArray) : Column.symCmp x y = .eq ↔ x.data.toList = y.data.toList := by
  have hx : x.size = x.data.toList.length := Array.length_toList.symm
  have hy : y.size = y.data.toList.length := Array.length_toList.symm
  unfold Column.symCmp
  simp only [bget]
  split
  · rename_i i hf
    have hne : x.data.toList[i]?.getD 0 ≠ y.data.toList[i]?.getD 0 := by simpa using List.find?_some hf
    -- not `Std.compare_eq_iff_eq`, whose `LawfulEqOrd UInt8` is classical
    rw [show ∀ a b : UInt8, compare a b = .eq ↔ a = b from fun _ _ =>
      compareOfLessAndEq_eq_eq UInt8.le_refl UInt8.not_le]
    exact ⟨fun h => absurd h hne, fun h => absurd (by rw [h]) hne⟩
  · rename_i hf
    rw [Nat.compare_eq_eq, hx, hy]
    refine ⟨fun hs => List.ext_getElem hs fun k hk _ => ?_, fun h => by rw [h]⟩
    have h1 := List.find?_eq_none.1 hf k (List.mem_range.2 (by omega))
    have h2 : x.data.toList[k]?.getD 0 = y.data.toList[k]?.getD 0 := by simpa using h1
    rwa [List.getElem?_eq_getElem hk, List.getElem?_eq_getElem (hs ▸ hk), Option.getD_some, Option.getD_some] at h2

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

theorem idWidth_toNat (o : Array Nat) : (Column.idWidth o).toUSize.toNat = Column.idWidth o := by
  have hW := laneWidth_cases (Column.widthFor (o.size - 1 - 1))
  simp only [show Column.laneWidth (Column.widthFor (o.size - 1 - 1)) = Column.idWidth o from rfl] at hW
  have hs : 2 ^ 32 ≤ USize.size := USize.le_size
  exact toUSize_toNat (by omega)

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

/-- One step of the fold that joins `syms` parts: the part's starts after its leading `0`, shifted past the blob so far, keep
every earlier entry and read the part's entry `k` at `k` past the earlier ones. -/
theorem concatSyms_step {blob b : ByteArray} {offs o : Array Nat} (hA : SymsWF blob offs) (hB : SymsWF b o) :
    SymsWF (blob ++ b) (offs ++ (o.extract 1 o.size).map (· + blob.size)) ∧
      (offs ++ (o.extract 1 o.size).map (· + blob.size)).size = offs.size + (o.size - 1) ∧
      (∀ i < offs.size - 1, symBytes (blob ++ b) (offs ++ (o.extract 1 o.size).map (· + blob.size)) i =
        symBytes blob offs i) ∧
      ∀ k < o.size - 1, symBytes (blob ++ b) (offs ++ (o.extract 1 o.size).map (· + blob.size)) (offs.size - 1 + k) =
        symBytes b o k := by
  have hsz : (offs ++ (o.extract 1 o.size).map (· + blob.size)).size = offs.size + (o.size - 1) := by
    rw [Array.size_append, Array.size_map, Array.size_extract, Nat.min_self]
  have hO : ∀ t, (offs ++ (o.extract 1 o.size).map (· + blob.size))[t]! =
      if t < offs.size then offs[t]! else if t < offs.size + (o.size - 1) then o[t - offs.size + 1]! + blob.size
      else 0 := by
    intro t
    by_cases h1 : t < offs.size
    · rw [if_pos h1, getElem!_pos (offs ++ (o.extract 1 o.size).map (· + blob.size)) t (by rw [hsz]; omega),
        getElem!_pos offs t h1, Array.getElem_append_left h1]
    · rw [if_neg h1]
      by_cases h2 : t < offs.size + (o.size - 1)
      · rw [if_pos h2, getElem!_pos (offs ++ (o.extract 1 o.size).map (· + blob.size)) t (by rw [hsz]; omega),
          getElem!_pos o (t - offs.size + 1) (by omega), Array.getElem_append_right (by omega)]
        -- not `Array.getElem_extract`, which is classical
        have hx := extract_getElem? o 1 o.size (t - offs.size)
        rw [if_pos (by omega), getElem?_pos (o.extract 1 o.size) (t - offs.size) (by rw [Array.size_extract]; omega),
          show 1 + (t - offs.size) = t - offs.size + 1 by omega, getElem?_pos o (t - offs.size + 1) (by omega)] at hx
        rw [Array.getElem_map, Option.some.inj hx]
      · rw [if_neg h2]; exact getElem!_neg (offs ++ (o.extract 1 o.size).map (· + blob.size)) t (by rw [hsz]; omega)
  have hl : (blob ++ b).data.toList = blob.data.toList ++ b.data.toList := by
    rw [ByteArray.data_append, Array.toList_append]
  have hbl : blob.data.toList.length = blob.size := Array.length_toList
  have hbs : (blob ++ b).size = blob.size + b.size := ByteArray.size_append
  have hp := hA.pos
  refine ⟨⟨by omega, by rw [hO, if_pos hp, hA.first], ?_, fun t _ => ?_, fun t ht => ?_⟩, hsz, fun i hi => ?_,
    fun k hk => ?_⟩
  · rw [hsz, hO, hbs]
    by_cases h0 : o.size - 1 = 0
    · rw [if_pos (by omega), h0, Nat.add_zero, hA.last]
      have := hB.last; rw [h0, hB.first] at this; omega
    · rw [if_neg (by omega), if_pos (by omega), show offs.size + (o.size - 1) - 1 - offs.size + 1 = o.size - 1 by omega,
        hB.last]; omega
  · rw [hO, hbs]
    split
    · have := hA.le t ‹_›; omega
    · split
      · have := hB.le (t - offs.size + 1) (by omega); omega
      · exact Nat.zero_le _
  · rw [hsz] at ht
    rw [hO, hO]
    by_cases h1 : t + 1 < offs.size
    · rw [if_pos (by omega), if_pos h1]; exact hA.mono t (by omega)
    · by_cases h2 : t < offs.size
      · have e : offs[t]! = blob.size := by rw [show t = offs.size - 1 by omega]; exact hA.last
        rw [if_pos h2, if_neg h1, if_pos (by omega), e]; omega
      · have := hB.mono (t - offs.size + 1) (by omega)
        rw [if_neg h2, if_neg h1, if_pos (by omega), if_pos (by omega),
          show t + 1 - offs.size + 1 = t - offs.size + 1 + 1 by omega]; omega
  · unfold symBytes
    have := hA.le i (by omega); have := hA.le (i + 1) (by omega)
    rw [hO i, hO (i + 1), if_pos (by omega), if_pos (by omega), hl, List.drop_append_of_le_length (by omega),
      List.take_append_of_le_length (by rw [List.length_drop]; omega)]
  · unfold symBytes
    have hlo : (offs ++ (o.extract 1 o.size).map (· + blob.size))[offs.size - 1 + k]! = blob.size + o[k]! := by
      rw [hO]
      by_cases k0 : k = 0
      · subst k0; rw [if_pos (by omega), Nat.add_zero, hA.last, hB.first, Nat.add_zero]
      · rw [if_neg (by omega), if_pos (by omega), show offs.size - 1 + k - offs.size + 1 = k by omega]; omega
    have hhi : (offs ++ (o.extract 1 o.size).map (· + blob.size))[offs.size - 1 + k + 1]! = blob.size + o[k + 1]! := by
      rw [hO, if_neg (by omega), if_pos (by omega), show offs.size - 1 + k + 1 - offs.size + 1 = k + 1 by omega]; omega
    rw [hlo, hhi, hl, ← hbl, List.drop_append, Nat.add_sub_add_left, List.drop_eq_nil_of_le (by omega),
      List.nil_append, Nat.add_sub_cancel_left]

/-- The fold that joins `syms` parts, over a list of well-formed parts from a well-formed blob: well formed, one entry per entry
of the parts, the blob's own entries kept, and part `p`'s entry `k` past the blob's and the parts' before `p`. -/
theorem concatSyms_foldl (L : List (ByteArray × Array Nat)) (hL : ∀ x ∈ L, SymsWF x.1 x.2) (acc : ByteArray × Array Nat)
    (hacc : SymsWF acc.1 acc.2) :
    SymsWF (L.foldl (fun acc x => (acc.1 ++ x.1, acc.2 ++ (x.2.extract 1 x.2.size).map (· + acc.1.size))) acc).1
        (L.foldl (fun acc x => (acc.1 ++ x.1, acc.2 ++ (x.2.extract 1 x.2.size).map (· + acc.1.size))) acc).2 ∧
      (L.foldl (fun acc x => (acc.1 ++ x.1, acc.2 ++ (x.2.extract 1 x.2.size).map (· + acc.1.size))) acc).2.size - 1 =
        acc.2.size - 1 + (L.map fun x => x.2.size - 1).sum ∧
      (∀ i < acc.2.size - 1,
        symBytes (L.foldl (fun acc x => (acc.1 ++ x.1, acc.2 ++ (x.2.extract 1 x.2.size).map (· + acc.1.size))) acc).1
          (L.foldl (fun acc x => (acc.1 ++ x.1, acc.2 ++ (x.2.extract 1 x.2.size).map (· + acc.1.size))) acc).2 i =
        symBytes acc.1 acc.2 i) ∧
      ∀ p (hp : p < L.length), ∀ k < L[p].2.size - 1,
        symBytes (L.foldl (fun acc x => (acc.1 ++ x.1, acc.2 ++ (x.2.extract 1 x.2.size).map (· + acc.1.size))) acc).1
          (L.foldl (fun acc x => (acc.1 ++ x.1, acc.2 ++ (x.2.extract 1 x.2.size).map (· + acc.1.size))) acc).2
          (acc.2.size - 1 + ((L.take p).map fun x => x.2.size - 1).sum + k) = symBytes L[p].1 L[p].2 k := by
  induction L generalizing acc with
  | nil => exact ⟨hacc, rfl, fun _ _ => rfl, fun p hp => absurd hp (Nat.not_lt_zero _)⟩
  | cons x L ih =>
    obtain ⟨s1, s2, s3, s4⟩ := concatSyms_step hacc (hL x (List.mem_cons_self ..))
    obtain ⟨i1, i2, i3, i4⟩ := ih (fun y hy => hL y (List.mem_cons_of_mem _ hy))
      (acc.1 ++ x.1, acc.2 ++ (x.2.extract 1 x.2.size).map (· + acc.1.size)) s1
    dsimp only at i2 i3 i4
    have hp := hacc.pos
    simp only [List.foldl_cons]
    refine ⟨i1, by rw [i2, s2, List.map_cons, List.sum_cons]; omega, fun i hi => ?_, fun p hp' k hk => ?_⟩
    · rw [i3 i (by omega), s3 i hi]
    · cases p with
      | zero =>
        simp only [List.take_zero, List.map_nil, List.sum_nil, Nat.add_zero, List.getElem_cons_zero] at hk ⊢
        rw [i3 _ (by omega), s4 k hk]
      | succ p =>
        simp only [List.take_succ_cons, List.map_cons, List.sum_cons, List.getElem_cons_succ] at hk ⊢
        rw [← i4 p (Nat.lt_of_succ_lt_succ hp') k hk, s2]
        congr 1; omega



end Rel.Verify
