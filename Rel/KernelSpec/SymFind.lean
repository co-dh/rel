import QLean.RelPart.Verify.FindMember
import QLean.RelPart.Verify.Encoding
import QLean.RelPart.Verify.Group
import QLean.RelPart.Kernel.Sort
import QLean.RelPart.Verify.Codes
import QLean.RelPart.Value
import QLean.RelPart.Kernel.Search
import QLean.RelPart.Verify.Assign

/-! The part of `QLean.Verify.SymFind` the Rel kernels reach; `QLean.Verify.SymFind` imports it. -/


namespace QLean.Verify
open QLean QLean.Kernel

/-- Symbol `i` of a blob as the kernels compare it: its bytes without the stored NUL. -/
def symAt (b : ByteArray) (o : Array Nat) (i : Nat) : List UInt8 := (Column.symKey b o i).data.toList

/-- The symbols of a symbol payload in element order: a blob's own, an interned column's dictionary
entry at each id. -/
def symsOf (n : Nat) : Enc → List (List UInt8)
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

/-- `findSymScalar` is the first index of the needle's bytes among the blob's symbols. -/
theorem findSymScalar_toNat (b : ByteArray) (o : Array Nat) (k : ByteArray) (h : o.size - 1 < USize.size) :
    (findSymScalar b o k).toNat = ((List.range (o.size - 1)).map (symAt b o)).idxOf k.data.toList := by
  have hb : ∀ i, ((Column.symKey b o i).data == k.data) = (symAt b o i == k.data.toList) := fun i =>
    Bool.eq_iff_iff.2 (by rw [arr_beq_iff, beq_iff_eq, symAt, Array.toList_inj])
  unfold findSymScalar
  simp only [hb, find?_range_getD]
  have := idxOf_le_length k.data.toList ((List.range (o.size - 1)).map (symAt b o))
  rw [List.length_map, List.length_range] at this
  exact USize.toNat_ofNat_of_lt' (by omega)

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

/-- `symsAt`'s offsets: one start per chosen symbol and one past the last, the first `0` and the last the blob's
size, none past the blob, and symbol `t` the `t`-th chosen one with its NUL. -/
theorem symsAt_inv (blob : ByteArray) (offs : Array Nat) (is : List Nat) :
    (Order.symsAt blob offs is).2.size = is.length + 1 ∧ (Order.symsAt blob offs is).2[0]! = 0 ∧
      (Order.symsAt blob offs is).2[is.length]! = (Order.symsAt blob offs is).1.size ∧
      (∀ t ≤ is.length, (Order.symsAt blob offs is).2[t]! ≤ (Order.symsAt blob offs is).1.size) ∧
      ∀ t (ht : t < is.length), symBytes (Order.symsAt blob offs is).1 (Order.symsAt blob offs is).2 t =
        symAt blob offs is[t] ++ [0] := by
  let B : List Nat → ByteArray := fun is => is.foldl (init := ByteArray.empty) fun acc i =>
    (acc ++ Column.symKey blob offs i).push 0
  let P : List Nat → Array Nat × Nat := fun is => is.foldl (init := (#[0], 0)) fun (o, pos) i =>
    (o.push (pos + (Column.symKey blob offs i).size + 1), pos + (Column.symKey blob offs i).size + 1)
  have inv : ∀ is : List Nat, (P is).1.size = is.length + 1 ∧ (P is).1[0]! = 0 ∧ (P is).1[is.length]! = (B is).size ∧
      (P is).2 = (B is).size ∧ (∀ t ≤ is.length, (P is).1[t]! ≤ (B is).size) ∧
      ∀ t (ht : t < is.length), symBytes (B is) (P is).1 t = symAt blob offs is[t] ++ [0] := by
    intro is
    induction is using list_rev_ind with
    | nil => exact ⟨rfl, rfl, rfl, rfl, fun t ht => by simp at ht; subst ht; exact Nat.le_refl _, fun t ht => absurd ht (by simp)⟩
    | append_singleton l i ih =>
      obtain ⟨h1, h0, h2, h3, h4, h5⟩ := ih
      have hB : B (l ++ [i]) = (B l ++ Column.symKey blob offs i).push 0 := by simp [B, List.foldl_append]
      have hP : P (l ++ [i]) = ((P l).1.push ((B (l ++ [i])).size), (B (l ++ [i])).size) := by
        have : P (l ++ [i]) = ((P l).1.push ((P l).2 + (Column.symKey blob offs i).size + 1),
            (P l).2 + (Column.symKey blob offs i).size + 1) := by simp [P, List.foldl_append]
        have hsz : (B (l ++ [i])).size = (B l).size + (Column.symKey blob offs i).size + 1 := by
          have := congrArg List.length (append_push_toList (B l) (Column.symKey blob offs i))
          simp only [Array.length_toList, List.length_append, List.length_singleton] at this
          rw [hB]; show ((B l ++ _).push 0).data.size = (B l).data.size + (Column.symKey blob offs i).data.size + 1
          omega
        rw [this, hsz, h3]
      have hob : (B (l ++ [i])).data.toList = (B l).data.toList ++ (symAt blob offs i ++ [0]) := by
        simp only [hB, append_push_toList, symAt]
      obtain ⟨g1, g2, g3, g4, g5⟩ := symBytes_push (B l) (B (l ++ [i])) (P l).1 l.length _ h1 h2 h4 hob
      rw [hP]
      simp only [List.length_append, List.length_singleton]
      refine ⟨g1, by rw [push_get!, if_pos (by omega)]; exact h0, g2, trivial, g3, fun t ht => ?_⟩
      rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ ht) with ht | rfl
      · rw [g5 t ht, h5 t ht, List.getElem_append_left ht]
      · rw [g4, List.getElem_append_right (Nat.le_refl _)]; simp
  obtain ⟨h1, h0, h2, -, h4, h5⟩ := inv is
  exact ⟨h1, h0, h2, h4, h5⟩

/-- `symsAt` lays the chosen symbols out as a blob that reads back as them. -/
theorem symsAt_spec (blob : ByteArray) (offs : Array Nat) (is : List Nat) :
    symsOf ((Order.symsAt blob offs is).2.size - 1) (.syms (Order.symsAt blob offs is).1 (Order.symsAt blob offs is).2) =
      is.map (symAt blob offs) := by
  obtain ⟨h1, -, -, h4, h5⟩ := symsAt_inv blob offs is
  simp only [symsOf, h1, Nat.add_sub_cancel]
  apply List.ext_getElem (by simp)
  intro t ht _
  simp only [List.getElem_map, List.getElem_range]
  simp only [List.length_map, List.length_range] at ht
  rw [symAt_eq_dropLast _ _ _ (h4 (t + 1) ht), h5 t ht, List.dropLast_concat]

/-- **`distinctSyms` answers the column's symbols with their repeats erased**, first occurrences in order. -/
theorem distinctSyms_eraseDups (blob : ByteArray) (offs : Array Nat) :
    symsOf ((Order.distinctSyms blob offs).2.size - 1)
      (.syms (Order.distinctSyms blob offs).1 (Order.distinctSyms blob offs).2) =
      (symsOf (offs.size - 1) (.syms blob offs)).eraseDups := by
  have hf : Order.symFirsts blob offs = firstsOf (symAt blob offs) (offs.size - 1) := by
    unfold Order.symFirsts firstsOf
    refine List.filter_congr fun i _ => List.all_congr rfl fun j => ?_
    have := symCmp_eq_iff (Column.symKey blob offs j) (Column.symKey blob offs i)
    cases hc : Column.symCmp (Column.symKey blob offs j) (Column.symKey blob offs i) <;>
      simp_all [symAt]
  rw [Order.distinctSyms, symsAt_spec, hf, firstsOf_eraseDups]; rfl

/-- info: 'QLean.Verify.distinctSyms_eraseDups' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms distinctSyms_eraseDups

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

/-- **`internSyms` round trip**: element `i`'s id names a dictionary entry, and that entry is element `i`'s
symbol. -/
theorem internSyms_symAt (blob : ByteArray) (offs : Array Nat) (h : offs.size - 1 < USize.size) {i : Nat}
    (hi : i < offs.size - 1) :
    Column.idAt (Order.internSyms blob offs).2.2 (Column.idWidth (Order.internSyms blob offs).2.1) i <
        (Order.internSyms blob offs).2.1.size - 1 ∧
      symAt (Order.internSyms blob offs).1 (Order.internSyms blob offs).2.1
          (Column.idAt (Order.internSyms blob offs).2.2 (Column.idWidth (Order.internSyms blob offs).2.1) i) =
        symAt blob offs i := by
  have hD := distinctSyms_eraseDups blob offs
  have e : Order.internSyms blob offs = ((Order.distinctSyms blob offs).1, (Order.distinctSyms blob offs).2,
      Column.packIds (Column.idWidth (Order.distinctSyms blob offs).2) (offs.size - 1) fun j =>
        (findSymScalar (Order.distinctSyms blob offs).1 (Order.distinctSyms blob offs).2
          (Column.symKey blob offs j)).toNat) := rfl
  rw [e]
  generalize Order.distinctSyms blob offs = r at hD ⊢
  obtain ⟨db, dof⟩ := r
  dsimp only [symsOf] at hD ⊢
  simp only [← firstsOf_eraseDups] at hD
  have hlen : dof.size - 1 ≤ offs.size - 1 := by
    have := congrArg List.length hD
    simp only [List.length_map, List.length_range] at this
    rw [this]; unfold firstsOf
    exact Nat.le_trans (List.length_filter_le _ _) (Nat.le_of_eq (List.length_range ..))
  have hmem : symAt blob offs i ∈ (List.range (dof.size - 1)).map (symAt db dof) := by
    rw [hD]; exact mem_firstsOf _ hi
  have hidx := idxOf_lt_of_mem hmem
  rw [List.length_map, List.length_range] at hidx
  have hf : (findSymScalar db dof (Column.symKey blob offs i)).toNat =
      ((List.range (dof.size - 1)).map (symAt db dof)).idxOf (symAt blob offs i) :=
    findSymScalar_toNat db dof _ (by omega)
  have hs : USize.size ≤ 2 ^ 64 := USize.size_le
  rw [Column.idWidth, idAt_packIds_idWidthOf (f := fun j => (findSymScalar db dof (Column.symKey blob offs j)).toNat)
    (by omega) hi (by show (findSymScalar db dof (Column.symKey blob offs i)).toNat < _; rw [hf]; exact hidx), hf]
  refine ⟨hidx, ?_⟩
  have := getElem_idxOf' _ _ (by rw [List.length_map, List.length_range]; exact hidx)
  rwa [List.getElem_map, List.getElem_range] at this

/-- `internSyms` writes its dictionary well formed (`SymsWF`): each entry holds at least its NUL, so the starts
grow. -/
theorem symsWF_internSyms (blob : ByteArray) (offs : Array Nat) :
    SymsWF (Order.internSyms blob offs).1 (Order.internSyms blob offs).2.1 := by
  obtain ⟨h1, h0, h2, h4, h5⟩ := symsAt_inv blob offs (Order.symFirsts blob offs)
  show SymsWF (Order.symsAt blob offs (Order.symFirsts blob offs)).1 (Order.symsAt blob offs (Order.symFirsts blob offs)).2
  refine ⟨by omega, h0, by rw [h1, Nat.add_sub_cancel]; exact h2, fun k hk => h4 k (by omega), fun k hk => ?_⟩
  have h5k := h5 k (by omega)
  unfold symBytes at h5k
  apply Nat.le_of_not_lt; intro hc
  rw [Nat.sub_eq_zero_of_le (Nat.le_of_lt hc), List.take_zero] at h5k
  exact absurd h5k.symm (by simp)

/-- info: 'QLean.Verify.internSyms_symAt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms internSyms_symAt

/-- info: 'QLean.Verify.symsWF_internSyms' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms symsWF_internSyms

/-- info: 'QLean.Verify.idAt_packIds_idWidthOf' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms idAt_packIds_idWidthOf

end QLean.Verify
