import QLean.RelPart.Verify.Encoding
import QLean.RelPart.Kernel.Sort
import QLean.RelPart.Kernel.Coc
import QLean.RelPart.Kernel.Reduce
import QLean.RelPart.Kernel.Scan
import QLean.RelPart.Value
import QLean.RelPart.Verify.Raw
import QLean.RelPart.Kernel.Elementwise

/-! The part of `QLean.Verify.Group` the Rel kernels reach; `QLean.Verify.Group` imports it. -/


namespace QLean.Verify

open QLean QLean.Kernel
open QLean.Kernel.Scan (Kind)

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

theorem ids_indices (is : List Nat) (h : ∀ i ∈ is, i < 2 ^ 64) : ids (Order.indices is) = is := by
  obtain ⟨hs, -, hg⟩ := foldl_pushBits (fun i : Nat => (Int64.ofNat i).toUInt64) 8 (by decide) is ByteArray.empty
  have hs : (Order.indices is).size = 8 * is.length := by rw [Order.indices, hs]; simp
  apply List.ext_getElem (by rw [ids, List.length_map, List.length_range, hs]; omega)
  intro j _ h2
  have e := hg j h2
  rw [show ByteArray.empty.size + 8 * j = j * 8 by simp [Nat.mul_comm]] at e
  simp only [ids, List.getElem_map, List.getElem_range]
  rw [Order.indices, e,
    show (UInt64.ofNat _).toNat = _ from BitVec.toNat_ofNat _ _,
    show ((Int64.ofNat is[j]).toUInt64).toNat = _ from BitVec.toNat_ofNat _ _,
    show 8 * 8 = 64 from rfl, Nat.mod_mod, Nat.mod_mod, Nat.mod_eq_of_lt (h _ (List.getElem_mem h2))]

theorem usize_lt (n : USize) : n.toNat < 2 ^ 64 := Nat.lt_of_lt_of_le n.toNat_lt_size USize.size_le

/-- **`groupIds` answers each element's group and the first occurrences**, keyed by `Order.keyAt` over the
`m` elements it reads. With `rows_groupOf`, group `j`'s rows are `bucketOf` of the `j`-th first index. -/
theorem groupIds_spec (k : Kind) (n : USize) (b : ByteArray) :
    (Order.groupIds k n b).1 =
        Column.packIds (Column.idWidthOf (firstsOf (Order.keyAt k b) (min n.toNat (k.avail b))).length)
          (min n.toNat (k.avail b)) (groupOf (Order.keyAt k b) (min n.toNat (k.avail b))) ∧
      ids (Order.groupIds k n b).2 = firstsOf (Order.keyAt k b) (min n.toNat (k.avail b)) := by
  have hm : min n.toNat (k.avail b) < 2 ^ 64 := Nat.lt_of_le_of_lt (Nat.min_le_left _ _) (usize_lt n)
  exact ⟨rfl, ids_indices _ fun i hi => Nat.lt_trans (firsts_lt _ _ hi) hm⟩

/-- Element `i`'s key read off the encoded form: `Order.rank` of the `foRBits` element cut to the kind's width. -/
def foRKey (k : Kind) (md pk : ByteArray) (i : Nat) : UInt64 :=
  Order.rank k (UInt64.ofNat ((Column.foRBits md pk (Column.blockStarts md) i).toNat % 2 ^ (8 * k.width)))

/-- The decoded payload holds all `n` elements, and its keys are `foRKey`'s. -/
theorem decode_keyAt (k : Kind) (hk : k ≠ .bit) (n : USize) (md pk : ByteArray) :
    k.avail (Coc.decode k.width.toUSize md pk n) = n.toNat ∧
      ∀ i < n.toNat, Order.keyAt k (Coc.decode k.width.toUSize md pk n) i = foRKey k md pk i := by
  have hw8 : k.width ≤ 8 := by cases k <;> decide
  have hw0 : 0 < k.width := by cases k <;> decide
  have hw : k.width.toUSize.toNat = k.width :=
    USize.toNat_ofNat_of_lt' (Nat.lt_of_le_of_lt hw8 (Nat.lt_of_lt_of_le (by decide) USize.le_size))
  obtain ⟨hs, hg⟩ := decodeW _ (by rw [hw]; exact hw8) md pk n
  rw [hw] at hs hg
  refine ⟨?_, fun i hi => ?_⟩
  · have : k.avail (Coc.decode k.width.toUSize md pk n) = (Coc.decode k.width.toUSize md pk n).size / k.width := by
      cases k <;> first | exact absurd rfl hk | rfl
    rw [this, hs, Nat.mul_div_cancel_left _ hw0]
  · rw [foRKey, ← hg i hi]
    cases k <;> first | exact absurd rfl hk | rfl

/-- **`groupIdsFoR` answers `groupIds_spec` over the decoded elements**, keyed by `foRKey` over all `n`
elements. -/
theorem groupIdsFoR_spec (k : Kind) (hk : k ≠ .bit) (n : USize) (md pk : ByteArray) :
    (Order.groupIdsFoR k n md pk).1 = Column.packIds (Column.idWidthOf (firstsOf (foRKey k md pk) n.toNat).length)
        n.toNat (groupOf (foRKey k md pk) n.toNat) ∧
      ids (Order.groupIdsFoR k n md pk).2 = firstsOf (foRKey k md pk) n.toNat := by
  obtain ⟨hav, hkey⟩ := decode_keyAt k hk n md pk
  have hc := groups_congr (Order.keyAt k (Coc.decode k.width.toUSize md pk n)) n.toNat
    (fun i hi j hj => by rw [hkey i hi, hkey j hj])
  obtain ⟨h1, h2⟩ := groupIds_spec k n (Coc.decode k.width.toUSize md pk n)
  rw [hav, Nat.min_self] at h1 h2
  refine ⟨h1.trans ?_, h2.trans hc.1⟩
  rw [hc.1]
  exact packIds_congr _ _ fun i hi => hc.2.2 i hi

section Over

variable (op : Coc.Over) (cls : UInt8) (nul : Int64) (ng w n : USize) (gid b : ByteArray)

/-- Row `i`'s group id and element, as `overGroups` reads them. -/
def gidAt (i : Nat) : Nat := Column.idAt gid w.toNat i
def valAt (i : Nat) : Int64 := Ew.signed cls (Ew.elem cls b i)

/-- The rows `overGroups` steps group `j` on: its id is `j` and its element is not skipped as null. -/
def rowsOf (j : Nat) : List Nat :=
  (List.range (Column.idsCap gid w.toNat (min n.toNat (b.size / Ew.width cls)))).filter fun i =>
    gidAt w gid i == j && (op.boolCast || valAt cls b i != nul)

/-- `overGroups`' step, which `overGroups_eq` checks is the body's. -/
def overStep : Array Int64 × Array Int64 → Nat → Array Int64 × Array Int64 := fun (fold, live) i =>
  let g := Column.idAt gid w.toNat i
  let x := Ew.signed cls (Ew.elem cls b i)
  if g ≥ ng.toNat || (!op.boolCast && x == nul) then (fold, live)
  else (fold.set! g (op.step fold[g]! x), live.set! g (live[g]! + 1))

/-- `overGroups`' answer: the folds then the counts, eight bytes a slot. -/
def slots (fold live : Array Int64) : ByteArray :=
  (fold ++ live).foldl (init := ByteArray.empty) fun acc v => Column.pushBits acc v.toUInt64 8

theorem overGroups_eq : overGroups op cls nul ng w n gid b =
    let r := (List.range (Column.idsCap gid w.toNat (min n.toNat (b.size / Ew.width cls)))).foldl (overStep op cls nul ng w gid b)
      (Array.replicate ng.toNat (op.denseSeed cls nul), Array.replicate ng.toNat 0)
    slots r.1 r.2 := rfl

theorem set!_get! (a : Array Int64) (g j : Nat) (v : Int64) (hj : j < a.size) :
    (a.set! g v)[j]! = if g = j then v else a[j]! := by
  rw [getElem!_pos (a.set! g v) j (by rw [Array.set!_eq_setIfInBounds, Array.size_setIfInBounds]; exact hj),
    getElem!_pos a j hj]
  simp only [Array.set!_eq_setIfInBounds, Array.getElem_setIfInBounds hj]

theorem overStep_fold (l : List Nat) (a c : Array Int64) (ha : a.size = ng.toNat) (hc : c.size = ng.toNat) :
    (l.foldl (overStep op cls nul ng w gid b) (a, c)).1.size = ng.toNat ∧
    (l.foldl (overStep op cls nul ng w gid b) (a, c)).2.size = ng.toNat ∧ ∀ j < ng.toNat,
      (l.foldl (overStep op cls nul ng w gid b) (a, c)).1[j]! =
        (l.filter fun i => gidAt w gid i == j && (op.boolCast || valAt cls b i != nul)).foldl
          (fun acc i => op.step acc (valAt cls b i)) a[j]! ∧
      (l.foldl (overStep op cls nul ng w gid b) (a, c)).2[j]! =
        c[j]! + Int64.ofNat (l.filter fun i => gidAt w gid i == j && (op.boolCast || valAt cls b i != nul)).length := by
  induction l generalizing a c with
  | nil => exact ⟨ha, hc, fun j _ => ⟨rfl, by rw [List.filter_nil, List.length_nil]; exact (Int64.add_zero _).symm⟩⟩
  | cons i l ih =>
    rw [List.foldl_cons]
    by_cases hs : (Column.idAt gid w.toNat i ≥ ng.toNat ||
        (!op.boolCast && Ew.signed cls (Ew.elem cls b i) == nul)) = true
    · have e : overStep op cls nul ng w gid b (a, c) i = (a, c) := by simp only [overStep, hs, if_true]
      rw [e]
      obtain ⟨h1, h2, h3⟩ := ih a c ha hc
      refine ⟨h1, h2, fun j hj => ?_⟩
      have hr : (gidAt w gid i == j && (op.boolCast || valAt cls b i != nul)) = false := by
        by_cases hg : ng.toNat ≤ gidAt w gid i
        · rw [Bool.eq_false_iff.2 fun h => absurd (beq_iff_eq.1 h) (by omega), Bool.false_and]
        · cases hb : op.boolCast
          · cases hx : (Ew.signed cls (Ew.elem cls b i) == nul)
            · rw [hb, hx] at hs
              simp only [Bool.not_false, Bool.and_false, Bool.or_false, decide_eq_true_eq] at hs
              exact absurd hs hg
            · simp only [valAt, bne, hx, Bool.not_true, Bool.or_false, Bool.and_false]
          · rw [hb] at hs
            simp only [Bool.not_true, Bool.false_and, Bool.or_false, decide_eq_true_eq] at hs
            exact absurd hs hg
      rw [List.filter_cons_of_neg (by rw [hr]; exact Bool.false_ne_true)]
      exact h3 j hj
    · have e : overStep op cls nul ng w gid b (a, c) i =
          (a.set! (gidAt w gid i) (op.step a[gidAt w gid i]! (valAt cls b i)),
            c.set! (gidAt w gid i) (c[gidAt w gid i]! + 1)) := by
        simp only [overStep, hs, if_false, Bool.false_eq_true]; rfl
      rw [e]
      obtain ⟨h1, h2, h3⟩ := ih (a.set! (gidAt w gid i) (op.step a[gidAt w gid i]! (valAt cls b i)))
        (c.set! (gidAt w gid i) (c[gidAt w gid i]! + 1))
        (by rw [Array.set!_eq_setIfInBounds, Array.size_setIfInBounds]; exact ha)
        (by rw [Array.set!_eq_setIfInBounds, Array.size_setIfInBounds]; exact hc)
      refine ⟨h1, h2, fun j hj => ?_⟩
      obtain ⟨h3a, h3b⟩ := h3 j hj
      rw [h3a, h3b, set!_get! _ _ _ _ (ha ▸ hj), set!_get! _ _ _ _ (hc ▸ hj)]
      have hk : (op.boolCast || valAt cls b i != nul) = true := by
        simp only [valAt]
        cases hb : op.boolCast
        · cases hx : (Ew.signed cls (Ew.elem cls b i) == nul)
          · simp only [bne, hx, Bool.not_false, Bool.or_true]
          · exact (hs (by rw [hb, hx, Bool.not_false, Bool.and_true, Bool.or_true])).elim
        · rfl
      by_cases hg : gidAt w gid i = j
      · rw [if_pos hg, if_pos hg, List.filter_cons_of_pos (by rw [beq_iff_eq.2 hg, hk]; rfl), List.foldl_cons,
          List.length_cons, Int64.ofNat_add, ← hg]
        exact ⟨rfl, by rw [Int64.add_assoc, Int64.add_comm 1]; rfl⟩
      · rw [if_neg hg, if_neg hg, List.filter_cons_of_neg (by rw [Bool.eq_false_iff.2 fun h => hg (beq_iff_eq.1 h)]; exact Bool.false_ne_true)]
        exact ⟨rfl, rfl⟩

theorem slots_spec (fold live : Array Int64) :
    (slots fold live).size = 8 * (fold.size + live.size) ∧
    ∀ j (hj : j < (fold ++ live).size), (Column.bitsAt (slots fold live) (j * 8) 8).toInt64 = (fold ++ live)[j] := by
  obtain ⟨hs, -, hg⟩ := foldl_pushBits (fun v : Int64 => v.toUInt64) 8 (by decide) (fold ++ live).toList ByteArray.empty
  rw [Array.foldl_toList] at hs hg
  refine ⟨by rw [slots, hs, Array.length_toList, Array.size_append]; simp, fun j hj => ?_⟩
  have e := hg j (by rw [Array.length_toList]; exact hj)
  rw [show ByteArray.empty.size + 8 * j = j * 8 by simp [Nat.mul_comm]] at e
  rw [slots, e, show 8 * 8 = 64 from rfl, Nat.mod_eq_of_lt (UInt64.toNat_lt _), UInt64.ofNat_toNat,
    Int64.toInt64_toUInt64, Array.getElem_toList]

/-- **`overGroups` answers, per group `j < ng`, `Over.step` folded from `Over.denseSeed` over `rowsOf j` —
the rows with id `j` whose element is not the null, every row at `.all`/`.any` — and then how many rows that
is**, each an `Int64` read at slot `j` and slot `ng + j`. The step is `Coc.Over.step`, so `.add` wraps at 64
bits. -/
theorem overGroups_spec :
    (overGroups op cls nul ng w n gid b).size = 16 * ng.toNat ∧ ∀ j < ng.toNat,
      (Column.bitsAt (overGroups op cls nul ng w n gid b) (j * 8) 8).toInt64 =
          (rowsOf op cls nul w n gid b j).foldl (fun acc i => op.step acc (valAt cls b i)) (op.denseSeed cls nul) ∧
      (Column.bitsAt (overGroups op cls nul ng w n gid b) ((ng.toNat + j) * 8) 8).toInt64 =
          Int64.ofNat (rowsOf op cls nul w n gid b j).length := by
  obtain ⟨h1, h2, h3⟩ := overStep_fold op cls nul ng w gid b (List.range (Column.idsCap gid w.toNat (min n.toNat (b.size / Ew.width cls))))
    (Array.replicate ng.toNat (op.denseSeed cls nul)) (Array.replicate ng.toNat 0) Array.size_replicate
    Array.size_replicate
  rw [overGroups_eq]
  dsimp only
  generalize List.foldl (overStep op cls nul ng w gid b) (Array.replicate ng.toNat (op.denseSeed cls nul),
    Array.replicate ng.toNat 0) (List.range (Column.idsCap gid w.toNat (min n.toNat (b.size / Ew.width cls)))) = r at h1 h2 h3 ⊢
  obtain ⟨hs, hg⟩ := slots_spec r.1 r.2
  refine ⟨by rw [hs, h1, h2]; omega, fun j hj => ?_⟩
  obtain ⟨ha, hc⟩ := h3 j hj
  have hl : ∀ a : Array Int64, a.size = ng.toNat → j < a.size := fun a e => e ▸ hj
  refine ⟨?_, ?_⟩
  · rw [hg j (by rw [Array.size_append, h1]; omega), Array.getElem_append_left (by rw [h1]; exact hj),
      ← getElem!_pos r.1 j (hl _ h1), ha,
      getElem!_pos (Array.replicate ng.toNat (op.denseSeed cls nul)) j (hl _ Array.size_replicate),
      Array.getElem_replicate]
    rfl
  · rw [hg (ng.toNat + j) (by rw [Array.size_append, h1, h2]; omega),
      Array.getElem_append_right (by rw [h1]; omega)]
    simp only [h1, Nat.add_sub_cancel_left]
    rw [← getElem!_pos r.2 j (hl _ h2), hc,
      getElem!_pos (Array.replicate ng.toNat (0 : Int64)) j (hl _ Array.size_replicate), Array.getElem_replicate,
      Int64.zero_add]
    rfl

/-- **`overGroups` over ids that read back as `groupOf g m`** (`groupIds_spec`, `groupIdsFoR_spec`): slot `j`
folds the non-null rows of the `j`-th bucket, and slot `ng + j` counts them. -/
theorem overGroups_buckets {α : Type} [DecidableEq α] {g : Nat → α} {m j : Nat}
    (hg : idsW w.toNat (min n.toNat (b.size / Ew.width cls)) gid =(List.range m).map (groupOf g m)) (hj : j < ng.toNat)
    (hf : j < (firstsOf g m).length) :
    (Column.bitsAt (overGroups op cls nul ng w n gid b) (j * 8) 8).toInt64 =
        ((bucketOf g m (firstsOf g m)[j]).filter fun i => op.boolCast || valAt cls b i != nul).foldl
          (fun acc i => op.step acc (valAt cls b i)) (op.denseSeed cls nul) ∧
      (Column.bitsAt (overGroups op cls nul ng w n gid b) ((ng.toNat + j) * 8) 8).toInt64 =
        Int64.ofNat ((bucketOf g m (firstsOf g m)[j]).filter fun i => op.boolCast || valAt cls b i != nul).length := by
  have hl : Column.idsCap gid w.toNat (min n.toNat (b.size / Ew.width cls)) = m := by
    have := congrArg List.length hg
    rwa [idsW, List.length_map, List.length_range, List.length_map, List.length_range] at this
  have key : rowsOf op cls nul w n gid b j = (bucketOf g m (firstsOf g m)[j]).filter
      fun i => op.boolCast || valAt cls b i != nul := by
    rw [rowsOf, hl, ← rows_groupOf g m hf, List.filter_filter]
    exact List.filter_congr fun i hi => by
      have e := congrArg (·[i]?) hg
      simp only [idsW, hl, List.getElem?_map, List.getElem?_range (List.mem_range.1 hi), Option.map_some,
        Option.some.injEq] at e
      rw [gidAt, e, Bool.and_comm]
  rw [← key]
  exact (overGroups_spec op cls nul ng w n gid b).2 j hj

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

/-- **`overGroups` over the ids `groupIds` answers, at the width it packs them at: slot `j` folds the
non-null rows whose key is the `j`-th group's key, slot `ng + j` counts them.** No width hypothesis but
`hw`, that `idAt` reads back what `packIds` wrote (`idAt_packIds`); `m` keys, at most the payload's rows. -/
theorem overGroups_groupIds (k : Kind) (kn : USize) (kb : ByteArray) {m : USize} {j : Nat}
    (hm : min kn.toNat (k.avail kb) = m.toNat) (hng : ng.toNat = (firstsOf (Order.keyAt k kb) m.toNat).length)
    (hwu : w.toNat = Column.idWidthOf ng.toNat)
    (hw : ∀ i < m.toNat, Column.idAt (Column.packIds w.toNat m.toNat (groupOf (Order.keyAt k kb) m.toNat)) w.toNat i =
      groupOf (Order.keyAt k kb) m.toNat i)
    (hb : m.toNat ≤ b.size / Ew.width cls) (hf : j < (firstsOf (Order.keyAt k kb) m.toNat).length) :
    (Column.bitsAt (overGroups op cls nul ng w m (Order.groupIds k kn kb).1 b) (j * 8) 8).toInt64 =
        ((bucketOf (Order.keyAt k kb) m.toNat (firstsOf (Order.keyAt k kb) m.toNat)[j]).filter
          fun i => op.boolCast || valAt cls b i != nul).foldl (fun acc i => op.step acc (valAt cls b i))
          (op.denseSeed cls nul) ∧
      (Column.bitsAt (overGroups op cls nul ng w m (Order.groupIds k kn kb).1 b) ((ng.toNat + j) * 8) 8).toInt64 =
        Int64.ofNat ((bucketOf (Order.keyAt k kb) m.toNat (firstsOf (Order.keyAt k kb) m.toNat)[j]).filter
          fun i => op.boolCast || valAt cls b i != nul).length := by
  have hgid : (Order.groupIds k kn kb).1 = Column.packIds w.toNat m.toNat (groupOf (Order.keyAt k kb) m.toNat) := by
    rw [(groupIds_spec k kn kb).1, hm, hwu, hng]
  refine overGroups_buckets op cls nul ng w m _ b ?_ (hng ▸ hf) hf
  rw [Nat.min_eq_left hb, idsW, hgid,
    idsCap_packIds (W := w.toNat) m.toNat _ (by rw [hwu]; exact laneWidth_cases _)]
  exact List.map_congr_left fun i hi => hw i (List.mem_range.1 hi)

end Over

/-- `Array.extract`'s loop: `bs`, then up to `i` elements of `a` from `j`. Core's `Array.getElem?_extract`
carries `Classical.choice`, so the read is taken from the loop here. -/
theorem extract_loop_getElem? {α : Type} (a bs : Array α) (i j k : Nat) :
    (Array.extract.loop a i j bs)[k]? = if k < bs.size then bs[k]? else
      if k - bs.size < i then if j + (k - bs.size) < a.size then a[j + (k - bs.size)]? else none else none := by
  induction i generalizing j bs with
  | zero =>
    rw [show Array.extract.loop a 0 j bs = bs by unfold Array.extract.loop; split <;> rfl]
    by_cases hk : k < bs.size
    · rw [if_pos hk]
    · rw [if_neg hk, if_neg (Nat.not_lt_zero _), Array.getElem?_eq_none (by omega)]
  | succ i ih =>
    unfold Array.extract.loop
    split
    · rename_i h
      show (Array.extract.loop a i (j + 1) (bs.push a[j]))[k]? = _
      rw [ih, Array.size_push, getElem?_push]
      repeat' split
      all_goals first | rfl | (exfalso; omega) | (congr 1; omega) | (simp only [show j + (k - bs.size) = j by omega, Array.getElem?_eq_getElem h])
    · rename_i h
      by_cases hk : k < bs.size
      · rw [if_pos hk]
      · rw [if_neg hk, Array.getElem?_eq_none (by omega)]
        by_cases hi : k - bs.size < i + 1
        · rw [if_pos hi, if_neg (by omega)]
        · rw [if_neg hi]

theorem extract_getElem? {α : Type} (a : Array α) (s e k : Nat) :
    (a.extract s e)[k]? = if k < min e a.size - s then a[s + k]? else none := by
  unfold Array.extract
  have h0 : ∀ c, (Array.emptyWithCapacity (α := α) c).size = 0 := fun _ => rfl
  rw [extract_loop_getElem?, h0, if_neg (Nat.not_lt_zero _), Nat.sub_zero, Nat.sub_eq]
  by_cases hk : k < min e a.size - s
  · rw [if_pos hk, if_pos hk, if_pos (by rw [Nat.lt_sub_iff_add_lt, Nat.lt_min] at hk; omega)]
  · rw [if_neg hk, if_neg hk]

theorem get!_eq (b : ByteArray) (k : Nat) : b.get! k = b[k]?.getD 0 := by
  rcases b with ⟨a⟩
  by_cases h : k < a.size
  · rw [getElem?_pos (ByteArray.mk a) k h]; simp [ByteArray.get!, h, ByteArray.getElem_eq_getElem_data]
  · rw [getElem?_neg (ByteArray.mk a) k h]; simp [ByteArray.get!, h]; rfl

/-- **`atI64` reads the eight bytes `bitsAt` does.** -/
theorem atI64_eq (b : ByteArray) (i : Nat) : atI64 b i = (Column.bitsAt b (i * 8) 8).toInt64 := by
  simp only [Column.bitsAt_succ, show Column.bitsAt b (i * 8) 0 = 0 from rfl, UInt64.zero_or, atI64, get!_eq,
    Nat.add_zero, show (8 * 0 : Nat).toUInt64 = 0 from rfl, UInt64.shiftLeft_zero]
  rfl

section Segs

variable (op : Coc.Over) (cls : UInt8) (nul : Int64) (offs b : ByteArray)

end Segs

#print axioms groupOf_eq_iff
#print axioms rows_groupOf
#print axioms groups_congr
#print axioms groupIds_spec
#print axioms groupIdsFoR_spec
#print axioms overGroups_spec
#print axioms overGroups_buckets
#print axioms atI64_eq
/-- info: 'QLean.Verify.idsCap_packIds' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms idsCap_packIds
/-- info: 'QLean.Verify.overGroups_groupIds' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms overGroups_groupIds

end QLean.Verify
