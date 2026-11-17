import Rel.KernelSpec.Encoding
import Rel.Kernel.Value
import Rel.Kernel.Search

/-! The part of `Rel.Verify.FindMember` the Rel kernels reach; `Rel.Verify.FindMember` imports it. -/


namespace Rel.Verify
open Rel Rel.Kernel

/-- A search over `List.range n` answering `n` for "absent" is the position of the first match. -/
theorem find?_range_getD {α : Type} [BEq α] (f : Nat → α) (y : α) (n : Nat) :
    ((List.range n).find? fun i => f i == y).getD n = ((List.range n).map f).idxOf y := by
  suffices h : ∀ k s, ((List.range' s k).find? fun i => f i == y).getD (s + k) =
      s + ((List.range' s k).map f).idxOf y by
    have := h n 0; rwa [Nat.zero_add, Nat.zero_add, ← List.range_eq_range'] at this
  intro k
  induction k with
  | zero => intro s; rfl
  | succ k ih =>
    intro s
    rw [List.range'_succ, List.find?_cons, List.map_cons, List.idxOf_cons]
    cases h : f s == y
    · simp only [cond_false]
      rw [show s + (k + 1) = s + 1 + k by omega, ih (s + 1)]; omega
    · rfl

theorem idxOf_le_length {α : Type} [BEq α] (y : α) (l : List α) : l.idxOf y ≤ l.length := by
  induction l with
  | nil => exact Nat.le_refl 0
  | cons a l ih =>
    rw [List.idxOf_cons, List.length_cons]
    cases a == y
    · exact Nat.succ_le_succ ih
    · exact Nat.zero_le _

theorem idxOf_lt_length {α : Type} [BEq α] [LawfulBEq α] (y : α) (l : List α) :
    l.idxOf y < l.length ↔ y ∈ l := by
  induction l with
  | nil => exact ⟨fun h => absurd h (Nat.not_lt_zero 0), fun h => nomatch h⟩
  | cons a l ih =>
    rw [List.idxOf_cons, List.length_cons, List.mem_cons]
    cases h : a == y
    · have hne : ¬ y = a := fun e => Bool.noConfusion ((beq_iff_eq.2 e.symm).symm.trans h)
      simp only [cond_false]
      rw [Nat.add_lt_add_iff_right, ih]
      exact ⟨Or.inr, fun o => o.elim (fun e => absurd e hne) id⟩
    · exact ⟨fun _ => Or.inl (beq_iff_eq.1 h).symm, fun _ => Nat.succ_pos _⟩

/-- **`findScalar` is `List.idxOf` on the decoded haystack**: the least index whose key is the
needle's, and the count when no key is. The count must fit a `USize`, which is what the C indexes by. -/
theorem findScalar_idxOf (w : USize) (float : Bool) (hay : ByteArray) (k : UInt64)
    (hn : hay.size / w.toNat < USize.size) :
    (findScalar w float hay k).toNat =
      ((elemsW w.toNat hay).map (normalise w.toNat float)).idxOf (normalise w.toNat float k) := by
  have hl := idxOf_le_length (normalise w.toNat float k) ((elemsW w.toNat hay).map (normalise w.toNat float))
  simp only [elemsW, List.map_map, List.length_map, List.length_range] at hl ⊢
  simp only [findScalar]
  rw [find?_range_getD (key w.toNat float hay)]
  exact USize.toNat_ofNat_of_lt' (Nat.lt_of_le_of_lt hl hn)

/-- **`findVec`'s answer is one index per needle**, eight bytes each: at a width up to eight the
`findScalar` index of the needle's key, and above eight the first haystack element
whose bytes are the needle's, both `List.idxOf` on the decoded haystack. -/
theorem findVec_idxOf (w : USize) (float : Bool) (hay ndl : ByteArray)
    (hn : hay.size / w.toNat < USize.size) :
    (findVec w float hay ndl).size = 8 * (ndl.size / w.toNat) ∧
    ∀ j < ndl.size / w.toNat, (Column.bitsAt (findVec w float hay ndl) (j * 8) 8).toNat =
      if w.toNat ≤ 8 then ((elemsW w.toNat hay).map (normalise w.toNat float)).idxOf
          (normalise w.toNat float (Column.bitsAt ndl (j * w.toNat) w.toNat))
      else ((List.range (hay.size / w.toNat)).map fun i =>
          (hay.extract (i * w.toNat) (i * w.toNat + w.toNat)).data).idxOf
            (ndl.extract (j * w.toNat) (j * w.toNat + w.toNat)).data := by
  let G : Nat → Nat := fun j =>
    if w.toNat ≤ 8 then (findScalar w float hay (Column.bitsAt ndl (j * w.toNat) w.toNat)).toNat
    else ((List.range (hay.size / w.toNat)).find? fun i => (hay.extract (i * w.toNat) (i * w.toNat + w.toNat)).data
      == (ndl.extract (j * w.toNat) (j * w.toNat + w.toNat)).data).getD (hay.size / w.toNat)
  obtain ⟨hs, -, hg⟩ := foldl_pushBits (fun j => (G j).toUInt64) 8 (Nat.le_refl 8)
    (List.range (ndl.size / w.toNat)) ByteArray.empty
  have hf : findVec w float hay ndl =
      (List.range (ndl.size / w.toNat)).foldl (fun acc j => Column.pushBits acc (G j).toUInt64 8) ByteArray.empty := rfl
  rw [hf]
  refine ⟨by simpa using hs, fun j hj => ?_⟩
  have h := hg j (by simpa using hj)
  simp only [ByteArray.size_empty, Nat.zero_add, List.getElem_range] at h
  rw [Nat.mul_comm j, h, show 8 * 8 = 64 from rfl, ofNat_toNat_mod64, Nat.toUInt64_eq, UInt64.toNat_ofNat']
  have h64 : USize.size ≤ 2 ^ 64 := USize.size_le
  by_cases hw : w.toNat ≤ 8
  · simp only [G, hw, ↓reduceIte]
    rw [findScalar_idxOf w float hay _ hn]
    have hl := idxOf_le_length (normalise w.toNat float (Column.bitsAt ndl (j * w.toNat) w.toNat))
      ((elemsW w.toNat hay).map (normalise w.toNat float))
    rw [List.length_map, elemsW, List.length_map, List.length_range] at hl
    exact Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt hl (Nat.lt_of_lt_of_le hn h64))
  · simp only [G, hw, ↓reduceIte]
    rw [find?_range_getD]
    have hl := idxOf_le_length (ndl.extract (j * w.toNat) (j * w.toNat + w.toNat)).data
      ((List.range (hay.size / w.toNat)).map fun i => (hay.extract (i * w.toNat) (i * w.toNat + w.toNat)).data)
    simp only [List.length_map, List.length_range] at hl
    exact Nat.mod_eq_of_lt (by omega)

theorem bit_eq_testBit (x : UInt8) (j : Nat) (hj : j < 8) :
    ((x >>> j.toUInt8) &&& 1 == 1) = x.toNat.testBit j := by
  have hj8 : j.toUInt8.toNat % 8 = j := by
    have hjn : j.toUInt8.toNat = j := by simp only [Nat.toUInt8, UInt8.toNat_ofNat']; omega
    omega
  have key : ((x >>> j.toUInt8) &&& 1).toNat = x.toNat / 2 ^ j % 2 := by
    rw [UInt8.toNat_and, UInt8.toNat_shiftRight, hj8, UInt8.toNat_one, Nat.and_one_is_mod,
      Nat.shiftRight_eq_div_pow]
  rw [Nat.testBit_eq_decide_div_mod_eq, ← key]
  apply Bool.eq_iff_iff.mpr
  simp only [beq_iff_eq, decide_eq_true_eq, ← UInt8.toNat_inj, UInt8.toNat_one]

theorem toNat_or_bit (c : UInt8) (j : Nat) (hj : j < 8) :
    (c ||| 1 <<< j.toUInt8).toNat = c.toNat ||| 2 ^ j := by
  have hj8 : j.toUInt8.toNat % 8 = j := by
    have hjn : j.toUInt8.toNat = j := by simp only [Nat.toUInt8, UInt8.toNat_ofNat']; omega
    omega
  have hp : 2 ^ j ≤ 2 ^ 7 := Nat.pow_le_pow_right (by decide) (by omega)
  rw [UInt8.toNat_or, UInt8.toNat_shiftLeft, hj8, UInt8.toNat_one, Nat.shiftLeft_eq, Nat.one_mul,
    Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt hp (by decide))]

/-- A byte built by setting bit `t` wherever `c t` holds. -/
theorem foldl_setBit (c : Nat → Bool) (l : List Nat) (hl : ∀ t ∈ l, t < 8) (a : UInt8) (j : Nat) :
    (l.foldl (fun byte t => if c t then byte ||| (1 <<< t.toUInt8) else byte) a).toNat.testBit j =
      (a.toNat.testBit j || l.any fun t => decide (t = j) && c t) := by
  induction l generalizing a with
  | nil => simp
  | cons t l ih =>
    rw [List.foldl_cons, ih (fun s hs => hl s (List.mem_cons_of_mem _ hs)), List.any_cons]
    cases hc : c t
    · simp only [Bool.false_eq_true, ↓reduceIte, Bool.and_false, Bool.false_or]
    · simp only [↓reduceIte, Bool.and_true]
      rw [toNat_or_bit _ _ (hl t List.mem_cons_self), Nat.testBit_or, Nat.testBit_two_pow, Bool.or_assoc]

/-- **`memberVec`'s bitmap is membership in the decoded haystack**: bit `i` is set exactly when `i` is
below the needle count and needle `i` is among the haystack's elements, so the last byte's tail bits
are zero: at a width up to eight compared by key, and above eight by its bytes whole. -/
theorem memberVec_mem (w : USize) (float : Bool) (xs hay : ByteArray)
    (hn : hay.size / w.toNat < USize.size) :
    (memberVec w float xs hay).size = (xs.size / w.toNat + 7) / 8 ∧
    ∀ i < 8 * ((xs.size / w.toNat + 7) / 8), Column.bitAt (memberVec w float xs hay) i =
      (decide (i < xs.size / w.toNat) &&
        if w.toNat ≤ 8 then decide (normalise w.toNat float (Column.bitsAt xs (i * w.toNat) w.toNat) ∈
          (elemsW w.toNat hay).map (normalise w.toNat float))
        else decide ((xs.extract (i * w.toNat) (i * w.toNat + w.toNat)).data.toList ∈
          (List.range (hay.size / w.toNat)).map fun k =>
            (hay.extract (k * w.toNat) (k * w.toNat + w.toNat)).data.toList)) := by
  let C : Nat → Bool := fun i => decide (i < xs.size / w.toNat) &&
    if w.toNat ≤ 8 then decide (findScalar w float hay (Column.bitsAt xs (i * w.toNat) w.toNat) < (hay.size / w.toNat).toUSize)
    else decide (((List.range (hay.size / w.toNat)).find? fun k =>
      (hay.extract (k * w.toNat) (k * w.toNat + w.toNat)).data.toList
        == (xs.extract (i * w.toNat) (i * w.toNat + w.toNat)).data.toList).getD (hay.size / w.toNat) < hay.size / w.toNat)
  let B : Nat → UInt8 := fun b =>
    (List.range 8).foldl (fun byte t => if C (b * 8 + t) then byte ||| (1 <<< t.toUInt8) else byte) 0
  have hf : memberVec w float xs hay =
      (List.range ((xs.size / w.toNat + 7) / 8)).foldl (fun acc b => acc.push (B b)) ByteArray.empty := rfl
  obtain ⟨hs, -, hg⟩ := foldl_push8 B (List.range ((xs.size / w.toNat + 7) / 8)) ByteArray.empty
  rw [hf]
  refine ⟨by simpa using hs, fun i hi => ?_⟩
  have hb : i / 8 < (xs.size / w.toNat + 7) / 8 := by omega
  have h := hg (i / 8) (by simpa using hb)
  simp only [ByteArray.size_empty, Nat.zero_add, List.getElem_range] at h
  have hm8 : i % 8 < 8 := Nat.mod_lt _ (by decide)
  have hbit : Column.bitAt ((List.range ((xs.size / w.toNat + 7) / 8)).foldl (fun acc b => acc.push (B b))
      ByteArray.empty) i = C i := by
    simp only [Column.bitAt, h, Option.getD_some]
    rw [bit_eq_testBit _ _ hm8, foldl_setBit _ _ (fun t ht => List.mem_range.1 ht), UInt8.toNat_zero,
      Nat.zero_testBit, Bool.false_or]
    apply Bool.eq_iff_iff.mpr
    rw [List.any_eq_true]
    constructor
    · rintro ⟨t, -, ht⟩
      rw [Bool.and_eq_true, decide_eq_true_eq] at ht
      obtain ⟨e, hc⟩ := ht
      subst e
      rwa [Nat.mul_comm, Nat.div_add_mod] at hc
    · intro hc
      refine ⟨i % 8, List.mem_range.2 hm8, ?_⟩
      rw [Bool.and_eq_true, decide_eq_true_eq, Nat.mul_comm, Nat.div_add_mod]
      exact ⟨rfl, hc⟩
  rw [hbit]
  simp only [C]
  congr 1
  by_cases hw : w.toNat ≤ 8
  · simp only [hw, ↓reduceIte]
    apply decide_eq_decide.mpr
    rw [USize.lt_iff_toNat_lt, findScalar_idxOf w float hay _ hn, USize.toNat_ofNat_of_lt' hn, ← idxOf_lt_length]
    simp only [elemsW, List.length_map, List.length_range]
  · simp only [hw, ↓reduceIte]
    apply decide_eq_decide.mpr
    rw [find?_range_getD, ← idxOf_lt_length]
    simp only [List.length_map, List.length_range]

end Rel.Verify
