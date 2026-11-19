import Rel.KernelSpec.FindMember
import Rel.KernelSpec.Encoding
import Rel.KernelSpec.Group
import Rel.Kernel.Sort
import Rel.Kernel.Structural
import Rel.Kernel.Value
import Rel.Kernel.Search

/-! The part of `Rel.Verify.Ids` the Rel kernels reach; `Rel.Verify.Ids` imports it. -/


namespace Rel.Verify
open Rel Rel.Kernel

/-- An id read at `w` bits is below `2 ^ w`: each byte's contribution is cut to `w` bits. -/
theorem idAt_lt (ids : ByteArray) (w i : Nat) (hw : w ≤ 64) : Column.idAt ids w i < 2 ^ w := by
  unfold Column.idAt Column.resAt
  generalize List.range' _ _ = l
  suffices h : ∀ (a : UInt64), a.toNat < 2 ^ w → (l.foldl (fun acc k =>
      acc ||| ((ids[0 + k]?.getD 0).toNat * 2 ^ (8 * k) / 2 ^ (i * w) % 2 ^ w).toUInt64) a).toNat < 2 ^ w from
    h 0 (Nat.two_pow_pos _)
  induction l with
  | nil => exact fun a ha => ha
  | cons k l ih =>
    intro a ha
    apply ih
    have ht : ((ids[0 + k]?.getD 0).toNat * 2 ^ (8 * k) / 2 ^ (i * w) % 2 ^ w) < 2 ^ w := Nat.mod_lt _ (Nat.two_pow_pos _)
    have h64 : 2 ^ w ≤ 2 ^ 64 := Nat.pow_le_pow_right (by decide) hw
    rw [UInt64.toNat_or, Nat.toUInt64_eq, UInt64.toNat_ofNat', Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le ht h64)]
    exact Nat.or_lt_two_pow ha ht

/-- `idsCap` never exceeds the count asked for. -/
theorem idsCap_le (ids : ByteArray) (w n : Nat) : Column.idsCap ids w n ≤ n := by
  unfold Column.idsCap; split
  · exact Nat.le_refl n
  · exact Nat.min_le_left _ _

/-- `packIds` at a whole-byte lane `8c`: `c` bytes an id, id `i` read back as `bitsAt` reads `c` bytes. -/
theorem packIds_bytes (c m : Nat) (f : Nat → Nat) (hc : 1 ≤ c) (hc8 : c ≤ 8) :
    (Column.packIds (8 * c) m f).size = c * m ∧
    ∀ i < m, f i < 2 ^ (8 * c) → Column.bitsAt (Column.packIds (8 * c) m f) (i * c) c = (f i).toUInt64 := by
  have hp : Column.packIds (8 * c) m f = (List.range m).foldl (fun acc i => Column.pushBits acc (f i).toUInt64 c)
      (ByteArray.emptyWithCapacity (m * c)) := by
    unfold Column.packIds
    rw [if_pos (by omega : 8 ≤ 8 * c), show 8 * c / 8 = c by omega, fold_eq_foldl_range]
  obtain ⟨hs, -, hg⟩ := foldl_pushBits (fun i => (f i).toUInt64) c hc8 (List.range m) (ByteArray.emptyWithCapacity (m * c))
  have he : (ByteArray.emptyWithCapacity (m * c)).size = 0 := rfl
  rw [hp]
  refine ⟨by rw [hs, he, List.length_range, Nat.zero_add], fun i hi hf => ?_⟩
  have h := hg i (by simpa using hi)
  simp only [List.getElem_range, he, Nat.zero_add] at h
  have hf64 := Nat.lt_of_lt_of_le hf (Nat.pow_le_pow_right (by decide) (by omega) : 2 ^ (8 * c) ≤ 2 ^ 64)
  rw [Nat.mul_comm i c, h, Nat.toUInt64_eq, UInt64.toNat_ofNat', Nat.mod_eq_of_lt hf64, Nat.mod_eq_of_lt hf]

/-- `idKeyWidth` at two lanes is a whole-byte search width holding both. -/
theorem idKeyWidth_spec (a b : USize) (ha : a.toNat ≤ 64) (hb : b.toNat ≤ 64) :
    ∃ c, (idKeyWidth a b).toNat = c ∧ (c = 1 ∨ c = 2 ∨ c = 4 ∨ c = 8) ∧ a.toNat ≤ 8 * c ∧ b.toNat ≤ 8 * c := by
  have lit : ∀ k, k < 2 ^ 32 → (USize.ofNat k).toNat = k := fun k hk =>
    USize.toNat_ofNat_of_lt' (Nat.lt_of_lt_of_le hk USize.le_size)
  have h8 : (8 : USize).toNat = 8 := lit 8 (by decide)
  have h16 : (16 : USize).toNat = 16 := lit 16 (by decide)
  have h32 : (32 : USize).toNat = 32 := lit 32 (by decide)
  have hm : (max a b).toNat = max a.toNat b.toNat := by
    show (if a ≤ b then b else a).toNat = _
    rw [Nat.max_def]
    by_cases h : a ≤ b
    · rw [if_pos h, if_pos (USize.le_iff_toNat_le.1 h)]
    · rw [if_neg h, if_neg (mt USize.le_iff_toNat_le.2 h)]
  have e : ∀ (k : USize) (K : Nat), k.toNat = K → (max a b ≤ k ↔ a.toNat ≤ K ∧ b.toNat ≤ K) := fun k K hK => by
    rw [USize.le_iff_toNat_le, hm, hK, Nat.max_le]
  unfold idKeyWidth
  by_cases c1 : max a b ≤ 8
  · rw [if_pos c1]; have := (e 8 8 h8).1 c1; exact ⟨1, lit 1 (by decide), by decide, by omega, by omega⟩
  rw [if_neg c1]
  by_cases c2 : max a b ≤ 16
  · rw [if_pos c2]; have := (e 16 16 h16).1 c2; exact ⟨2, lit 2 (by decide), by decide, by omega, by omega⟩
  rw [if_neg c2]
  by_cases c3 : max a b ≤ 32
  · rw [if_pos c3]; have := (e 32 32 h32).1 c3; exact ⟨4, lit 4 (by decide), by decide, by omega, by omega⟩
  rw [if_neg c3]
  exact ⟨8, lit 8 (by decide), by decide, by omega, by omega⟩

/-- `idsOperand` at a whole-byte width `c` holding the lane: `c` bytes an id, and id `i` is the
payload's `idAt` read. -/
theorem idsOperand_bytes (k w : USize) (ids : ByteArray) (n : USize) (c : Nat) (hk : k.toNat = c)
    (hc : c = 1 ∨ c = 2 ∨ c = 4 ∨ c = 8) (hw : w.toNat ≤ 8 * c) :
    (idsOperand k w ids n).size = c * Column.idsCap ids w.toNat n.toNat ∧
    ∀ i < Column.idsCap ids w.toNat n.toNat,
      Column.bitsAt (idsOperand k w ids n) (i * c) c = (Column.idAt ids w.toNat i).toUInt64 := by
  have hc1 : 1 ≤ c := by omega
  obtain ⟨hs, hg⟩ := packIds_bytes c (Column.idsCap ids w.toNat n.toNat) (Column.idAt ids w.toNat) hc1 (by omega)
  unfold idsOperand
  rw [hk]
  exact ⟨hs, fun i hi => hg i hi (Nat.lt_of_lt_of_le (idAt_lt ids _ i (by omega)) (Nat.pow_le_pow_right (by decide) hw))⟩

/-- An operand's decoded elements are its ids as `UInt64`s. -/
theorem elemsW_idsOperand (k w : USize) (ids : ByteArray) (n : USize) (c : Nat) (hk : k.toNat = c)
    (hc : c = 1 ∨ c = 2 ∨ c = 4 ∨ c = 8) (hw : w.toNat ≤ 8 * c) :
    elemsW c (idsOperand k w ids n) =
      ((List.range (Column.idsCap ids w.toNat n.toNat)).map (Column.idAt ids w.toNat)).map Nat.toUInt64 := by
  obtain ⟨hs, hg⟩ := idsOperand_bytes k w ids n c hk hc hw
  rw [elemsW, hs, Nat.mul_div_cancel_left _ (by omega), List.map_map]
  exact List.map_congr_left fun i hi => hg i (List.mem_range.1 hi)

/-- `Nat.toUInt64` is injective below `2 ^ 64`, so a search through it is the search on `Nat`s. -/
theorem toUInt64_beq {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) : (a.toUInt64 == b.toUInt64) = (a == b) := by
  apply Bool.eq_iff_iff.2
  rw [beq_iff_eq, beq_iff_eq, ← UInt64.toNat_inj, Nat.toUInt64_eq, Nat.toUInt64_eq, UInt64.toNat_ofNat',
    UInt64.toNat_ofNat', Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb]

theorem idxOf_toUInt64 (l : List Nat) (y : Nat) (hl : ∀ a ∈ l, a < 2 ^ 64) (hy : y < 2 ^ 64) :
    (l.map Nat.toUInt64).idxOf y.toUInt64 = l.idxOf y := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [List.map_cons, List.idxOf_cons, List.idxOf_cons, toUInt64_beq (hl a List.mem_cons_self) hy,
      ih fun x hx => hl x (List.mem_cons_of_mem _ hx)]

theorem mem_toUInt64 (l : List Nat) (y : Nat) (hl : ∀ a ∈ l, a < 2 ^ 64) (hy : y < 2 ^ 64) :
    y.toUInt64 ∈ l.map Nat.toUInt64 ↔ y ∈ l := by
  rw [← idxOf_lt_length, ← idxOf_lt_length, idxOf_toUInt64 l y hl hy, List.length_map]

/-- The ids of a payload at a lane are below `2 ^ 64`. -/
theorem ids_lt64 (ids : ByteArray) (w n : Nat) (hw : w ≤ 64) :
    ∀ a ∈ (List.range (Column.idsCap ids w n)).map (Column.idAt ids w), a < 2 ^ 64 := fun a ha => by
  obtain ⟨i, -, rfl⟩ := List.mem_map.1 ha
  exact Nat.lt_of_lt_of_le (idAt_lt ids w i hw) (Nat.pow_le_pow_right (by decide) hw)

/-- **`findIdsVec` answers, at needle `j`, the first haystack index whose id is the needle's**, and
the haystack's id count when none is: eight bytes a needle, one per id the needle payload holds. -/
theorem findIdsVec_idxOf (hw nw hn nn : USize) (hay ndl : ByteArray)
    (hhw : hw.toNat = 0 ∨ hw.toNat = 1 ∨ hw.toNat = 2 ∨ hw.toNat = 4 ∨ hw.toNat = 8 ∨ hw.toNat = 16 ∨
      hw.toNat = 32 ∨ hw.toNat = 64)
    (hnw : nw.toNat = 0 ∨ nw.toNat = 1 ∨ nw.toNat = 2 ∨ nw.toNat = 4 ∨ nw.toNat = 8 ∨ nw.toNat = 16 ∨
      nw.toNat = 32 ∨ nw.toNat = 64) :
    (findIdsVec hw hay hn nw ndl nn).size = 8 * Column.idsCap ndl nw.toNat nn.toNat ∧
    ∀ j < Column.idsCap ndl nw.toNat nn.toNat,
      (Column.bitsAt (findIdsVec hw hay hn nw ndl nn) (j * 8) 8).toNat =
        ((List.range (Column.idsCap hay hw.toNat hn.toNat)).map (Column.idAt hay hw.toNat)).idxOf
          (Column.idAt ndl nw.toNat j) := by
  have hh64 : hw.toNat ≤ 64 := by omega
  have hn64 : nw.toNat ≤ 64 := by omega
  obtain ⟨c, hk, hc, hhc, hnc⟩ := idKeyWidth_spec hw nw hh64 hn64
  obtain ⟨hHs, -⟩ := idsOperand_bytes (idKeyWidth hw nw) hw hay hn c hk hc hhc
  obtain ⟨hNs, hNg⟩ := idsOperand_bytes (idKeyWidth hw nw) nw ndl nn c hk hc hnc
  have hc0 : 0 < c := by omega
  have hsz : (idsOperand (idKeyWidth hw nw) hw hay hn).size / (idKeyWidth hw nw).toNat < USize.size := by
    rw [hHs, hk, Nat.mul_div_cancel_left _ hc0]
    exact Nat.lt_of_le_of_lt (idsCap_le _ _ _) hn.toNat_lt_size
  obtain ⟨hs, hg⟩ := findVec_idxOf (idKeyWidth hw nw) false _ _ hsz
  have hfv : findIdsVec hw hay hn nw ndl nn = findVec (idKeyWidth hw nw) false
      (idsOperand (idKeyWidth hw nw) hw hay hn) (idsOperand (idKeyWidth hw nw) nw ndl nn) := rfl
  have hnorm : ∀ v, normalise c false v = v := fun _ => rfl
  rw [hfv]
  rw [hk, hNs, Nat.mul_div_cancel_left _ hc0] at hs hg
  refine ⟨hs, fun j hj => ?_⟩
  rw [hg j hj, if_pos (by omega), hnorm, List.map_congr_left (fun v _ => hnorm v), List.map_id',
    elemsW_idsOperand _ hw hay hn c hk hc hhc, hNg j hj,
    idxOf_toUInt64 _ _ (ids_lt64 hay _ _ hh64)
      (Nat.lt_of_lt_of_le (idAt_lt ndl _ j hn64) (Nat.pow_le_pow_right (by decide) hn64))]

/-- **`memberIdsVec` answers, at needle `i`, whether some haystack id is the needle's**, as a bitmap
whose bits past the needle count are zero. -/
theorem memberIdsVec_mem (xw hw xn hn : USize) (xs hay : ByteArray)
    (hxw : xw.toNat = 0 ∨ xw.toNat = 1 ∨ xw.toNat = 2 ∨ xw.toNat = 4 ∨ xw.toNat = 8 ∨ xw.toNat = 16 ∨
      xw.toNat = 32 ∨ xw.toNat = 64)
    (hhw : hw.toNat = 0 ∨ hw.toNat = 1 ∨ hw.toNat = 2 ∨ hw.toNat = 4 ∨ hw.toNat = 8 ∨ hw.toNat = 16 ∨
      hw.toNat = 32 ∨ hw.toNat = 64) :
    (memberIdsVecBitmap xw xs xn hw hay hn).size = (Column.idsCap xs xw.toNat xn.toNat + 7) / 8 ∧
    ∀ i < 8 * ((Column.idsCap xs xw.toNat xn.toNat + 7) / 8),
      Column.bitAt (memberIdsVecBitmap xw xs xn hw hay hn) i =
        (decide (i < Column.idsCap xs xw.toNat xn.toNat) &&
          decide (Column.idAt xs xw.toNat i ∈
            (List.range (Column.idsCap hay hw.toNat hn.toNat)).map (Column.idAt hay hw.toNat))) := by
  have hx64 : xw.toNat ≤ 64 := by omega
  have hh64 : hw.toNat ≤ 64 := by omega
  obtain ⟨c, hk, hc, hxc, hhc⟩ := idKeyWidth_spec xw hw hx64 hh64
  obtain ⟨hXs, hXg⟩ := idsOperand_bytes (idKeyWidth xw hw) xw xs xn c hk hc hxc
  obtain ⟨hHs, -⟩ := idsOperand_bytes (idKeyWidth xw hw) hw hay hn c hk hc hhc
  have hc0 : 0 < c := by omega
  have hsz : (idsOperand (idKeyWidth xw hw) hw hay hn).size / (idKeyWidth xw hw).toNat < USize.size := by
    rw [hHs, hk, Nat.mul_div_cancel_left _ hc0]
    exact Nat.lt_of_le_of_lt (idsCap_le _ _ _) hn.toNat_lt_size
  obtain ⟨hs, hg⟩ := memberVec_mem (idKeyWidth xw hw) false _ _ hsz
  have hmv : memberIdsVecBitmap xw xs xn hw hay hn = memberVecBitmap (idKeyWidth xw hw) false
      (idsOperand (idKeyWidth xw hw) xw xs xn) (idsOperand (idKeyWidth xw hw) hw hay hn) := rfl
  have hnorm : ∀ v, normalise c false v = v := fun _ => rfl
  rw [hmv]
  rw [hk, hXs, Nat.mul_div_cancel_left _ hc0] at hs hg
  refine ⟨hs, fun i hi => ?_⟩
  rw [hg i hi, if_pos (by omega)]
  by_cases hix : i < Column.idsCap xs xw.toNat xn.toNat
  · simp only [hix, decide_true, Bool.true_and]
    rw [hnorm, List.map_congr_left (fun v _ => hnorm v), List.map_id', elemsW_idsOperand _ hw hay hn c hk hc hhc,
      hXg i hix]
    exact decide_eq_decide.2 (mem_toUInt64 _ _ (ids_lt64 hay _ _ hh64)
      (Nat.lt_of_lt_of_le (idAt_lt xs _ i hx64) (Nat.pow_le_pow_right (by decide) hx64)))
  · simp only [hix, decide_false, Bool.false_and]

/-- info: 'Rel.Verify.findIdsVec_idxOf' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms findIdsVec_idxOf

/-- info: 'Rel.Verify.memberIdsVec_mem' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms memberIdsVec_mem

/-- **`memberBits`' bit `i` is set exactly when `i` is below the needle count and needle bit `i` is
one of the haystack's bits**, so the last byte's tail bits are zero. -/
theorem memberBits_mem (m n : USize) (xs hay : ByteArray) :
    (memberBitsBitmap m xs n hay).size = (m.toNat + 7) / 8 ∧
    ∀ i < 8 * ((m.toNat + 7) / 8), Column.bitAt (memberBitsBitmap m xs n hay) i =
      (decide (i < m.toNat) && decide (Column.bitAt xs i ∈ (List.range n.toNat).map (Column.bitAt hay))) := by
  let C : Nat → Bool := fun i => decide (i < m.toNat) && decide (findBit n hay (Column.bitAt xs i) < n)
  let B : Nat → UInt8 := fun b =>
    (List.range 8).foldl (fun byte t => if C (b * 8 + t) then byte ||| (1 <<< t.toUInt8) else byte) 0
  have hf : memberBitsBitmap m xs n hay =
      (List.range ((m.toNat + 7) / 8)).foldl (fun acc b => acc.push (B b)) ByteArray.empty := rfl
  obtain ⟨hs, -, hg⟩ := foldl_push8 B (List.range ((m.toNat + 7) / 8)) ByteArray.empty
  rw [hf]
  refine ⟨by simpa using hs, fun i hi => ?_⟩
  have hb : i / 8 < (m.toNat + 7) / 8 := by omega
  have h := hg (i / 8) (by simpa using hb)
  simp only [ByteArray.size_empty, Nat.zero_add, List.getElem_range] at h
  have hm8 : i % 8 < 8 := Nat.mod_lt _ (by decide)
  have hbit : Column.bitAt ((List.range ((m.toNat + 7) / 8)).foldl (fun acc b => acc.push (B b))
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
  apply decide_eq_decide.mpr
  have hl := idxOf_le_length (Column.bitAt xs i) ((List.range n.toNat).map (Column.bitAt hay))
  rw [List.length_map, List.length_range] at hl
  unfold findBit
  rw [USize.lt_iff_toNat_lt, find?_range_getD, USize.toNat_ofNat_of_lt' (Nat.lt_of_le_of_lt hl n.toNat_lt_size),
    ← idxOf_lt_length, List.length_map, List.length_range]

/-- info: 'Rel.Verify.memberBits_mem' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms memberBits_mem

/-- A search over `List.range n` that answers `n` matched nowhere. -/
theorem find?_toUSize {f : Nat → Bool} {n : USize}
    (h : (((List.range n.toNat).find? f).getD n.toNat).toUSize = n) : ∀ i < n.toNat, f i = false := by
  cases hf : (List.range n.toNat).find? f with
  | none => exact fun i hi => Bool.eq_false_iff.2 (List.find?_eq_none.1 hf i (List.mem_range.2 hi))
  | some k =>
    have hk := List.mem_range.1 (List.mem_of_find?_eq_some hf)
    rw [hf, Option.getD_some] at h
    have := congrArg USize.toNat h
    rw [USize.toNat_ofNat_of_lt' (Nat.lt_trans hk n.toNat_lt_size)] at this
    omega

/-- **`enumIds`' id at row `i` is the row's domain index**, and `nullId` at `0Nj`, wherever its second
component reports every row in range: the ids are packed at a lane `w` holding the domain and `nullId`. -/
theorem enumIds_idAt (n d nullId w : USize) (b : ByteArray)
    (hw : w.toNat = 0 ∨ w.toNat = 1 ∨ w.toNat = 2 ∨ w.toNat = 4 ∨ w.toNat = 8 ∨ w.toNat = 16 ∨
      w.toNat = 32 ∨ w.toNat = 64)
    (hd : d.toNat ≤ 2 ^ w.toNat) (hnull : nullId.toNat < 2 ^ w.toNat)
    (hok : (enumIds n d nullId w b).2 = n) {i : Nat} (hi : i < n.toNat) :
    Column.idAt (enumIds n d nullId w b).1 w.toNat i =
      if (Column.bitsAt b (i * 8) 8).toInt64 = Int64.minValue then nullId.toNat
      else (Column.bitsAt b (i * 8) 8).toInt64.toInt.toNat := by
  unfold enumIds at hok
  have hall := find?_toUSize hok i hi
  unfold enumIds
  by_cases hn : (Column.bitsAt b (i * 8) 8).toInt64 = Int64.minValue
  · rw [idAt_packIds hw hi (by simp only [hn]; exact hnull)]
    rw [if_pos hn]; exact if_pos (decide_eq_true hn : ((Column.bitsAt b (i * 8) 8).toInt64 == Int64.minValue) = true)
  · have hlt : (Column.bitsAt b (i * 8) 8).toInt64.toInt.toNat < d.toNat := by
      have hne : ((Column.bitsAt b (i * 8) 8).toInt64 != Int64.minValue) = true := by
        show (!decide (_ = _)) = true; rw [decide_eq_false hn]; rfl
      rw [hne, Bool.true_and] at hall
      cases hc : (decide (0 ≤ (Column.bitsAt b (i * 8) 8).toInt64) &&
          decide ((Column.bitsAt b (i * 8) 8).toInt64.toInt.toNat < d.toNat))
      · rw [hc] at hall; exact absurd hall (by decide)
      · rw [Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq] at hc; exact hc.2
    have hb : ((Column.bitsAt b (i * 8) 8).toInt64 == Int64.minValue) = false := decide_eq_false hn
    rw [idAt_packIds hw hi (by simp only [hb, Bool.false_eq_true, ↓reduceIte]; exact Nat.lt_of_lt_of_le hlt hd)]
    simp only [hb, hn, Bool.false_eq_true, ↓reduceIte]

/-- info: 'Rel.Verify.enumIds_idAt' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms enumIds_idAt

/-- An id below `L` fits the width `idWidthOf L` packs at, for any count a `USize` holds. -/
theorem lt_two_pow_idWidthOf {L k : Nat} (hL : L ≤ 2 ^ 64) (hk : k < L) : k < 2 ^ Column.idWidthOf L := by
  unfold Column.idWidthOf Column.widthFor
  by_cases h0 : L - 1 = 0
  · rw [if_pos h0]; have : k = 0 := by omega
    subst this; exact Nat.two_pow_pos _
  rw [if_neg h0]
  have h1 := Nat.lt_log2_self (n := L - 1)
  have h2 : (L - 1).log2 < 64 := (Nat.log2_lt h0).2 (by omega)
  have h3 : (L - 1).log2 + 1 ≤ Column.laneWidth ((L - 1).log2 + 1) := by
    unfold Column.laneWidth; repeat' split
    all_goals omega
  exact Nat.lt_of_lt_of_le (by omega) (Nat.pow_le_pow_right (by decide) h3 |> Nat.le_trans (Nat.le_refl _) |>
    fun h => Nat.le_trans (Nat.succ_le_of_lt h1) h)

/-- **`idGroups` gives two rows one group id exactly when their ids name one dictionary entry**
(`idKey`, every id past the dictionary being the one empty symbol), read at the width it packs at. -/
theorem idGroups_eq_iff (d n w : USize) (ids : ByteArray) {i j : Nat} (hi : i < n.toNat) (hj : j < n.toNat) :
    Column.idAt (Order.idGroups d n w ids).1 (Column.idWidthOf (Order.idFirsts d.toNat n.toNat w.toNat ids).length) i =
      Column.idAt (Order.idGroups d n w ids).1
        (Column.idWidthOf (Order.idFirsts d.toNat n.toNat w.toNat ids).length) j ↔
    Order.idKey d.toNat ids w.toNat i = Order.idKey d.toNat ids w.toNat j := by
  have hb : ∀ a c : Nat, (a == c) = decide (a = c) := fun a c => Bool.eq_iff_iff.2 (by rw [beq_iff_eq, decide_eq_true_iff])
  have hF : Order.idFirsts d.toNat n.toNat w.toNat ids = firstsOf (Order.idKey d.toNat ids w.toNat) n.toNat := by
    simp only [Order.idFirsts, firstsOf, bne, hb]
  have hG : (Order.idGroups d n w ids).1 = Column.packIds (Column.idWidthOf (firstsOf (Order.idKey d.toNat ids w.toNat)
      n.toNat).length) n.toNat (groupOf (Order.idKey d.toNat ids w.toNat) n.toNat) := by
    simp only [Order.idGroups, hF, hb]; rfl
  have hW := laneWidth_cases (Column.widthFor ((firstsOf (Order.idKey d.toNat ids w.toNat) n.toNat).length - 1))
  simp only [show ∀ x, Column.laneWidth (Column.widthFor (x - 1)) = Column.idWidthOf x from fun _ => rfl] at hW
  have hL : (firstsOf (Order.idKey d.toNat ids w.toNat) n.toNat).length ≤ 2 ^ 64 := by
    have := List.length_filter_le (fun i => (List.range i).all fun j =>
      !decide (Order.idKey d.toNat ids w.toNat j = Order.idKey d.toNat ids w.toNat i)) (List.range n.toNat)
    rw [List.length_range] at this
    exact Nat.le_trans this (Nat.le_of_lt (usize_lt n))
  rw [hF, hG, idAt_packIds hW hi (lt_two_pow_idWidthOf hL (groupOf_lt hi)),
    idAt_packIds hW hj (lt_two_pow_idWidthOf hL (groupOf_lt hj)),
    groupOf_eq_iff (g := Order.idKey d.toNat ids w.toNat) hi (groupOf_lt hj), groupOf_get (g := Order.idKey d.toNat ids w.toNat) hj]

/-- info: 'Rel.Verify.idGroups_eq_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms idGroups_eq_iff

end Rel.Verify
