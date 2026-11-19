import Rel.KernelSpec.Encoding
import Rel.KernelSpec.Group
import Rel.Kernel.Need
import Rel.Kernel.Sort
import Rel.Kernel.Coc
import Rel.Kernel.Scan
import Rel.Kernel.Value
import Rel.Kernel.Search

/-! The part of `Rel.Verify.Codes` the Rel kernels reach; `Rel.Verify.Codes` imports it. -/


open Rel.Ext
namespace Rel.Verify

open Rel Rel.Kernel
open Rel.Kernel.Scan (Kind)

/-- Two indices share a group exactly when they share a key. -/
theorem groupOf_iff {α : Type} [DecidableEq α] {g : Nat → α} {m i j : Nat} (hi : i < m) (hj : j < m) :
    groupOf g m i = groupOf g m j ↔ g i = g j :=
  ⟨fun e => ((groupOf_eq_iff hi (groupOf_lt hj)).1 e).trans (groupOf_get hj),
   fun e => (groupOf_eq_iff hi (groupOf_lt hj)).2 (e.trans (groupOf_get hj).symm)⟩

/-- Every id below `n` fits the width `idWidthOf n` packs it at, for any count a `USize` holds. -/
theorem lt_idWidthOf {x n : Nat} (hx : x < n) (hn : n ≤ 2 ^ 64) : x < 2 ^ Column.idWidthOf n := by
  unfold Column.idWidthOf Column.widthFor
  split
  · exact Nat.lt_of_lt_of_le (show x < 1 by omega) (Nat.one_le_two_pow)
  · rename_i h0
    have hl := widthFor_le (n - 1) (by omega)
    rw [Column.widthFor, if_neg h0] at hl
    have hlane : Nat.log2 (n - 1) + 1 ≤ Column.laneWidth (Nat.log2 (n - 1) + 1) := by
      unfold Column.laneWidth; repeat' split
      all_goals omega
    exact Nat.lt_of_le_of_lt (Nat.le_sub_one_of_lt hx)
      (Nat.lt_of_lt_of_le Nat.lt_log2_self (Nat.pow_le_pow_right (by decide) hlane))

/-- The kernels' `firstsBy` (a `BEq` key) is the specification's `firstsOf` at a lawful one. -/
theorem firstsBy_eq {α : Type} [BEq α] [LawfulBEq α] [DecidableEq α] (m : Nat) (key : Nat → α) :
    Order.firstsBy m key = firstsOf key m := by
  have hb : ∀ a b : α, (a != b) = !decide (a = b) := fun a b => by
    rw [bne, Bool.eq_iff_iff.2 (show (a == b) = true ↔ decide (a = b) = true by rw [beq_iff_eq, decide_eq_true_iff])]
  unfold Order.firstsBy firstsOf; simp only [hb]

/-- The kernels' group rule (`groupIn` over `firstsBy`, a `BEq` key) is the specification's `groupOf` at a lawful one. -/
theorem groupIn_firstsBy {α : Type} [BEq α] [LawfulBEq α] [DecidableEq α] (m : Nat) (key : Nat → α) (i : Nat) :
    Order.groupIn (Order.firstsBy m key) key i = groupOf key m i := by
  have hb : ∀ a b : α, (a == b) = decide (a = b) := fun a b => Bool.eq_iff_iff.2 (by
    rw [beq_iff_eq, decide_eq_true_iff])
  simp only [Order.groupIn, groupOf, firstsBy_eq, hb]

/-- **`idsBy` read back**: the ids are `groupOf`, packed at the width of the first occurrences' count,
and the second payload holds one long per first occurrence. -/
theorem idsBy_spec {α : Type} [BEq α] [LawfulBEq α] [DecidableEq α] (m : Nat) (key : Nat → α) :
    (Order.idsBy m key).1 = Column.packIds (Column.idWidthOf (firstsOf key m).length) m (groupOf key m) ∧
      (Order.idsBy m key).2.size = 8 * (firstsOf key m).length := by
  have hf := firstsBy_eq m key
  refine ⟨?_, ?_⟩
  · show Column.packIds (Column.idWidthOf (Order.firstsBy m key).length) m
      (Order.groupIn (Order.firstsBy m key) key) = _
    rw [show Order.groupIn (Order.firstsBy m key) key = groupOf key m from funext (groupIn_firstsBy m key), hf]
  · show (Order.indices (Order.firstsBy m key)).size = _
    obtain ⟨hs, -⟩ := foldl_pushBits (fun i : Nat => (Int64.ofNat i).toUInt64) 8 (by decide)
      (Order.firstsBy m key) ByteArray.empty
    rw [Order.indices, hs, hf]; simp

/-- **Equal ids exactly where the keys are equal**, the ids read at the width their own group count
gives, as `groupLongs` reads them. -/
theorem idsBy_iff {α : Type} [BEq α] [LawfulBEq α] {m : Nat} (hm : m < 2 ^ 64) (key : Nat → α)
    {i j : Nat} (hi : i < m) (hj : j < m) :
    Column.idAt (Order.idsBy m key).1 (Column.idWidthOf ((Order.idsBy m key).2.size / 8)) i =
        Column.idAt (Order.idsBy m key).1 (Column.idWidthOf ((Order.idsBy m key).2.size / 8)) j ↔
      key i = key j := by
  letI : DecidableEq α := instDecidableEqOfLawfulBEq
  obtain ⟨h1, h2⟩ := idsBy_spec m key
  have hl : (firstsOf key m).length ≤ m := by
    have := List.length_filter_le (fun i => (List.range i).all fun j => !decide (key j = key i)) (List.range m)
    rwa [List.length_range] at this
  have hw := laneWidth_cases (Column.widthFor ((firstsOf key m).length - 1))
  rw [show Column.laneWidth (Column.widthFor ((firstsOf key m).length - 1)) = Column.idWidthOf (firstsOf key m).length from rfl] at hw
  have hlt : ∀ x < m, groupOf key m x < 2 ^ Column.idWidthOf (firstsOf key m).length := fun x hx =>
    lt_idWidthOf (groupOf_lt hx) (by omega)
  rw [h2, Nat.mul_div_cancel_left _ (by decide), h1, idAt_packIds hw hi (hlt i hi), idAt_packIds hw hj (hlt j hj)]
  exact groupOf_iff hi hj

/-- **`groupIdsColumn`'s ids agree exactly where the elements do**, at every layout it claims, read at
the width `groupLongs` reads them: an interned column's ids (`idKey`, the dictionary index), a symbol
blob's ids once interned, and otherwise `Order.keyAt` over the payload `groupIds` numbers — the bitmap,
a Frame of Reference column decoded, or the dense bytes. At every integral kind
`keyAt_eq_iff` says two keys agree exactly when the stored bits do. -/
theorem groupIdsColumn_spec {t : QAtomicType} {n : USize} {e : Ext.Enc X} {p : ByteArray × ByteArray}
    (h : groupIdsColumn t n e = some p) :
    (∃ d dof ids, e = .enum d dof ids ∧ ∀ i < n.toNat, ∀ j < n.toNat,
      (Column.idAt p.1 (Column.idWidthOf (p.2.size / 8)) i = Column.idAt p.1 (Column.idWidthOf (p.2.size / 8)) j ↔
        Order.idKey (dof.size - 1) ids (Column.idWidth dof).toUSize.toNat i =
          Order.idKey (dof.size - 1) ids (Column.idWidth dof).toUSize.toNat j)) ∨
    (∃ blob offs, e = .syms blob offs ∧ ∃ db dof ids, Order.internSyms blob offs = (db, dof, ids) ∧
      ∀ i < n.toNat, ∀ j < n.toNat,
      (Column.idAt p.1 (Column.idWidthOf (p.2.size / 8)) i = Column.idAt p.1 (Column.idWidthOf (p.2.size / 8)) j ↔
        Order.idKey (dof.size - 1) ids (Column.idWidth dof).toUSize.toNat i =
          Order.idKey (dof.size - 1) ids (Column.idWidth dof).toUSize.toNat j)) ∨
    (∃ k u b, p = Order.groupIds k u b ∧
      ((t = .u1 ∧ k = .bit ∧ e = .bits b) ∨
        ((orderKind t = some k ∨ orderKind t = some .bit ∧ k = .u8) ∧
          ∃ md pk, e = .foR md pk ∧ b = Coc.decode k.width.toUSize md pk n) ∨
        (orderKind t = some k ∧ Enc.bytesOf t n e = some b)) ∧
      ∀ i < min u.toNat (k.avail b), ∀ j < min u.toNat (k.avail b),
        (Column.idAt p.1 (Column.idWidthOf (p.2.size / 8)) i = Column.idAt p.1 (Column.idWidthOf (p.2.size / 8)) j ↔
          Order.keyAt k b i = Order.keyAt k b j)) := by
  have keyed : ∀ k n b, (∀ i < min n.toNat (k.avail b), ∀ j < min n.toNat (k.avail b),
      (Column.idAt (Order.groupIds k n b).1 (Column.idWidthOf ((Order.groupIds k n b).2.size / 8)) i =
        Column.idAt (Order.groupIds k n b).1 (Column.idWidthOf ((Order.groupIds k n b).2.size / 8)) j ↔
          Order.keyAt k b i = Order.keyAt k b j)) := fun k n b i hi j hj =>
    idsBy_iff (Nat.lt_of_le_of_lt (Nat.min_le_left _ _) (usize_lt n)) (Order.keyAt k b) hi hj
  unfold groupIdsColumn at h
  split at h
  · simp only [needSize, need, stop] at h
    split at h
    · rename_i hd
      unfold Order.idGroups at h
      cases Option.some.inj h
      rw [USize.toNat_ofNat_of_lt' hd]
      exact Or.inl ⟨_, _, _, rfl, fun i hi j hj => idsBy_iff (usize_lt _) _ hi hj⟩
    · nomatch h
  · split at h
    simp only [needSize, need, stop] at h
    split at h
    · rename_i hd
      unfold Order.idGroups at h
      cases Option.some.inj h
      rw [USize.toNat_ofNat_of_lt' hd]
      exact Or.inr (Or.inl ⟨_, _, rfl, _, _, _, ‹_›, fun i hi j hj => idsBy_iff (usize_lt _) _ hi hj⟩)
    · nomatch h
  · cases Option.some.inj h
    exact Or.inr (Or.inr ⟨_, _, _, rfl, Or.inl ⟨rfl, rfl, rfl⟩, keyed _ _ _⟩)
  · split at h
    · nomatch h
    · rename_i k hk
      split at h
      · cases Option.some.inj h
        refine Or.inr (Or.inr ⟨_, _, _, rfl, Or.inr (Or.inl ⟨?_, _, _, rfl, rfl⟩), keyed _ _ _⟩)
        by_cases hb : k = .bit
        · subst hb; exact .inr ⟨hk, rfl⟩
        · exact .inl (by simp [hb, hk])
      · split at h
        · nomatch h
        · cases hb : Enc.bytesOf t n e with
          | none => rw [hb] at h; cases h
          | some b =>
            rw [hb] at h
            cases Option.some.inj h
            exact Or.inr (Or.inr ⟨_, _, _, rfl, Or.inr (Or.inr ⟨hk, rfl⟩), keyed _ _ _⟩)

/-- info: 'Rel.Verify.groupIdsColumn_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms groupIdsColumn_spec

/-- **`groupIdsPair`'s ids agree exactly where both codes do.** -/
theorem groupIdsPair_iff (k₁ k₂ : Kind) (n : USize) (a b : ByteArray) {i j : Nat}
    (hi : i < min n.toNat (min (k₁.avail a) (k₂.avail b))) (hj : j < min n.toNat (min (k₁.avail a) (k₂.avail b))) :
    Column.idAt (Order.groupIdsPair k₁ k₂ n a b).1 (Column.idWidthOf ((Order.groupIdsPair k₁ k₂ n a b).2.size / 8)) i =
        Column.idAt (Order.groupIdsPair k₁ k₂ n a b).1
          (Column.idWidthOf ((Order.groupIdsPair k₁ k₂ n a b).2.size / 8)) j ↔
      Order.keyAt k₁ a i = Order.keyAt k₁ a j ∧ Order.keyAt k₂ b i = Order.keyAt k₂ b j :=
  (idsBy_iff (Nat.lt_of_le_of_lt (Nat.min_le_left _ _) (usize_lt n)) (fun i => (Order.keyAt k₁ a i, Order.keyAt k₂ b i))
    hi hj).trans (Iff.of_eq (Prod.mk.injEq _ _ _ _))

/-- info: 'Rel.Verify.groupIdsPair_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms groupIdsPair_iff

/-- A `long` lane of ids: `n` ids at eight bytes hold all `n`, and element `i`'s key is a bijection of id `i`. -/
theorem keyAt_packIds64 (m : Nat) (f : Nat → Nat) :
    Kind.i64.avail (Column.packIds 64 m f) = m ∧ ∀ i < m,
      Order.keyAt .i64 (Column.packIds 64 m f) i = Order.rank .i64 (UInt64.ofNat ((f i).toUInt64.toNat % 2 ^ 64)) := by
  have hp : Column.packIds 64 m f = (List.range m).foldl (fun acc i => Column.pushBits acc (f i).toUInt64 8)
      (ByteArray.emptyWithCapacity (m * 8)) := by
    unfold Column.packIds
    rw [if_pos (by decide)]
    exact fold_eq_foldl_range m (fun i acc => Column.pushBits acc (f i).toUInt64 8) _
  obtain ⟨hs, -, hg⟩ := foldl_pushBits (fun i => (f i).toUInt64) 8 (by decide) (List.range m)
    (ByteArray.emptyWithCapacity (m * 8))
  have h0 : (ByteArray.emptyWithCapacity (m * 8)).size = 0 := rfl
  refine ⟨?_, fun i hi => ?_⟩
  · show (Column.packIds 64 m f).size / 8 = m
    rw [hp, hs, h0, List.length_range]; omega
  · have e := hg i (by rw [List.length_range]; exact hi)
    rw [h0, Nat.zero_add, List.getElem_range] at e
    show Order.rank .i64 (Column.bitsAt (Column.packIds 64 m f) (i * 8) 8) = _
    rw [hp, show i * 8 = 8 * i from Nat.mul_comm i 8, e]

/-- **`groupIdsPairIds`' ids agree exactly where both id payloads do**, over the ids both hold. -/
theorem groupIdsPairIds_iff (wa wb n : USize) (a b : ByteArray) {i j : Nat}
    (hi : i < min n.toNat (min (Column.idsCap a wa.toNat n.toNat) (Column.idsCap b wb.toNat n.toNat)))
    (hj : j < min n.toNat (min (Column.idsCap a wa.toNat n.toNat) (Column.idsCap b wb.toNat n.toNat))) :
    Column.idAt (Order.groupIdsPairIds wa wb n a b).1
          (Column.idWidthOf ((Order.groupIdsPairIds wa wb n a b).2.size / 8)) i =
        Column.idAt (Order.groupIdsPairIds wa wb n a b).1
          (Column.idWidthOf ((Order.groupIdsPairIds wa wb n a b).2.size / 8)) j ↔
      Column.idAt a wa.toNat i = Column.idAt a wa.toNat j ∧ Column.idAt b wb.toNat i = Column.idAt b wb.toNat j := by
  obtain ⟨ha, ga⟩ := keyAt_packIds64 (Column.idsCap a wa.toNat n.toNat) (Column.idAt a wa.toNat)
  obtain ⟨hb, gb⟩ := keyAt_packIds64 (Column.idsCap b wb.toNat n.toNat) (Column.idAt b wb.toNat)
  have hia : i < Column.idsCap a wa.toNat n.toNat := by omega
  have hja : j < Column.idsCap a wa.toNat n.toNat := by omega
  have hib : i < Column.idsCap b wb.toNat n.toNat := by omega
  have hjb : j < Column.idsCap b wb.toNat n.toNat := by omega
  have hr : ∀ x y : Nat, x < 2 ^ 64 → y < 2 ^ 64 → (Order.rank .i64 (UInt64.ofNat (x.toUInt64.toNat % 2 ^ 64)) =
      Order.rank .i64 (UInt64.ofNat (y.toUInt64.toNat % 2 ^ 64)) ↔ x = y) := fun x y hx hy => by
    refine ⟨fun e => ?_, fun e => by rw [e]⟩
    have t : ∀ a, (UInt64.ofNat a).toNat = a % 2 ^ 64 := fun a => BitVec.toNat_ofNat _ _
    have e := congrArg UInt64.toNat (UInt64.xor_left_inj _ |>.1 e)
    simp only [t, Nat.toUInt64_eq] at e
    simp only [Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hy] at e
    exact e
  have lt : ∀ (x : ByteArray) w k, Column.idAt x w k < 2 ^ 64 := fun x w k => (Column.resAt x 0 w k).toBitVec.isLt
  have e8 : 8 * (8 : USize).toNat = 64 := by
    rw [show (8 : USize).toNat = 8 from USize.toNat_ofNat_of_lt' (Nat.lt_of_lt_of_le (by decide) USize.le_size)]
  have hi' : i < min n.toNat (min (Kind.i64.avail (idsOperand 8 wa a n)) (Kind.i64.avail (idsOperand 8 wb b n))) := by
    rw [idsOperand, idsOperand, e8, ha, hb]; exact hi
  have hj' : j < min n.toNat (min (Kind.i64.avail (idsOperand 8 wa a n)) (Kind.i64.avail (idsOperand 8 wb b n))) := by
    rw [idsOperand, idsOperand, e8, ha, hb]; exact hj
  unfold Order.groupIdsPairIds
  refine (groupIdsPair_iff .i64 .i64 n _ _ hi' hj').trans ?_
  rw [idsOperand, idsOperand, e8, ga i hia, ga j hja, gb i hib, gb j hjb,
    hr _ _ (lt _ _ _) (lt _ _ _), hr _ _ (lt _ _ _) (lt _ _ _)]

/-- info: 'Rel.Verify.groupIdsPairIds_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms groupIdsPairIds_iff

/-- **`idLongs` widens faithfully**: long `i` of the answer is id `i`, for every id the payload holds. -/
theorem ids_idLongs (n w : USize) (x : ByteArray) :
    ids (Order.idLongs n w x) = (List.range (Column.idsCap x w.toNat n.toNat)).map (Column.idAt x w.toNat ·) :=
  ids_indices _ fun _ hi => by
    obtain ⟨k, -, rfl⟩ := List.mem_map.1 hi
    exact (Column.resAt x 0 w.toNat k).toBitVec.isLt

/-- info: 'Rel.Verify.ids_idLongs' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms ids_idLongs
/-- info: 'Rel.Verify.groupOf_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms groupOf_iff
/-- info: 'Rel.Verify.lt_idWidthOf' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms lt_idWidthOf
/-- info: 'Rel.Verify.idsBy_spec' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms idsBy_spec
/-- info: 'Rel.Verify.idsBy_iff' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms idsBy_iff
/-- info: 'Rel.Verify.keyAt_packIds64' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms keyAt_packIds64

end Rel.Verify
