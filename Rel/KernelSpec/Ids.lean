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











end Rel.Verify

namespace Rel

/-- `Coc.bools n p` reads back as `p`: at width 1 a key is zero-extended, so element `i` is the 0/1 byte `i` it encodes
    (`foRBits_encode`). Here, beside `packIds_bytes`, so the driver law (`raw_ofRaw`) reads a boolean answer too. -/
theorem foRBits_bools (n : Nat) (p : Nat → Bool) {i : Nat} (hi : i < n) :
    Column.foRBits (Kernel.Coc.bools n p).1 (Kernel.Coc.bools n p).2 (Column.blockStarts (Kernel.Coc.bools n p).1) i =
      (p i).toNat.toUInt64 := by
  have h1 : USize.ofNat32 1 (by decide) = (1 : Nat).toUSize := USize.toNat_inj.mp (by
    rcases System.Platform.numBits_eq with h | h <;> simp [h])
  obtain ⟨hs, hb⟩ := Verify.packIds_bytes 1 n (fun i => (p i).toNat) (by decide) (by decide)
  simp only [Nat.mul_one] at hs hb
  simp only [Kernel.Coc.bools, h1]
  rw [Verify.foRBits_encode Column.lgEnc (by decide) 1 (by decide) (by decide) _ i (by rw [hs]; simpa using hi)]
  simp only [Kernel.Coc.keyAt, Column.sext, beq_self_eq_true, if_true, Nat.mul_one,
    hb i hi (by cases p i <;> decide)]
  cases p i <;> rfl

end Rel
