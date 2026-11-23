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
















end Rel.Verify

namespace Rel

/-- `Coc.bools n p` reads back as `p`: at width 1 a key is zero-extended, so element `i` is the 0/1 byte `i` it encodes
    (`foROpt_encode` with no null rows), through the null-aware read and so through the raw one. Here, beside
    `packIds_bytes`, so the driver law (`raw_ofRaw`) reads a boolean answer too. -/
theorem foRBits_bools (n : Nat) (p : Nat → Bool) {i : Nat} (hi : i < n) :
    Column.foROpt (Kernel.Coc.bools n p).1 (Kernel.Coc.bools n p).2 (Column.blockStarts (Kernel.Coc.bools n p).1) i =
      some (p i).toNat.toUInt64 ∧
    Column.foRBits (Kernel.Coc.bools n p).1 (Kernel.Coc.bools n p).2 (Column.blockStarts (Kernel.Coc.bools n p).1) i =
      (p i).toNat.toUInt64 := by
  have h1 : USize.ofNat32 1 (by decide) = (1 : Nat).toUSize := USize.toNat_inj.mp (by
    rcases System.Platform.numBits_eq with h | h <;> simp)
  obtain ⟨hs, hb⟩ := Verify.packIds_bytes 1 n (fun i => (p i).toNat) (by decide) (by decide)
  simp only [Nat.mul_one] at hs hb
  have ho : Column.foROpt (Kernel.Coc.bools n p).1 (Kernel.Coc.bools n p).2
      (Column.blockStarts (Kernel.Coc.bools n p).1) i = some (p i).toNat.toUInt64 := by
    simp only [Kernel.Coc.bools, h1]
    rw [Verify.foROpt_encode Column.lgEnc (by decide) 1 (by decide) (by decide) _ .empty i (by rw [hs]; simpa using hi)
      fun _ _ _ j _ _ _ => Verify.bitAt_empty j]
    simp only [Verify.bitAt_empty, Bool.false_eq_true, ↓reduceIte, Kernel.Coc.keyAt, Column.sext, beq_self_eq_true,
      if_true, Nat.mul_one, hb i hi (by cases p i <;> decide)]
    cases p i <;> rfl
  refine ⟨ho, ?_⟩
  unfold Column.foROpt at ho; split at ho; · cases ho
  exact Option.some.inj ho

end Rel
