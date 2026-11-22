import Rel.KernelSpec.FindMember
import Rel.KernelSpec.Encoding
import Rel.Kernel.Coc
import Rel.KernelSpec.Gather
import Rel.Kernel.Structural
import Rel.KernelSpec.Alp
import Rel.Kernel.Value

/-! The part of `Rel.Verify.AlpConcat` the Rel kernels reach; `Rel.Verify.AlpConcat` imports it. -/


namespace Rel.Verify
open Rel Rel.Kernel

/-- An ALP element is no wider than the blob's element size: an exception is read at it and a
decimal of a `real` column is narrowed to four bytes. -/
theorem alpBits_lt (M P a : ByteArray) (s : Array Nat) (i : Nat) :
    (Column.alpBits M P a s i).toNat < 2 ^ (8 * Column.alpEsz a) := by
  unfold Column.alpBits
  split
  · exact bitsAt_lt _ _ _ (by unfold Column.alpEsz; split <;> decide)
  · unfold Column.alpDec Column.alpEsz
    cases Column.alpF32 a
    · simp only [Bool.false_eq_true, ↓reduceIte]; exact UInt64.toNat_lt _
    · simp only [↓reduceIte, UInt32.toNat_toUInt64]; exact Nat.lt_of_lt_of_le (UInt32.toNat_lt _) (by decide)






end Rel.Verify
