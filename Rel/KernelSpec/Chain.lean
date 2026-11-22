import Rel.KernelSpec.FindMember
import Rel.KernelSpec.Encoding
import Rel.Kernel.Coc
import Rel.Kernel.Value
import Rel.Kernel.Elementwise

/-! The part of `Rel.Verify.Chain` the Rel kernels reach; `Rel.Verify.Chain` imports it. -/


namespace Rel.Verify

open Rel Rel.Kernel



/-- A one-byte read is the byte. -/
theorem bitsAt_one (b : ByteArray) (o : Nat) : Column.bitsAt b o 1 = (b[o]?.getD 0).toUInt64 := by
  rw [Column.bitsAt_succ]; simp [Column.bitsAt]








end Rel.Verify
