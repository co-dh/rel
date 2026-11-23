module

public import Rel.KernelSpec.FindMember
public import Rel.KernelSpec.Encoding
public import Rel.Kernel.Coc
public import Rel.Kernel.Value
public import Rel.Kernel.Elementwise

-- exposed: every def body is a spec a downstream `rfl`/`decide`/`simp` may unfold (PLAN W.8)
@[expose] public section

/-! The part of `Rel.Verify.Chain` the Rel kernels reach; `Rel.Verify.Chain` imports it. -/


namespace Rel.Verify

open Rel Rel.Kernel



/-- A one-byte read is the byte. -/
theorem bitsAt_one (b : ByteArray) (o : Nat) : Column.bitsAt b o 1 = (b[o]?.getD 0).toUInt64 := by
  rw [Column.bitsAt_succ]; simp [Column.bitsAt]








end Rel.Verify
