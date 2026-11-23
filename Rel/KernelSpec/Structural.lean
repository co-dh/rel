module

public import Rel.KernelSpec.FindMember
public import Rel.KernelSpec.Encoding
public import Rel.KernelSpec.Group
public import Rel.KernelSpec.Distinct
public import Rel.Kernel.Structural
public import Rel.Kernel.Value

-- exposed: every def body is a spec a downstream `rfl`/`decide`/`simp` may unfold (PLAN W.8)
@[expose] public section

/-! The part of `Rel.Verify.Structural` the Rel kernels reach; `Rel.Verify.Structural` imports it. -/


namespace Rel.Verify

open Rel Rel.Kernel







end Rel.Verify

