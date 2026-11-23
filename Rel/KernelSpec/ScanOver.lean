module

public import Rel.KernelSpec.Encoding
public import Rel.Kernel.Coc
public import Rel.Kernel.Scan
public import Rel.KernelSpec.Where
public import Rel.Kernel.Value

-- exposed: every def body is a spec a downstream `rfl`/`decide`/`simp` may unfold (PLAN W.8)
@[expose] public section

/-! The part of `Rel.Verify.ScanOver` the Rel kernels reach; `Rel.Verify.ScanOver` imports it. -/


namespace Rel.Verify
open Rel Rel.Kernel Rel.Kernel.Scan






end Rel.Verify
