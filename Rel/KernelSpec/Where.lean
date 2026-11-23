module

public import Rel.KernelSpec.Encoding
public import Rel.Kernel.Coc
public import Rel.Kernel.Value
public import Rel.Kernel.Search
public import Rel.Kernel.Elementwise
public import Rel.KernelSpec.Raw

-- exposed: every def body is a spec a downstream `rfl`/`decide`/`simp` may unfold (PLAN W.8)
@[expose] public section

/-! The part of `Rel.Verify.Where` the Rel kernels reach; `Rel.Verify.Where` imports it. -/


namespace Rel.Verify
open Rel Rel.Kernel










end Rel.Verify


namespace Rel.Verify
open Rel Rel.Kernel


end Rel.Verify
