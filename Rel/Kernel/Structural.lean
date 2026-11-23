module

public import Rel.Kernel.Need
public import Rel.Kernel.Sort
public import Rel.Kernel.Coc
public import Rel.Kernel.Value
public import Rel.Kernel.Search
public import Rel.Kernel.Elementwise

-- exposed: every def body is a spec a downstream `rfl`/`decide`/`simp` may unfold (PLAN W.8)
@[expose] public section

/-! The part of `Rel.Kernel.Structural` the Rel kernels reach; `Rel.Kernel.Structural` imports it. -/


open Rel.Ext
namespace Rel.Kernel






























end Rel.Kernel


namespace Rel.Kernel









end Rel.Kernel
