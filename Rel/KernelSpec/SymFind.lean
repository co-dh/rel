module

public import Rel.KernelSpec.FindMember
public import Rel.KernelSpec.Encoding
public import Rel.KernelSpec.Group
public import Rel.Kernel.Sort
public import Rel.KernelSpec.Codes
public import Rel.Kernel.Value
public import Rel.Kernel.Search
public import Rel.KernelSpec.Assign
public import Rel.Kernel.Need
public import Rel.Kernel.Structural

-- exposed: every def body is a spec a downstream `rfl`/`decide`/`simp` may unfold (PLAN W.8)
@[expose] public section

/-! The part of `Rel.Verify.SymFind` the Rel kernels reach; `Rel.Verify.SymFind` imports it. -/


namespace Rel.Verify
open Rel Rel.Kernel







/-- **An id below the dictionary's count reads back from `packIds` at that count's width.** -/
theorem idAt_packIds_idWidthOf {nd n i : Nat} {f : Nat → Nat} (hnd : nd ≤ 2 ^ 64) (hi : i < n) (hf : f i < nd) :
    Column.idAt (Column.packIds (Column.idWidthOf nd) n f) (Column.idWidthOf nd) i = f i :=
  idAt_packIds (laneWidth_cases _) hi (lt_idWidthOf hf hnd)




end Rel.Verify


namespace Rel.Verify
open Rel Rel.Kernel





end Rel.Verify
