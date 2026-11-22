import Rel.KernelSpec.FindMember
import Rel.KernelSpec.Encoding
import Rel.KernelSpec.Group
import Rel.Kernel.Sort
import Rel.KernelSpec.Codes
import Rel.Kernel.Value
import Rel.Kernel.Search
import Rel.KernelSpec.Assign
import Rel.Kernel.Need
import Rel.Kernel.Structural

/-! The part of `Rel.Verify.SymFind` the Rel kernels reach; `Rel.Verify.SymFind` imports it. -/


namespace Rel.Verify
open Rel Rel.Kernel







/-- **An id below the dictionary's count reads back from `packIds` at that count's width.** -/
theorem idAt_packIds_idWidthOf {nd n i : Nat} {f : Nat → Nat} (hnd : nd ≤ 2 ^ 64) (hi : i < n) (hf : f i < nd) :
    Column.idAt (Column.packIds (Column.idWidthOf nd) n f) (Column.idWidthOf nd) i = f i :=
  idAt_packIds (laneWidth_cases _) hi (lt_idWidthOf hf hnd)



/-- info: 'Rel.Verify.idAt_packIds_idWidthOf' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms idAt_packIds_idWidthOf

end Rel.Verify


namespace Rel.Verify
open Rel Rel.Kernel





end Rel.Verify
