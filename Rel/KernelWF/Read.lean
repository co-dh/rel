import Rel.Kernel.Dep.Monadic
import Rel.Kernel.Scan
import Rel.Kernel.Structural
import Rel.KernelSpec.Alp
import Rel.KernelSpec.AlpConcat
import Rel.KernelSpec.BinWin
import Rel.KernelSpec.Chain
import Rel.KernelSpec.Elementwise
import Rel.KernelSpec.Encoding
import Rel.KernelSpec.EwEnc
import Rel.KernelSpec.Gather
import Rel.KernelSpec.Grade
import Rel.KernelSpec.Group
import Rel.KernelSpec.Ids
import Rel.KernelSpec.ScanOver
import Rel.KernelSpec.Search
import Rel.KernelSpec.Structural
import Rel.KernelSpec.SymFind
import Rel.ObjOrder
import Rel.Run.Core
import Rel.Rep

/-! Read lemmas of the run path's own definitions (`Enc.get`, `Enc.raw`, `Vals.row`, the foR block layout, the
    symbol id widths), kept from the deleted `Rel.KernelWF.*` modules whose other contents were about the old layer.
    Each section names the module it came from. -/

-- from Rel.KernelWF.AppendFoR
namespace Rel.KernelWF

open Tab Rel.Kernel Rel












end Rel.KernelWF

-- from Rel.Run.KernelWF.Raze
-- the lane widths an id pack may have: one home for the disjunction every lane hypothesis states
notation "laneOK(" w ")" => (w = 1 ∨ w = 2 ∨ w = 4 ∨ w = 8 ∨ w = 16 ∨ w = 32 ∨ w = 64)

namespace Rel.KernelWF

open Rel.Kernel Rel

/-- A `Nat.fold` that pushes a byte a step answers one byte per step. -/
private theorem fold_push_size (g : Nat → UInt8) :
    ∀ (k : Nat) (b : ByteArray), (Nat.fold k (fun i _ acc => acc.push (g i)) b).size = b.size + k
  | 0, b => by simp
  | k + 1, b => by
    rw [Nat.fold_succ, ← Nat.add_assoc, ← fold_push_size g k b]
    simp only [ByteArray.size, ByteArray.push, Array.size_push]


end Rel.KernelWF

-- from Rel.KernelWF.Driver
open Rel.Ext

namespace Rel.Kernel
open Column




end Rel.Kernel

-- from Rel.KernelWF.Lane
namespace Rel.Alg

open Tab Rel.Kernel Rel


end Rel.Alg

-- from Rel.KernelWF.RazeSpec
open Rel.Ext

namespace Rel.KernelWF

open Tab Rel.Kernel Rel.Dep Rel Rel.Alg





end Rel.KernelWF

-- from Rel.KernelWF.RazeSym
open Rel.Ext

namespace Rel.KernelWF

open Tab Rel.Kernel Rel.Dep Rel Rel.Alg

end Rel.KernelWF

-- from Rel.KernelWF.RazeRowN
namespace Rel.KernelWF

open Tab Rel.Kernel Rel.Dep Rel Rel.Alg Rel.Rep
open scoped Rel.Core.Rel
open Rel.Core.Rel hiding id comp recip inter union zero le inl inr junc



end Rel.KernelWF

-- from Rel.KernelWF.RazeRowRec
namespace Rel.KernelWF

open Tab Rel.Kernel Rel.Dep Rel Rel.Alg Rel.Rep
open scoped Rel.Core.Rel
open Rel.Core.Rel hiding id comp recip inter union zero le inl inr junc


end Rel.KernelWF

-- from Rel.KernelWF.PickSpec
open Rel.Ext

namespace Rel.KernelWF

open Tab Rel.Kernel Rel.Verify






end Rel.KernelWF

namespace Rel.Alg

open Tab Rel.Kernel Rel




end Rel.Alg

-- from Rel.KernelWF.RowsSpec
namespace Rel.Alg

open Tab Rel.Kernel Rel.Verify Rel


end Rel.Alg

-- from Rel.KernelWF.PickRow
open Rel.Ext

namespace Rel.Alg

open Tab Rel.Kernel Rel.Verify Rel




end Rel.Alg

-- from Rel.KernelWF.CodesSpec
open Rel.Ext

namespace Rel.Alg

open Tab Rel.Dep Rel.Kernel Rel.Verify Rel








end Rel.Alg

-- from Rel.KernelWF.CodesSym
open Rel.Ext

namespace Rel.Alg

open Tab Rel.Dep Rel.Kernel Rel.Verify Rel


end Rel.Alg

-- from Rel.KernelWF.CodesProd
namespace Rel.Alg

open Tab Rel.Dep Rel.Kernel Rel.Verify Rel


end Rel.Alg

-- from Rel.KernelWF.AscSpec
open Rel.Ext

namespace Rel.Alg

open Tab Rel.Dep Rel.Kernel Rel.Verify Rel Rel.KernelWF





/-- **`¬ Obj.lt` is antisymmetric where `Obj.key` is injective**: neither below the other means equal keys
    (`lt_trichotomy`), so equal elements. `Ordered` alone does not give it: every general atom keys as `[]`. -/
theorem _root_.Rel.Obj.eq_of_not_lt (A : Obj) (hA : ∀ x y : A.El, A.key x = A.key y → x = y) {x y : A.El}
    (h1 : ¬ A.lt x y) (h2 : ¬ A.lt y x) : x = y :=
  hA x y (((A.lt_trichotomy x y).resolve_left h1).resolve_right h2)

end Rel.Alg

-- from Rel.KernelWF.CrossSpec
namespace Rel.KernelWF

open Tab Rel.Kernel Rel Rel.Alg


end Rel.KernelWF

-- from Rel.KernelWF.JoinContent
namespace Rel.Alg

open Tab Rel.Kernel Rel.Verify Rel


end Rel.Alg

-- from Rel.KernelWF.RunSpec
namespace Rel.Alg

open Tab Rel.Kernel Rel.Verify Rel Rel.KernelWF



end Rel.Alg
