import Rel.KernelSpec.Encoding
import Rel.Kernel.Coc
import Rel.Kernel.Value
import Rel.Kernel.Search
import Rel.Kernel.Elementwise
import Rel.KernelSpec.Raw

/-! The part of `Rel.Verify.Where` the Rel kernels reach; `Rel.Verify.Where` imports it. -/


namespace Rel.Verify
open Rel Rel.Kernel





/-- The elements a dense fold reads at class `cls`, in order: `Ew.signed`'s value of each. -/
def denseElems (cls : UInt8) (b : ByteArray) : List Int64 :=
  (List.range (b.size / Ew.width cls)).map fun i => Ew.signed cls (Ew.elem cls b i)





end Rel.Verify


namespace Rel.Verify
open Rel Rel.Kernel


end Rel.Verify
