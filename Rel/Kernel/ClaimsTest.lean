import Rel.Kernel.Elementwise

/-! The part of `Rel.Kernel.ClaimsTest` the Rel kernels reach; `Rel.Kernel.ClaimsTest` imports it. -/


namespace Rel.Kernel.ClaimsTest

open Rel Rel.Kernel

/-- The three operand shapes, so that a claim made for two vectors is not read as a claim for a
vector against an atom. Every `dyadColumn` gap found in the audit was present at all three. -/
def shapes : List UInt8 := [Ew.vv, Ew.va, Ew.av]

end Rel.Kernel.ClaimsTest
