import QLean.RelPart.Kernel.Elementwise

/-! The part of `QLean.Kernel.ClaimsTest` the Rel kernels reach; `QLean.Kernel.ClaimsTest` imports it. -/


namespace QLean.Kernel.ClaimsTest

open QLean QLean.Kernel

/-- The three operand shapes, so that a claim made for two vectors is not read as a claim for a
vector against an atom. Every `dyadColumn` gap found in the audit was present at all three. -/
def shapes : List UInt8 := [Ew.vv, Ew.va, Ew.av]

end QLean.Kernel.ClaimsTest
