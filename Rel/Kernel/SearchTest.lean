import QLean.RelPart.Value
import QLean.RelPart.Kernel.Search

/-! The part of `QLean.Kernel.SearchTest` the Rel kernels reach; `QLean.Kernel.SearchTest` imports it. -/


namespace QLean.Kernel
example : normalise 8 true QLean.nanBits = QLean.nanBits := by decide
example : normalise 4 true QLean.nanBits32.toUInt64 = QLean.nanBits32.toUInt64 := by decide

end QLean.Kernel
