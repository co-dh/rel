import Rel.Kernel.Value
import Rel.Kernel.Search

/-! The part of `Rel.Kernel.SearchTest` the Rel kernels reach; `Rel.Kernel.SearchTest` imports it. -/


namespace Rel.Kernel
example : normalise 8 true Rel.nanBits = Rel.nanBits := by decide
example : normalise 4 true Rel.nanBits32.toUInt64 = Rel.nanBits32.toUInt64 := by decide

end Rel.Kernel
