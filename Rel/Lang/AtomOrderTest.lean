import Rel.Lang.Den
import Rel.ObjOrder

/-! The two orders on a float atom, checked at `-0.0` (the word `2^63`) and `+0.0` (the word `0`), design
§3.5 / batch B5's unverified items. IEEE's comparisons (`Op.flt`, `Op.fle`) are `Float` operations, opaque to the
kernel, so their side is a `#guard` (compiled evaluation); `fval` and `Obj.lt` reduce, so theirs is a proof.

- `≤ ≜ < ∪ 𝟙` fails at `f64` (`f32` alike): `leAt .f64 (-0.0) (+0.0)` holds, `ltAt` does not, and the two words
  differ. So `le` is a native row beside `lt` (`cmpOps`), not a definition.
- `Obj.lt` (q's `asc` order, on the stored bits) is not `ltAt` at a float atom: `Obj.lt` puts `-0.0` before
  `+0.0`, IEEE's `<` does not. So a float atom's `<` stays its own native row (`lt`, IEEE's), and `Obj.lt` serves
  `asc` only. -/

namespace Rel.Lang

-- IEEE: `-0.0 ≤ +0.0`, not `-0.0 < +0.0`
#guard (Kernel.Op.fle.eval 0x8000000000000000 0).toOption == some 1
#guard (Kernel.Op.flt.eval 0x8000000000000000 0).toOption == some 0

/-- The two zeros are two values of `f64`. -/
example : (0x8000000000000000 : UInt64) ≠ 0 := by decide

/-- q's `asc` order puts `-0.0` first. -/
example : Obj.lt (.atom .f64) (0x8000000000000000 : UInt64) (0 : UInt64) := by decide

end Rel.Lang
