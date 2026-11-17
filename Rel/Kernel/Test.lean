import QLean.RelPart.Kernel.Coc
import QLean.RelPart.Kernel.TestChecks
import QLean.RelPart.Value

/-! The part of `QLean.Kernel.Test` the Rel kernels reach; `QLean.Kernel.Test` imports it. -/


namespace QLean.Kernel

open TestChecks

-- Element order is signed, and biasing is what makes unsigned comparison agree with it. Read
-- unsigned, `-1` would be the largest 64-bit element rather than the smallest.
example : QLean.Kernel.Coc.keyAt 8 ⟨#[255,255,255,255,255,255,255,255]⟩ 0 = 2 ^ 63 - 1 := by decide
example : QLean.Kernel.Coc.keyAt 8 ⟨#[5,0,0,0,0,0,0,0]⟩ 0 = 2 ^ 63 + 5 := by decide
-- and one byte, q's only unsigned fixed-width case, biases by nothing
example : QLean.Kernel.Coc.keyAt 1 ⟨#[255]⟩ 0 = 255 := by decide

-- A block minimum goes back out sign-extended to 64 bits, whatever the element width: `-1` as a
-- short is stored as the `int64_t` -1, because that is what `Column.baseAt` reads and adds to.
example : QLean.Kernel.Coc.unbias 2 (QLean.Kernel.Coc.keyAt 2 ⟨#[255,255]⟩ 0) = 0xffffffffffffffff :=
  by decide
example : QLean.Kernel.Coc.unbias 1 (QLean.Kernel.Coc.keyAt 1 ⟨#[255]⟩ 0) = 255 := by decide

-- The width a range needs, at each boundary. `widthFor 0 = 0` is a block of one repeated value,
-- which stores no residual bytes at all.
example : QLean.Column.widthFor 0 = 0 := by decide
example : QLean.Column.widthFor 1 = 1 := by decide
example : QLean.Column.widthFor 2 = 2 := by decide
example : QLean.Column.widthFor 3 = 2 := by decide
example : QLean.Column.widthFor 4 = 3 := by decide
example : QLean.Column.widthFor 15 = 4 := by decide
example : QLean.Column.widthFor 16 = 5 := by decide
example : QLean.Column.widthFor 255 = 8 := by decide
example : QLean.Column.widthFor 256 = 9 := by decide
example : QLean.Column.widthFor (2 ^ 32) = 33 := by decide
example : QLean.Column.widthFor (2 ^ 46) = 47 := by decide
example : QLean.Column.widthFor (2 ^ 64 - 1) = 64 := by decide

-- `resAt`'s specification, which the `#guard`s below cannot reach past `resAtImpl`: a 3-bit field
-- straddling a byte boundary, and a 63-bit one spread over nine bytes.
example : QLean.Column.resAt ⟨#[0xff, 0x01]⟩ 0 3 2 = 7 := by decide
example : QLean.Column.resAt ⟨#[0x2c, 0x01]⟩ 0 3 1 = 5 := by decide
example : QLean.Column.resAt ⟨Array.replicate 16 0xff⟩ 0 63 1 = 0x7fffffffffffffff := by decide

#guard addShift 56 2 7.0 == (0x401e3d70a3d70a3e, 0x401e3d70a3d70a3d)
#guard addShift 137 3 7.0 == (0x401c8c49ba5e3540, 0x401c8c49ba5e353f)

end QLean.Kernel
