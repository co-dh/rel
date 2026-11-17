import Rel.Kernel.Coc
import Rel.Kernel.TestChecks
import Rel.Kernel.Value

/-! The part of `Rel.Kernel.Test` the Rel kernels reach; `Rel.Kernel.Test` imports it. -/


namespace Rel.Kernel

open TestChecks

-- Element order is signed, and biasing is what makes unsigned comparison agree with it. Read
-- unsigned, `-1` would be the largest 64-bit element rather than the smallest.
example : Rel.Kernel.Coc.keyAt 8 ⟨#[255,255,255,255,255,255,255,255]⟩ 0 = 2 ^ 63 - 1 := by decide
example : Rel.Kernel.Coc.keyAt 8 ⟨#[5,0,0,0,0,0,0,0]⟩ 0 = 2 ^ 63 + 5 := by decide
-- and one byte, q's only unsigned fixed-width case, biases by nothing
example : Rel.Kernel.Coc.keyAt 1 ⟨#[255]⟩ 0 = 255 := by decide

-- A block minimum goes back out sign-extended to 64 bits, whatever the element width: `-1` as a
-- short is stored as the `int64_t` -1, because that is what `Column.baseAt` reads and adds to.
example : Rel.Kernel.Coc.unbias 2 (Rel.Kernel.Coc.keyAt 2 ⟨#[255,255]⟩ 0) = 0xffffffffffffffff :=
  by decide
example : Rel.Kernel.Coc.unbias 1 (Rel.Kernel.Coc.keyAt 1 ⟨#[255]⟩ 0) = 255 := by decide

-- The width a range needs, at each boundary. `widthFor 0 = 0` is a block of one repeated value,
-- which stores no residual bytes at all.
example : Rel.Column.widthFor 0 = 0 := by decide
example : Rel.Column.widthFor 1 = 1 := by decide
example : Rel.Column.widthFor 2 = 2 := by decide
example : Rel.Column.widthFor 3 = 2 := by decide
example : Rel.Column.widthFor 4 = 3 := by decide
example : Rel.Column.widthFor 15 = 4 := by decide
example : Rel.Column.widthFor 16 = 5 := by decide
example : Rel.Column.widthFor 255 = 8 := by decide
example : Rel.Column.widthFor 256 = 9 := by decide
example : Rel.Column.widthFor (2 ^ 32) = 33 := by decide
example : Rel.Column.widthFor (2 ^ 46) = 47 := by decide
example : Rel.Column.widthFor (2 ^ 64 - 1) = 64 := by decide

-- `resAt`'s specification, which the `#guard`s below cannot reach past `resAtImpl`: a 3-bit field
-- straddling a byte boundary, and a 63-bit one spread over nine bytes.
example : Rel.Column.resAt ⟨#[0xff, 0x01]⟩ 0 3 2 = 7 := by decide
example : Rel.Column.resAt ⟨#[0x2c, 0x01]⟩ 0 3 1 = 5 := by decide
example : Rel.Column.resAt ⟨Array.replicate 16 0xff⟩ 0 63 1 = 0x7fffffffffffffff := by decide

#guard addShift 56 2 7.0 == (0x401e3d70a3d70a3e, 0x401e3d70a3d70a3d)
#guard addShift 137 3 7.0 == (0x401c8c49ba5e3540, 0x401c8c49ba5e353f)

end Rel.Kernel
