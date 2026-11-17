import Rel.Kernel.Sort
import Rel.Kernel.Value

/-! The part of `Rel.Kernel.SortTest` the Rel kernels reach; `Rel.Kernel.SortTest` imports it. -/


namespace Rel.Kernel.OrderTest

open Rel Rel.Kernel Rel.Kernel.Order
open Rel.Kernel.Scan (Kind)

-- Every NaN is q's null and sorts below everything. Measured on a float vector built with
-- `v[3]:abs 0n`: `iasc v` is `0 3 2 1`, `count distinct v` is `3`, `(abs 0n)~0n` is `1b`.
example : rank64 Rel.nanBits = 0 := by decide
-- and the same four rules at `real`. `count distinct (0e;-0e)` is `1`.
example : rank32 Rel.nanBits32.toUInt64.toUInt32 = 0 := by decide
example : rank .i16 5 = 0x8005 := by decide
example : rank .i32 0x80000000 = 0 := by decide
example : rank .i32 0xfffffffd = 0x7ffffffd := by decide
-- `iasc "a"," ",("c"$0),"a"` is `2 1 0 3`: NUL below blank below `"a"`, so `char` is its own byte
-- and the blank is not lifted out of the order the way `Eval.missing` lifts it out of `^`.
example : rank .u8 0 < rank .u8 32 := by decide
example : rank .u8 32 < rank .u8 97 := by decide
example : rank .u8 255 = 255 := by decide
-- `asc 0x02ff01` is `0x0102ff`: `byte` is unsigned too.
example : rank .u8 1 < rank .u8 255 := by decide
example : rank .bit 0 < rank .bit 1 := by decide
example : keyAt .bit ⟨#[2]⟩ 1 = 1 := by decide

end Rel.Kernel.OrderTest
