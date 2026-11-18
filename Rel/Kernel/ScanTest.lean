import Rel.Kernel.Scan

/-! The part of `Rel.Kernel.ScanTest` the Rel kernels reach; `Rel.Kernel.ScanTest` imports it. -/


namespace Rel.Kernel.Scan
-- The narrowing `sums` does at four bytes, which is the one arithmetic rule that is not the fold's.
example : narrow 4 4000000000 = Int32.minValue.toInt64.toUInt64 := by decide
example : narrow 4 2000000000 = (2000000000 : Int64).toUInt64 := by decide
example : narrow 8 4000000000 = (4000000000 : Int64).toUInt64 := by decide
example : Kind.avail .bit ⟨#[0, 0, 0]⟩ = 24 := by decide

end Rel.Kernel.Scan


namespace Rel.Kernel

/-- An answer's words, `[]` at an error: `Except` has no `DecidableEq`, a `List` does. -/
private def kwords : Except String (Array UInt64) → List UInt64
  | .ok a => a.toList
  | .error _ => []
/-- `kscan`'s answer read back at `long`, `[]` at an error. -/
private def kread (r : Except String Enc) : List UInt64 := match r with
  | .ok e => (e.raw .i64 4).toList
  | .error _ => []

/-- Rows 0 and 2 start a segment; the seed is 100 on every row, the folded column `1 2 3 4`. -/
private def kseg : Enc := .bits ⟨#[0b0101]⟩
private def kcols : List Enc := [.bytes (Column.packIds 64 4 fun _ => 100), .bytes (Column.packIds 64 4 (· + 1))]

-- The kernel cannot reduce a `USize` (`System.Platform.numBits` is opaque), so `decide` runs `kscan`'s row fold on the
-- rows `kseg` and `kcols` hold and `#guard` runs the Rust on the columns: `100+1, 101+2 | 100+3, 103+4`
example : kwords ((List.range 4).foldlM (kscanRow .add #[1, 0, 1, 0] #[100, 100, 100, 100] [#[1, 2, 3, 4]]) #[]) =
    [101, 103, 103, 107] := by decide
#guard kread (kscan .add .i64 .i64 4 kseg kcols) = [101, 103, 103, 107]
-- an `Op.eval` error reaches the caller: `0 div 0` at row 0, both columns zeros
example : ((List.range 4).foldlM (kscanRow .div #[1, 0, 1, 0] #[0, 0, 0, 0] [#[0, 0, 0, 0]]) #[]).toBool = false := by
  decide
#guard (kscan .div .i64 .i64 4 kseg [.bytes (Column.packIds 64 4 fun _ => 0), .bytes (Column.packIds 64 4 fun _ => 0)]).toBool = false

end Rel.Kernel


namespace Rel.Kernel.Scan

/-- info: 'Rel.Kernel.Scan.scanOf_size' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Rel.Kernel.Scan.scanOf_size

end Rel.Kernel.Scan
