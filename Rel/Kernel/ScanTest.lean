import Rel.Kernel.Scan

/-! The part of `Rel.Kernel.ScanTest` the Rel kernels reach; `Rel.Kernel.ScanTest` imports it. -/


namespace Rel.Kernel.Scan
-- The narrowing `sums` does at four bytes, which is the one arithmetic rule that is not the fold's.
example : narrow 4 4000000000 = Int32.minValue.toInt64.toUInt64 := by decide
example : narrow 4 2000000000 = (2000000000 : Int64).toUInt64 := by decide
example : narrow 8 4000000000 = (4000000000 : Int64).toUInt64 := by decide
example : Kind.avail .bit ⟨#[0, 0, 0]⟩ = 24 := by decide

end Rel.Kernel.Scan


namespace Rel.Kernel.Scan

/-- info: 'Rel.Kernel.Scan.scanOf_size' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Rel.Kernel.Scan.scanOf_size

end Rel.Kernel.Scan
