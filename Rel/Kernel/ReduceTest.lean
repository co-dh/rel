import Rel.Kernel.Sort
import Rel.Kernel.Coc
import Rel.Kernel.Scan
import Rel.Kernel.Value
import Rel.Kernel.Elementwise

/-! The part of `Rel.Kernel.ReduceTest` the Rel kernels reach; `Rel.Kernel.ReduceTest` imports it. -/


namespace Rel.Kernel

/-- Seven groups, interleaved: the row a group holds is never next to another of its own. -/
def gkeys : ByteArray :=
  (List.range 3005).foldl (init := ByteArray.empty) fun acc i =>
    Column.pushBits acc (Int64.ofNat (i % 7)).toUInt64 8

/-- A null every eleventh row, and group 6 entirely null — which is where the seeds show: `min` of
it is `0W`, `max` is `-0W`, `sum` is `0` and `prd` is `1`. -/
def gvals : ByteArray :=
  (List.range 3005).foldl (init := ByteArray.empty) fun acc i =>
    Column.pushBits acc (if i % 11 == 0 || i % 7 == 6 then Int64.minValue.toUInt64
      else (Int64.ofNat (i * 37 % 1009)).toUInt64) 8

def gids : ByteArray := (Order.groupIds .i64 3005 gkeys).1

-- a metadata with blocks past the count, as a mapped file may hold, whose minimum 1 and maximum 900
-- lie outside the column's 5s: every view stops at the count's blocks, so the fold is the dense one
def extraMd : ByteArray := Coc.foRMeta Rel.Column.lgEnc 0 0 #[(5, 5, 0, 0), (1, 1, 0, 0), (900, 900, 0, 0)]
def classes : List (UInt8 × Int64) :=
  [(Ew.i64, Int64.minValue), (Ew.i32, -2147483648), (Ew.i16, -32768), (Ew.u8, -1)]

/-- Floats with a NaN every eleventh, read at both widths. -/
def fvals : ByteArray :=
  (List.range 3005).foldl (init := ByteArray.empty) fun acc i =>
    Column.pushBits acc (if i % 11 == 0 then Rel.nanBits else (Float.ofNat (i * 37 % 1009) * 0.37).toBits) 8

end Rel.Kernel
