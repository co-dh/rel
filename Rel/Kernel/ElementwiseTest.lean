import Rel.Kernel.Value
import Rel.Kernel.Elementwise

/-! The part of `Rel.Kernel.ElementwiseTest` the Rel kernels reach; `Rel.Kernel.ElementwiseTest` imports it. -/


namespace Rel.Kernel.ElementwiseTest

open Rel Rel.Kernel

-- `0N+1` is `0N` and `0W+0W` is `-2`: a null operand is answered before the arithmetic, and
-- everything else wraps.
example : Ew.intStep Ew.add Int64.minValue Int64.minValue 1 = Int64.minValue := by decide
example : Ew.intStep Ew.add Int64.minValue Int64.maxValue Int64.maxValue = -2 := by decide
-- `0N&1` is `0N` and `0N|1` is `1`: q's null is the least value, so the extremes need no null case.
example : Ew.intStep Ew.lesser Int64.minValue Int64.minValue 1 = Int64.minValue := by decide
example : Ew.intStep Ew.greater Int64.minValue Int64.minValue 1 = 1 := by decide
-- `0N^1` is `1` and `1^0N` is `1`: only the right operand's null is read.
example : Ew.intStep Ew.fill Int64.minValue Int64.minValue 1 = 1 := by decide
example : Ew.intStep Ew.fill Int64.minValue 1 Int64.minValue = 1 := by decide
-- `1-0n` is `0x7ff8…` where `0n-1` is `0xfff8…`: q subtracts by negating and adding.
example : Ew.f64Step Ew.sub 0x3ff0000000000000 Rel.nanBits = Ew.pnan64 := by decide
example : Ew.f64Step Ew.sub Rel.nanBits 0x3ff0000000000000 = Rel.nanBits := by decide
-- and the same at `real`: `1e-0Ne` is `0x7fc00000`.
example : Ew.f32Step Ew.sub 0x3f800000 Rel.nanBits32 = Ew.pnan32 := by decide
-- `0n<1.0` and `0n=0n` are both `1b`: q sorts a null below everything, where C sorts it nowhere.
#guard Ew.cmpStep Ew.lt Ew.f64 Rel.nanBits 0x3ff0000000000000
example : Ew.cmpStep Ew.eq Ew.f64 Rel.nanBits Rel.nanBits = true := by decide
example : Ew.cmpStep Ew.lt Ew.i64 0x8000000000000000 1 = true := by decide
-- `neg 0f` is `-0f`, which `0f-0f` is not: the monadic case of `-` flips the sign bit.
example : Ew.monStep Ew.neg Ew.f64 0 0 = 0x8000000000000000 := by decide
-- `abs 0n` is the negated null and `abs -0f` is `0f`.
example : Ew.monStep Ew.abs Ew.f64 0 Rel.nanBits = Ew.pnan64 := by decide
example : Ew.monStep Ew.abs Ew.f64 0 0x8000000000000000 = 0 := by decide
-- `mon` over each kind it reads (`Kernel.map`), read back through `raw`: a short dense `long` column (the answer dense,
-- below `encodeMin`), 200 `long`s Frame-of-Reference encoded and 200 `float`s ALP encoded (the answers encoded too).
-- No `decide` twin: `Enc.answer`'s `n < encodeMin` is a `USize` test, which the kernel does not reduce.
#guard (Ew.mon Ew.neg Ew.i64 Int64.minValue .long 3 (.bytes (dense 8 #[1, 0x8000000000000000, 5]))).raw .long 3
  == #[0xffffffffffffffff, 0x8000000000000000, 0xfffffffffffffffb]
#guard let xs := (Array.range 200).map fun i => (i * 3 : Nat).toUInt64
  let (m, p) := Coc.encode 8 (dense 8 xs)
  (Ew.mon Ew.neg Ew.i64 Int64.minValue .long 200 (.foR m p)).raw .long 200 == xs.map (0 - ·)
#guard let fs := (Array.range 200).map fun i => (Float.ofNat i / 100).toBits
  let (m, p, a) := Coc.alpEncode64 (dense 8 fs)
  (Ew.mon Ew.neg Ew.f64 0 .float 200 (.alp m p a)).raw .float 200 == fs.map (· ^^^ 0x8000000000000000)
-- `floor 0n` is `0N`, and that branch answers before any conversion.
example : Ew.floorStep Ew.f64 Rel.nanBits = Int64.minValue := by decide
-- `0Nh+1h` is `0Ni`: the promotion remaps the null rather than converting it.
example : Ew.widenStep Ew.i32 (-32768) (-2147483648) (-32768) = 0xffffffff80000000 := by decide

-- The steps that do real float arithmetic cannot be reduced by `decide` at all: `Float.ofBits`,
-- `+` and `.floor` are native, so the kernel gets stuck on them whatever the input. These are the
-- same specification statements run in the interpreter instead, which is the most that can be
-- checked of them outside the corpus. The other side of `0f-0f` is `neg 0f` above.
#guard Ew.f64Step Ew.sub 0 0 == 0
-- `floor 0w` and `floor 9.3e18` are `0N`; `floor -1.5` is `-2`.
#guard Ew.floorStep Ew.f64 0x7ff0000000000000 == Int64.minValue
#guard Ew.floorStep Ew.f64 0x43e0dcf1d9a1b2a0 == Int64.minValue
#guard Ew.floorStep Ew.f64 0xbff8000000000000 == -2

/-- The metadata `Column.encode` wrote with its trailer zeroed, which is metadata that says it
carries no sums — the state `coc_sums_drop` leaves and the one `Column.appendFoR` leaves, its `sumn`
being a shorter column's. -/
def noSums (m : ByteArray) : ByteArray :=
  (List.range 16).foldl (init := m) fun (acc : ByteArray) i =>
    acc.set! (32 * Column.nblk m + i) 0

end Rel.Kernel.ElementwiseTest
