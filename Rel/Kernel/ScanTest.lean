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
#guard kread (kscan .add false .i64 .i64 4 kseg kcols) = [101, 103, 103, 107]
-- reversed (D.6): the forward fold of every column reversed, read back reversed. Rows 3 and 2 start a segment walking
-- back: `100+4 | 100+3, 103+2 | 100+1`
example : kwords ((List.range 4).foldlM (kscanRow .add #[0, 1, 0, 1] #[100, 100, 100, 100] [#[4, 3, 2, 1]]) #[]) =
    [104, 103, 105, 101] := by decide
#guard kread (kscan .add true .i64 .i64 4 kseg kcols) = [101, 105, 103, 104]
-- an `Op.eval` error reaches the caller: `0 div 0` at row 0, both columns zeros
example : ((List.range 4).foldlM (kscanRow .div #[1, 0, 1, 0] #[0, 0, 0, 0] [#[0, 0, 0, 0]]) #[]).toBool = false := by
  decide
#guard (kscan .div false .i64 .i64 4 kseg [.bytes (Column.packIds 64 4 fun _ => 0), .bytes (Column.packIds 64 4 fun _ => 0)]).toBool = false

/-- `0n`'s word: a `min` from a zero seed carries it, the word being negative as an `i64`. -/
private def knan : Enc := .bytes (Column.packIds 64 4 fun i => [1, 0xfff8000000000000, 3, 2][i]!)
-- a NaN word both ways: forward `0, 0 min 0n | 0, 0 min 2`, reversed rows `0 | 0, 0 min 0n | 0`
example : kwords ((List.range 4).foldlM (kscanRow .min #[1, 0, 1, 0] #[0, 0, 0, 0] [#[1, 0xfff8000000000000, 3, 2]])
    #[]) = [0, 0xfff8000000000000, 0, 0] := by decide
example : kwords ((List.range 4).foldlM (kscanRow .min #[0, 1, 0, 1] #[0, 0, 0, 0] [#[2, 3, 0xfff8000000000000, 1]])
    #[]) = [0, 0, 0xfff8000000000000, 0] := by decide
#guard kread (kscan .min false .i64 .i64 4 kseg [.bytes (Column.packIds 64 4 fun _ => 0), knan]) =
  [0, 0xfff8000000000000, 0, 0]
#guard kread (kscan .min true .i64 .i64 4 kseg [.bytes (Column.packIds 64 4 fun _ => 0), knan]) =
  [0, 0xfff8000000000000, 0, 0]
-- the float path on the same words: a NaN is the least float (`fmin`), and `0.0` is the word 0
#guard kread (kscan .fmin false .f64 .f64 4 kseg [.bytes (Column.packIds 64 4 fun _ => 0),
  .bytes (Column.packIds 64 4 fun i => [0x3ff0000000000000, 0xfff8000000000000, 0x4008000000000000, 0x4000000000000000][i]!)]) =
  [0, 0xfff8000000000000, 0, 0]

/-- A boolean answer read back at `boolean`, `[]` unless it is a `foR` (D.5: a boolean is a `foR` of `u1`). -/
private def kbool (r : Except String Enc) : List UInt64 := match r with
  | .ok (.foR m p) => ((Enc.foR m p : Enc).raw .u1 4).toList
  | _ => []
-- a compare answers a boolean: forward `100>1, 1>2 | 100>3, 1>4`; reversed rows `100>4 | 100>3, 1>2 | 100>1`
example : kwords ((List.range 4).foldlM (kscanRow .gt #[1, 0, 1, 0] #[100, 100, 100, 100] [#[1, 2, 3, 4]]) #[]) =
    [1, 0, 1, 0] := by decide
example : kwords ((List.range 4).foldlM (kscanRow .gt #[0, 1, 0, 1] #[100, 100, 100, 100] [#[4, 3, 2, 1]]) #[]) =
    [1, 1, 0, 1] := by decide
#guard kbool (kscan .gt false .i64 .u1 4 kseg kcols) = [1, 0, 1, 0]
#guard kbool (kscan .gt true .i64 .u1 4 kseg kcols) = [1, 0, 1, 1]
-- a boolean answer cut to its low bit: `add` of `1 2 3 4` from 100 at rows 0 and 2 is `101 103 103 107`
#guard kbool (kscan .add false .i64 .u1 4 kseg kcols) = [1, 1, 1, 1]
-- a `foR` boolean is a `seg` and a boolean column: the compare's own answer `1 0 1 0` segments as `kseg` does, and
-- reversed, `or` of it with itself carries row 2's `1` back into row 1: rows `0 | 1|1, 1|0 | 1|1`
#guard kread (kscan .gt false .i64 .u1 4 kseg kcols >>= fun g => kscan .add false .i64 .i64 4 g kcols) =
  [101, 103, 103, 107]
example : kwords ((List.range 4).foldlM (kscanRow .or #[0, 1, 0, 1] #[0, 1, 0, 1] [#[0, 1, 0, 1]]) #[]) =
    [0, 1, 1, 1] := by decide
#guard kbool (kscan .gt false .i64 .u1 4 kseg kcols >>= fun g => kscan .or true .u1 .u1 4 g [g, g]) =
  [1, 1, 1, 0]

-- `pos` (PLAN 6.13) as the seed: row `i` reads `i`, `0+1, 1+2 | 2+3, 5+4`
example : (Ext.Enc.raw (X := Empty) .i64 (USize.ofNat32 4 (by decide)) .pos).toList = [0, 1, 2, 3] := by decide +kernel
example : kwords ((List.range 4).foldlM (kscanRow .add #[1, 0, 1, 0] #[0, 1, 2, 3] [#[1, 2, 3, 4]]) #[]) =
    [1, 3, 5, 9] := by decide
#guard kread (kscan .add false .i64 .i64 4 kseg [.pos, .bytes (Column.packIds 64 4 (· + 1))]) = [1, 3, 5, 9]
-- `pos` is `i64` only: as `seg` (read as booleans) and read at `i32` it holds no raw elements, the error
example : (Ext.Enc.raw (X := Empty) .u1 (USize.ofNat32 4 (by decide)) .pos).size = 0 := by decide +kernel
#guard (kscan .add false .i64 .i64 4 .pos kcols).toBool = false
#guard (kscan .add false .i32 .i64 4 kseg [.pos]).toBool = false

end Rel.Kernel


namespace Rel.Kernel.Scan

/-- info: 'Rel.Kernel.Scan.scanOf_size' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Rel.Kernel.Scan.scanOf_size

end Rel.Kernel.Scan
