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
private def kread (r : Except String (Enc × Option UInt64)) : List UInt64 := match r with
  | .ok (e, _) => (e.raw .i64 4).toList
  | .error _ => []

/-- Rows 0 and 2 start a segment; the seed is 100 on every row, the folded column `1 2 3 4`. -/
private def kseg : Enc := .foR (Coc.bools 4 (· % 2 == 0)).1 (Coc.bools 4 (· % 2 == 0)).2
private def kcols : List Enc := [Ext.Enc.ofBytes 8 (Column.packIds 64 4 fun _ => 100), Ext.Enc.ofBytes 8 (Column.packIds 64 4 (· + 1))]

-- The kernel cannot reduce a `USize` (`System.Platform.numBits` is opaque), so `decide` runs `kscan`'s row fold on the
-- rows `kseg` and `kcols` hold and `#guard` runs the Rust on the columns: `100+1, 101+2 | 100+3, 103+4`
example : kwords ((List.range 4).foldlM (kscanRow .add #[1, 0, 1, 0] #[100, 100, 100, 100] [#[1, 2, 3, 4]]) #[]) =
    [101, 103, 103, 107] := by decide
#guard kread (kscan .add false .i64 .i64 4 kseg kcols) = [101, 103, 103, 107]
-- a per-row chain with every row its own segment (`seg = none`): `(s + 1) + (x + 1)`, then `+ 10`
example : (chain [(.add, 1), (.add, 10)] 5).toOption = some 16 := by decide
#guard kread (kscan .add false .i64 .i64 4 none kcols [(.add, 1)] [(.add, 10)]) = [113, 114, 115, 116]
#guard (kscan .add false .i64 .i64 4 none kcols [(.div, 1)]).toBool = false
-- a constant divisor is a post step (`rdiv`, `rmod`): `(100 + x) / 3 % 5` for `x = 1 … 4` is `33 34 34 34 % 5`; a
-- divisor `0` is refused where a row exists (`Op.stepFails`), and passes at `n = 0`; `rdiv` is no scan's op
example : (chain [(.rdiv, 3), (.rmod, 5)] 101).toOption = some 3 ∧ Op.stepFails .rdiv 0 = true ∧
    Op.stepFails .rmod 3 = false ∧ (chain [(.rdiv, 0)] 7).toBool = false := by decide
#guard kread (kscan .add false .i64 .i64 4 none kcols [] [(.rdiv, 3), (.rmod, 5)]) = [3, 4, 4, 4]
#guard (kscan .add false .i64 .i64 4 none kcols [] [(.rdiv, 0)]).toBool = false
#guard (kscan .add false .i64 .i64 4 none kcols [] [(.rmod, 0)]).toBool = false
#guard (kscan .add false .i64 .i64 0 none kcols [] [(.rdiv, 0)]).toBool = true
#guard (kscan .rdiv false .i64 .i64 4 none kcols).toBool = false
-- reversed (D.6): the forward fold of every column reversed, read back reversed. Rows 3 and 2 start a segment walking
-- back: `100+4 | 100+3, 103+2 | 100+1`
example : kwords ((List.range 4).foldlM (kscanRow .add #[0, 1, 0, 1] #[100, 100, 100, 100] [#[4, 3, 2, 1]]) #[]) =
    [104, 103, 105, 101] := by decide
#guard kread (kscan .add true .i64 .i64 4 kseg kcols) = [101, 105, 103, 104]
-- an `Op.eval` error reaches the caller: `0 div 0` at row 0, both columns zeros
example : ((List.range 4).foldlM (kscanRow .div #[1, 0, 1, 0] #[0, 0, 0, 0] [#[0, 0, 0, 0]]) #[]).toBool = false := by
  decide
#guard (kscan .div false .i64 .i64 4 kseg [Ext.Enc.ofBytes 8 (Column.packIds 64 4 fun _ => 0), Ext.Enc.ofBytes 8 (Column.packIds 64 4 fun _ => 0)]).toBool = false

/-- `0n`'s word: a `min` from a zero seed carries it, the word being negative as an `i64`. -/
private def knan : Enc := Ext.Enc.ofBytes 8 (Column.packIds 64 4 fun i => [1, 0xfff8000000000000, 3, 2][i]!)
-- a NaN word both ways: forward `0, 0 min 0n | 0, 0 min 2`, reversed rows `0 | 0, 0 min 0n | 0`
example : kwords ((List.range 4).foldlM (kscanRow .min #[1, 0, 1, 0] #[0, 0, 0, 0] [#[1, 0xfff8000000000000, 3, 2]])
    #[]) = [0, 0xfff8000000000000, 0, 0] := by decide
example : kwords ((List.range 4).foldlM (kscanRow .min #[0, 1, 0, 1] #[0, 0, 0, 0] [#[2, 3, 0xfff8000000000000, 1]])
    #[]) = [0, 0, 0xfff8000000000000, 0] := by decide
#guard kread (kscan .min false .i64 .i64 4 kseg [Ext.Enc.ofBytes 8 (Column.packIds 64 4 fun _ => 0), knan]) =
  [0, 0xfff8000000000000, 0, 0]
#guard kread (kscan .min true .i64 .i64 4 kseg [Ext.Enc.ofBytes 8 (Column.packIds 64 4 fun _ => 0), knan]) =
  [0, 0xfff8000000000000, 0, 0]
-- the float path on the same words: a NaN is the least float (`fmin`), and `0.0` is the word 0
#guard kread (kscan .fmin false .f64 .f64 4 kseg [Ext.Enc.ofBytes 8 (Column.packIds 64 4 fun _ => 0),
  Ext.Enc.ofBytes 8 (Column.packIds 64 4 fun i => [0x3ff0000000000000, 0xfff8000000000000, 0x4008000000000000, 0x4000000000000000][i]!)]) =
  [0, 0xfff8000000000000, 0, 0]

/-- A boolean answer read back at `boolean`, `[]` unless it is a `foR` (D.5: a boolean is a `foR` of `u1`). -/
private def kbool (r : Except String (Enc × Option UInt64)) : List UInt64 := match r with
  | .ok (.foR m p, _) => ((Enc.foR m p : Enc).raw .u1 4).toList
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

/-- `$` (`Op.cast s t`) as a map over the `n` words `ws` of a `w`-byte column read at `s`, every row a segment: the
    row model by `decide`, the Rust by `#guard`. `2^63` is a row with no image. -/
private def castRows (s t : QAtomicType) (ws : List UInt64) : List UInt64 :=
  kwords ((List.range ws.length).foldlM (kscanRow (.cast s t) (ws.map fun _ => 1).toArray ws.toArray [ws.toArray]) #[])
private def castRun (s t : QAtomicType) (w : Nat) (ws : List UInt64) : List UInt64 :=
  let c : Enc := Ext.Enc.ofBytes w (Column.packIds (8 * w) ws.length fun i => (ws.getD i 0).toNat)
  match kscan (.cast s t) false s t (USize.ofNat ws.length) (some <| .foR (Coc.bools ws.length fun _ => true).1
      (Coc.bools ws.length fun _ => true).2) [c, c] with
  | .ok (e, _) => (e.raw .i64 (USize.ofNat ws.length)).toList
  | .error _ => []
-- `i64 → f64` at 0, ±1, -7, 2^53, 2^53 + 1 (no image), 2^62, the null, 2^63 - 1 (no image)
private def i64s : List UInt64 := [0, 1, (-1 : Int64).toUInt64, (-7 : Int64).toUInt64, 9007199254740992,
  9007199254740993, 4611686018427387904, 0x8000000000000000, 0x7fffffffffffffff]
private def i64f64 : List UInt64 := [0, 0x3ff0000000000000, 0xbff0000000000000, 0xc01c000000000000,
  0x4340000000000000, 0x8000000000000000, 0x43d0000000000000, 0x8000000000000000, 0x8000000000000000]
example : castRows .i64 .f64 i64s = i64f64 := by decide
#guard castRun .i64 .f64 8 i64s = i64f64
-- `i32 → i64` at -5, 0, the `i32` null (no image), `2^31 - 1`; `f32 → f64` at 1.5, the least subnormal, `inf` and
-- `-0` (to `+0`)
example : castRows .i32 .i64 [0xfffffffb, 0, 0x80000000, 0x7fffffff] =
    [0xfffffffffffffffb, 0, 0x8000000000000000, 0x7fffffff] := by decide
#guard castRun .i32 .i64 4 [0xfffffffb, 0, 0x80000000, 0x7fffffff] =
    [0xfffffffffffffffb, 0, 0x8000000000000000, 0x7fffffff]
example : castRows .f32 .f64 [0x3fc00000, 1, 0x7f800000, 0x80000000] =
    [0x3ff8000000000000, 0x36a0000000000000, 0x8000000000000000, 0] := by decide
#guard castRun .f32 .f64 4 [0x3fc00000, 1, 0x7f800000, 0x80000000] =
    [0x3ff8000000000000, 0x36a0000000000000, 0x8000000000000000, 0]
-- a `foR` boolean is a `seg` and a boolean column: the compare's own answer `1 0 1 0` segments as `kseg` does, and
-- reversed, `or` of it with itself carries row 2's `1` back into row 1: rows `0 | 1|1, 1|0 | 1|1`
#guard kread (kscan .gt false .i64 .u1 4 kseg kcols >>= fun g => kscan .add false .i64 .i64 4 g.1 kcols) =
  [101, 103, 103, 107]
example : kwords ((List.range 4).foldlM (kscanRow .or #[0, 1, 0, 1] #[0, 1, 0, 1] [#[0, 1, 0, 1]]) #[]) =
    [0, 1, 1, 1] := by decide
#guard kbool (kscan .gt false .i64 .u1 4 kseg kcols >>= fun g => kscan .or true .u1 .u1 4 g.1 [g.1, g.1]) =
  [1, 1, 1, 0]

-- `pos` (PLAN 6.13) as the seed: row `i` reads `i`, `0+1, 1+2 | 2+3, 5+4`
example : (Ext.Enc.raw (X := Empty) .i64 (USize.ofNat32 4 (by decide)) .pos).toList = [0, 1, 2, 3] := by decide +kernel
example : kwords ((List.range 4).foldlM (kscanRow .add #[1, 0, 1, 0] #[0, 1, 2, 3] [#[1, 2, 3, 4]]) #[]) =
    [1, 3, 5, 9] := by decide
#guard kread (kscan .add false .i64 .i64 4 kseg [.pos, Ext.Enc.ofBytes 8 (Column.packIds 64 4 (· + 1))]) = [1, 3, 5, 9]
-- `pos` is `i64` only: as `seg` (read as booleans) and read at `i32` it holds no raw elements, the error
example : (Ext.Enc.raw (X := Empty) .u1 (USize.ofNat32 4 (by decide)) .pos).size = 0 := by decide +kernel
#guard (kscan .add false .i64 .i64 4 (some .pos) kcols).toBool = false
#guard (kscan .add false .i32 .i64 4 kseg [.pos]).toBool = false

-- The fold result: the word of the row the fold visits last, read off the row fold `out` (in fold order) as its last
-- word cut to the answer type, and `none` with no rows. Forward and segmented: row 3, `103+4`
example : ((List.range 4).foldlM (kscanRow .add #[1, 0, 1, 0] #[100, 100, 100, 100] [#[1, 2, 3, 4]]) #[]).toOption.map
    (·.back?) = some (some 107) := by decide
#guard (kscan .add false .i64 .i64 4 kseg kcols).toOption.map (·.2) = some (some 107)
-- reversed: the fold visits row 0 last, `100+1`
example : ((List.range 4).foldlM (kscanRow .add #[0, 1, 0, 1] #[100, 100, 100, 100] [#[4, 3, 2, 1]]) #[]).toOption.map
    (·.back?) = some (some 101) := by decide
#guard (kscan .add true .i64 .i64 4 kseg kcols).toOption.map (·.2) = some (some 101)
-- no rows: no row is visited, so there is no fold result
example : ((List.range 0).foldlM (kscanRow .add #[] #[] [#[]]) #[]).toOption.map (·.back?) = some none := by decide
#guard (kscan .add false .i64 .i64 0 (some .pos) [.pos, .pos]).toOption.map (·.2) = some none
-- at a float type: `fneg` of row 3's `4.0` is `-4.0`, the sign bit flipped
example : ((List.range 4).foldlM (kscanRow .fneg #[1, 0, 1, 0] #[0, 0, 0, 0]
    [#[0x3ff0000000000000, 0x4000000000000000, 0x4008000000000000, 0x4010000000000000]]) #[]).toOption.map (·.back?) =
    some (some 0xc010000000000000) := by decide
#guard (kscan .fneg false .f64 .f64 4 kseg [Ext.Enc.ofBytes 8 (Column.packIds 64 4 fun _ => 0), Ext.Enc.ofBytes 8 (Column.packIds 64 4
  fun i => [0x3ff0000000000000, 0x4000000000000000, 0x4008000000000000, 0x4010000000000000][i]?.getD 0)]).toOption.map (·.2) =
  some (some 0xc010000000000000)
-- at a narrower answer type: the 64-bit accumulator `2^32 + 107` read at `int` is `107`
example : ((List.range 4).foldlM (kscanRow .add #[1, 0, 1, 0] #[0x100000064, 0x100000064, 0x100000064, 0x100000064]
    [#[1, 2, 3, 4]]) #[]).toOption.map (·.back?.map fun v => UInt64.ofNat (v.toNat % 2 ^ 32)) = some (some 107) := by
  decide
#guard (kscan .add false .i64 .i32 4 kseg [Ext.Enc.ofBytes 8 (Column.packIds 64 4 fun _ => 0x100000064), Ext.Enc.ofBytes 8 (Column.packIds 64 4 (· + 1))]).toOption.map
  (·.2) = some (some 107)

-- A compare against a constant equal to a patched block's frame: `Tab.comp`'s `p < n` of 81 × 729, each of the `n`
-- rows before its `m` partners, so block 0 is framed at 81 with the rows 0 and 1 patched below it. `LT` at `v = frame`
-- once wrapped its bound `0 - 1` and matched every row of that block. Only a block of 1024 rows chooses that frame, so
-- the expected rows are plain arithmetic, not a `decide` of the row fold.
private def kperm : Array Nat := (Array.range 81).flatMap fun g => #[g] ++ (Array.range 729).map (81 + 729 * g + ·)
/-- `kperm`'s rows `f` encoded as the writer encodes a kernel's answer (`Coc.encode 8`). -/
private def kpermCol (f : Nat → Nat) : Enc :=
  let c := Coc.encode 8 (Column.packIds 64 kperm.size fun i => f (kperm[i]?.getD 0))
  .foR c.1 c.2
#guard (kscan .lt false .i64 .u1 (USize.ofNat kperm.size) (some <| .foR (Coc.bools kperm.size fun _ => true).1
    (Coc.bools kperm.size fun _ => true).2) [kpermCol id, kpermCol fun _ => 81]).toOption.map
  (fun r => (r.1.raw .u1 (USize.ofNat kperm.size)).toList) = some (kperm.toList.map fun v => if v < 81 then 1 else 0)
-- every compare at, below and above that frame, the constant on either side: each row's bit is `Op.eval` of its two
-- words, run compiled
private def kconst (v : Nat) : Enc := kpermCol fun _ => v
#guard [80, 81, 82].all fun v => [Op.eq, .ne, .lt, .le, .gt, .ge].all fun op => [false, true].all fun sw =>
  (kscan op false .i64 .u1 (USize.ofNat kperm.size) (some <| .foR (Coc.bools kperm.size fun _ => true).1
    (Coc.bools kperm.size fun _ => true).2) (if sw then [kconst v, kpermCol id] else [kpermCol id, kconst v])).toOption.map
  (fun r => (r.1.raw .u1 (USize.ofNat kperm.size)).toList) == some (kperm.toList.map fun p =>
    (op.eval (if sw then v else p).toUInt64 (if sw then p else v).toUInt64).toOption.getD 2)

-- Past a block, `#guard` only: 2500 rows, a segment starting at every thousandth row and at `i % 37 = 3`, the seed and
-- the folded column with patches (every 97th word an outlier), each op's answer against `kscanRow`'s fold run compiled
private def kn : Nat := 2500
private def kstarts : Array UInt64 := (Array.range kn).map fun i => if i % 1000 = 0 || i % 37 = 3 then 1 else 0
private def kpatched (k : Nat) : Array UInt64 :=
  (Array.range kn).map fun i => (if i % 97 = k then i * 2 ^ 33 else i * 7919 % 5000 + k).toUInt64
private def kfoR (ws : Array UInt64) : Enc :=
  let c := Coc.encode 8 (Column.packIds 64 ws.size fun i => (ws[i]?.getD 0).toNat)
  .foR c.1 c.2
#guard [Op.add, .sub, .min, .max, .first, .last, .and, .or, .lt, .eq].all fun op =>
  (kscan op false .i64 .i64 (USize.ofNat kn) (some <| .foR (Coc.bools kn fun i => kstarts[i]? == some 1).1
    (Coc.bools kn fun i => kstarts[i]? == some 1).2) [kfoR (kpatched 5), kfoR (kpatched 11)]).toOption.map
    (fun r => (r.1.raw .i64 (USize.ofNat kn)).toList) ==
  ((List.range kn).foldlM (kscanRow op kstarts (kpatched 5) [kpatched 11]) #[]).toOption.map (·.toList)

end Rel.Kernel


namespace Rel.Kernel.Scan

/-- info: 'Rel.Kernel.Scan.scanOf_size' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Rel.Kernel.Scan.scanOf_size

end Rel.Kernel.Scan
