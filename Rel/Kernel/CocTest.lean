import Rel.Kernel.Scatter
import Rel.Kernel.Elementwise
import Rel.Kernel.Search

/-! `Coc.encode`'s `decide`-beside-`#guard` pairs on the exact bytes: each `example` evaluates the Lean body, each
`#guard` the Rust export, against one literal. The blocks are a tie in `Coc.cost` (the narrower width wins), an
outlier a patch is cheaper for, and a low outlier under which the frame is lifted; then the patched and framed
columns through the Rust readers `qlean_coc_decode`, `qlean_coc_over` and `qlean_k_scatter`. -/

namespace Rel.Kernel.CocTest
open Ext.Enc

/-- `k` as a `USize` whose `toNat` the kernel reduces: a literal's is `k % 2 ^ numBits`, and `numBits` is opaque. -/
def u (k : Nat) (h : k < 4294967296 := by decide) : USize := USize.ofNat32 k h

/-- `xs` as 8-byte elements. -/
def dense (xs : List UInt64) : ByteArray := xs.foldl (init := .empty) fun acc w => Column.pushBits acc w 8

/-- `xs` encoded at 8 bytes, as the metadata and pack bytes. -/
def enc (xs : List UInt64) : List UInt8 × List UInt8 :=
  let r := Coc.encode (u 8) (dense xs)
  (r.1.data.toList, r.2.data.toList)

/-- `v` as `k` little-endian bytes. -/
def le (v : UInt64) (k : Nat := 8) : List UInt8 := (List.range k).map fun i => (v >>> (8 * i).toUInt64).toUInt8

/-- One block's metadata: base, maximum, offset 0, sum, the trailer (null, count, `lg` 10), the width. -/
def md (mn mx s n : UInt64) (w : UInt8) : List UInt8 :=
  le mn ++ le mx ++ le 0 ++ le s ++ le 0x8000000000000000 ++ le n ++ le 10 ++ [w]

/-- A one-block patch list of 8-byte elements: its count, its flag word, the elements, `exc_off`, `exc_pos` (each
section padded to 8 bytes) and `last`. -/
def patches (word : UInt64) (raw : List UInt64) (pos : List Nat) (last : List UInt8) : List UInt8 :=
  le raw.length.toUInt64 ++ le word ++ raw.flatMap (le ·) ++ le 0 ++ le raw.length.toUInt64
    ++ pos.flatMap (fun p => le p.toUInt64 2) ++ List.replicate ((8 - 2 * pos.length % 8) % 8) 0 ++ last

-- residuals 4 0 5 0: width 3 (2 bytes); width 4 costs the same 2 bytes, and the narrower wins
example : enc [11, 7, 12, 7] = (md 7 12 37 4 3, [68, 1] ++ List.replicate 382 0) := by decide +kernel
#guard enc [11, 7, 12, 7] == (md 7 12 37 4 3, [68, 1] ++ List.replicate 382 0)

-- residuals 0 1: width 1 (1 byte); width 0 with a patch costs 10
example : enc [0, 1] = (md 0 1 1 2 1, [2] ++ List.replicate 127 0) := by decide +kernel
#guard enc [0, 1] == (md 0 1 1 2 1, [2] ++ List.replicate 127 0)

-- Each instance below is the fewest elements its case needs: `decide +kernel`'s memory grows with the elements read and
-- the pack's `2 ^ lgEnc * width / 8` bytes (17 at width 4 took 13.7 GB through `kscatter`); a large outlier lets three win.
-- one outlier 2 ^ 32 after two zeros: width 0 and 2 ^ 32 patched (10 bytes), not width 33 (13 bytes)
def outlier : List UInt64 := [0, 0, 4294967296]
def outlierBytes : List UInt8 × List UInt8 := (md 0 4294967296 4294967296 3 0, patches 8 [4294967296] [2] [])
example : enc outlier = outlierBytes := by decide +kernel
#guard enc outlier == outlierBytes

-- a low outlier 0 under 2 ^ 32 and 2 ^ 32 + 1: the frame lifted to 2 ^ 32 at width 1 (1 byte) and 0 patched, 11 bytes
-- in all, under width 33 from the minimum (13 bytes); the frame section holds 2 ^ 32
def lifted : List UInt64 := [0, 4294967296, 4294967297]
def liftedBytes : List UInt8 × List UInt8 :=
  (md 0 4294967297 8589934593 3 1, [4] ++ List.replicate 127 0 ++ patches (8 ||| 256) [0] [0] (le 4294967296))
example : enc lifted = liftedBytes := by decide +kernel
#guard enc lifted == liftedBytes

/-- `xs` (`n` elements) encoded, decoded back by `Coc.decode`. -/
def decoded (xs : List UInt64) (n : USize) : List UInt8 :=
  let r := Coc.encode (u 8) (dense xs)
  (Coc.decode (u 8) r.1 r.2 n).data.toList

example : decoded outlier (u 3) = (dense outlier).data.toList := by decide +kernel
#guard decoded outlier (u 3) == (dense outlier).data.toList
example : decoded lifted (u 3) = (dense lifted).data.toList := by decide +kernel
#guard decoded lifted (u 3) == (dense lifted).data.toList

/-- `xs` (`n` elements) encoded, summed by `Coc.over`. -/
def summed (xs : List UInt64) (n : USize) : Int64 :=
  let r := Coc.encode (u 8) (dense xs)
  Coc.over .add Int64.minValue r.1 r.2 n

example : summed outlier (u 3) = 4294967296 := by decide +kernel
#guard summed outlier (u 3) == 4294967296
example : summed lifted (u 3) = 8589934593 := by decide +kernel
#guard summed lifted (u 3) == 8589934593

/-- `xs` at 8 bytes with the rows `ns` null, encoded by `Coc.encode`, as the metadata and pack bytes. -/
def encN (xs : List UInt64) (ns : List Nat) : List UInt8 × List UInt8 :=
  let r := Coc.encode (u 8) (dense xs) (Column.packIds 1 xs.length fun i => (ns.contains i).toNat)
  (r.1.data.toList, r.2.data.toList)

/-- Each row of `encN xs ns` read back by `Column.foROpt`: `none` at a null, tested on the block. -/
def readN (xs : List UInt64) (ns : List Nat) : List (Option UInt64) :=
  let r := Coc.encode (u 8) (dense xs) (Column.packIds 1 xs.length fun i => (ns.contains i).toNat)
  (List.range xs.length).map (Column.foROpt r.1 r.2 #[])

-- values 3 4 6 at rows 0 2 3, nulls at 1 4: range 3 = `2 ^ 2 - 1` reaches the top residual, so width 3, flagged (131);
-- residuals 0 7 1 3 7
example : encN [3, 0, 4, 6, 0] [1, 4] = (md 3 6 13 5 131, [120, 118] ++ List.replicate 382 0) := by decide +kernel
#guard encN [3, 0, 4, 6, 0] [1, 4] == (md 3 6 13 5 131, [120, 118] ++ List.replicate 382 0)
example : readN [3, 0, 4, 6, 0] [1, 4] = [some 3, none, some 4, some 6, none] := by decide +kernel
#guard readN [3, 0, 4, 6, 0] [1, 4] == [some 3, none, some 4, some 6, none]

-- `Int64.min`, `Int64.max` and a null in one block: the range is all `2 ^ 64` keys, width 64 cannot widen, and
-- `Int64.max - Int64.min = 2 ^ 64 - 1` is the null's code, so the `Int64.max` row is patched and reads as itself
example : readN [0x8000000000000000, 0x7fffffffffffffff, 0] [2] =
    [some 0x8000000000000000, some 0x7fffffffffffffff, none] := by decide +kernel
#guard readN [0x8000000000000000, 0x7fffffffffffffff, 0] [2] ==
    [some 0x8000000000000000, some 0x7fffffffffffffff, none]

-- every row null: width 0, flagged (128), no residual bytes
example : encN [0, 0] [0, 1] = (md 0 0 0 2 128, []) := by decide +kernel
#guard encN [0, 0] [0, 1] == (md 0 0 0 2 128, [])

-- no null: the unpatched column, here the same bytes as `encode`'s
example : encN [11, 7, 12, 7] [] = enc [11, 7, 12, 7] := by decide +kernel
#guard encN [11, 7, 12, 7] [] == enc [11, 7, 12, 7]

/-- `xs` as a `foR` column. -/
def col (xs : List UInt64) : Enc := let r := Coc.encode (u 8) (dense xs); .foR r.1 r.2

/-- A `kscatter` answer as its metadata and pack bytes. -/
def view : Except String Enc → String ⊕ (List UInt8 × List UInt8)
  | .error s => .inl s
  | .ok (.foR md p) => .inr (md.data.toList, p.data.toList)
  | .ok _ => .inl "not foR"

-- the patched and the framed column as `kscatter`'s `e`, each row to its own cell: the answer is the column again
example : view (kscatter .last (u 3) (col ((List.range 3).map (·.toUInt64))) (col outlier) (u 3) 0) = .inr outlierBytes := by
  decide +kernel
#guard view (kscatter .last (u 3) (col ((List.range 3).map (·.toUInt64))) (col outlier) (u 3) 0) == .inr outlierBytes
example : view (kscatter .last (u 3) (col ((List.range 3).map (·.toUInt64))) (col lifted) (u 3) 0) = .inr liftedBytes := by
  decide +kernel
#guard view (kscatter .last (u 3) (col ((List.range 3).map (·.toUInt64))) (col lifted) (u 3) 0) == .inr liftedBytes

/-! Element width 1 through `qlean_coc_encode` and `qlean_coc_decode`: the first block above at one byte an element. -/

/-- `xs` as 1-byte elements. -/
def bytes1 (xs : List UInt8) : ByteArray := ⟨xs.toArray⟩

example : (fun r : ByteArray × ByteArray => (r.1.data.toList, r.2.data.toList)) (Coc.encode (u 1) (bytes1 [11, 7, 12, 7]))
    = (md 7 12 37 4 3, [68, 1] ++ List.replicate 382 0) := by decide +kernel
#guard (fun r : ByteArray × ByteArray => (r.1.data.toList, r.2.data.toList)) (Coc.encode (u 1) (bytes1 [11, 7, 12, 7]))
    == (md 7 12 37 4 3, [68, 1] ++ List.replicate 382 0)
example : (Coc.decode (u 1) (Coc.encode (u 1) (bytes1 [11, 7, 12, 7])).1 (Coc.encode (u 1) (bytes1 [11, 7, 12, 7])).2 (u 4)).data.toList
    = [11, 7, 12, 7] := by decide +kernel
#guard (Coc.decode (u 1) (Coc.encode (u 1) (bytes1 [11, 7, 12, 7])).1 (Coc.encode (u 1) (bytes1 [11, 7, 12, 7])).2 (u 4)).data.toList
    == [11, 7, 12, 7]

/-! The boolean writers' pairs: each answers `Coc.bools`' `u1` column — a mixed block width 1 with its bitmap as the
residuals, an all-0 or all-1 block width 0 at base 0 or 1 and no residual. -/

/-- A writer's answer as the metadata and pack bytes. -/
def parts (r : ByteArray × ByteArray) : List UInt8 × List UInt8 := (r.1.data.toList, r.2.data.toList)

/-- One mixed block's pack: the bitmap byte, then the rest of the block's 128 residual bytes. -/
def mixed (b : UInt8) : List UInt8 := b :: List.replicate 127 0

-- 1 5 2 7 3 against 4: `<` is 1 0 1 0 1 (bitmap 21), `<` against 100 all 1, `>` against 100 all 0
example : parts (Ew.cmp Ew.lt Ew.i64 Ew.va (dense [1, 5, 2, 7, 3]) (dense [4]) (u 5)) = (md 0 1 3 5 1, mixed 21) := by
  decide +kernel
#guard parts (Ew.cmp Ew.lt Ew.i64 Ew.va (dense [1, 5, 2, 7, 3]) (dense [4]) (u 5)) == (md 0 1 3 5 1, mixed 21)
example : parts (Ew.cmp Ew.lt Ew.i64 Ew.va (dense [1, 5, 2, 7, 3]) (dense [100]) (u 5)) = (md 1 1 5 5 0, []) := by
  decide +kernel
#guard parts (Ew.cmp Ew.lt Ew.i64 Ew.va (dense [1, 5, 2, 7, 3]) (dense [100]) (u 5)) == (md 1 1 5 5 0, [])
example : parts (Ew.cmp Ew.gt Ew.i64 Ew.va (dense [1, 5, 2, 7, 3]) (dense [100]) (u 5)) = (md 0 0 0 5 0, []) := by
  decide +kernel
#guard parts (Ew.cmp Ew.gt Ew.i64 Ew.va (dense [1, 5, 2, 7, 3]) (dense [100]) (u 5)) == (md 0 0 0 5 0, [])

-- 10111 & 11101 is 10101; & with an all-0 atom is all 0
example : parts (Ew.bit Ew.lesser Ew.vv (bytes1 [0b11101]) (bytes1 [0b10111]) (u 5)) = (md 0 1 3 5 1, mixed 21) := by
  decide +kernel
#guard parts (Ew.bit Ew.lesser Ew.vv (bytes1 [0b11101]) (bytes1 [0b10111]) (u 5)) == (md 0 1 3 5 1, mixed 21)
example : parts (Ew.bit Ew.lesser Ew.va (bytes1 [0b11101]) (bytes1 [0]) (u 5)) = (md 0 0 0 5 0, []) := by decide +kernel
#guard parts (Ew.bit Ew.lesser Ew.va (bytes1 [0b11101]) (bytes1 [0]) (u 5)) == (md 0 0 0 5 0, [])

-- `boolsOf`'s Rust against its body: a mixed, an all-0 and a short all-1 block, and a bitmap shorter than `n`
#guard parts (Coc.boolsOf (u 2600) (packOf 2600 fun i => (i % 3 == 0 && i < 1024) || 2048 ≤ i)) ==
  parts (Coc.bools 2600 (Column.bitAt (packOf 2600 fun i => (i % 3 == 0 && i < 1024) || 2048 ≤ i)))
#guard parts (Coc.boolsOf (u 12) (bytes1 [0b101])) == parts (Coc.bools 12 (Column.bitAt (bytes1 [0b101])))

end Rel.Kernel.CocTest
