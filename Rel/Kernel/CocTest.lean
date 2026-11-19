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
  le raw.length.toUInt64 ++ le word ++ raw.flatMap (le ·) ++ le 0 4 ++ le raw.length.toUInt64 4
    ++ pos.flatMap (fun p => le p.toUInt64 2) ++ List.replicate ((8 - 2 * pos.length % 8) % 8) 0 ++ last

-- residuals 4 0 5 0: width 3 (2 bytes); width 4 costs the same 2 bytes, and the narrower wins
example : enc [11, 7, 12, 7] = (md 7 12 37 4 3, [68, 1] ++ List.replicate 382 0) := by decide +kernel
#guard enc [11, 7, 12, 7] == (md 7 12 37 4 3, [68, 1] ++ List.replicate 382 0)

-- residuals 0 1: width 1 (1 byte); width 0 with a patch costs 10
example : enc [0, 1] = (md 0 1 1 2 1, [2] ++ List.replicate 127 0) := by decide +kernel
#guard enc [0, 1] == (md 0 1 1 2 1, [2] ++ List.replicate 127 0)

-- one outlier 255 after ten zeros: width 0 and 255 patched (10 bytes), not width 8 (11 bytes)
def outlier : List UInt64 := List.replicate 10 0 ++ [255]
def outlierBytes : List UInt8 × List UInt8 := (md 0 255 255 11 0, patches 8 [255] [10] [])
example : enc outlier = outlierBytes := by decide +kernel
#guard enc outlier == outlierBytes

-- a low outlier 0 under 1000 .. 1015: the frame lifted to 1000 at width 4 (9 bytes) and 0 patched, 19 bytes in all,
-- under width 10 from the minimum (22 bytes); the frame section holds 1000
def lifted : List UInt64 := 0 :: (List.range 16).map fun k => (1000 + k).toUInt64
def liftedBytes : List UInt8 × List UInt8 :=
  (md 0 1015 16120 17 4, [0, 33, 67, 101, 135, 169, 203, 237, 15] ++ List.replicate 503 0
    ++ patches (8 ||| 256) [0] [0] (le 1000))
example : enc lifted = liftedBytes := by decide +kernel
#guard enc lifted == liftedBytes

/-- `xs` (`n` elements) encoded, decoded back by `Coc.decode`. -/
def decoded (xs : List UInt64) (n : USize) : List UInt8 :=
  let r := Coc.encode (u 8) (dense xs)
  (Coc.decode (u 8) r.1 r.2 n).data.toList

example : decoded outlier (u 11) = (dense outlier).data.toList := by decide +kernel
#guard decoded outlier (u 11) == (dense outlier).data.toList
example : decoded lifted (u 17) = (dense lifted).data.toList := by decide +kernel
#guard decoded lifted (u 17) == (dense lifted).data.toList

/-- `xs` (`n` elements) encoded, summed by `Coc.over`. -/
def summed (xs : List UInt64) (n : USize) : Int64 :=
  let r := Coc.encode (u 8) (dense xs)
  Coc.over .add Int64.minValue r.1 r.2 n

example : summed outlier (u 11) = 255 := by decide +kernel
#guard summed outlier (u 11) == 255
example : summed lifted (u 17) = 16120 := by decide +kernel
#guard summed lifted (u 17) == 16120

/-- `xs` as a `foR` column. -/
def col (xs : List UInt64) : Enc := let r := Coc.encode (u 8) (dense xs); .foR r.1 r.2

/-- A `kscatter` answer as its metadata and pack bytes. -/
def view : Except String Enc → String ⊕ (List UInt8 × List UInt8)
  | .error s => .inl s
  | .ok (.foR md p) => .inr (md.data.toList, p.data.toList)
  | .ok _ => .inl "not foR"

-- the patched and the framed column as `kscatter`'s `e`, each row to its own cell: the answer is the column again
example : view (kscatter (u 11) (col ((List.range 11).map (·.toUInt64))) (col outlier) (u 11) 0) = .inr outlierBytes := by
  decide +kernel
#guard view (kscatter (u 11) (col ((List.range 11).map (·.toUInt64))) (col outlier) (u 11) 0) == .inr outlierBytes
example : view (kscatter (u 17) (col ((List.range 17).map (·.toUInt64))) (col lifted) (u 17) 0) = .inr liftedBytes := by
  decide +kernel
#guard view (kscatter (u 17) (col ((List.range 17).map (·.toUInt64))) (col lifted) (u 17) 0) == .inr liftedBytes

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

-- `memberVec`, `memberIdsVec` and `memberBits` have no `decide`: `findScalar` and `findBit` take `Nat.toUSize`, which the
-- kernel cannot reduce (`USize.ofNat` reads `System.Platform.numBits`), so their pairs are `#guard` only
-- 1 5 2 in 5 9 is 0 1 0, at longs and at 8-bit ids; 1 0 1 in a haystack holding both bits is all 1
#guard parts (memberVec (u 8) false (dense [1, 5, 2]) (dense [5, 9])) == (md 0 1 1 3 1, mixed 2)
#guard parts (memberIdsVec (u 8) (bytes1 [1, 5, 2]) (u 3) (u 8) (bytes1 [5, 9]) (u 2)) == (md 0 1 1 3 1, mixed 2)
#guard parts (memberBits (u 3) (bytes1 [0b101]) (u 2) (bytes1 [0b10])) == (md 1 1 3 3 0, [])

end Rel.Kernel.CocTest
