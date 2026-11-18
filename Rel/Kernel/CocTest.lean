import Rel.Kernel.Coc

/-! `Coc.encode`'s `decide`-beside-`#guard` pairs on the exact bytes: each `example` evaluates the Lean body, each
`#guard` the Rust export `qlean_coc_encode`, against one literal. The blocks are ones where a cost-minimising width
would differ from the bit length `Coc.blockOf` takes: a tie in the bytes of a short block, and an outlier a patch
would be cheaper for. -/

namespace Rel.Kernel.CocTest

/-- `k` as a `USize` whose `toNat` the kernel reduces: a literal's is `k % 2 ^ numBits`, and `numBits` is opaque. -/
def u (k : Nat) (h : k < 4294967296 := by decide) : USize := USize.ofNat32 k h

/-- `xs` encoded at 8 bytes, as the metadata and pack bytes. -/
def enc (xs : List UInt64) : List UInt8 × List UInt8 :=
  let r := Coc.encode (u 8) (xs.foldl (init := .empty) fun acc w => Column.pushBits acc w 8)
  (r.1.data.toList, r.2.data.toList)

/-- `v` as 8 little-endian bytes. -/
def le (v : UInt64) : List UInt8 := (List.range 8).map fun i => (v >>> (8 * i).toUInt64).toUInt8

/-- One block's metadata: base, maximum, offset 0, sum, the trailer (null, count, `lg` 10), the width. -/
def md (mn mx s n : UInt64) (w : UInt8) : List UInt8 :=
  le mn ++ le mx ++ le 0 ++ le s ++ le 0x8000000000000000 ++ le n ++ le 10 ++ [w]

-- residuals 4 0 5 0: width 3 (384 bytes); width 4 costs the same 2 bytes of 4 residuals
example : enc [11, 7, 12, 7] = (md 7 12 37 4 3, [68, 1] ++ List.replicate 382 0) := by decide +kernel
#guard enc [11, 7, 12, 7] == (md 7 12 37 4 3, [68, 1] ++ List.replicate 382 0)

-- residuals 0 1: width 1 (128 bytes); widths 2 to 4 cost the same 1 byte
example : enc [0, 1] = (md 0 1 1 2 1, [2] ++ List.replicate 127 0) := by decide +kernel
#guard enc [0, 1] == (md 0 1 1 2 1, [2] ++ List.replicate 127 0)

-- one outlier 255 after ten zeros: width 8 (1024 bytes), never a patch, though one costs 10 bytes to width 8's 11
example : enc (List.replicate 10 0 ++ [255]) =
    (md 0 255 255 11 8, List.replicate 10 0 ++ [255] ++ List.replicate 1013 0) := by decide +kernel
#guard enc (List.replicate 10 0 ++ [255]) == (md 0 255 255 11 8, List.replicate 10 0 ++ [255] ++ List.replicate 1013 0)

end Rel.Kernel.CocTest
