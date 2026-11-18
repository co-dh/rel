import Rel.Kernel.Gather

/-! `kgather`'s `decide`-beside-`#guard` pairs: each `example` evaluates the Lean body (the composition), each `#guard` the
Rust export `qlean_k_gather` (the fused form), against one literal. -/

namespace Rel.Kernel.GatherTest
open Ext.Enc

/-- `k` as a `USize` whose `toNat` the kernel reduces: a literal's is `k % 2 ^ numBits`, and `numBits` is opaque. -/
def u (k : Nat) (h : k < 4294967296 := by decide) : USize := USize.ofNat32 k h

/-- `xs` as the `foR` column the kernels answer (`wordsFoR`). -/
def col (xs : List UInt64) : Enc := wordsFoR xs.toArray

/-- An answer as its error, or its metadata and pack bytes: equal to `col`'s of the expected words, caches included. -/
def view : Except String Enc → String ⊕ (List UInt8 × List UInt8)
  | .error s => .inl s
  | .ok (.foR md pk) => .inr (md.toList, pk.toList)
  | .ok _ => .inl "not foR"

-- rows read `e` at 2, 0, 2, 3
example : view (kgather (u 4) (col [2, 0, 2, 3]) (u 4) (col [10, 11, 12, 13])) = view (.ok (col [12, 10, 12, 13])) := by
  decide +kernel
#guard view (kgather (u 4) (col [2, 0, 2, 3]) (u 4) (col [10, 11, 12, 13])) == view (.ok (col [12, 10, 12, 13]))

-- an index `≥ n` is the error, named with its row, never a fill
def past : String ⊕ (List UInt8 × List UInt8) := .inl "gather: index 3 at row 1 is not below n = 3"
example : view (kgather (u 3) (col [1, 3, 9]) (u 3) (col [1, 2, 3])) = past := by decide +kernel
#guard view (kgather (u 3) (col [1, 3, 9]) (u 3) (col [1, 2, 3])) == past

-- a form other than `foR`, and a `foR` whose blocks do not cover the count, named by the argument they came in
def dense : String ⊕ (List UInt8 × List UInt8) := .inl "gather: e: constructor 0 is not foR"
example : view (kgather (u 2) (col [0, 1]) (u 2) (.bytes (ByteArray.mk (Array.replicate 16 0)))) = dense := by
  decide +kernel
#guard view (kgather (u 2) (col [0, 1]) (u 2) (.bytes (ByteArray.mk (Array.replicate 16 0)))) == dense
def short : String ⊕ (List UInt8 × List UInt8) := .inl "gather: ix: foR: 1 blocks of 2^10 and a 128-byte pack are not the layout of 2000 elements"
example : view (kgather (u 2000) (col [0, 1]) (u 2) (col [0, 1])) = short := by decide +kernel
#guard view (kgather (u 2000) (col [0, 1]) (u 2) (col [0, 1])) == short

end Rel.Kernel.GatherTest
