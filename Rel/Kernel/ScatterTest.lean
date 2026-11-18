import Rel.Kernel.Scatter

/-! `kscatter`'s `decide`-beside-`#guard` pairs: each `example` evaluates the Lean body, each `#guard` the Rust export
`qlean_k_scatter`, against one literal. -/

namespace Rel.Kernel.ScatterTest
open Ext.Enc

/-- `k` as a `USize` whose `toNat` the kernel reduces: a literal's is `k % 2 ^ numBits`, and `numBits` is opaque. -/
def u (k : Nat) (h : k < 4294967296 := by decide) : USize := USize.ofNat32 k h

/-- `xs` as a `packed` column at blocks of `2 ^ 3`, the way `pack.rs` encodes one. -/
def col (xs : List UInt64) : Enc :=
  Coc.packedOf 3 (u 8) (xs.foldl (init := .empty) fun acc w => Column.pushBits acc w 8)

/-- An answer as its error, or its block size, bases, widths, payload size and the `n` words `Enc.raw` reads from it: with
the bases and widths equal, the words pin the payload's bits. -/
def view (n : USize) : Except String Enc → String ⊕ (UInt8 × List UInt8 × List UInt8 × Nat × List UInt64)
  | .error s => .inl s
  | .ok o@(.packed lg b w p) => .inr (lg, b.toList, w.toList, p.size, (raw .long n o).toList)
  | .ok _ => .inl "not packed"

-- row 2 overwrites row 0's cell; cells 1 and 3 keep the fill; one block of `2 ^ 10`, base 7, width 3 (`12 - 7 < 2 ^ 3`)
def wrote : String ⊕ (UInt8 × List UInt8 × List UInt8 × Nat × List UInt64) :=
  .inr (10, [7, 0, 0, 0, 0, 0, 0, 0], [3], 384, [11, 7, 12, 7])
example : view (u 4) (kscatter (u 3) (col [2, 0, 2]) (col [10, 11, 12]) (u 4) 7) = wrote := by decide +kernel
#guard view (u 4) (kscatter (u 3) (col [2, 0, 2]) (col [10, 11, 12]) (u 4) 7) == wrote

-- an index `≥ n` is the error, named with its row, never dropped
def past : String ⊕ (UInt8 × List UInt8 × List UInt8 × Nat × List UInt64) :=
  .inl "scatter: index 5 at row 1 is not below n = 3"
example : view (u 3) (kscatter (u 3) (col [1, 5, 9]) (col [1, 2, 3]) (u 3) 0) = past := by decide +kernel
#guard view (u 3) (kscatter (u 3) (col [1, 5, 9]) (col [1, 2, 3]) (u 3) 0) == past

-- a form other than `packed`, and a `packed` whose blocks do not cover `m`
def dense : String ⊕ (UInt8 × List UInt8 × List UInt8 × Nat × List UInt64) :=
  .inl "scatter: e: constructor 0 is not packed"
example : view (u 2) (kscatter (u 2) (col [0, 1]) (.bytes (ByteArray.mk (Array.replicate 16 0))) (u 2) 0) = dense := by
  decide +kernel
#guard view (u 2) (kscatter (u 2) (col [0, 1]) (.bytes (ByteArray.mk (Array.replicate 16 0))) (u 2) 0) == dense
def short : String ⊕ (UInt8 × List UInt8 × List UInt8 × Nat × List UInt64) :=
  .inl "scatter: ix: packed: 1 widths for 2 blocks of 2^3 at n = 9"
example : view (u 9) (kscatter (u 9) (col [0, 1, 2]) (col [0, 1, 2]) (u 9) 0) = short := by decide +kernel
#guard view (u 9) (kscatter (u 9) (col [0, 1, 2]) (col [0, 1, 2]) (u 9) 0) == short

end Rel.Kernel.ScatterTest
