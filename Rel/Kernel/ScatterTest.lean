import Rel.Kernel.Scatter

/-! `kscatter`'s `decide`-beside-`#guard` pairs: each `example` evaluates the Lean body, each `#guard` the Rust export
`qlean_k_scatter`, against one literal. -/

namespace Rel.Kernel.ScatterTest
open Ext.Enc

/-- `k` as a `USize` whose `toNat` the kernel reduces: a literal's is `k % 2 ^ numBits`, and `numBits` is opaque. -/
def u (k : Nat) (h : k < 4294967296 := by decide) : USize := USize.ofNat32 k h

/-- `xs` as a `foR` column, `Coc.encode` at 8 bytes. -/
def col (xs : List UInt64) : Enc :=
  let r := Coc.encode (u 8) (xs.foldl (init := .empty) fun acc w => Column.pushBits acc w 8)
  .foR r.1 r.2

/-- An answer as its error, or its block size `lg`, whether `Coc.foRStd` admits its layout at `n`, and the `n` words
`Enc.raw` reads from it. Not the widths or the pack: the encoding owes the words, and Rust's `width_exc` breaks a cost
tie toward the wider width where `Coc.encode` takes the bit length, so the bytes are a choice the two may differ on. -/
def view (n : USize) : Except String Enc → String ⊕ (UInt8 × Bool × List UInt64)
  | .error s => .inl s
  | .ok o@(.foR md p) => .inr ((Column.lgAt md).toUInt8, Coc.foRStd n md p, (raw .long n o).toList)
  | .ok _ => .inl "not foR"

-- row 2 overwrites row 0's cell; cells 1 and 3 keep the fill; one block of `2 ^ 10`
def wrote : String ⊕ (UInt8 × Bool × List UInt64) := .inr (10, true, [11, 7, 12, 7])
example : view (u 4) (kscatter (u 3) (col [2, 0, 2]) (col [10, 11, 12]) (u 4) 7) = wrote := by decide +kernel
#guard view (u 4) (kscatter (u 3) (col [2, 0, 2]) (col [10, 11, 12]) (u 4) 7) == wrote

-- an index `≥ n` is the error, named with its row, never dropped
def past : String ⊕ (UInt8 × Bool × List UInt64) := .inl "scatter: index 5 at row 1 is not below n = 3"
example : view (u 3) (kscatter (u 3) (col [1, 5, 9]) (col [1, 2, 3]) (u 3) 0) = past := by decide +kernel
#guard view (u 3) (kscatter (u 3) (col [1, 5, 9]) (col [1, 2, 3]) (u 3) 0) == past

-- a form other than `foR`, and a `foR` whose blocks do not cover `m`
def dense : String ⊕ (UInt8 × Bool × List UInt64) := .inl "scatter: e: constructor 0 is not foR"
example : view (u 2) (kscatter (u 2) (col [0, 1]) (.bytes (ByteArray.mk (Array.replicate 16 0))) (u 2) 0) = dense := by
  decide +kernel
#guard view (u 2) (kscatter (u 2) (col [0, 1]) (.bytes (ByteArray.mk (Array.replicate 16 0))) (u 2) 0) == dense
def short : String ⊕ (UInt8 × Bool × List UInt64) :=
  .inl "scatter: ix: foR: 1 blocks of 2^10 and a 256-byte pack are not the layout of 1025 elements"
example : view (u 9) (kscatter (u 1025) (col [0, 1, 2]) (col [0, 1, 2]) (u 9) 0) = short := by decide +kernel
#guard view (u 9) (kscatter (u 1025) (col [0, 1, 2]) (col [0, 1, 2]) (u 9) 0) == short

end Rel.Kernel.ScatterTest
