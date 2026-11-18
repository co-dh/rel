import Rel.Kernel.Distinct

/-! `kdistinct`'s `decide`-beside-`#guard` pairs: each `example` evaluates the Lean body, each `#guard` the Rust export
`qlean_k_distinct`, against one literal. -/

namespace Rel.Kernel.DistinctTest
open Ext.Enc

/-- `k` as a `USize` whose `toNat` the kernel reduces: a literal's is `k % 2 ^ numBits`, and `numBits` is opaque. -/
def u (k : Nat) (h : k < 4294967296 := by decide) : USize := USize.ofNat32 k h

/-- `xs` as the `foR` column `Coc.encode` writes at 8 bytes. -/
def col (xs : List UInt64) : Enc :=
  let (md, pk) := Coc.encodeAt Column.lgEnc (u 8) (xs.foldl (init := .empty) fun acc w => Column.pushBits acc w 8)
  .foR md pk

/-- An answer as its error, or its count and the `m` words `Enc.raw` reads from it; `m` is the count the literal
expects, a `USize` the kernel reduces. -/
def view (m : USize) : Except String (Nat × Enc) → String ⊕ (Nat × List UInt64)
  | .error s => .inl s
  | .ok (k, o) => .inr (k, (raw .long m o).toList)

-- rows (1,0) (1,0) (2,0) (2,1) (2,1): runs start at rows 0, 2 and 3
def runs : String ⊕ (Nat × List UInt64) := .inr (3, [0, 2, 3])
example : view (u 3) (kdistinct (u 5) [col [1, 1, 2, 2, 2], col [0, 0, 0, 1, 1]]) = runs := by decide +kernel
#guard view (u 3) (kdistinct (u 5) [col [1, 1, 2, 2, 2], col [0, 0, 0, 1, 1]]) == runs

-- no column: every row is the empty row, one run
def one : String ⊕ (Nat × List UInt64) := .inr (1, [0])
example : view (u 1) (kdistinct (u 3) []) = one := by decide +kernel
#guard view (u 1) (kdistinct (u 3) []) == one

-- a column that is not `foR`, and a `foR` whose blocks do not cover `n`, are the error, named by their place in `es`
def dense : String ⊕ (Nat × List UInt64) := .inl "distinct: es[1]: constructor 0 is not foR"
example : view (u 0) (kdistinct (u 2) [col [0, 1], .bytes (ByteArray.mk (Array.replicate 16 0))]) = dense := by
  decide +kernel
#guard view (u 0) (kdistinct (u 2) [col [0, 1], .bytes (ByteArray.mk (Array.replicate 16 0))]) == dense
def short : String ⊕ (Nat × List UInt64) := .inl "distinct: es[0]: foR: 1 blocks of 2^10 and a 128-byte pack are not the layout of 2000 elements"
example : view (u 0) (kdistinct (u 2000) [col [0, 1]]) = short := by decide +kernel
#guard view (u 0) (kdistinct (u 2000) [col [0, 1]]) == short

end Rel.Kernel.DistinctTest
