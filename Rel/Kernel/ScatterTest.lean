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

/-- An answer as its error, or its metadata and pack bytes. -/
def view : Except String Enc → String ⊕ (List UInt8 × List UInt8)
  | .error s => .inl s
  | .ok (.foR md p) => .inr (md.data.toList, p.data.toList)
  | .ok _ => .inl "not foR"

-- row 2 overwrites row 0's cell; cells 1 and 3 keep the fill: the bytes the Lean model `Coc.encodeAt` writes for
-- `[11, 7, 12, 7]`, not the extern `Coc.encode`, so the `#guard` holds the Rust against Lean
def wrote : String ⊕ (List UInt8 × List UInt8) :=
  let r := Coc.encodeAt Column.lgEnc (u 8) ([11, 7, 12, 7].foldl (init := .empty) fun acc w => Column.pushBits acc w 8)
  .inr (r.1.data.toList, r.2.data.toList)
example : view (kscatter (u 3) (col [2, 0, 2]) (col [10, 11, 12]) (u 4) 7) = wrote := by decide +kernel
#guard view (kscatter (u 3) (col [2, 0, 2]) (col [10, 11, 12]) (u 4) 7) == wrote

-- an index `≥ n` is the error, named with its row, never dropped
def past : String ⊕ (List UInt8 × List UInt8) := .inl "scatter: index 5 at row 1 is not below n = 3"
example : view (kscatter (u 3) (col [1, 5, 9]) (col [1, 2, 3]) (u 3) 0) = past := by decide +kernel
#guard view (kscatter (u 3) (col [1, 5, 9]) (col [1, 2, 3]) (u 3) 0) == past

-- a form other than `foR`, and a `foR` whose blocks do not cover `m`
def dense : String ⊕ (List UInt8 × List UInt8) := .inl "scatter: e: constructor 0 is not foR"
example : view (kscatter (u 2) (col [0, 1]) (.bytes (ByteArray.mk (Array.replicate 16 0))) (u 2) 0) = dense := by
  decide +kernel
#guard view (kscatter (u 2) (col [0, 1]) (.bytes (ByteArray.mk (Array.replicate 16 0))) (u 2) 0) == dense
def short : String ⊕ (List UInt8 × List UInt8) :=
  .inl "scatter: ix: foR: 1 blocks of 2^10 and a 256-byte pack are not the layout of 1025 elements"
example : view (kscatter (u 1025) (col [0, 1, 2]) (col [0, 1, 2]) (u 9) 0) = short := by decide +kernel
#guard view (kscatter (u 1025) (col [0, 1, 2]) (col [0, 1, 2]) (u 9) 0) == short

/-- `Coc.encodeAt lgEnc 8` of the words `ws`, as `view` shows an answer. -/
def enc8 (ws : List UInt64) : String ⊕ (List UInt8 × List UInt8) :=
  let r := Coc.encodeAt Column.lgEnc (u 8) (ws.foldl (init := .empty) fun acc w => Column.pushBits acc w 8)
  .inr (r.1.data.toList, r.2.data.toList)
-- `pos` (PLAN 6.13), the positions read as the loop index. S1: `ix = pos` at `m = n` answers `e`; at `m < n` the rest
-- of the cells keep `fill`; at `m > n` row `n` is the error
example : view (kscatter (u 3) .pos (col [10, 11, 12]) (u 3) 7) = enc8 [10, 11, 12] := by decide +kernel
#guard view (kscatter (u 3) .pos (col [10, 11, 12]) (u 3) 7) == enc8 [10, 11, 12]
example : view (kscatter (u 2) .pos (col [10, 11]) (u 4) 7) = enc8 [10, 11, 7, 7] := by decide +kernel
#guard view (kscatter (u 2) .pos (col [10, 11]) (u 4) 7) == enc8 [10, 11, 7, 7]
def posPast : String ⊕ (List UInt8 × List UInt8) := .inl "scatter: index 3 at row 3 is not below n = 3"
example : view (kscatter (u 4) .pos .pos (u 3) 0) = posPast := by decide +kernel
#guard view (kscatter (u 4) .pos .pos (u 3) 0) == posPast
-- `e = pos` writes each row's number at its index: the inverse of the permutation `2 0 1` (RANK)
example : view (kscatter (u 3) (col [2, 0, 1]) .pos (u 3) 9) = enc8 [1, 2, 0] := by decide +kernel
#guard view (kscatter (u 3) (col [2, 0, 1]) .pos (u 3) 9) == enc8 [1, 2, 0]

end Rel.Kernel.ScatterTest
