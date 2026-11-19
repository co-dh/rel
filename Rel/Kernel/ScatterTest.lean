import Rel.Kernel.Seen

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
example : view (kscatter .last (u 3) (col [2, 0, 2]) (col [10, 11, 12]) (u 4) 7) = wrote := by decide +kernel
#guard view (kscatter .last (u 3) (col [2, 0, 2]) (col [10, 11, 12]) (u 4) 7) == wrote

-- an index `≥ n` is the error, named with its row, never dropped
def past : String ⊕ (List UInt8 × List UInt8) := .inl "scatter: index 5 at row 1 is not below n = 3"
example : view (kscatter .last (u 3) (col [1, 5, 9]) (col [1, 2, 3]) (u 3) 0) = past := by decide +kernel
#guard view (kscatter .last (u 3) (col [1, 5, 9]) (col [1, 2, 3]) (u 3) 0) == past

-- a form other than `foR`, and a `foR` whose blocks do not cover `m`
def dense : String ⊕ (List UInt8 × List UInt8) := .inl "scatter: e: constructor 0 is not foR"
example : view (kscatter .last (u 2) (col [0, 1]) (.bytes (ByteArray.mk (Array.replicate 16 0))) (u 2) 0) = dense := by
  decide +kernel
#guard view (kscatter .last (u 2) (col [0, 1]) (.bytes (ByteArray.mk (Array.replicate 16 0))) (u 2) 0) == dense
def short : String ⊕ (List UInt8 × List UInt8) :=
  .inl "scatter: ix: foR: 1 blocks of 2^10 and a 256-byte pack are not the layout of 1025 elements"
example : view (kscatter .last (u 1025) (col [0, 1, 2]) (col [0, 1, 2]) (u 9) 0) = short := by decide +kernel
#guard view (kscatter .last (u 1025) (col [0, 1, 2]) (col [0, 1, 2]) (u 9) 0) == short

/-- `Coc.encodeAt lgEnc 8` of the words `ws`, as `view` shows an answer. -/
def enc8 (ws : List UInt64) : String ⊕ (List UInt8 × List UInt8) :=
  let r := Coc.encodeAt Column.lgEnc (u 8) (ws.foldl (init := .empty) fun acc w => Column.pushBits acc w 8)
  .inr (r.1.data.toList, r.2.data.toList)
-- `pos` (PLAN 6.13), the positions read as the loop index. S1: `ix = pos` at `m = n` answers `e`; at `m < n` the rest
-- of the cells keep `fill`; at `m > n` row `n` is the error
example : view (kscatter .last (u 3) .pos (col [10, 11, 12]) (u 3) 7) = enc8 [10, 11, 12] := by decide +kernel
#guard view (kscatter .last (u 3) .pos (col [10, 11, 12]) (u 3) 7) == enc8 [10, 11, 12]
example : view (kscatter .last (u 2) .pos (col [10, 11]) (u 4) 7) = enc8 [10, 11, 7, 7] := by decide +kernel
#guard view (kscatter .last (u 2) .pos (col [10, 11]) (u 4) 7) == enc8 [10, 11, 7, 7]
def posPast : String ⊕ (List UInt8 × List UInt8) := .inl "scatter: index 3 at row 3 is not below n = 3"
example : view (kscatter .last (u 4) .pos .pos (u 3) 0) = posPast := by decide +kernel
#guard view (kscatter .last (u 4) .pos .pos (u 3) 0) == posPast
-- `e = pos` writes each row's number at its index: the inverse of the permutation `2 0 1` (RANK)
example : view (kscatter .last (u 3) (col [2, 0, 1]) .pos (u 3) 9) = enc8 [1, 2, 0] := by decide +kernel
#guard view (kscatter .last (u 3) (col [2, 0, 1]) .pos (u 3) 9) == enc8 [1, 2, 0]

-- the `Op` combines a cell with each row naming it, in row order, starting from `fill`. No collision: `add` adds each
-- value to `fill` once
example : view (kscatter .add (u 3) (col [2, 0, 1]) (col [5, 6, 7]) (u 3) 1) = enc8 [7, 8, 6] := by decide +kernel
#guard view (kscatter .add (u 3) (col [2, 0, 1]) (col [5, 6, 7]) (u 3) 1) == enc8 [7, 8, 6]
-- collisions under `add`: cell 0 is `7 + 11`, cell 2 `7 + 10 + 12` (under `.last` the same rows give `wrote`)
example : view (kscatter .add (u 3) (col [2, 0, 2]) (col [10, 11, 12]) (u 4) 7) = enc8 [18, 7, 29, 7] := by
  decide +kernel
#guard view (kscatter .add (u 3) (col [2, 0, 2]) (col [10, 11, 12]) (u 4) 7) == enc8 [18, 7, 29, 7]
-- an `Op.eval` error reaches the caller, named with its row: `100 / 5`, then `/ 0`
def divZero : String ⊕ (List UInt8 × List UInt8) := .inl "scatter: Op.div: integer division by 0 at row 1"
example : view (kscatter .div (u 2) (col [0, 0]) (col [5, 0]) (u 1) 100) = divZero := by decide +kernel
#guard view (kscatter .div (u 2) (col [0, 0]) (col [5, 0]) (u 1) 100) == divZero
-- no rows: `n` cells of `fill`, none at `n = 0`
example : view (kscatter .add (u 0) (col []) (col []) (u 0) 7) = enc8 [] := by decide +kernel
#guard view (kscatter .add (u 0) (col []) (col []) (u 0) 7) == enc8 []
example : view (kscatter .add (u 0) (col []) (col []) (u 2) 7) = enc8 [7, 7] := by decide +kernel
#guard view (kscatter .add (u 0) (col []) (col []) (u 2) 7) == enc8 [7, 7]

/-- The parity of each of the first `m` rows: index `k % 2`, so every row collides with the rows of its parity. -/
def parityWords (m : Nat) : Array UInt64 := ((List.range m).map fun k => (k % 2).toUInt64).toArray
def parity (m : Nat) : Enc := col (parityWords m).toList
/-- `scatterWords`, the Lean body's fold, of the parity index and the positions `0 .. m`, run compiled. -/
def parityModel (op : Op) (m : Nat) : Option (List UInt64) :=
  (scatterWords op (parityWords m) ((List.range m).map Nat.toUInt64).toArray 2 0).toOption.map (·.toList)
-- block boundaries: the rows of one cell span the 1024-row blocks. `add` of the positions: `0 + 2 + .. + 1022`,
-- `1 + 3 + .. + 1023`, and at 1025 rows `+ 1024` on cell 0; `last` keeps the last even and the last odd row.
-- Encoding a 1024-row column is more than `decide +kernel` reduces (as `AscTest`'s `pview` notes), so the Lean side
-- of each pair is the body's `scatterWords` run compiled against the same literal, the `#guard` beside it the Rust
#guard parityModel .add 1024 == some [261632, 262144]
#guard view (kscatter .add (u 1024) (parity 1024) .pos (u 2) 0) == enc8 [261632, 262144]
#guard parityModel .add 1025 == some [262656, 262144]
#guard view (kscatter .add (u 1025) (parity 1025) .pos (u 2) 0) == enc8 [262656, 262144]
#guard parityModel .last 1024 == some [1022, 1023]
#guard view (kscatter .last (u 1024) (parity 1024) .pos (u 2) 0) == enc8 [1022, 1023]
#guard parityModel .last 1025 == some [1024, 1023]
#guard view (kscatter .last (u 1025) (parity 1025) .pos (u 2) 0) == enc8 [1024, 1023]

-- `last`, each group's last row in group order: the positions scattered to `kseen`'s `g` under `.last`. `A B B` (in
-- `kasc` order, as `kseen` takes it) has `g = 0 1 1` (2 groups), so `last = 0 2`
def lastABB : Except String Enc := do
  let (_, g, _) ← kseen (u 3) [(.i64, wordsFoR #[1, 2, 2])]
  kscatter .last (u 3) g .pos (u 2) 0
example : view lastABB = enc8 [0, 2] := by decide +kernel
#guard view lastABB == enc8 [0, 2]

end Rel.Kernel.ScatterTest
