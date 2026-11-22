import Rel.Kernel.Seen

/-! `kseen`'s `decide`-beside-`#guard` pairs: each `example` evaluates the Lean body, each `#guard` the Rust export
`qlean_k_seen`, against one literal. -/

namespace Rel.Kernel.SeenTest
open Ext.Enc

/-- `k` as a `USize` whose `toNat` the kernel reduces: a literal's is `k % 2 ^ numBits`, and `numBits` is opaque. -/
def u (k : Nat) (h : k < 4294967296 := by decide) : USize := USize.ofNat32 k h

/-- `xs` as an `i64` key column in the `foR` the kernels answer (`wordsFoR`). -/
def col (xs : List UInt64) : AscKey × Enc := (.atom .i64, wordsFoR xs.toArray)

/-- An answer as its error, or its count and the words `Enc.raw` reads from `g` (`n` of them) and `first` (`k`); `n`
and `k` are the counts the literal expects, as `USize`s the kernel reduces. -/
def view (n k : USize) : Except String (Nat × Enc × Enc) → String ⊕ (Nat × List UInt64 × List UInt64)
  | .error s => .inl s
  | .ok (c, g, f) => .inr (c, (raw .i64 n g).toList, (raw .i64 k f).toList)

/-- The error of rows out of `kasc` order, row `i + 1` sorting before row `i`. -/
def unsorted (i : Nat) : String ⊕ (Nat × List UInt64 × List UInt64) :=
  .inl s!"seen: row {i + 1} sorts before row {i}; kseen takes rows in kasc order, so sort them with kasc first"

-- `B A B` is out of order at row 1; sorted, `A B B` is two runs
example : view (u 0) (u 0) (kseen (u 3) [col [2, 1, 2]]) = unsorted 0 := by decide +kernel
#guard view (u 0) (u 0) (kseen (u 3) [col [2, 1, 2]]) == unsorted 0
def abb : String ⊕ (Nat × List UInt64 × List UInt64) := .inr (2, [0, 1, 1], [0, 1])
example : view (u 3) (u 2) (kseen (u 3) [col [1, 2, 2]]) = abb := by decide +kernel
#guard view (u 3) (u 2) (kseen (u 3) [col [1, 2, 2]]) == abb

-- two columns: rows (1,0) (2,0) (1,0) (2,1) (1,0) are out of order at row 2, the first column deciding; sorted,
-- (1,0) (1,0) (1,0) (2,0) (2,1) are three runs, the second column splitting the last
example : view (u 0) (u 0) (kseen (u 5) [col [1, 2, 1, 2, 1], col [0, 0, 0, 1, 0]]) = unsorted 1 := by decide +kernel
#guard view (u 0) (u 0) (kseen (u 5) [col [1, 2, 1, 2, 1], col [0, 0, 0, 1, 0]]) == unsorted 1
def pairs : String ⊕ (Nat × List UInt64 × List UInt64) := .inr (3, [0, 0, 0, 1, 2], [0, 3, 4])
example : view (u 5) (u 3) (kseen (u 5) [col [1, 1, 1, 2, 2], col [0, 0, 0, 0, 1]]) = pairs := by decide +kernel
#guard view (u 5) (u 3) (kseen (u 5) [col [1, 1, 1, 2, 2], col [0, 0, 0, 0, 1]]) == pairs
-- the second column out of order where the first ties
example : view (u 0) (u 0) (kseen (u 3) [col [1, 1, 2], col [1, 0, 0]]) = unsorted 0 := by decide +kernel
#guard view (u 0) (u 0) (kseen (u 3) [col [1, 1, 2], col [1, 0, 0]]) == unsorted 0

-- no row: no group; no column: every row is the empty key, one group
def none0 : String ⊕ (Nat × List UInt64 × List UInt64) := .inr (0, [], [])
example : view (u 0) (u 0) (kseen (u 0) [col []]) = none0 := by decide +kernel
#guard view (u 0) (u 0) (kseen (u 0) [col []]) == none0
def one : String ⊕ (Nat × List UInt64 × List UInt64) := .inr (1, [0, 0, 0], [0])
example : view (u 3) (u 1) (kseen (u 3) []) = one := by decide +kernel
#guard view (u 3) (u 1) (kseen (u 3) []) == one

-- a `pos` column has no ties and ascends, so every row is its own group and the order is the columns' before it:
-- after ties it answers, first it orders any later columns, after rows out of order it is the error
def every : String ⊕ (Nat × List UInt64 × List UInt64) := .inr (3, [0, 1, 2], [0, 1, 2])
example : view (u 3) (u 3) (kseen (u 3) [col [5, 5, 5], (.atom .i64, .pos)]) = every := by decide +kernel
#guard view (u 3) (u 3) (kseen (u 3) [col [5, 5, 5], (.atom .i64, .pos)]) == every
example : view (u 3) (u 3) (kseen (u 3) [(.atom .i64, .pos), col [3, 1, 2]]) = every := by decide +kernel
#guard view (u 3) (u 3) (kseen (u 3) [(.atom .i64, .pos), col [3, 1, 2]]) == every
example : view (u 0) (u 0) (kseen (u 3) [col [5, 6, 5], (.atom .i64, .pos)]) = unsorted 1 := by decide +kernel
#guard view (u 0) (u 0) (kseen (u 3) [col [5, 6, 5], (.atom .i64, .pos)]) == unsorted 1

-- `f64` at `kasc`'s equality, the stored bits: in totalOrder `-0.0`, `0.0`, `1.0`, a signalling NaN (payload 1) and the
-- quiet NaN are five keys; two bit-identical `0.0`s are one
def floats : String ⊕ (Nat × List UInt64 × List UInt64) := .inr (5, [0, 1, 2, 3, 4], [0, 1, 2, 3, 4])
example : view (u 5) (u 5) (kseen (u 5)
    [(.atom .f64, wordsFoR #[0x8000000000000000, 0, 0x3ff0000000000000, 0x7ff0000000000001, 0x7ff8000000000000])]) = floats := by
  decide +kernel
#guard view (u 5) (u 5) (kseen (u 5)
    [(.atom .f64, wordsFoR #[0x8000000000000000, 0, 0x3ff0000000000000, 0x7ff0000000000001, 0x7ff8000000000000])]) == floats
def sameBits : String ⊕ (Nat × List UInt64 × List UInt64) := .inr (3, [0, 1, 1, 2], [0, 1, 3])
example : view (u 4) (u 3) (kseen (u 4)
    [(.atom .f64, wordsFoR #[0x8000000000000000, 0, 0, 0x7ff8000000000000])]) = sameBits := by decide +kernel
#guard view (u 4) (u 3) (kseen (u 4) [(.atom .f64, wordsFoR #[0x8000000000000000, 0, 0, 0x7ff8000000000000])]) == sameBits

-- a block with a patch (the outlier `2^40` among small words), beside a second column
def patched : String ⊕ (Nat × List UInt64 × List UInt64) := .inr (3, [0, 0, 0, 0, 0, 0, 1, 2], [0, 6, 7])
example : view (u 8) (u 3) (kseen (u 8) [col [1, 1, 1, 1, 1, 1, 1, 2 ^ 40], col [0, 0, 0, 0, 0, 0, 1, 1]]) = patched := by
  decide +kernel
#guard view (u 8) (u 3) (kseen (u 8) [col [1, 1, 1, 1, 1, 1, 1, 2 ^ 40], col [0, 0, 0, 0, 0, 0, 1, 1]]) == patched

-- a column that is not `foR`, and a `foR` whose blocks do not cover `n` are the error, named by
-- their place in `es`
def dense : String ⊕ (Nat × List UInt64 × List UInt64) := .inl s!"seen: es[1]: asc: constructor {(.gen #[] : Enc).ctorIdx} is not foR"
example : view (u 0) (u 0) (kseen (u 2) [col [0, 1], (.atom .i64, .gen #[])]) = dense := by
  decide +kernel
#guard view (u 0) (u 0) (kseen (u 2) [col [0, 1], (.atom .i64, .gen #[])]) == dense
-- a symbol column is ordered as its ids, an `i64` column (PLAN 8.3)
example : view (u 2) (u 2) (kseen (u 2) [(.atom .sym, wordsFoR #[0, 1])]) = view (u 2) (u 2) (kseen (u 2) [(.atom .i64, wordsFoR #[0, 1])]) := by decide +kernel
#guard view (u 2) (u 2) (kseen (u 2) [(.atom .sym, wordsFoR #[0, 1])]) == view (u 2) (u 2) (kseen (u 2) [(.atom .i64, wordsFoR #[0, 1])])
def short : String ⊕ (Nat × List UInt64 × List UInt64) :=
  .inl "seen: es[0]: asc: foR: 1 blocks of 2^10 and a 128-byte pack are not the layout of 2000 elements"
example : view (u 0) (u 0) (kseen (u 2000) [col [0, 1]]) = short := by decide +kernel
#guard view (u 0) (u 0) (kseen (u 2000) [col [0, 1]]) == short

-- a `pos` column of another type than `i64` is the error, named by its place in `es`
def posType : String ⊕ (Nat × List UInt64 × List UInt64) := .inl "seen: es[0]: asc: a pos column is type 4, not 3"
example : view (u 0) (u 0) (kseen (u 2) [(.atom .i32, .pos)]) = posType := by decide +kernel
#guard view (u 0) (u 0) (kseen (u 2) [(.atom .i32, .pos)]) == posType

-- the key's range does not matter: rows in order answer at any range, and rows out of order are the error at every
-- range, narrow or wide, one column or two (the second's `2^40` a patch)
def two : String ⊕ (Nat × List UInt64 × List UInt64) := .inr (2, [0, 1], [0, 1])
example : view (u 0) (u 0) (kseen (u 2) [col [1031, 0]]) = unsorted 0 := by decide +kernel
#guard view (u 0) (u 0) (kseen (u 2) [col [1031, 0]]) == unsorted 0
example : view (u 2) (u 2) (kseen (u 2) [col [0, 1032]]) = two := by decide +kernel
#guard view (u 2) (u 2) (kseen (u 2) [col [0, 1032]]) == two
example : view (u 0) (u 0) (kseen (u 2) [col [1032, 0]]) = unsorted 0 := by decide +kernel
#guard view (u 0) (u 0) (kseen (u 2) [col [1032, 0]]) == unsorted 0
example : view (u 0) (u 0) (kseen (u 2) [col [1, 0], col [0, 2 ^ 40]]) = unsorted 0 := by decide +kernel
#guard view (u 0) (u 0) (kseen (u 2) [col [1, 0], col [0, 2 ^ 40]]) == unsorted 0
example : view (u 2) (u 2) (kseen (u 2) [col [0, 1], col [2 ^ 40, 0]]) = two := by decide +kernel
#guard view (u 2) (u 2) (kseen (u 2) [col [0, 1], col [2 ^ 40, 0]]) == two

/-! `cells` keys: rows are equal when their cells have one length and equal element codes, whichever cells they
name. -/

/-- A `cells` key of the cells `[lo[r], hi[r])` over the payload columns `els` of `c` rows, row `i` naming cell
`ix[i]`. -/
def cells (n c : USize) (lo hi : List UInt64) (els : List (AscKey × Enc)) (ix : List UInt64) : AscKey × Enc :=
  (.cells n c (wordsFoR lo.toArray) (wordsFoR hi.toArray) els, wordsFoR ix.toArray)

-- payload `5 1 5`; cells `[]`, `[5]`, `[5,1]`, `[1]`, `[5]`: rows `[] [] [1] [5] [5] [5,1]` in `kasc` order, the two
-- `[5]`s naming cells 1 and 4 one group; the empty cell a group of its own
def runs : String ⊕ (Nat × List UInt64 × List UInt64) := .inr (4, [0, 0, 1, 2, 2, 3], [0, 2, 3, 5])
example : view (u 6) (u 4) (kseen (u 6)
    [cells (u 5) (u 3) [0, 0, 0, 1, 2] [0, 1, 2, 2, 3] [col [5, 1, 5]] [0, 0, 3, 1, 4, 2]]) = runs := by decide +kernel
#guard view (u 6) (u 4) (kseen (u 6)
    [cells (u 5) (u 3) [0, 0, 0, 1, 2] [0, 1, 2, 2, 3] [col [5, 1, 5]] [0, 0, 3, 1, 4, 2]]) == runs
-- `[5,1]` before its proper prefix `[5]` is out of order
example : view (u 0) (u 0) (kseen (u 2) [cells (u 2) (u 2) [0, 0] [2, 1] [col [5, 1]] [0, 1]]) = unsorted 0 := by
  decide +kernel
#guard view (u 0) (u 0) (kseen (u 2) [cells (u 2) (u 2) [0, 0] [2, 1] [col [5, 1]] [0, 1]]) == unsorted 0

-- a tuple element, a nested cells element and a float element: `[(0,9)] [(1,5)] [(1,5)]`, then inner `[q] [q] [q,r]`
-- (`q = [1,2]`, `r = []`), then `[-0.0] [0.0] [0.0]`; the floats' bits split `-0.0` from `0.0`
def tuple : String ⊕ (Nat × List UInt64 × List UInt64) := .inr (2, [0, 1, 1], [0, 1])
example : view (u 3) (u 2) (kseen (u 3)
    [cells (u 3) (u 3) [2, 0, 1] [3, 1, 2] [col [1, 1, 0], (.atom .i32, wordsFoR #[5, 5, 9])] [0, 1, 2]]) = tuple := by
  decide +kernel
#guard view (u 3) (u 2) (kseen (u 3)
    [cells (u 3) (u 3) [2, 0, 1] [3, 1, 2] [col [1, 1, 0], (.atom .i32, wordsFoR #[5, 5, 9])] [0, 1, 2]]) == tuple
def nest : List (AscKey × Enc) :=
  [cells (u 3) (u 3) [0, 1, 1] [1, 2, 3] [cells (u 2) (u 2) [0, 0] [2, 0] [col [1, 2]] [0, 0, 1]] [0, 1, 2]]
example : view (u 3) (u 2) (kseen (u 3) nest) = .inr (2, [0, 0, 1], [0, 2]) := by decide +kernel
#guard view (u 3) (u 2) (kseen (u 3) nest) == .inr (2, [0, 0, 1], [0, 2])
def fl : List (AscKey × Enc) :=
  [cells (u 3) (u 3) [0, 1, 2] [1, 2, 3] [(.atom .f64, wordsFoR #[0x8000000000000000, 0, 0])] [0, 1, 2]]
example : view (u 3) (u 2) (kseen (u 3) fl) = tuple := by decide +kernel
#guard view (u 3) (u 2) (kseen (u 3) fl) == tuple

-- past a block of `2 ^ 10`, `#guard` only: the payload `0 … 1099`, cells `C = [0, 1100)`, `B = [1020, 1029)` and its
-- extension `A = [1020, 1030)`, 400 rows of `C`, 400 of `B`, 300 of `A`: three runs
def edge : String ⊕ (Nat × List UInt64 × List UInt64) :=
  .inr (3, List.replicate 400 0 ++ List.replicate 400 1 ++ List.replicate 300 2, [0, 400, 800])
#guard view (u 1100) (u 3) (kseen (u 1100) [cells (u 3) (u 1100) [1020, 1020, 0] [1030, 1029, 1100]
    [col ((List.range 1100).map Nat.toUInt64)] (List.replicate 400 2 ++ List.replicate 400 1 ++ List.replicate 300 0)]) == edge

end Rel.Kernel.SeenTest
