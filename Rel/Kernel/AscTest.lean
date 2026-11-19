import Rel.Kernel.Asc

/-! `kasc`'s `decide`-beside-`#guard` pairs: each `example` evaluates the Lean body, each `#guard` the Rust export
`qlean_k_asc`, against one literal. -/

namespace Rel.Kernel.AscTest
open Ext.Enc

/-- `k` as a `USize` whose `toNat` the kernel reduces: a literal's is `k % 2 ^ numBits`, and `numBits` is opaque. -/
def u (k : Nat) (h : k < 4294967296 := by decide) : USize := USize.ofNat32 k h

/-- `xs` as a `foR` column of 8-byte elements at blocks of `2 ^ 6`, the least block the layout takes. -/
def col (xs : List UInt64) : Enc :=
  let (md, pk) := Coc.encodeAt 6 (u 8) (xs.foldl (init := .empty) fun acc w => Column.pushBits acc w 8)
  .foR md pk

/-- An answer as its error, or the `n` words `Enc.raw` reads from each sorted column and from the permutation. -/
def view (n : USize) : Except String (List Enc × Enc) → String ⊕ (List (List UInt64) × List UInt64)
  | .error s => .inl s
  | .ok (vs, p) => .inr (vs.map fun v => (raw .i64 n v).toList, (raw .i64 n p).toList)

/-- An answer's permutation alone. The kernel builds no answer column it is not asked for, and one whose residuals are
32 or 64 bits wide in `lgEnc`'s blocks of 1024 is more than `decide` reduces, so a case with such values `decide`s this
and `#guard`s `view`. -/
def pview (n : USize) : Except String (List Enc × Enc) → String ⊕ List UInt64
  | .error s => .inl s
  | .ok (_, p) => .inr (raw .i64 n p).toList

/-- `2 ^ 64 - 1`, the long `-1`. -/
def neg1 : UInt64 := 0xffffffffffffffff

-- two long keys: `-1` sorts first (the sign flip); rows 0 and 2 tie in both columns and keep their input order;
-- rows 1 and 3 tie in the first and the second column decides
def lex : List (AscKey × Enc) := [(.atom .i64, col [3, 1, 3, 1, neg1]), (.atom .i64, col [0, 9, 0, 5, 7])]
def lexOut : String ⊕ (List (List UInt64) × List UInt64) := .inr ([[neg1, 1, 1, 3, 3], [7, 5, 9, 0, 0]], [4, 3, 1, 0, 2])
example : view (u 5) (kasc (u 5) lex) = lexOut := by decide +kernel
#guard view (u 5) (kasc (u 5) lex) == lexOut

-- an `int` is ordered at its 32 bits: `0x80000000` is the least, `neg1` is `-1`; the words move whole
def i32 : List (AscKey × Enc) := [(.atom .i32, col [5, neg1, 0x80000000, 2])]
def i32Out : String ⊕ (List (List UInt64) × List UInt64) := .inr ([[0x80000000, neg1, 2, 5]], [2, 1, 3, 0])
example : pview (u 4) (kasc (u 4) i32) = .inr [2, 1, 3, 0] := by decide +kernel
#guard view (u 4) (kasc (u 4) i32) == i32Out

-- an `i8` is signed at its byte: `0x80` (`-128`) is the least, `0xff` is `-1`, then `0`; the words move whole
def i8 : List (AscKey × Enc) := [(.atom .i8, col [5, 0xff, 0x80, 2, 0])]
def i8Out : String ⊕ (List (List UInt64) × List UInt64) := .inr ([[0x80, 0xff, 0, 2, 5]], [2, 1, 4, 3, 0])
example : pview (u 5) (kasc (u 5) i8) = .inr [2, 1, 4, 3, 0] := by decide +kernel
#guard view (u 5) (kasc (u 5) i8) == i8Out

-- floats by `ordCode`, IEEE totalOrder on the stored bits: `-1.0 < -0.0 < 0.0 < 1.0 < NaN`, `-0.0` and `0.0` apart
def flt : List (AscKey × Enc) :=
  [(.atom .f64, col [0x3ff0000000000000, 0x7ff8000000000000, 0x8000000000000000, 0xbff0000000000000, 0])]
def fltOut : String ⊕ (List (List UInt64) × List UInt64) :=
  .inr ([[0xbff0000000000000, 0x8000000000000000, 0, 0x3ff0000000000000, 0x7ff8000000000000]], [3, 2, 4, 0, 1])
example : pview (u 5) (kasc (u 5) flt) = .inr [3, 2, 4, 0, 1] := by decide +kernel
#guard view (u 5) (kasc (u 5) flt) == fltOut

-- no key column: the identity permutation
example : view (u 3) (kasc (u 3) []) = .inr ([], [0, 1, 2]) := by decide +kernel
#guard view (u 3) (kasc (u 3) []) == .inr ([], [0, 1, 2])

-- the errors, the first in the order of `es`: a type with no order, then `foRWords`' (a form other than `foR`, a `foR`
-- whose blocks hold fewer than `m` elements)
def gen : String ⊕ (List (List UInt64) × List UInt64) := .inl "asc: type 12 has no fixed-width order"
example : view (u 2) (kasc (u 2) [(.atom .general, col [0, 1]), (.atom .i64, .bytes .empty)]) = gen := by decide +kernel
#guard view (u 2) (kasc (u 2) [(.atom .general, col [0, 1]), (.atom .i64, .bytes .empty)]) == gen
def dense : String ⊕ (List (List UInt64) × List UInt64) := .inl "asc: constructor 0 is not foR"
example : view (u 2) (kasc (u 2) [(.atom .i64, .bytes .empty), (.atom .general, col [0, 1])]) = dense := by decide +kernel
#guard view (u 2) (kasc (u 2) [(.atom .i64, .bytes .empty), (.atom .general, col [0, 1])]) == dense
-- one block of `2 ^ 6` holds fewer than `65` elements
def short : String ⊕ (List (List UInt64) × List UInt64) :=
  .inl "asc: foR: 1 blocks of 2^6 and a 8-byte pack are not the layout of 65 elements"
example : view (u 65) (kasc (u 65) [(.atom .i64, col [0, 1])]) = short := by decide +kernel
#guard view (u 65) (kasc (u 65) [(.atom .i64, col [0, 1])]) == short

-- `pos` (PLAN 6.13). A2: a `pos` first key leaves every row in place, the permutation is the positions
def posFirst : String ⊕ (List (List UInt64) × List UInt64) := .inr ([[0, 1, 2], [5, 1, 3]], [0, 1, 2])
example : view (u 3) (kasc (u 3) [(.atom .i64, .pos), (.atom .i64, col [5, 1, 3])]) = posFirst := by decide +kernel
#guard view (u 3) (kasc (u 3) [(.atom .i64, .pos), (.atom .i64, col [5, 1, 3])]) == posFirst
-- A1: a `pos` key breaks every tie of the keys before it in row order, so the keys after it decide nothing
def posMid : String ⊕ (List (List UInt64) × List UInt64) := .inr ([[0, 0, 1, 1], [1, 3, 0, 2], [8, 6, 9, 7]], [1, 3, 0, 2])
example : view (u 4) (kasc (u 4) [(.atom .i64, col [1, 0, 1, 0]), (.atom .i64, .pos), (.atom .i64, col [9, 8, 7, 6])]) = posMid := by
  decide +kernel
#guard view (u 4) (kasc (u 4) [(.atom .i64, col [1, 0, 1, 0]), (.atom .i64, .pos), (.atom .i64, col [9, 8, 7, 6])]) == posMid
-- `pos` is `i64` only: at another type its codes would wrap
def posI32 : String ⊕ (List (List UInt64) × List UInt64) := .inl "asc: a pos column is type 4, not 3"
example : view (u 2) (kasc (u 2) [(.atom .i32, .pos)]) = posI32 := by decide +kernel
#guard view (u 2) (kasc (u 2) [(.atom .i32, .pos)]) == posI32
-- and at most `2 ^ 63` rows, past which the code `i ^^^ 2 ^ 63` no longer ascends with `i`; the export answers the
-- error before it allocates a row. `Rust` side only: `decide` reduces no `USize` past `u`'s `2 ^ 32`
def posBig : String ⊕ (List (List UInt64) × List UInt64) :=
  .inl "asc: a pos column of 9223372036854775809 rows is past 2^63, where its order codes wrap"
#guard view (USize.ofNat (2 ^ 63 + 1)) (kasc (USize.ofNat (2 ^ 63 + 1)) [(.atom .i64, .pos)]) == posBig

/-! `cells` keys: a row names a cell, a cell is a range of payload rows, cells order lexicographically by their elements'
codes, a proper prefix first. -/

/-- A `cells` key of the cells `[lo[r], hi[r])` over the payload columns `els` of `c` rows, row `i` naming cell
`ix[i]` (`.pos`: cell `i`). -/
def cells (n c : USize) (lo hi : List UInt64) (els : List (AscKey × Enc)) (ix : Enc := .pos) : AscKey × Enc :=
  (.cells n c (col lo) (col hi) els, ix)

-- payload `5 1 5`; cells `[]`, `[5]`, `[5,1]`, `[1]`, `[5]` (the second `[5]` at another payload row). Rows name
-- `[5,1] [] [5] [1] [5] []`: the empty cell first, a proper prefix `[5]` before `[5,1]`, the two `[]`s and the two `[5]`s
-- (cells 1 and 4, equal elements) tie in input order across non-adjacent rows
def prefix : List (AscKey × Enc) :=
  [cells (u 5) (u 3) [0, 0, 0, 1, 2] [0, 1, 2, 2, 3] [(.atom .i64, col [5, 1, 5])] (col [2, 0, 1, 3, 4, 0])]
def prefixOut : String ⊕ (List (List UInt64) × List UInt64) := .inr ([[0, 0, 3, 1, 4, 2]], [1, 5, 3, 2, 4, 0])
example : view (u 6) (kasc (u 6) prefix) = prefixOut := by decide +kernel
#guard view (u 6) (kasc (u 6) prefix) == prefixOut

-- a tuple element (`i64`, `i32`): cells `[(1,5)]`, `[(1,-2^31)]`, `[(0,9)]`; the first atom decides, then the `i32`
-- at its sign
def tuple : List (AscKey × Enc) :=
  [cells (u 3) (u 3) [1, 0, 2] [2, 1, 3] [(.atom .i64, col [1, 1, 0]), (.atom .i32, col [0x80000000, 5, 9])]]
example : pview (u 3) (kasc (u 3) tuple) = .inr [2, 1, 0] := by decide +kernel
#guard pview (u 3) (kasc (u 3) tuple) == .inr [2, 1, 0]

-- nested cells: the inner cells `p = [3]`, `q = [1,2]`, `r = []` (so `r < q < p`); the outer payload `p q q r` and its
-- cells `[p,q]`, `[q,r]`, `[q]`: `[q]` first, a proper prefix of `[q,r]`, then `[p,q]`
def nested : List (AscKey × Enc) :=
  [cells (u 3) (u 4) [0, 2, 1] [2, 4, 2] [cells (u 3) (u 3) [0, 1, 0] [1, 3, 0] [(.atom .i64, col [3, 1, 2])] (col [0, 1, 1, 2])]]
example : pview (u 3) (kasc (u 3) nested) = .inr [2, 1, 0] := by decide +kernel
#guard pview (u 3) (kasc (u 3) nested) == .inr [2, 1, 0]

-- a float element by `ordCode`, the stored bits: `[0.0]`, `[-0.0]`, `[NaN]`, `[-1.0]` order `-1.0 < -0.0 < 0.0 < NaN`
def fcells : List (AscKey × Enc) :=
  [cells (u 4) (u 4) [0, 1, 2, 3] [1, 2, 3, 4] [(.atom .f64, col [0, 0x8000000000000000, 0x7ff8000000000000, 0xbff0000000000000])]]
example : pview (u 4) (kasc (u 4) fcells) = .inr [3, 1, 0, 2] := by decide +kernel
#guard pview (u 4) (kasc (u 4) fcells) == .inr [3, 1, 0, 2]

-- a word naming no cell is the error
def noCell : String ⊕ (List (List UInt64) × List UInt64) := .inl "asc: cells: row word 2 names no cell of 2"
example : view (u 2) (kasc (u 2) [cells (u 2) (u 1) [0, 0] [1, 1] [(.atom .i64, col [7])] (col [0, 2])]) = noCell := by
  decide +kernel
#guard view (u 2) (kasc (u 2) [cells (u 2) (u 1) [0, 0] [1, 1] [(.atom .i64, col [7])] (col [0, 2])]) == noCell

-- past a block of `2 ^ 10`, `#guard` only (`decide` does not reduce `1100` rows of codes): the payload `0 … 1099`, cells
-- `A = [1020, 1030)`, its proper prefix `B = [1020, 1029)` and `C = [0, 1100)`, row `i` naming cell `i % 3`, so the
-- rows of `C` come first, then `B`'s, then `A`'s, each in input order
def edge : List (AscKey × Enc) :=
  [(.cells (u 3) (u 1100) (col [1020, 1020, 0]) (col [1030, 1029, 1100])
      [(.atom .i64, wordsFoR ((List.range 1100).map Nat.toUInt64).toArray)],
    wordsFoR ((List.range 1100).map fun i => (i % 3).toUInt64).toArray)]
#guard pview (u 1100) (kasc (u 1100) edge) ==
  .inr ([2, 1, 0].flatMap fun r => ((List.range 1100).filter (· % 3 = r)).map Nat.toUInt64)

end Rel.Kernel.AscTest
