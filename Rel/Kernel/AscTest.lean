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
def lex : List (QAtomicType × Enc) := [(.i64, col [3, 1, 3, 1, neg1]), (.i64, col [0, 9, 0, 5, 7])]
def lexOut : String ⊕ (List (List UInt64) × List UInt64) := .inr ([[neg1, 1, 1, 3, 3], [7, 5, 9, 0, 0]], [4, 3, 1, 0, 2])
example : view (u 5) (kasc (u 5) lex) = lexOut := by decide +kernel
#guard view (u 5) (kasc (u 5) lex) == lexOut

-- an `int` is ordered at its 32 bits: `0x80000000` is the least, `neg1` is `-1`; the words move whole
def i32 : List (QAtomicType × Enc) := [(.i32, col [5, neg1, 0x80000000, 2])]
def i32Out : String ⊕ (List (List UInt64) × List UInt64) := .inr ([[0x80000000, neg1, 2, 5]], [2, 1, 3, 0])
example : pview (u 4) (kasc (u 4) i32) = .inr [2, 1, 3, 0] := by decide +kernel
#guard view (u 4) (kasc (u 4) i32) == i32Out

-- an `i8` is signed at its byte: `0x80` (`-128`) is the least, `0xff` is `-1`, then `0`; the words move whole
def i8 : List (QAtomicType × Enc) := [(.i8, col [5, 0xff, 0x80, 2, 0])]
def i8Out : String ⊕ (List (List UInt64) × List UInt64) := .inr ([[0x80, 0xff, 0, 2, 5]], [2, 1, 4, 3, 0])
example : pview (u 5) (kasc (u 5) i8) = .inr [2, 1, 4, 3, 0] := by decide +kernel
#guard view (u 5) (kasc (u 5) i8) == i8Out

-- floats by `ordKey`: NaN below every number, `-0.0` equal to `0.0` (a tie, so input order)
def flt : List (QAtomicType × Enc) :=
  [(.f64, col [0x3ff0000000000000, 0x7ff8000000000000, 0x8000000000000000, 0xbff0000000000000, 0])]
def fltOut : String ⊕ (List (List UInt64) × List UInt64) :=
  .inr ([[0x7ff8000000000000, 0xbff0000000000000, 0x8000000000000000, 0, 0x3ff0000000000000]], [1, 3, 2, 4, 0])
example : pview (u 5) (kasc (u 5) flt) = .inr [1, 3, 2, 4, 0] := by decide +kernel
#guard view (u 5) (kasc (u 5) flt) == fltOut

-- no key column: the identity permutation
example : view (u 3) (kasc (u 3) []) = .inr ([], [0, 1, 2]) := by decide +kernel
#guard view (u 3) (kasc (u 3) []) == .inr ([], [0, 1, 2])

-- the errors, the first in the order of `es`: a type with no order, then `foRWords`' (a form other than `foR`, a `foR`
-- whose blocks hold fewer than `m` elements)
def gen : String ⊕ (List (List UInt64) × List UInt64) := .inl "asc: type 12 has no fixed-width order"
example : view (u 2) (kasc (u 2) [(.general, col [0, 1]), (.i64, .bytes .empty)]) = gen := by decide +kernel
#guard view (u 2) (kasc (u 2) [(.general, col [0, 1]), (.i64, .bytes .empty)]) == gen
def dense : String ⊕ (List (List UInt64) × List UInt64) := .inl "asc: constructor 0 is not foR"
example : view (u 2) (kasc (u 2) [(.i64, .bytes .empty), (.general, col [0, 1])]) = dense := by decide +kernel
#guard view (u 2) (kasc (u 2) [(.i64, .bytes .empty), (.general, col [0, 1])]) == dense
-- one block of `2 ^ 6` holds fewer than `65` elements
def short : String ⊕ (List (List UInt64) × List UInt64) :=
  .inl "asc: foR: 1 blocks of 2^6 and a 8-byte pack are not the layout of 65 elements"
example : view (u 65) (kasc (u 65) [(.i64, col [0, 1])]) = short := by decide +kernel
#guard view (u 65) (kasc (u 65) [(.i64, col [0, 1])]) == short

-- `pos` (PLAN 6.13). A2: a `pos` first key leaves every row in place, the permutation is the positions
def posFirst : String ⊕ (List (List UInt64) × List UInt64) := .inr ([[0, 1, 2], [5, 1, 3]], [0, 1, 2])
example : view (u 3) (kasc (u 3) [(.i64, .pos), (.i64, col [5, 1, 3])]) = posFirst := by decide +kernel
#guard view (u 3) (kasc (u 3) [(.i64, .pos), (.i64, col [5, 1, 3])]) == posFirst
-- A1: a `pos` key breaks every tie of the keys before it in row order, so the keys after it decide nothing
def posMid : String ⊕ (List (List UInt64) × List UInt64) := .inr ([[0, 0, 1, 1], [1, 3, 0, 2], [8, 6, 9, 7]], [1, 3, 0, 2])
example : view (u 4) (kasc (u 4) [(.i64, col [1, 0, 1, 0]), (.i64, .pos), (.i64, col [9, 8, 7, 6])]) = posMid := by
  decide +kernel
#guard view (u 4) (kasc (u 4) [(.i64, col [1, 0, 1, 0]), (.i64, .pos), (.i64, col [9, 8, 7, 6])]) == posMid
-- `pos` is `i64` only: at another type its codes would wrap
def posI32 : String ⊕ (List (List UInt64) × List UInt64) := .inl "asc: a pos column is type 4, not 3"
example : view (u 2) (kasc (u 2) [(.i32, .pos)]) = posI32 := by decide +kernel
#guard view (u 2) (kasc (u 2) [(.i32, .pos)]) == posI32
-- and at most `2 ^ 63` rows, past which the code `i ^^^ 2 ^ 63` no longer ascends with `i`; the export answers the
-- error before it allocates a row. `Rust` side only: `decide` reduces no `USize` past `u`'s `2 ^ 32`
def posBig : String ⊕ (List (List UInt64) × List UInt64) :=
  .inl "asc: a pos column of 9223372036854775809 rows is past 2^63, where its order codes wrap"
#guard view (USize.ofNat (2 ^ 63 + 1)) (kasc (USize.ofNat (2 ^ 63 + 1)) [(.i64, .pos)]) == posBig

end Rel.Kernel.AscTest
