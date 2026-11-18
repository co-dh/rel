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
  | .ok (vs, p) => .inr (vs.map fun v => (raw .long n v).toList, (raw .long n p).toList)

/-- An answer's permutation alone. The kernel builds no answer column it is not asked for, and one whose residuals are
32 or 64 bits wide in `lgEnc`'s blocks of 1024 is more than `decide` reduces, so a case with such values `decide`s this
and `#guard`s `view`. -/
def pview (n : USize) : Except String (List Enc × Enc) → String ⊕ List UInt64
  | .error s => .inl s
  | .ok (_, p) => .inr (raw .long n p).toList

/-- `2 ^ 64 - 1`, the long `-1`. -/
def neg1 : UInt64 := 0xffffffffffffffff

-- two long keys: `-1` sorts first (the sign flip); rows 0 and 2 tie in both columns and keep their input order;
-- rows 1 and 3 tie in the first and the second column decides
def lex : List (QAtomicType × Enc) := [(.long, col [3, 1, 3, 1, neg1]), (.long, col [0, 9, 0, 5, 7])]
def lexOut : String ⊕ (List (List UInt64) × List UInt64) := .inr ([[neg1, 1, 1, 3, 3], [7, 5, 9, 0, 0]], [4, 3, 1, 0, 2])
example : view (u 5) (kasc (u 5) lex) = lexOut := by decide +kernel
#guard view (u 5) (kasc (u 5) lex) == lexOut

-- an `int` is ordered at its 32 bits: `0x80000000` is the least, `neg1` is `-1`; the words move whole
def i32 : List (QAtomicType × Enc) := [(.int, col [5, neg1, 0x80000000, 2])]
def i32Out : String ⊕ (List (List UInt64) × List UInt64) := .inr ([[0x80000000, neg1, 2, 5]], [2, 1, 3, 0])
example : pview (u 4) (kasc (u 4) i32) = .inr [2, 1, 3, 0] := by decide +kernel
#guard view (u 4) (kasc (u 4) i32) == i32Out

-- floats by `ordKey`: NaN below every number, `-0.0` equal to `0.0` (a tie, so input order)
def flt : List (QAtomicType × Enc) :=
  [(.float, col [0x3ff0000000000000, 0x7ff8000000000000, 0x8000000000000000, 0xbff0000000000000, 0])]
def fltOut : String ⊕ (List (List UInt64) × List UInt64) :=
  .inr ([[0x7ff8000000000000, 0xbff0000000000000, 0x8000000000000000, 0, 0x3ff0000000000000]], [1, 3, 2, 4, 0])
example : pview (u 5) (kasc (u 5) flt) = .inr [1, 3, 2, 4, 0] := by decide +kernel
#guard view (u 5) (kasc (u 5) flt) == fltOut

-- no key column: the identity permutation
example : view (u 3) (kasc (u 3) []) = .inr ([], [0, 1, 2]) := by decide +kernel
#guard view (u 3) (kasc (u 3) []) == .inr ([], [0, 1, 2])

-- the errors, the first in the order of `es`: a type with no order, then `foRWords`' (a form other than `foR`, a `foR`
-- whose blocks hold fewer than `m` elements)
def gen : String ⊕ (List (List UInt64) × List UInt64) := .inl "asc: type 0 has no fixed-width order"
example : view (u 2) (kasc (u 2) [(.general, col [0, 1]), (.long, .bytes .empty)]) = gen := by decide +kernel
#guard view (u 2) (kasc (u 2) [(.general, col [0, 1]), (.long, .bytes .empty)]) == gen
def dense : String ⊕ (List (List UInt64) × List UInt64) := .inl "asc: constructor 0 is not foR"
example : view (u 2) (kasc (u 2) [(.long, .bytes .empty), (.general, col [0, 1])]) = dense := by decide +kernel
#guard view (u 2) (kasc (u 2) [(.long, .bytes .empty), (.general, col [0, 1])]) == dense
-- one block of `2 ^ 6` holds fewer than `65` elements
def short : String ⊕ (List (List UInt64) × List UInt64) :=
  .inl "asc: foR: 1 blocks of 2^6 and a 8-byte pack are not the layout of 65 elements"
example : view (u 65) (kasc (u 65) [(.long, col [0, 1])]) = short := by decide +kernel
#guard view (u 65) (kasc (u 65) [(.long, col [0, 1])]) == short

end Rel.Kernel.AscTest
