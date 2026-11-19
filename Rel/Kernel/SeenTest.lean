import Rel.Kernel.Seen

/-! `kseen`'s `decide`-beside-`#guard` pairs: each `example` evaluates the Lean body, each `#guard` the Rust export
`qlean_k_seen`, against one literal. -/

namespace Rel.Kernel.SeenTest
open Ext.Enc

/-- `k` as a `USize` whose `toNat` the kernel reduces: a literal's is `k % 2 ^ numBits`, and `numBits` is opaque. -/
def u (k : Nat) (h : k < 4294967296 := by decide) : USize := USize.ofNat32 k h

/-- `xs` as an `i64` key column in the `foR` the kernels answer (`wordsFoR`). -/
def col (xs : List UInt64) : QAtomicType × Enc := (.i64, wordsFoR xs.toArray)

/-- An answer as its error, or its count and the words `Enc.raw` reads from `g` (`n` of them) and `first` (`k`); `n`
and `k` are the counts the literal expects, as `USize`s the kernel reduces. -/
def view (n k : USize) : Except String (Nat × Enc × Enc) → String ⊕ (Nat × List UInt64 × List UInt64)
  | .error s => .inl s
  | .ok (c, g, f) => .inr (c, (raw .i64 n g).toList, (raw .i64 k f).toList)

-- `B A B`: row 2 has `B`'s group, first seen at row 0
def bab : String ⊕ (Nat × List UInt64 × List UInt64) := .inr (2, [0, 1, 0], [0, 1])
example : view (u 3) (u 2) (kseen (u 3) [col [2, 1, 2]]) = bab := by decide +kernel
#guard view (u 3) (u 2) (kseen (u 3) [col [2, 1, 2]]) == bab

-- two columns, unsorted: rows (1,0) (2,0) (1,0) (2,1) (1,0), so (2,1) is the third key
def pairs : String ⊕ (Nat × List UInt64 × List UInt64) := .inr (3, [0, 1, 0, 2, 0], [0, 1, 3])
example : view (u 5) (u 3) (kseen (u 5) [col [1, 2, 1, 2, 1], col [0, 0, 0, 1, 0]]) = pairs := by decide +kernel
#guard view (u 5) (u 3) (kseen (u 5) [col [1, 2, 1, 2, 1], col [0, 0, 0, 1, 0]]) == pairs

-- no row: no group; no column: every row is the empty key, one group
def none0 : String ⊕ (Nat × List UInt64 × List UInt64) := .inr (0, [], [])
example : view (u 0) (u 0) (kseen (u 0) [col []]) = none0 := by decide +kernel
#guard view (u 0) (u 0) (kseen (u 0) [col []]) == none0
def one : String ⊕ (Nat × List UInt64 × List UInt64) := .inr (1, [0, 0, 0], [0])
example : view (u 3) (u 1) (kseen (u 3) []) = one := by decide +kernel
#guard view (u 3) (u 1) (kseen (u 3) []) == one

-- a `pos` column has no ties, so every row is its own group, whatever the other columns hold
def every : String ⊕ (Nat × List UInt64 × List UInt64) := .inr (3, [0, 1, 2], [0, 1, 2])
example : view (u 3) (u 3) (kseen (u 3) [col [5, 5, 5], (.i64, .pos)]) = every := by decide +kernel
#guard view (u 3) (u 3) (kseen (u 3) [col [5, 5, 5], (.i64, .pos)]) == every

-- `f64` at `kasc`'s equality: two NaNs (quiet, and signalling with payload 1) are one key, `-0.0` and `0.0` another
def floats : String ⊕ (Nat × List UInt64 × List UInt64) := .inr (3, [0, 0, 1, 1, 2], [0, 2, 4])
example : view (u 5) (u 3) (kseen (u 5)
    [(.f64, wordsFoR #[0x7ff8000000000000, 0x7ff0000000000001, 0x8000000000000000, 0, 0x3ff0000000000000])]) = floats := by
  decide +kernel
#guard view (u 5) (u 3) (kseen (u 5)
    [(.f64, wordsFoR #[0x7ff8000000000000, 0x7ff0000000000001, 0x8000000000000000, 0, 0x3ff0000000000000])]) == floats

-- a block with a patch (the outlier `2^40` among small words), beside a second column
def patched : String ⊕ (Nat × List UInt64 × List UInt64) := .inr (3, [0, 0, 0, 0, 0, 0, 1, 2], [0, 6, 7])
example : view (u 8) (u 3) (kseen (u 8) [col [1, 1, 1, 1, 1, 1, 1, 2 ^ 40], col [0, 0, 0, 0, 0, 0, 1, 1]]) = patched := by
  decide +kernel
#guard view (u 8) (u 3) (kseen (u 8) [col [1, 1, 1, 1, 1, 1, 1, 2 ^ 40], col [0, 0, 0, 0, 0, 0, 1, 1]]) == patched

-- a column that is not `foR`, a type with no order, and a `foR` whose blocks do not cover `n` are the error, named by
-- their place in `es`
def dense : String ⊕ (Nat × List UInt64 × List UInt64) := .inl "seen: es[1]: asc: constructor 0 is not foR"
example : view (u 0) (u 0) (kseen (u 2) [col [0, 1], (.i64, .bytes (ByteArray.mk (Array.replicate 16 0)))]) = dense := by
  decide +kernel
#guard view (u 0) (u 0) (kseen (u 2) [col [0, 1], (.i64, .bytes (ByteArray.mk (Array.replicate 16 0)))]) == dense
def sym : String ⊕ (Nat × List UInt64 × List UInt64) := .inl "seen: es[0]: asc: type 9 has no fixed-width order"
example : view (u 0) (u 0) (kseen (u 2) [(.sym, wordsFoR #[0, 1])]) = sym := by decide +kernel
#guard view (u 0) (u 0) (kseen (u 2) [(.sym, wordsFoR #[0, 1])]) == sym
def short : String ⊕ (Nat × List UInt64 × List UInt64) :=
  .inl "seen: es[0]: asc: foR: 1 blocks of 2^10 and a 128-byte pack are not the layout of 2000 elements"
example : view (u 0) (u 0) (kseen (u 2000) [col [0, 1]]) = short := by decide +kernel
#guard view (u 0) (u 0) (kseen (u 2000) [col [0, 1]]) == short

end Rel.Kernel.SeenTest
