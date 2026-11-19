import Rel.Kernel.Scatter
import Rel.Kernel.Search
import Rel.Kernel.Sort

/-! `asc`, the stable sort (`doc/rel-architecture.zh.typ` §4): `m` rows of several `foR` key columns, ordered
lexicographically, the first column the most significant and equal rows kept in input order. It answers every column
sorted and the permutation, because sorting one column carries the other columns of the same row along (`gather`).

The body is design §4's composition: the sort phase (`ascGrade`) answers the permutation `p`, and `scatterWords`,
`kscatter`'s model, writes the rest: `til m` through `p` is each row's destination, and each column through the
destinations is that column sorted. `crate/src/asc.rs` is the fused form, an LSD radix sort over the bytes of the order
codes. The `k` in the name is temporary until 6.11. -/

namespace Rel.Kernel
open Ext.Enc
open Rel.Kernel.Scan (Kind)

/-- The order code of a raw word of a column of type `t`, as an unsigned word: `ordKey` at `t`'s layout
(`orderKind`), so a signed integer flips its sign bit and a float folds `-0.0` and every NaN below every number and then
flips (q's order; PLAN 6.9's map replaces it). `symbol` and `general` have no fixed-width order: `none`. -/
def ascOrd (t : QAtomicType) : Option (UInt64 → UInt64) :=
  (orderKind t).map fun k => ordKey k.width (k == .f32 || k == .f64) (k == .i16 || k == .i32 || k == .i64)

/-- Row `i` no later than row `j` in the lexicographic order of the code columns `ks`, the first the most significant:
the first column where the two differ decides, and rows equal in every column answer `true`. -/
def lexLe : List (Array UInt64) → Nat → Nat → Bool
  | [], _, _ => true
  | c :: cs, i, j => decide (c[i]?.getD 0 < c[j]?.getD 0) || (c[i]?.getD 0 == c[j]?.getD 0 && lexLe cs i j)

/-- `x` inserted into `l` after every element `le` puts no later than it: a later index lands after its ties. -/
def ascIns (le : Nat → Nat → Bool) (x : Nat) : List Nat → List Nat
  | [] => [x]
  | y :: ys => if le y x then y :: ascIns le x ys else x :: y :: ys

/-- The sort phase: `til m` stably ordered by `lexLe ks`, inserted one index at a time. An insertion sort and not
`List.mergeSort`, whose well-founded recursion the kernel does not unfold, so `decide` checks this body (`AscTest`). -/
def ascGrade (m : Nat) (ks : List (Array UInt64)) : List Nat :=
  (List.range m).foldl (fun acc x => ascIns (lexLe ks) x acc) []

/-- A key column's `m` words, `foRWords`', but a `pos` column is `i64` (PLAN 6.13): at another type its positions'
order codes would wrap, so it is the error there; at `i64` its codes are in row order, which is law A1. -/
def ascWords (m : USize) : QAtomicType × Enc → Except String (Array UInt64)
  | (.i64, .pos) => foRWords "asc" m .pos
  | (t, .pos) => .error s!"asc: a pos column is type {QAtomicType.i64.ctorIdx}, not {t.ctorIdx}"
  | (_, e) => foRWords "asc" m e

/-- One key column of `kasc`: its `m` words as every kernel of design §4 reads a `foR` (`foRWords`) and their order
codes at its type (`ascOrd`, which cuts a word to the type's width), or why it has none: a type with no order, then
`ascWords`' error. -/
def ascCol (m : USize) (c : QAtomicType × Enc) : Except String (Array UInt64 × Array UInt64) :=
  match ascOrd c.1 with
  | none => .error s!"asc: type {c.1.ctorIdx} has no fixed-width order"
  | some f => (fun x => (x, x.map f)) <$> ascWords m c

/-- **The asc kernel** (design §4, `asc_sorted` and `asc_perm`): the `m` rows of the columns `es`, each a type and a
`foR` column, sorted stably and lexicographically by their order codes. The answer is every column's words sorted and
the permutation, row `k` of the answer being input row `p[k]`, each as `wordsFoR`. The first error in the order of
`es` is the answer (`ascCol`). -/
@[extern "qlean_k_asc"]
def kasc (m : USize) (es : @& List (QAtomicType × Enc)) : Except String (List Enc × Enc) := do
  let cs ← es.mapM (ascCol m)
  let p := ((ascGrade m.toNat (cs.map (·.2))).map Nat.toUInt64).toArray
  let r ← scatterWords p ((List.range m.toNat).map Nat.toUInt64).toArray m.toNat 0
  let vs ← cs.mapM fun c => scatterWords r c.1 m.toNat 0
  pure (vs.map wordsFoR, wordsFoR p)

end Rel.Kernel
