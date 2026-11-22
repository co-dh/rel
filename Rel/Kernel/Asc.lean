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

/-- The layout a column of type `t` is ordered at (`orderKind`): its width in bytes, whether it is a float and whether
it is signed, `asc::order` in `crate/src/asc.rs`. `symbol` and `general` have no fixed-width order: `none`. The flags
are one exhaustive match, so a new `Kind` has to state its own (a test `k == .i16 || …` left `i8` unsigned). -/
def ascLayout (t : QAtomicType) : Option (Nat × Bool × Bool) :=
  (orderKind t).map fun k => match k with
    | .bit | .u8 | .c8 => (k.width, false, false)
    | .i8 | .i16 | .i32 | .i64 => (k.width, false, true)
    | .f32 | .f64 => (k.width, true, false)

/-- **The order code** of the low `w` bytes of `v` (PLAN 6.9's map): unsigned, so comparing codes as unsigned words
orders the values, and one to one on the `w`-byte word, so equal codes are equal stored bits (`ascOrd_atom`). A signed
integer flips its sign bit; a float takes IEEE 754 totalOrder: a non-negative one sets its sign bit and a negative one
flips every bit, so `-NaN < -∞ < … < -0.0 < 0.0 < … < ∞ < NaN` and no two bit patterns share a code. Normalising a
`-0.0` or a NaN belongs to whatever produces float words, not here. The non-float branches are `ordKey`'s
(`Rel/Kernel/Search.lean`, `rfl`), a copy that dies with `ordKey`'s `bin` path (W5). -/
def ordCode (w : Nat) (float signed : Bool) (v : UInt64) : UInt64 :=
  let mask : UInt64 := if w == 8 then 0xffffffffffffffff else (2 ^ (8 * w) - 1).toUInt64
  let top : UInt64 := (2 ^ (8 * w - 1)).toUInt64
  let u := v &&& mask
  if float then (if u &&& top != 0 then u ^^^ mask else u ||| top) else if signed then u ^^^ top else u

/-- What `ordCode` runs as: its masks by `Column.ones` and `Column.pow2`; the `Nat` `2 ^ 63` at `w = 8` is a
GMP number. -/
private def ordCodeImpl (w : Nat) (float signed : Bool) (v : UInt64) : UInt64 :=
  let mask : UInt64 := if w == 8 then 0xffffffffffffffff else Column.ones (8 * w)
  let top : UInt64 := Column.pow2 (8 * w - 1)
  let u := v &&& mask
  if float then (if u &&& top != 0 then u ^^^ mask else u ||| top) else if signed then u ^^^ top else u

@[csimp] private theorem ordCode_eq_impl : @ordCode = @ordCodeImpl := by
  funext w f s v
  simp only [ordCode, ordCodeImpl, Column.ones_eq, Column.pow2_eq,
    show Nat.toUInt64 2 = 2 from rfl]

/-- The order code of a raw word of a column of type `t`: `ordCode` at `t`'s layout (`ascLayout`). -/
def ascOrd (t : QAtomicType) : Option (UInt64 → UInt64) :=
  (ascLayout t).map fun (w, f, s) => ordCode w f s

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

/-- A key column's `m` words, `foRWords`', but a `pos` column is the error wherever its positions' order codes are not
in row order (PLAN 6.13): at a type other than `i64` they wrap at its width, and at `i64` the code of `i` is
`i ^^^ 2^63`, which ascends with `i` only up to `2^63` rows. Within that bound the rows are in order, laws A1 and A2. -/
def ascWords (m : USize) : QAtomicType × Enc → Except String (Array UInt64)
  | (.i64, .pos) => if m.toNat ≤ 2 ^ 63 then foRWords "asc" m .pos
    else .error s!"asc: a pos column of {m} rows is past 2^63, where its order codes wrap"
  | (t, .pos) => .error s!"asc: a pos column is type {QAtomicType.i64.ctorIdx}, not {t.ctorIdx}"
  | (_, e) => foRWords "asc" m e

/-- What a key column of `kasc` and `kseen` holds, the column itself (an `Enc` of the key's rows) beside it. `atom t`:
the column is words of type `t`, row `i` its word `i`. `cells n c lo hi els`: an `arr` side (`Obj.arr`) of `n` cells,
`lo` and `hi` its two `i64` columns of `n` words and `els` the key columns of its payload of `c` rows; the column is
words below `n`, row `i` the cell its word names, that cell the payload rows `j` with `lo ≤ j < hi`, clamped to
`[0, c)` (`Vals.row`). The column is the only part `kasc` carries, so after a sort the cells stay where they were
and the column names them in the new order: the sorted column is again a key of the same `cells`. -/
inductive AscKey where
  | atom (t : QAtomicType)
  | cells (n c : USize) (lo hi : Enc) (els : List (AscKey × Enc))

/-- The first payload row of cell `r`: its `lo` word as an `Int64`, clamped to `[0, c]`. -/
def cellStart (c : Nat) (lo : Array UInt64) (r : UInt64) : Nat := min (max (lo[r.toNat]?.getD 0).toInt64.toInt 0).toNat c

/-- The length of cell `r`: its `hi` word clamped to `c`, less `cellStart`; `0` where `hi` is not past `lo`. -/
def cellLen (c : Nat) (lo hi : Array UInt64) (r : UInt64) : Nat :=
  (min (hi[r.toNat]?.getD 0).toInt64.toInt (c : Int)).toNat - cellStart c lo r

/-- The order codes of a `cells` key over `c` payload rows, each a function of a row's word `r` (the cell it names),
the payload rows coded by the columns `xs`: per element position `j < c`, whether cell `r` reaches `j` (`1`, else `0`)
and then each payload column's code of its element there (`0` past the end). `lexLe` over them orders cells
lexicographically by their elements' codes, a proper prefix first, and two rows are equal in every code exactly when
their cells have one length and equal codes element by element. Functions of the word alone, so a permuted column
has the permuted codes; every cell lies in `[0, c)`, so `c` positions cover the longest. -/
def cellFns (c : Nat) (lo hi : Array UInt64) (xs : List (Array UInt64)) : List (UInt64 → UInt64) :=
  let s := cellStart c lo
  let len := cellLen c lo hi
  (List.range c).flatMap fun j =>
    (fun r => if j < len r then 1 else 0) :: xs.map fun x r => if j < len r then x[s r + j]?.getD 0 else 0

/-- The code columns of an atom column `e` of `m` rows whose order codes are `c`: `[c]` where `e` holds no null
(`hasNul`); else the null as a value of its own, q's order: first a column `0` at a null and `1` elsewhere, so a null
sorts before every value, then `c` with `0` at a null, so all nulls are one value. -/
def nulCodes (m : USize) (e : Enc) (c : Array UInt64) : List (Array UInt64) :=
  if hasNul e then let ns := foRNuls m e
    [ns.map (1 - ·), c.mapIdx fun i v => if ns[i]?.getD 0 == 0 then v else 0]
  else [c]

mutual
/-- One key column of `kasc` at `m` rows: the words it carries and its order code columns, or why it has none. An
`atom` column carries its `m` words (`ascWords`) coded at its type (`ascOrd`, which cuts a word to the type's width):
a type with no order, then `ascWords`' error. A `cells` column carries its `m` words, each below its `n` cells, and is
coded by `cellFns` over `lo`, `hi` and its payload's codes (`ascCodes` at `c` rows): the column, a word naming no
cell, `lo`, `hi`, then the payload's first error. -/
def ascCol (m : USize) : AscKey × Enc → Except String (Array UInt64 × List (Array UInt64))
  | (.atom t, e) => match ascOrd t with
    | none => .error s!"asc: type {t.ctorIdx} has no fixed-width order"
    | some f => (fun x => (x, nulCodes m e (x.map f))) <$> ascWords m (t, e)
  | (.cells n c lo hi els, e) => do
    let ix ← foRWords "asc: cells" m e
    match ix.find? (n.toNat ≤ ·.toNat) with
    | some r => .error s!"asc: cells: row word {r} names no cell of {n}"
    | none => do
      let l ← foRWords "asc: cells lo" n lo
      let h ← foRWords "asc: cells hi" n hi
      let ks ← ascCodes c els
      pure (ix, (cellFns c.toNat l h ks).map fun f => ix.map f)

/-- The order code columns of the key columns `es` at `m` rows, `ascCol`'s in the order of `es`. -/
def ascCodes (m : USize) : List (AscKey × Enc) → Except String (List (Array UInt64))
  | [] => .ok []
  | k :: ks => do pure ((← ascCol m k).2 ++ (← ascCodes m ks))
end

/-- **The asc kernel** (design §4, `asc_sorted` and `asc_perm`): the `m` rows of the key columns `es` (`AscKey`),
sorted stably and lexicographically by their order codes. The answer is every column's words sorted and the
permutation, row `k` of the answer being input row `p[k]`, each as `wordsFoR`. The first error in the order of `es` is
the answer (`ascCol`). -/
@[extern "qlean_k_asc"]
def kasc (m : USize) (es : @& List (AscKey × Enc)) : Except String (List Enc × Enc) := do
  let cs ← es.mapM (ascCol m)
  let p := ((ascGrade m.toNat (cs.flatMap (·.2))).map Nat.toUInt64).toArray
  let r ← scatterWords .last p ((List.range m.toNat).map Nat.toUInt64).toArray m.toNat 0
  let vs ← cs.mapM fun c => scatterWords .last r c.1 m.toNat 0
  -- each column's null flags move with its words
  let ns ← es.mapM fun (_, e) =>
    if hasNul e then nulMap <$> scatterWords .last r (foRNuls m e) m.toNat 0 else pure .empty
  pure (vs.zipWith (fun v n => wordsFoR v n) ns, wordsFoR p)

end Rel.Kernel
