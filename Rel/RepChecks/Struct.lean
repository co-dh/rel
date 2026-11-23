import Rel.RepChecks.Canon
import Rel.RepStruct

/-! The `#guard` checks of `Rel.RepStruct`, kept outside the module: a `#guard` runs compiled code, whose IR a `module` does not export (PLAN perf9e). -/

namespace Rel
open Rel.Ext Rel.Kernel Rel.Verify Ext.Enc
open scoped Rel.Core.Rel

section Checks

/-- The `i64` column of the integers `ws`, `foR` (`Arr.ofFn`). -/
private def col (ws : List Int64) : Arr .i64 ws.length.toUSize := Arr.ofFn .i64 _ fun i => (ws.getD i.1 0).toUInt64

/-- The table of the pairs `ps` as given, unsorted, both columns `col`. -/
private def tabW (ps : List (Int64 × Int64)) : Tab .long .long :=
  ⟨ps.length.toUSize, List.length_map _ ▸ col (ps.map (·.1)), List.length_map _ ▸ col (ps.map (·.2))⟩

/-- `-0.0`, `+0.0`, NaN with payloads `1` and `2`, `+inf`, `-inf`, `1.5`, `-0.0` again, as `f64` bits. -/
private def f64s : List UInt64 := [0x8000000000000000, 0, 0x7ff8000000000001, 0x7ff8000000000002, 0x7ff0000000000000,
  0xfff0000000000000, 0x3ff8000000000000, 0x8000000000000000]

/-- Integer tables: duplicate rows, negatives, one row, none. -/
private def ints : List (List (Int64 × Int64)) :=
  [[(3, 1), (1, 2), (3, 1), (-1, 2), (1, 2), (2, 7)], [(2, 5), (1, -3), (2, 6), (3, 3), (2, 5)], [(4, 8)], []]

/-- A float value column with a duplicate row (`-0.0` at key `3` twice). -/
private def F : Tab .long (.atom .f64) := ⟨8, col [3, 1, 2, 1, 4, 4, 0, 3], Arr.ofFn .f64 8 (f64s.getD · 0)⟩
/-- A tuple value column with duplicate rows. -/
private def P : Tab .long (.prod .long .long) := ⟨5, col [3, 1, 3, 1, 3], (col [1, 1, 1, 2, 1], col [5, 6, 5, 6, 5])⟩
-- `𝟘` at an atom, a float, a tuple, an `arr` and a `sum` side
#guard specOk (Tab.zero : Except String (Tab .long (.atom .f64))) [] &&
  specOk (Tab.zero : Except String (Tab (.prod .long .long) (.arr .long))) [] &&
  specOk (Tab.zero : Except String (Tab (.sum .long .long) .long)) []

-- `𝟙` on the values `X`: duplicates, a float, a tuple, none
#guard ints.all fun ps => let R := tabW ps
  specOk (Tab.idU R.key) (R.key.toList.map fun a => (a, a))
#guard specOk (Tab.idU F.val) ((Vals.rows F.val).map fun a => (a, a)) &&
  specOk (Tab.idU P.val) ((Vals.rows P.val).map fun a => (a, a))


/-- `top X Y` against `X × Y` as a set. -/
private def topOk {A B : Obj} [BEq A.El] [BEq B.El] {n m : USize} (X : Vals A n) (Y : Vals B m) : Bool :=
    specOk (Tab.top X Y) ((Vals.rows X).flatMap fun a => (Vals.rows Y).map fun b => (a, b))

-- `⊤`: integers (an empty side on either end), a float, a tuple
#guard ints.all fun ps => ints.all fun qs => topOk (tabW ps).key (tabW qs).val
#guard topOk P.val F.val && topOk F.val P.val

/-- `outl X`, `outr X` against the projections as sets. -/
private def outOk {A B : Obj} [BEq A.El] [BEq B.El] {n : USize} (X : Vals (.prod A B) n) : Bool :=
    specOk (Tab.outl X) ((Vals.rows X).map fun p => (p, p.1)) && specOk (Tab.outr X) ((Vals.rows X).map fun p => (p, p.2))

-- `π₁`, `π₂`: integer pairs with duplicates, none, a float component, a tuple component
#guard ints.all fun ps => let R := tabW ps; outOk (A := .long) (B := .long) (R.key, R.val)
#guard outOk (A := .long) (B := .atom .f64) (F.key, F.val) && outOk (A := .long) (B := .prod .long .long) (P.key, P.val)

/-- `pair` against its denotation as a set. -/
private def pairOk {A B C : Obj} [BEq A.El] [BEq B.El] [BEq C.El] (R : Tab A B) (S : Tab A C) : Bool :=
    specOk (R.pair S) (R.toList.flatMap fun (a, b) => S.toList.filterMap fun (a', c) =>
      if a == a' then some (a, (b, c)) else none)

-- `⟨R, S⟩`: integers (duplicates, an empty side, no common key), a float and a tuple value
#guard ints.all fun ps => ints.all fun qs => pairOk (tabW ps) (tabW qs)
#guard pairOk F P && pairOk P F

/-- `flat X R` against `Rᴵ` on `X` as a set: `((i, a), b)` for `(i, a)` of `X` and `(i, (a, b))` of `R`. -/
private def flatOk {I A B : Obj} [BEq I.El] [BEq A.El] [BEq B.El] {n : USize} (X : Vals (.prod I A) n)
    (R : Tab I (.prod A B)) : Bool :=
  specOk (Tab.flat X R) ((Vals.rows X).flatMap fun p => R.toList.filterMap fun (i, a, b) =>
    if p.1 == i && p.2 == a then some (p, b) else none)

-- `Rᴵ`: a tuple family on integer pairs (duplicates, a pair `R` misses), on none, and a float source
#guard flatOk (I := .long) (A := .long) (col [3, 1, 3, 3, 9], col [1, 2, 1, 5, 1]) P &&
  flatOk (I := .long) (A := .long) (col [], col []) P &&
  flatOk (I := .long) (A := .atom .f64) (F.key, F.val) (⟨F.n, F.key, (F.val, F.key)⟩ : Tab .long (.prod (.atom .f64) .long))

/-- `inl X` and `inr X` against the injections as sets. -/
private def injOk {A B : Obj} [BEq A.El] [BEq B.El] {n : USize} (X : Vals A n) (Y : Vals B n) : Bool :=
    specOk (Tab.inl (B := B) X) ((Vals.rows X).map fun a => (a, .inl a)) &&
    specOk (Tab.inr (A := A) Y) ((Vals.rows Y).map fun b => (b, .inr b))

/-- `inl°`, `inr°` on the sum values `inl X` and `inr Y` give, against the converses as sets: `X`'s values on the
left ones, none on the right ones (a payload of no value on the other side), and the mirror. -/
private def injConvOk {A B : Obj} [BEq A.El] [BEq B.El] {n : USize} (X : Vals A n) (Y : Vals B n) : Bool :=
  match Tab.inl (B := B) X, Tab.inr (A := A) Y with
  | .ok L, .ok R =>
    specOk (Tab.inlConv L.val) ((Vals.rows X).map fun a => (.inl a, a)) && specOk (Tab.inrConv L.val) [] &&
    specOk (Tab.inrConv R.val) ((Vals.rows Y).map fun b => (.inr b, b)) && specOk (Tab.inlConv R.val) []
  | _, _ => false

-- `inl`, `inr`: duplicates, none, a float and a tuple summand
#guard ints.all fun ps => let R := tabW ps; injOk R.key R.val
#guard injOk F.val F.key && injOk P.val P.key
-- `inl°`, `inr°`: duplicates, none, a float and a tuple summand
#guard ints.all fun ps => let R := tabW ps; injConvOk R.key R.val
#guard injConvOk F.val F.key && injConvOk P.val P.key

end Checks

end Rel
