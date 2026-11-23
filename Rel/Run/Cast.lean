module

public import Rel.Run.Arith
public import Rel.Kernel.Cast
public import Rel.Kernel.Db.Csv

-- exposed: every def body is a spec a downstream `rfl`/`decide`/`simp` may unfold (PLAN W.8)
@[expose] public section

/-! The row `$` (typed base S6, owner ruling J) as an operator on `Tab`: each value in demand to the same number at the
target atom (`QAtomicType.embed`), the rows with no image dropped (`Tab.keep`).

One `kscan` map of `Op.cast s t` on the encoded column writes the target words, the null word `nulWord` where the value
has no image (`QAtomicType.castWord`, never an image's word: `word_ne_nul`); the flag is `colMap .ne` against it. -/

namespace Rel
open Rel.Ext Rel.Kernel

namespace Tab

/-- **`$` on the values `X`** (`rowDens`: the graph of `QAtomicType.embed s t`): each value `x` of `X` to the word of
    `t` holding the number `x` holds (`colArr (.cast s t)`), kept where that word is not `nulWord`
    (`Tab.keep`, which keeps a canonical table canonical: no `canon`). -/
def cast {A B : Obj} {n : USize} (X : Vals A n) : Except String (Tab A B) :=
  match A, B, X with
  | .atom s, .atom t, X =>
    -- the elaborator admits only `castOK` pairs; elsewhere `colMap` would keep `t`'s low bits of the null word
    if QAtomicType.castOK s t then do
      let w ← colArr (.cast s t) n X.enc X.enc t
      let flag ← colMap .first n w.enc w.enc .i64 .i64 [] [(.ne, nulWord)]
      Tab.keep (k := .atom s) (v := .atom t) ⟨n, X, w⟩ flag
    else .error s!"$: no cast from {repr s} to {repr t}"
  | _, _, _ => .error "$: casts a number object to a number object"

end Tab

/-- The float verbs, each a row of `prims` under its q name with its `Op` and the atom of its target `D`: the `Op` on
    the operands' `f64` words, the answer written at `D` (`Tab.floatOp`). An `Op` that reads one operand
    (`Op.readsAcc` false) is a row `F ⟶ D`, one that reads two a row `F×F ⟶ D` (`x xexp y` is `x^y`, libm `pow`, so a
    negative base with an integer exponent has its value). `floor` answers at `i64` as q's `floor` does, and `round`
    (half to even, `Op.roundEven`; q has none) with it, the rest at `f64`. -/
def floatOps : List (String × Op × QAtomicType) :=
  [("sqrt", .fsqrt, .f64), ("neg", .fneg, .f64), ("abs", .fabs, .f64), ("exp", .fexp, .f64), ("log", .flog, .f64),
   ("sin", .fsin, .f64), ("cos", .fcos, .f64), ("tan", .ftan, .f64), ("asin", .fasin, .f64), ("acos", .facos, .f64),
   ("atan", .fatan, .f64), ("floor", .ffloor, .i64), ("round", .fround, .i64), ("xexp", .fpow, .f64)]

namespace Tab

/-- **The row `s` of `floatOps` on the values `X`** (`rowDens`: `floatDen`): `fmapCols` of its `Op` from `X`'s float
    atom (each component's, for a row reading two operands) to `B`'s number atom, each value to the answer, kept where
    that is a word of `B`'s atom (`Tab.keep`, no `canon`). The row is the first argument so `kernRows` names one
    constant for every name. -/
def floatOp (s : String) {A B : Obj} {n : USize} (X : Vals A n) : Except String (Tab A B) :=
  match floatOps.lookup s, A, B, X with
  | some (o, _), .atom t, .atom u, X =>
    if o.readsAcc = false ∧ (t = .f32 ∨ t = .f64) ∧ u.storeFmt?.isSome then do
      let (w, flag) ← fmapCols t u o n X.enc X.enc
      Tab.keep (k := .atom t) (v := .atom u) ⟨n, X, w⟩ flag
    else .error s!"{s} runs from a float object to a number object, found {repr t} to {repr u}"
  | some (o, _), .prod (.atom t) (.atom t'), .atom u, X =>
    if o.readsAcc = true ∧ t = t' ∧ (t = .f32 ∨ t = .f64) ∧ u.storeFmt?.isSome then do
      let (w, flag) ← fmapCols t u o n X.1.enc X.2.enc
      Tab.keep (k := .prod (.atom t) (.atom t')) (v := .atom u) ⟨n, X, w⟩ flag
    else .error s!"{s} runs from a pair of one float object to a number object, found {repr t}×{repr t'} to {repr u}"
  | some _, _, _, _ => .error s!"{s} runs from a float object, or a pair of one, to a number object"
  | none, _, _, _ => .error s!"{s}: no float verb"

/-- **`ymd` on the texts `X`** (`rowDens`: the graph of `Db.Csv.ymd`): each cell's chars read as a day
    (`yyyy.mm.dd` or `yyyy-mm-dd`, `Db.Csv.ymd`), written at `date` (`Arr.ofFn`), kept where the cell reads as one
    (`Tab.keep`, which keeps a canonical table canonical: no `canon`). The cells are read once, front to back
    (`Tab.toList`).
    Owner decision 2026-11-23: this decodes each char cell to its bytes in Lean, approved because the day count
    (H. Hinnant's `days_from_civil`) must have one source, `Db.Csv.ymd`, shared with the CSV reader and literals. -/
def ymd {A B : Obj} {n : USize} (X : Vals A n) : Except String (Tab A B) :=
  match A, B, X with
  | .arr (.atom .char), .atom .date, X =>
    let rs := (Tab.toList (k := .arr (.atom .char)) (v := .one) ⟨n, X, ()⟩).toArray
    let d (i : Fin n.toNat) : Option Int := Db.Csv.ymd ((rs[i.1]?.map (·.1)).getD [])
    Tab.keep ⟨n, X, Arr.ofFn .date n fun i => (Int32.ofInt ((d i).getD 0)).toUInt32.toUInt64⟩
      (Arr.ofFn .i64 n fun i => if (d i).isSome then 1 else 0).enc
  -- the elaborator admits only `[char] ⟶ date` (`Prim.num`)
  | _, _, _ => .error "ymd runs from a text [char] to a date, found other objects"

end Tab
end Rel
