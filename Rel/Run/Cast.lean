import Rel.Run.Arith
import Rel.Kernel.Cast

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
      let flag ← colMap .ne n w.enc (← colConst n nulWord)
      Tab.keep (k := .atom s) (v := .atom t) ⟨n, X, w⟩ flag
    else .error s!"$: no cast from {repr s} to {repr t}"
  | _, _, _ => .error "$: casts a number object to a number object"

end Tab

/-- The unary float verbs, each a row `F ⟶ F` of `prims` under its q name: its `Op` on each value's `f64` word
    (`Tab.unary`). Every `Op` that reads one operand at `f64` and answers one there. -/
def unaryOps : List (String × Op) :=
  [("sqrt", .fsqrt), ("neg", .fneg), ("abs", .fabs), ("exp", .fexp), ("log", .flog), ("sin", .fsin),
   ("cos", .fcos), ("tan", .ftan), ("asin", .fasin), ("acos", .facos), ("atan", .fatan), ("floor", .ffloor)]

namespace Tab

/-- **The row `s` of `unaryOps` on the values `X`** (`rowDens`: `unaryDen`): `fmapCols` of its `Op` at `X`'s float
    atom, each value to the answer, kept where that is a word of the atom (not a NaN;
    `Tab.keep`, no `canon`). The row is the
    first argument so `kernRows` names one constant for every name. -/
def unary (s : String) {A : Obj} {n : USize} (X : Vals A n) : Except String (Tab A A) :=
  match unaryOps.lookup s, A, X with
  | some o, .atom t, X =>
    if t = .f32 ∨ t = .f64 then do
      let (w, flag) ← fmapCols t o n X.enc
      Tab.keep (k := .atom t) (v := .atom t) ⟨n, X, w⟩ flag
    else .error s!"{s} runs on a float object, found one of {repr t}"
  | some _, _, _ => .error s!"{s} runs on a float object"
  | none, _, _ => .error s!"{s}: no unary float verb"

end Tab
end Rel
