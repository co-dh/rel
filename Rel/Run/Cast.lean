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
    `t` holding the number `x` holds (`colArr (.cast s t)`), kept where that word is not `nulWord`; then `canon`. -/
def cast {A B : Obj} {n : USize} (X : Vals A n) : Except String (Tab A B) :=
  match A, B, X with
  | .atom s, .atom t, X =>
    -- the elaborator admits only `castOK` pairs; elsewhere `colMap` would keep `t`'s low bits of the null word
    if QAtomicType.castOK s t then do
      let w ← colArr (.cast s t) n X.enc X.enc t
      let flag ← colMap .ne n w.enc (← colConst n nulWord)
      Tab.keep (k := .atom s) (v := .atom t) ⟨n, X, w⟩ flag >>= Tab.canon
    else .error s!"$: no cast from {repr s} to {repr t}"
  | _, _, _ => .error "$: casts a number object to a number object"

end Tab
end Rel
