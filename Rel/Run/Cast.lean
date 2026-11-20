import Rel.Run.Canon
import Rel.Run.SetOps
import Rel.Kernel.Cast

/-! The row `$` (typed base S6, owner ruling J) as an operator on `Tab`: each value in demand to the same number at the
target atom (`QAtomicType.embed`), the rows with no image dropped (`Tab.keep`).

The values are read and the target words written by Lean, element by element (`Arr.get`, `Arr.ofFn`), not by a kernel
on the encoded column: no `Op` turns an integer word into a float word (design S7), and the float `Op`s are opaque to a
proof, so a `kscan` pipeline could not be shown to agree with `embed`. -/

namespace Rel
open Rel.Ext Rel.Kernel

namespace Tab

/-- **`$` on the values `X`** (`rowDens`: the graph of `QAtomicType.embed s t`): each value `x` of `X` to the word of
    `t` holding the number `x` holds, kept where there is one (`keep` of the flag `1`/`0`); then `canon`. -/
def cast {A B : Obj} {n : USize} (X : Vals A n) : Except String (Tab A B) :=
  match A, B, X with
  | .atom s, .atom t, X =>
    if hu : t ≠ .u1 ∧ t.width.isSome then do
      let w : Fin n.toNat → Option (Dep.Carrier t) := fun i => QAtomicType.embed s t (X.get i)
      let val := Arr.ofFn t n (fun i => ((w i).map t.word).getD 0) hu
      let flag := Arr.ofFn .i64 n fun i => if (w i).isSome then 1 else 0
      (← Tab.keep (k := .atom s) (v := .atom t) ⟨n, X, val⟩ flag.enc).canon
    else .error s!"$: the atom {repr t} has no fixed width"
  | _, _, _ => .error "$: casts a number object to a number object"

end Tab
end Rel
