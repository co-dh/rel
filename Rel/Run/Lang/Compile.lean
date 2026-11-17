import Rel.Run.Lang.Gen

/-! `compile`'s environment (`doc/rel-denotation-design.md` §3.2): the code each variable is bound to, the code
    side of `Val`. A `μ`/`ν` body's variable is bound to the round's table, an earlier binding of a program to its
    constant. -/

namespace Rel.Lang

open Rel Rel.Alg Gen

/-- The plan each variable `k` is bound to, at the objects and demand bit the term asks for. -/
abbrev Env := Nat → (A B : Obj) → (d : Bool) → Pl d A B

/-- `η` with the variable `k` bound to the table `X : A ⟶ B`, read at every demand. A use of `k` at other objects
    is ill-typed and reads `𝟘`, as `Val.bind` reads it, so the two stay one binder. -/
def Env.bind (η : Env) (k : Nat) {A B : Obj} (X : CRel A B) : Env := fun j A' B' d =>
  if j = k then (if h : A = A' ∧ B = B' then fun _ => (.val (h.1 ▸ h.2 ▸ X.rel), X.ok) else fun _ => (.zero, true))
  else η j A' B' d

end Rel.Lang
