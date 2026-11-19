/-
  The executable relation algebra `Alg` read in the allegory of sets: `rep R` is the relation `R.Holds` as a
  `Rel(Set)` arrow, and each theorem says `rep` of an `Alg` op is the `Rel(Set)` op on the `rep`s.
-/
import Rel.Run.Alg
import Rel.Core.Rel
import Rel.Run.Lang.Lazy

namespace Rel.Rep

open Tab
open scoped Rel.Core.Rel
open Rel.Core.Rel hiding id comp recip inter union zero le inl inr junc

variable {A B C : Obj}

/-- The `Rel(Set)` arrow a `Rel` denotes: `x` to `y` when some row holds `(x, y)`. -/
def rep (R : Tab A B) : Core.Rel (A.El) (B.El) := R.Holds

/-- The coreflexives `K` confines a relation's two sides to: `𝟙` on an unknown side, `rep (idU c)` (the
    coreflexive on `c`'s values, `rep_idU`) on a known one. -/
def _root_.Rel.Known.den (K : Known A B) : Core.Rel A.El A.El × Core.Rel B.El B.El :=
  (K.dom.elim (𝟙 _) fun c => rep (Alg.idU c.2), K.ran.elim (𝟙 _) fun c => rep (Alg.idU c.2))

/-- `r` represents `R` in the context `K`, as `run` computes it there: a table agrees with `R` on `K`'s sides
    only, since `Gen.Sound` fixes a term only at the keys it is given and a caller that passes `K.ran` cuts the
    result itself; a `tab none` (a run past capacity) represents anything. -/
def _root_.Rel.Rel.Reps (K : Known A B) : Rel A B → Core.Rel A.El B.El → Prop
  | .tab (.error _), _ => True
  | .tab (.ok t), R => K.den.1 ≫ rep t ≫ K.den.2 = K.den.1 ≫ R ≫ K.den.2
  | .lazy f, R => (f K).Reps K R
  | .bits g w o x ra y rc, R => match Tab.ofBits g w o x ra y rc with
    | .error _ => True
    | .ok t => K.den.1 ≫ rep t ≫ K.den.2 = K.den.1 ≫ R ≫ K.den.2

/-- What `r` computes in `K` agrees with `R` on `K`'s sides, where `r` represents `R` there. -/
theorem _root_.Rel.Rel.Reps.run {K : Known A B} : ∀ {r : Rel A B} {R : Core.Rel A.El B.El} {t : Tab A B},
    r.Reps K R → r.run K = some t → K.den.1 ≫ rep t ≫ K.den.2 = K.den.1 ≫ R ≫ K.den.2
  | .tab (.error _), _, _, _, e => by simp [Rel.run, Except.toOption] at e
  | .tab (.ok _), _, _, h, e => by simp only [Rel.run, Except.toOption, Option.some.injEq] at e; subst e; exact h
  | .lazy f, _, _, h, e => Rel.Reps.run (r := f K) h e
  | .bits g w o x ra y rc, _, _, h, e => by
    simp only [Rel.Reps] at h; simp only [Rel.run] at e
    revert h e; cases Tab.ofBits g w o x ra y rc <;> intro h e <;>
      simp only [Except.toOption, Option.some.injEq, reduceCtorEq] at e h ⊢ <;> (try subst e) <;> (try exact h)

/-- `rep R x y` is `R.Holds x y`, by definition. -/
theorem rep_apply (R : Tab A B) (x : A.El) (y : B.El) : rep R x y = R.Holds x y := rfl

section Ops

open Rel.Alg

/-- `rep (R°) = (rep R)°`: the converse swaps the two fields. -/
theorem rep_conv (R : Tab A B) : rep (R°) = (rep R)° :=
  Core.Rel.ext fun y x => convArr_holds R.key R.val x y

/-- `rep 𝟘 = 𝟘`: no row, no pair. -/
theorem rep_zero : rep (Alg.zero : Tab A B) = 𝟘 :=
  Core.Rel.ext fun _ _ => ⟨fun ⟨i, _⟩ => i.elim0, False.elim⟩

/-- `rep (idU U)` is the coreflexive on the elements `U` lists — not `𝟙`, which it is only when `U` lists every
    element of `A.El`. -/
theorem rep_idU {m : USize} (U : Vals A m) :
    rep (idU U) = corefl (α := A.El) fun x => ∃ i, U.row i = x :=
  Core.Rel.ext fun x y => (idU_holds U x y).trans ⟨fun ⟨h, hx⟩ => ⟨h, hx⟩, fun ⟨h, hx⟩ => ⟨h, hx⟩⟩

/-- `rep (outl T) = rep T ≫ π₁`: `outl` on a relation into a product is that relation followed by the first
    projection, the graph of `Prod.fst` (`relProd`'s `π₁`). -/
theorem rep_outl (T : Tab A (.prod B C)) :
    rep (outl T) = rep T ≫ (graph Prod.fst : Core.Rel (B.El × C.El) (B.El)) :=
  Core.Rel.ext fun x y => (outl_holds T x y).trans
    ⟨fun ⟨z, h⟩ => ⟨(y, z), h, rfl⟩, fun ⟨⟨y', z⟩, h, e⟩ => ⟨z, (show y = y' from e) ▸ h⟩⟩

/-- `rep (outr T) = rep T ≫ π₂`: the second projection, the graph of `Prod.snd`. -/
theorem rep_outr (T : Tab A (.prod B C)) :
    rep (outr T) = rep T ≫ (graph Prod.snd : Core.Rel (B.El × C.El) (C.El)) :=
  Core.Rel.ext fun x z => (outr_holds T x z).trans
    ⟨fun ⟨y, h⟩ => ⟨(y, z), h, rfl⟩, fun ⟨⟨y, z'⟩, h, e⟩ => ⟨y, (show z = z' from e) ▸ h⟩⟩

end Ops

-- `Classical.choice` below comes with `Rel.Holds` itself (through qlean's `Carrier`), not from the proofs
#print axioms Holds
#print axioms rep_conv
#print axioms rep_zero
#print axioms rep_idU
#print axioms rep_outl
#print axioms rep_outr

end Rel.Rep
