import Rel.Lang.Laws.AopS2_10
import Rel.Lang.Laws.LamTotal

/-! # List-combinator laws of freyd `AOP/A5_6_ListCombinators.lean`, on the concrete core

`Rel/Programs/Aop/A5_6_ListCombinators.lean` states each as `theorem <name> … by Rel.Lang.Tm.<name>_den`. -/

namespace Rel.Lang
open Tab Rel.Rep
open scoped Rel.Core.Rel
open Rel.Core.Rel hiding id comp recip inter union zero le inl inr junc

/-- `Λ(R S) = Λ(R) E(S)`, `E(S) = Λ(∋ S)`: the image of the set `Λ(R)` under `S`, when `Λ(R)` has a set at every point
    (`dom(Λ(R)) = 𝟙`). `Tm.Ecomp_den` is the case `R = ∋ R'`. -/
theorem Tm.lamE_den {A B C : Obj} {R : Tm A B} {S : Tm B C} (ρ : Val)
    (h : (Tm.dom (.lam R)).den ρ = (Tm.id (A := A)).den ρ) :
    (Tm.lam (.comp R S)).den ρ = (Tm.comp (.lam R) (.lam (.comp .mem S))).den ρ :=
  (lamDen_absorb (R.den ρ) (S.den ρ) (Tm.entire_of_dom h)).symm

end Rel.Lang
