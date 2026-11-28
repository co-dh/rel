import Rel.Lang.Laws.Map

/-! # Laws of freyd §6.5 `AOP/A6_5.lean` that name no relator, on the concrete core

`Rel.Lang.Tm.<name>_den` is the law of the freyd declaration `<name>` read off `Tm.den`; `Rel/Programs/Aop/A6_5.lean`
states it as `theorem <name> … by Rel.Lang.Tm.<name>_den`. -/

namespace Rel.Lang
open Tab Rel.Rep
open scoped Rel.Core.Rel
open Rel.Core.Rel hiding id comp recip inter union zero le inl inr junc

/-- `((X/R)/S) R R ⊑ X` when `R R ⊑ S R`: `(X/R)/S` at `a b` sends every `S`-image `e` of `b` to an `X/R` image of `a`,
    and `R b c, R c d` factors as `S b e, R e d`. The universes of the divisions only restrict them. -/
theorem Tm.div_div_comp_le_den {A B : Obj} {X : Tm B A} {R S : Tm A A} {UB UB' : Tm B B} {UA UA' : Tm A A} (ρ : Val)
    (h : (Tm.comp R R).den ρ ⊑ (Tm.comp S R).den ρ) :
    (Tm.comp (Tm.comp (Tm.rdiv (Tm.rdiv X R UB UA) S UB' UA') R) R).den ρ ⊑ X.den ρ := by
  simp only [Tm.den] at h ⊢
  refine Core.Rel.le_iff.2 fun a d ⟨c, ⟨b, hb, hbc⟩, hcd⟩ => ?_
  obtain ⟨e, hse, hed⟩ := Core.Rel.le_iff.1 h b d ⟨c, hbc, hcd⟩
  exact ((rdivDen_iff.1 ((rdivDen_iff.1 hb).1 e hse)).1 d hed)

end Rel.Lang
