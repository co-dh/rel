import Rel.Lang.Laws.Map

/-! # Laws of freyd §6.1 `AOP/A6_1_RelSet.lean`, on the concrete core

`(𝟙×Q) π₂ = π₂ Q`: an identity first component slides any `Q` past the second projection. Stated for every relation `Q`
(the book's use at `h := π₂` needs nothing of `Q`). -/

namespace Rel.Lang
open Tab Rel.Rep
open scoped Rel.Core.Rel
open Rel.Core.Rel hiding id comp recip inter union zero le inl inr junc

theorem Tm.rprodIdSnd_den {A B C : Obj} {Q : Tm B C} (ρ : Val) :
    ((Tm.comp (Tm.pair (Tm.comp Tm.outl Tm.id) (Tm.comp Tm.outr Q)) Tm.outr : Tm (.prod A B) C).den ρ)
      = ((Tm.comp Tm.outr Q : Tm (.prod A B) C).den ρ) := by
  simp only [Tm.den]
  apply Core.Rel.ext
  intro p c
  constructor
  · rintro ⟨q, ⟨⟨u, hu, hid⟩, ⟨v, hv, hq⟩⟩, hc⟩
    subst hc
    exact ⟨v, hv, hq⟩
  · rintro ⟨v, hv, hq⟩
    exact ⟨(p.1, c), ⟨⟨p.1, rfl, rfl⟩, ⟨v, hv, hq⟩⟩, rfl⟩

end Rel.Lang
