import Rel.Lang.Laws.Map

/-! # Laws of freyd §9.3 `AOP/A9_3_Bracket.lean`, on the concrete core

`[R,S]` elaborates to `inl°R ∪ inr°S` (`Pre.junc`), so the β-law of a junction at `inl` is a law of that
composite, whatever the arms `R`, `S` are. -/

namespace Rel.Lang
open Tab Rel.Rep
open scoped Rel.Core.Rel
open Rel.Core.Rel hiding id comp recip inter union zero le inl inr junc

theorem Tm.gFnInl_den {A B C : Obj} {R : Tm A C} {S : Tm B C} (ρ : Val) :
    (Tm.comp Tm.inl (Tm.join (Tm.comp (Tm.conv Tm.inl) R) (Tm.comp (Tm.conv Tm.inr) S) :
      Tm (.sum A B) C)).den ρ = R.den ρ := by
  simp only [Tm.den]
  refine Core.Rel.ext fun a c => ⟨?_, fun h => ?_⟩
  · rintro ⟨x, hx, ⟨y, hy, h⟩ | ⟨y, hy, h⟩⟩
    · have hy' : Sum.inl a = (Sum.inl y : _ ⊕ _) := hx.symm.trans hy
      obtain rfl := Sum.inl.inj hy'
      exact h
    · exact absurd (hx.symm.trans hy) (by simp)
  · exact ⟨Sum.inl a, rfl, Or.inl ⟨a, rfl, h⟩⟩

end Rel.Lang
