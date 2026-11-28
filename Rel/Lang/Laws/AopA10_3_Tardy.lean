import Rel.Lang.Laws.Map

/-! # Laws of freyd §10.3 `AOP/A10_3_Tardy.lean` that name no relator, on the concrete core

`Rel.Lang.Tm.<name>_den` is the law of the freyd declaration `<name>` read off `Tm.den`; `Rel/Programs/Aop/A10_3_Tardy.lean`
states it as `theorem <name> … by Rel.Lang.Tm.<name>_den`. -/

namespace Rel.Lang
open Tab Rel.Rep
open scoped Rel.Core.Rel
open Rel.Core.Rel hiding id comp recip inter union zero le inl inr junc

/-- A step `Y` after a refinement `P ⊑ H` keeps it: `P Y ⊑ H Y`. `pick_branch_le` is this at `P = pick`,
    `H = Λ(arm₂ β°) est(Q')` and `Y = (X×𝟙) arm₂ α`. -/
theorem Tm.pickBranchLe_den {A B C : Obj} {P H : Tm A B} {Y : Tm B C} (ρ : Val) (h : P.den ρ ⊑ H.den ρ) :
    (Tm.comp P Y).den ρ ⊑ (Tm.comp H Y).den ρ :=
  Core.Rel.le_iff.2 fun a c ⟨b, hb, hy⟩ => ⟨b, Core.Rel.le_iff.1 h a b hb, hy⟩

/-- `inl [Z,P] = Z`: the first arm of a junction. -/
theorem Tm.gInl_den {A B C : Obj} {Z : Tm A C} {P : Tm B C} (ρ : Val) :
    (Tm.comp Tm.inl (Tm.join (Tm.comp Tm.inl.conv Z) (Tm.comp Tm.inr.conv P))).den ρ = Z.den ρ := by
  simp only [Tm.den]
  refine Core.Rel.ext fun a c => ?_
  constructor
  · rintro ⟨s, (hs : s = Sum.inl a), h | h⟩
    · obtain ⟨x, (hx : s = Sum.inl x), hz⟩ := h
      obtain rfl := Sum.inl.inj (hs.symm.trans hx)
      exact hz
    · obtain ⟨y, (hy : s = Sum.inr y), _⟩ := h
      exact absurd (hs.symm.trans hy) Sum.inl_ne_inr
  · intro hz
    exact ⟨Sum.inl a, rfl, Or.inl ⟨a, rfl, hz⟩⟩

end Rel.Lang
