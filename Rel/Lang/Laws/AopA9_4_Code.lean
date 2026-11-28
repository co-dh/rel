import Rel.Lang.Laws.AopA5_3

/-! # Laws of freyd §9.4 `AOP/A9_4_Code.lean`, on the concrete core

`F(U,V) = 𝟙 + (V×U)` is the sum `[𝟙 inl, ⟨π₁V,π₂U⟩ inr]` of the snoc functor (`Q = F(⊤+⊤,prefix°)` and the steps of
`code_thin_condition` are written with it); its composition laws hold for any relations. -/

namespace Rel.Lang
open Tab Rel.Rep
open scoped Rel.Core.Rel
open Rel.Core.Rel hiding id comp recip inter union zero le inl inr junc

/-- `𝟙 ⊕ ⟨π₁X,π₂Y⟩`: the action `F(Y,X)` of `F(E,X) = 1+(X×E)` on a pair of relations, as the elaborator builds it. -/
abbrev Tm.snocBi {O A B E F : Obj} (X : Tm A B) (Y : Tm E F) : Tm (.sum O (.prod A E)) (.sum O (.prod B F)) :=
  (Tm.comp Tm.inl.conv (Tm.comp Tm.id Tm.inl)).join
    (Tm.comp Tm.inr.conv ((Tm.pair (Tm.comp Tm.outl X) (Tm.comp Tm.outr Y)).comp Tm.inr))

theorem Tm.snocBi_comp_den {O A B C E F : Obj} {V : Tm A B} {W : Tm B C} {U : Tm E F} (ρ : Val) :
    (Tm.comp (Tm.snocBi (O := O) V U) (Tm.snocBi W (Tm.id (A := F)))).den ρ =
      (Tm.snocBi (O := O) (Tm.comp V W) U).den ρ := by
  refine Core.Rel.ext fun x y => ?_
  cases x <;> cases y <;>
    simp [Tm.den, Core.Rel.union, Core.Rel.comp, Core.Rel.recip, Core.Rel.inl, Core.Rel.inr, Core.Rel.graph,
      Core.Rel.id, Core.Rel.rpair]
  · exact eq_comm
  · constructor
    · rintro ⟨_, ⟨a, b, ⟨h1, h2⟩, rfl⟩, a', h3, h4⟩
      obtain ⟨rfl, rfl⟩ := by simpa using h3
      exact ⟨⟨a, h1, h4⟩, h2⟩
    · rintro ⟨⟨b, h1, h2⟩, h3⟩
      exact ⟨_, ⟨b, _, ⟨h1, h3⟩, rfl⟩, b, rfl, h2⟩

theorem Tm.snocBi_comp_left_den {O A B C E F : Obj} {D : Tm A B} {R : Tm B C} {U : Tm E F} (ρ : Val) :
    (Tm.comp (Tm.snocBi (O := O) D (Tm.id (A := E))) (Tm.snocBi R U)).den ρ =
      (Tm.snocBi (O := O) (Tm.comp D R) U).den ρ := by
  refine Core.Rel.ext fun x y => ?_
  cases x <;> cases y <;>
    simp [Tm.den, Core.Rel.union, Core.Rel.comp, Core.Rel.recip, Core.Rel.inl, Core.Rel.inr, Core.Rel.graph,
      Core.Rel.id, Core.Rel.rpair]
  · exact eq_comm
  · constructor
    · rintro ⟨_, ⟨a, b, ⟨h1, rfl⟩, rfl⟩, a', b', h3, h4, h5⟩
      obtain ⟨rfl, rfl⟩ := by simpa using h3
      exact ⟨⟨a, h1, h4⟩, h5⟩
    · rintro ⟨⟨b, h1, h2⟩, h3⟩
      exact ⟨_, ⟨b, _, ⟨h1, rfl⟩, rfl⟩, b, _, rfl, h2, h3⟩

end Rel.Lang
