import Rel.Lang.Laws.Map

/-! # Laws of freyd §8.4 `AOP/A8_4_Knapsack.lean`, on the concrete core

The two arms `[nil,π₂]` of the knapsack step algebra (`knap_mono_drop`, `knap_sort_drop`) drop the head item, so
`(Q×𝟙) π₂ ⊑ π₂ Q` holds for every relation `Q`; the knapsack's `Q` and `R` are two instances. On snoc lists the
dropping arm is `π₁`, so the law is stated as `⟨π₁Q,π₂⟩π₁ ⊑ π₁Q`. -/

namespace Rel.Lang
open Tab Rel.Rep
open scoped Rel.Core.Rel
open Rel.Core.Rel hiding id comp recip inter union zero le inl inr junc

theorem Tm.knapMonoDrop_den {A B C : Obj} {Q : Tm A B} (ρ : Val) :
    ((Tm.comp (Tm.pair (Tm.comp Tm.outl Q) Tm.outr) Tm.outl : Tm (.prod A C) B).den ρ).le
      ((Tm.comp Tm.outl Q : Tm (.prod A C) B).den ρ) := by
  simp only [Tm.den]
  rw [Core.Rel.le_iff]
  rintro a b ⟨p, ⟨⟨u, hu, hq⟩, -⟩, hb⟩
  subst hb
  exact ⟨u, hu, hq⟩

end Rel.Lang
