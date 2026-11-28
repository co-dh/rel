import Rel.Lang.Laws.AopS2_10

/-! # Laws of `Freyd/A4_2.lean` (B&dM §4.2), on the concrete core: `Rel/Programs/Aop/A4_2.lean` states each as
`theorem <name> … by Rel.Lang.Tm.<name>_den`. -/

namespace Rel.Lang
open Tab Rel.Rep
open scoped Rel.Core.Rel
open Rel.Core.Rel hiding id comp recip inter union zero le inl inr junc

theorem Tm.recip_of_comp_id_den {A B : Obj} {R : Tm A B} {S : Tm B A} (ρ : Val)
    (h1 : (Tm.id (A := A)).den ρ ⊑ (Tm.comp R S).den ρ) (h2 : (Tm.comp S R).den ρ ⊑ (Tm.id (A := B)).den ρ) :
    S.den ρ = (Tm.conv R).den ρ := by
  simp only [Tm.den] at h1 h2 ⊢
  refine Core.Rel.ext fun b a => ⟨fun hs => ?_, fun hr => ?_⟩
  · obtain ⟨b', hr, hs'⟩ := Core.Rel.le_iff.1 h1 a a rfl
    have e : b = b' := Core.Rel.le_iff.1 h2 b b' ⟨a, hs, hr⟩
    subst e; exact hr
  · obtain ⟨b', hr', hs'⟩ := Core.Rel.le_iff.1 h1 a a rfl
    have e : b' = b := Core.Rel.le_iff.1 h2 b' b ⟨a, hs', hr⟩
    subst e; exact hs'

/-- The entire half of `Map R` in `recip_of_comp_id`. -/
theorem Tm.entire_of_comp_id_den {A B : Obj} {R : Tm A B} {S : Tm B A} (ρ : Val)
    (h1 : (Tm.id (A := A)).den ρ ⊑ (Tm.comp R S).den ρ) : (Tm.dom R).den ρ = (Tm.id (A := A)).den ρ := by
  simp only [Tm.den] at h1
  rw [Tm.dom_den]
  exact dom_of_entire fun a => let ⟨b, hb, _⟩ := Core.Rel.le_iff.1 h1 a a rfl; ⟨b, hb⟩

/-- The simple half of `Map R` in `recip_of_comp_id`: `S = R°` turns `S R ⊑ 𝟙` into `R° R ⊑ 𝟙`. -/
theorem Tm.simple_of_comp_id_den {A B : Obj} {R : Tm A B} {S : Tm B A} (ρ : Val)
    (h1 : (Tm.id (A := A)).den ρ ⊑ (Tm.comp R S).den ρ) (h2 : (Tm.comp S R).den ρ ⊑ (Tm.id (A := B)).den ρ) :
    (Tm.comp R.conv R).den ρ ⊑ (Tm.id (A := B)).den ρ := by
  have e := Tm.recip_of_comp_id_den ρ h1 h2
  simp only [Tm.den] at h2 ⊢
  simp only [Tm.den] at e
  rw [e] at h2; exact h2

theorem Tm.simple_dist_inter_recip_den {A B C : Obj} {g : Tm C B} {X Y : Tm A B} (ρ : Val)
    (hg : (Tm.comp g.conv g).den ρ ⊑ (Tm.id (A := B)).den ρ) :
    (Tm.comp (Tm.meet X Y) g.conv).den ρ = (Tm.meet (Tm.comp X g.conv) (Tm.comp Y g.conv)).den ρ := by
  have sg := fun_of_simple hg
  simp only [Tm.den]
  exact Core.Rel.ext fun a c => ⟨fun ⟨b, ⟨hx, hy⟩, hc⟩ => ⟨⟨b, hx, hc⟩, ⟨b, hy, hc⟩⟩,
    fun ⟨⟨b, hx, hc⟩, ⟨b', hy, hc'⟩⟩ => ⟨b, ⟨hx, sg c b' b hc' hc ▸ hy⟩, hc⟩⟩

end Rel.Lang
