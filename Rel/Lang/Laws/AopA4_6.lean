import Rel.Lang.Laws.AopS2_10
import Rel.Lang.Laws.Eunion

/-! # Laws of `Freyd/A4_6.lean` (B&dM §4.6, the power transpose), on the concrete core: `Rel/Programs/Aop/A4_6.lean`
states each as `theorem <name> … by Rel.Lang.Tm.<name>_den`. `Λ(R)` has an array at `a` only where `R a` is finite, so
`Λ(R) ∋ = R` carries the premise `dom(Λ(R)) = 𝟙` that freyd's power allegory has for free. -/

namespace Rel.Lang
open Tab Rel.Rep
open scoped Rel.Core.Rel
open Rel.Core.Rel hiding id comp recip inter union zero le inl inr junc

theorem Tm.lam_comp_mem_den {A B : Obj} {R : Tm A B} (ρ : Val)
    (h : (Tm.dom (Tm.lam R)).den ρ = (Tm.id (A := A)).den ρ) : (Tm.comp (Tm.lam R) Tm.mem).den ρ = R.den ρ := by
  have e := Tm.entire_of_dom h
  simp only [Tm.den]
  exact Core.Rel.ext fun a b => ⟨fun ⟨ys, hy, hb⟩ => (((lamDen_iff _ a ys).1 hy).2 b).1 hb, fun hr =>
    let ⟨ys, hys⟩ := e a
    ⟨ys, hys, (((lamDen_iff _ a ys).1 hys).2 b).2 hr⟩⟩

theorem Tm.lam_fusion_den {A B D : Obj} {f : Tm D A} {R : Tm A B} (ρ : Val)
    (hf : (Tm.dom f).den ρ = (Tm.id (A := D)).den ρ) (hs : (Tm.comp f.conv f).den ρ ⊑ (Tm.id (A := A)).den ρ) :
    (Tm.lam (Tm.comp f R)).den ρ = (Tm.comp f (Tm.lam R)).den ρ := by
  have ef := Tm.entire_of_dom hf
  have sf := fun_of_simple hs
  simp only [Tm.den]
  have key : ∀ a c, f.den ρ a c → ∀ b, (f.den ρ ≫ R.den ρ) a b ↔ R.den ρ c b := fun a c hc b =>
    ⟨fun ⟨c', hc', hr⟩ => (sf a c' c hc' hc) ▸ hr, fun hr => ⟨c, hc, hr⟩⟩
  refine Core.Rel.ext fun a ys => ⟨fun h => ?_, fun ⟨c, hc, hl⟩ => ?_⟩
  · obtain ⟨c, hc⟩ := ef a
    obtain ⟨hp, hm⟩ := (lamDen_iff _ a ys).1 h
    exact ⟨c, hc, (lamDen_iff _ c ys).2 ⟨hp, fun b => (hm b).trans (key a c hc b)⟩⟩
  · obtain ⟨hp, hm⟩ := (lamDen_iff _ c ys).1 hl
    exact (lamDen_iff _ a ys).2 ⟨hp, fun b => (hm b).trans (key a c hc b).symm⟩

/-- `f Λ(𝟙) = Λ(f)`: the elaborator fuses `Λ(𝟙) E(f)` to `Λ(f)`. -/
theorem Tm.singleton_natural_den {A B : Obj} {f : Tm A B} (ρ : Val)
    (hf : (Tm.dom f).den ρ = (Tm.id (A := A)).den ρ) (hs : (Tm.comp f.conv f).den ρ ⊑ (Tm.id (A := B)).den ρ) :
    (Tm.comp f (Tm.lam Tm.id)).den ρ = (Tm.lam f).den ρ := by
  have := Tm.lam_fusion_den (R := Tm.id) ρ hf hs
  simp only [Tm.den, Core.Rel.comp_id] at this ⊢
  exact this.symm

end Rel.Lang
