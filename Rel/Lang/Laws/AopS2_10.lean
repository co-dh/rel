import Rel.Lang.Laws.Map

/-! # Allegory laws of freyd §2.10 `Freyd/S2_10.lean`, on the concrete core

Each `Rel.Lang.Tm.<name>_den` is the law of the freyd declaration `<name>` read off `Tm.den`, so that
`Rel/Programs/Aop/S2_10.lean` states it as `theorem <name> … by Rel.Lang.Tm.<name>_den`. A premise `Entire R` is
`dom(R) = 𝟙`, `Simple f` is `f°f ⊑ 𝟙` (the Prelude's `simple`), as `Tm.entire_of_dom` and `simple_of_fun` read them. -/

namespace Rel.Lang
open Tab Rel.Rep
open scoped Rel.Core.Rel
open Rel.Core.Rel hiding id comp recip inter union zero le inl inr junc

/-- `f° f ⊑ 𝟙` read as: at most one image. -/
theorem fun_of_simple {α β : Type} {T : Core.Rel α β} (h : T° ≫ T ⊑ 𝟙 β) : ∀ a b b', T a b → T a b' → b = b' :=
  fun a b b' h₁ h₂ => Core.Rel.le_iff.1 h b b' ⟨a, h₁, h₂⟩

/-- `dom(R) = 𝟙` read as: an image at every point (`Tm.entire_of_dom` without the term). -/
theorem entire_of_dom_eq {α β : Type} {R : Core.Rel α β} (h : 𝟙 α ∩ R ≫ R° = 𝟙 α) : ∀ a, ∃ b, R a b := fun a =>
  let ⟨b, hab, _⟩ := (h.symm ▸ (rfl : (𝟙 α) a a) : (𝟙 α ∩ R ≫ R°) a a).2
  ⟨b, hab⟩

theorem Tm.recip_inter_den {A B : Obj} {R S : Tm A B} (ρ : Val) :
    (Tm.conv (Tm.meet R S)).den ρ = (Tm.meet (Tm.conv R) (Tm.conv S)).den ρ := rfl

theorem Tm.recip_mono_den {A B : Obj} {R S : Tm A B} (ρ : Val) (h : R.den ρ ⊑ S.den ρ) :
    (Tm.conv R).den ρ ⊑ (Tm.conv S).den ρ :=
  Core.Rel.le_iff.2 fun b a hr => Core.Rel.le_iff.1 h a b hr

theorem Tm.dom_inter_den {A B : Obj} {R S : Tm A B} (ρ : Val) :
    (Tm.dom (Tm.meet R S)).den ρ = (Tm.meet Tm.id (Tm.comp S (Tm.conv R))).den ρ := by
  simp only [Tm.dom_den, Tm.den]
  refine Core.Rel.ext fun a b => ⟨fun ⟨e, c, ⟨h₁, h₂⟩, _⟩ => ⟨e, c, h₂, e ▸ h₁⟩, fun ⟨e, c, h₂, h₁⟩ => ⟨e, c, ⟨e ▸ h₁, h₂⟩, ⟨h₁, e ▸ h₂⟩⟩⟩

theorem Tm.dom_comp_le_den {A B C : Obj} {R : Tm A B} {S : Tm B C} (ρ : Val) :
    (Tm.dom (Tm.comp R S)).den ρ ⊑ (Tm.dom R).den ρ := by
  simp only [Tm.dom_den, Tm.den]
  exact Core.Rel.le_iff.2 fun a b ⟨e, c, ⟨d, hr, _⟩, hb⟩ => ⟨e, d, hr, e ▸ hr⟩

theorem Tm.entire_comp_den {A B C : Obj} {R : Tm A B} {S : Tm B C} (ρ : Val)
    (hR : (Tm.dom R).den ρ = (Tm.id (A := A)).den ρ) (hS : (Tm.dom S).den ρ = (Tm.id (A := B)).den ρ) :
    (Tm.dom (Tm.comp R S)).den ρ = (Tm.id (A := A)).den ρ := by
  have eR := Tm.entire_of_dom hR
  have eS := Tm.entire_of_dom hS
  rw [Tm.dom_den, Tm.den]
  exact dom_of_entire fun a => let ⟨b, hb⟩ := eR a; let ⟨c, hc⟩ := eS b; ⟨c, b, hb, hc⟩

theorem Tm.entire_of_comp_entire_den {A B C : Obj} {R : Tm A B} {S : Tm B C} (ρ : Val)
    (h : (Tm.dom (Tm.comp R S)).den ρ = (Tm.id (A := A)).den ρ) :
    (Tm.dom R).den ρ = (Tm.id (A := A)).den ρ := by
  have e := Tm.entire_of_dom h
  rw [Tm.dom_den]
  exact dom_of_entire fun a => let ⟨_, b, hb, _⟩ := e a; ⟨b, hb⟩

theorem Tm.simple_comp_den {A B C : Obj} {f : Tm A B} {g : Tm B C} (ρ : Val)
    (hf : (Tm.comp f.conv f).den ρ ⊑ (Tm.id (A := B)).den ρ) (hg : (Tm.comp g.conv g).den ρ ⊑ (Tm.id (A := C)).den ρ) :
    (Tm.comp (Tm.comp f g).conv (Tm.comp f g)).den ρ ⊑ (Tm.id (A := C)).den ρ := by
  have sf := fun_of_simple hf
  have sg := fun_of_simple hg
  simp only [Tm.den] at hf hg ⊢
  refine simple_of_fun fun a c c' ⟨b, hb, hc⟩ ⟨b', hb', hc'⟩ => ?_
  obtain rfl := sf a b b' hb hb'
  exact sg b c c' hc hc'

theorem Tm.map_entire_le_den {A B : Obj} {f : Tm A B} (ρ : Val) (h : (Tm.dom f).den ρ = (Tm.id (A := A)).den ρ) :
    (Tm.id (A := A)).den ρ ⊑ (Tm.comp f f.conv).den ρ :=
  Core.Rel.le_iff.2 fun a b (e : a = b) => let ⟨c, hc⟩ := Tm.entire_of_dom h a; ⟨c, hc, e ▸ hc⟩

theorem Tm.eq_of_le_entire_simple_den {A B : Obj} {X Y : Tm A B} (ρ : Val)
    (hX : (Tm.dom X).den ρ = (Tm.id (A := A)).den ρ) (hY : (Tm.comp Y.conv Y).den ρ ⊑ (Tm.id (A := B)).den ρ)
    (h : X.den ρ ⊑ Y.den ρ) : X.den ρ = Y.den ρ :=
  Core.Rel.ext fun a b => ⟨Core.Rel.le_iff.1 h a b, fun hy =>
    let ⟨c, hc⟩ := Tm.entire_of_dom hX a
    (fun_of_simple hY a c b (Core.Rel.le_iff.1 h a c hc) hy) ▸ hc⟩

end Rel.Lang
