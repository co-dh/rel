import Rel.Lang.Laws.Map

/-! # Division laws of freyd §2.30 `Freyd/S2_30.lean`, on the concrete core

A program states `R/S`, `R\S` with `𝟙` for both universes (`Tm.ldiv R S id id`), where the bounded division
`ldivDen`/`rdivDen` is the plain `Core.Rel.ldiv`/`rdiv` (`ldivDen_id`, `rdivDen_id`). Each `Tm.<name>_den` is the law of
the freyd declaration `<name>` read off `Tm.den`, so that `Rel/Programs/Aop/S2_30.lean` states it as
`theorem <name> … by Rel.Lang.Tm.<name>_den`. -/

namespace Rel.Lang
open Tab Rel.Rep
open scoped Rel.Core.Rel
open Rel.Core.Rel hiding id comp recip inter union zero le inl inr junc

/-- Within the identity universes `ldivDen` is the book's left division. -/
theorem ldivDen_id {A B C : Obj} {R : Core.Rel (Obj.El A) (Obj.El B)} {S : Core.Rel (Obj.El A) (Obj.El C)} :
    ldivDen R S (𝟙 (Obj.El B)) (𝟙 (Obj.El C)) = ldiv R S :=
  Core.Rel.ext fun b c => ldivDen_iff.trans ⟨fun h => h.1, fun h => ⟨h, Or.inr ⟨⟨b, rfl⟩, c, rfl⟩⟩⟩

/-- Within the identity universes `rdivDen` is the book's right division. -/
theorem rdivDen_id {A B C : Obj} {R : Core.Rel (Obj.El A) (Obj.El C)} {S : Core.Rel (Obj.El B) (Obj.El C)} :
    rdivDen R S (𝟙 (Obj.El A)) (𝟙 (Obj.El B)) = rdiv R S :=
  Core.Rel.ext fun a b => rdivDen_iff.trans ⟨fun h => h.1, fun h => ⟨h, Or.inr ⟨⟨a, rfl⟩, b, rfl⟩⟩⟩

theorem Tm.div_comp_le_den {A B C : Obj} {R : Tm A C} {S : Tm B C} (ρ : Val) :
    (Tm.comp (Tm.rdiv R S Tm.id Tm.id) S).den ρ ⊑ R.den ρ := by
  simp only [Tm.den, rdivDen_id]
  exact Core.Rel.le_iff.2 fun a c ⟨b, h₁, h₂⟩ => h₁ c h₂

theorem Tm.div_comp_den {A B C D : Obj} {X : Tm A D} {S : Tm B D} {W : Tm C D} (ρ : Val) :
    (Tm.comp (Tm.rdiv X S Tm.id Tm.id) (Tm.rdiv S W Tm.id Tm.id)).den ρ ⊑ (Tm.rdiv X W Tm.id Tm.id).den ρ := by
  simp only [Tm.den, rdivDen_id]
  exact Core.Rel.le_iff.2 fun a c ⟨b, h₁, h₂⟩ d hd => h₁ d (h₂ d hd)

theorem Tm.div_comp_assoc_den {A B C D : Obj} {X : Tm A D} {S₁ : Tm B C} {S₂ : Tm C D} (ρ : Val) :
    (Tm.rdiv X (Tm.comp S₁ S₂) Tm.id Tm.id).den ρ = (Tm.rdiv (Tm.rdiv X S₂ Tm.id Tm.id) S₁ Tm.id Tm.id).den ρ := by
  simp only [Tm.den, rdivDen_id]
  exact Core.Rel.ext fun a b => ⟨fun h c hc d hd => h d ⟨c, hc, hd⟩, fun h d ⟨c, hc, hd⟩ => h c hc d hd⟩

theorem Tm.div_inter_eq_den {A B C : Obj} {R R' : Tm A C} {S : Tm B C} (ρ : Val) :
    (Tm.rdiv (Tm.meet R R') S Tm.id Tm.id).den ρ = (Tm.meet (Tm.rdiv R S Tm.id Tm.id) (Tm.rdiv R' S Tm.id Tm.id)).den ρ := by
  simp only [Tm.den, rdivDen_id]
  exact Core.Rel.ext fun a b => ⟨fun h => ⟨fun c hc => (h c hc).1, fun c hc => (h c hc).2⟩, fun h c hc => ⟨h.1 c hc, h.2 c hc⟩⟩

theorem Tm.div_self_comp_den {A B : Obj} {X : Tm A B} (ρ : Val) :
    (Tm.comp (Tm.rdiv X X Tm.id Tm.id) X).den ρ = X.den ρ := by
  simp only [Tm.den, rdivDen_id]
  exact Core.Rel.ext fun a c => ⟨fun ⟨b, h₁, h₂⟩ => h₁ c h₂, fun h => ⟨a, fun _ hc => hc, h⟩⟩

theorem Tm.div_self_comp_self_den {A B : Obj} {X : Tm A B} (ρ : Val) :
    (Tm.comp (Tm.rdiv X X Tm.id Tm.id) (Tm.rdiv X X Tm.id Tm.id)).den ρ = (Tm.rdiv X X Tm.id Tm.id).den ρ := by
  simp only [Tm.den, rdivDen_id]
  exact Core.Rel.ext fun a c => ⟨fun ⟨b, h₁, h₂⟩ d hd => h₁ d (h₂ d hd), fun h => ⟨a, fun _ hc => hc, h⟩⟩

theorem Tm.div_union_den {A B C : Obj} {X : Tm A C} {S₁ S₂ : Tm B C} (ρ : Val) :
    (Tm.rdiv X (Tm.join S₁ S₂) Tm.id Tm.id).den ρ = (Tm.meet (Tm.rdiv X S₁ Tm.id Tm.id) (Tm.rdiv X S₂ Tm.id Tm.id)).den ρ := by
  simp only [Tm.den, rdivDen_id]
  exact Core.Rel.ext fun a b => ⟨fun h => ⟨fun c hc => h c (Or.inl hc), fun c hc => h c (Or.inr hc)⟩,
    fun h c hc => hc.elim (h.1 c) (h.2 c)⟩

theorem Tm.left_div_comp_den {A B C D : Obj} {S₁ : Tm A B} {S₂ : Tm B C} {X : Tm A D} (ρ : Val) :
    (Tm.ldiv (Tm.comp S₁ S₂) X Tm.id Tm.id).den ρ = (Tm.ldiv S₂ (Tm.ldiv S₁ X Tm.id Tm.id) Tm.id Tm.id).den ρ := by
  simp only [Tm.den, ldivDen_id]
  exact Core.Rel.ext fun c d => ⟨fun h b hb a ha => h a ⟨b, ha, hb⟩, fun h a ⟨b, ha, hb⟩ => h b hb a ha⟩

theorem Tm.left_div_comp_le_den {A B C : Obj} {S : Tm A B} {X : Tm A C} (ρ : Val) :
    (Tm.comp S (Tm.ldiv S X Tm.id Tm.id)).den ρ ⊑ X.den ρ := by
  simp only [Tm.den, ldivDen_id]
  exact Core.Rel.le_iff.2 fun a c ⟨b, h₁, h₂⟩ => h₂ a h₁

theorem Tm.left_div_div_den {A B C D : Obj} {S : Tm A B} {X : Tm A D} {W : Tm C D} (ρ : Val) :
    (Tm.ldiv S (Tm.rdiv X W Tm.id Tm.id) Tm.id Tm.id).den ρ = (Tm.rdiv (Tm.ldiv S X Tm.id Tm.id) W Tm.id Tm.id).den ρ := by
  simp only [Tm.den, ldivDen_id, rdivDen_id]
  exact Core.Rel.ext fun b c => ⟨fun h d hd a ha => h a ha d hd, fun h a ha d hd => h d hd a ha⟩

theorem Tm.left_div_inter_den {A B C : Obj} {S : Tm A B} {R R' : Tm A C} (ρ : Val) :
    (Tm.ldiv S (Tm.meet R R') Tm.id Tm.id).den ρ = (Tm.meet (Tm.ldiv S R Tm.id Tm.id) (Tm.ldiv S R' Tm.id Tm.id)).den ρ := by
  simp only [Tm.den, ldivDen_id]
  exact Core.Rel.ext fun b c => ⟨fun h => ⟨fun a ha => (h a ha).1, fun a ha => (h a ha).2⟩, fun h a ha => ⟨h.1 a ha, h.2 a ha⟩⟩

theorem Tm.one_le_div_self_den {A B : Obj} {X : Tm A B} (ρ : Val) :
    (Tm.id (A := A)).den ρ ⊑ (Tm.rdiv X X Tm.id Tm.id).den ρ := by
  simp only [Tm.den, rdivDen_id]
  exact Core.Rel.le_iff.2 fun a b (e : a = b) c hc => e ▸ hc

end Rel.Lang
