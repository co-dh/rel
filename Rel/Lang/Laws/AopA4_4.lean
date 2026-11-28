import Rel.Lang.Laws.AopS2_10

/-! # Laws of `Freyd/A4_4.lean` (B&dM §4.4), on the concrete core: `Rel/Programs/Aop/A4_4.lean` states each as
`theorem <name> … by Rel.Lang.Tm.<name>_den`. `R ⇒ S` is the prelude's `∼R ∪ S`, a call read through `Val.args`. -/

namespace Rel.Lang
open Tab Rel.Rep
open scoped Rel.Core.Rel
open Rel.Core.Rel hiding id comp recip inter union zero le inl inr junc

/-- The prelude's `R ⇒ S` as the elaborator emits it: the call of `∼R ∪ S` (`⊤` onto the universe `𝟙`) on `𝟙, R, S`. -/
abbrev Tm.implC {A B : Obj} (c : Lean.Name) (cv : Option Lean.Name) (os : List Obj) (R S : Tm A B) : Tm A B :=
  .arg (.arg (.arg (.call [1, 2, 3] c cv os (((Tm.var 1 : Tm B B).top.diff (Tm.var 2)).join (Tm.var 3))) (Tm.id : Tm B B)) R) S

theorem Tm.implC_den {A B : Obj} (c : Lean.Name) (cv : Option Lean.Name) (os : List Obj) (R S : Tm A B) (ρ : Val)
    (a : Obj.El A) (b : Obj.El B) : (Tm.implC c cv os R S).den ρ a b ↔ (¬ R.den ρ a b ∨ S.den ρ a b) := by
  simp [Tm.den, Tm.argDen, Val.args, Val.bind, Core.Rel.diff_apply, Core.Rel.union_apply, Core.Rel.comp_apply,
    Core.Rel.top, Core.Rel.id]

/-- `X / S` with the universe `𝟙`: `x (X/S) y` iff every image of `y` under `S` is an image of `x` under `X`. -/
theorem rdivDen_one_iff {A B C : Obj} (TR : Core.Rel (Obj.El A) (Obj.El C)) (TS : Core.Rel (Obj.El B) (Obj.El C))
    (x : Obj.El A) (y : Obj.El B) : rdivDen TR TS (𝟙 _) (𝟙 _) x y ↔ ∀ c, TS y c → TR x c :=
  (rdivDen_iff).trans ⟨fun h => h.1, fun h => ⟨h, Or.inr ⟨⟨x, rfl⟩, ⟨y, rfl⟩⟩⟩⟩

theorem Tm.impl_inter_den {A B : Obj} {R S T : Tm A B} {c : Lean.Name} {cv : Option Lean.Name} {os : List Obj}
    (ρ : Val) :
    (Tm.implC c cv os R (Tm.meet S T)).den ρ =
      (Tm.meet (Tm.implC c cv os R S) (Tm.implC c cv os R T)).den ρ :=
  Core.Rel.ext fun a b => (Tm.implC_den c cv os R _ ρ a b).trans <|
    Iff.trans (show (¬ R.den ρ a b ∨ (S.den ρ a b ∧ T.den ρ a b)) ↔ _ from or_and_left)
      (and_congr (Tm.implC_den c cv os R S ρ a b).symm (Tm.implC_den c cv os R T ρ a b).symm)

theorem Tm.impl_curry_den {A B : Obj} {R S T : Tm A B} {c₁ c₂ c₃ : Lean.Name} {cv₁ cv₂ cv₃ : Option Lean.Name}
    {os₁ os₂ os₃ : List Obj} (ρ : Val) :
    (Tm.implC c₁ cv₁ os₁ R (Tm.implC c₂ cv₂ os₂ S T)).den ρ = (Tm.implC c₃ cv₃ os₃ (Tm.meet R S) T).den ρ :=
  Core.Rel.ext fun a b => (Tm.implC_den c₁ cv₁ os₁ R _ ρ a b).trans <|
    (or_congr_right (Tm.implC_den c₂ cv₂ os₂ S T ρ a b)).trans <|
      Iff.trans (show (¬ R.den ρ a b ∨ (¬ S.den ρ a b ∨ T.den ρ a b)) ↔ (¬ (R.den ρ a b ∧ S.den ρ a b) ∨ T.den ρ a b) by
        by_cases hr : R.den ρ a b <;> by_cases hs : S.den ρ a b <;> simp [hr, hs])
        (Tm.implC_den c₃ cv₃ os₃ (Tm.meet R S) T ρ a b).symm

theorem Tm.map_comp_div_den {A B C D : Obj} {f : Tm D A} {R : Tm A C} {S : Tm B C} (ρ : Val)
    (hf : (Tm.dom f).den ρ = (Tm.id (A := D)).den ρ) (hs : (Tm.comp f.conv f).den ρ ⊑ (Tm.id (A := A)).den ρ) :
    (Tm.comp f (Tm.rdiv R S Tm.id Tm.id)).den ρ = (Tm.rdiv (Tm.comp f R) S Tm.id Tm.id).den ρ := by
  have ef := Tm.entire_of_dom hf
  have sf := fun_of_simple hs
  simp only [Tm.den]
  refine Core.Rel.ext fun d b => ⟨fun ⟨a, hfa, h⟩ => (rdivDen_one_iff _ _ d b).2 fun c hc =>
      ⟨a, hfa, (rdivDen_one_iff _ _ a b).1 h c hc⟩, fun h => ?_⟩
  obtain ⟨a, hfa⟩ := ef d
  refine ⟨a, hfa, (rdivDen_one_iff _ _ a b).2 fun c hc => ?_⟩
  obtain ⟨a', hfa', hr⟩ := (rdivDen_one_iff _ _ d b).1 h c hc
  exact (sf d a' a hfa' hfa) ▸ hr

theorem Tm.div_comp_recip_map_den {A B C D : Obj} {f : Tm D B} {R : Tm A C} {S : Tm B C} (ρ : Val)
    (hf : (Tm.dom f).den ρ = (Tm.id (A := D)).den ρ) (hs : (Tm.comp f.conv f).den ρ ⊑ (Tm.id (A := B)).den ρ) :
    (Tm.rdiv R (Tm.comp f S) Tm.id Tm.id).den ρ = (Tm.comp (Tm.rdiv R S Tm.id Tm.id) f.conv).den ρ := by
  have ef := Tm.entire_of_dom hf
  have sf := fun_of_simple hs
  simp only [Tm.den]
  refine Core.Rel.ext fun a d => ⟨fun h => ?_, fun ⟨b, hdiv, hfb⟩ => ?_⟩
  · obtain ⟨b, hfb⟩ := ef d
    exact ⟨b, (rdivDen_one_iff _ _ a b).2 fun c hc => (rdivDen_one_iff _ _ a d).1 h c ⟨b, hfb, hc⟩, hfb⟩
  · exact (rdivDen_one_iff _ _ a d).2 fun c ⟨b', hfb', hs'⟩ =>
      (rdivDen_one_iff _ _ a b).1 hdiv c ((sf d b' b hfb' hfb) ▸ hs')

end Rel.Lang
