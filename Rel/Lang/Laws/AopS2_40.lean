import Rel.Lang.Laws.AopS2_10
import Rel.Lang.Laws.Eunion

/-! # Power-allegory laws of freyd §2.4 `Freyd/S2_40.lean`, on the concrete core

The power object `[β]` is the lists of `β` and `Λ(R)` (`lamDen`) the strictly ascending list of the images of `R`, so the
laws that freyd states for every `R` (`UnguardedPowerAllegory`) hold here where `Λ(R)` has an array at the point: that is the
premise `dom(Λ(R)) = 𝟙`, as in `absorption`. `Rel/Programs/Aop/S2_40.lean` states each `Rel.Lang.Tm.<name>_den` as
`theorem <name> … by Rel.Lang.Tm.<name>_den`. -/

namespace Rel.Lang
open Tab Rel.Rep
open scoped Rel.Core.Rel
open Rel.Core.Rel hiding id comp recip inter union zero le inl inr junc

/-- `Λ(R)` is simple (the simple half of `Λ_is_map'`): one array per point. -/
theorem Tm.lam_simple_den {A B : Obj} {R : Tm A B} (ρ : Val) :
    (Tm.comp (Tm.comp Tm.id (Tm.lam R)).conv (Tm.lam R)).den ρ ⊑ (Tm.id (A := Obj.arr B)).den ρ :=
  Core.Rel.le_iff.2 fun _ _ ⟨_, ⟨_, e, h₁⟩, h₂⟩ => lamDen_unique _ (e ▸ h₁) h₂

/-- `Λ(R)∋ = R` where `Λ(R)` has an array at every point (`Λ_eps_eq'`). -/
theorem Tm.lam_eps_eq_den {A B : Obj} {R : Tm A B} (ρ : Val)
    (h : (Tm.dom (Tm.lam R)).den ρ = (Tm.id (A := A)).den ρ) :
    (Tm.comp (Tm.lam R) Tm.mem).den ρ = R.den ρ :=
  Core.Rel.ext fun a b => ⟨fun ⟨ys, hy, hb⟩ => ((lamDen_iff _ a ys).1 hy).2 b |>.1 hb,
    fun hr => let ⟨ys, hy⟩ := Tm.entire_of_dom h a; ⟨ys, hy, ((lamDen_iff _ a ys).1 hy).2 b |>.2 hr⟩⟩
/-- `Λ(1)Λ(1)° ⊑ 𝟙` (`singletonMap_monic`); the converse of `Λ(1)` carries the `𝟙` the elaborator writes, as in `lam_simple_den`. -/
theorem Tm.lam_id_monic_den {A : Obj} (ρ : Val) :
    (Tm.comp (Tm.lam (Tm.id (A := A))) (Tm.comp Tm.id (Tm.lam (Tm.id (A := A)))).conv).den ρ ⊑ (Tm.id (A := A)).den ρ :=
  Core.Rel.le_iff.2 fun a _ ⟨ys, h₁, _, e, h₂⟩ => by obtain rfl := e; exact
    ((((lamDen_iff _ _ _).1 h₂).2 a).1 ((((lamDen_iff _ _ _).1 h₁).2 a).2 rfl)).symm

/-- `Λ(f) = f Λ(1)` for a map `f` (`Λ_of_map`). -/
theorem Tm.lam_of_map_den {A B : Obj} {f : Tm A B} (ρ : Val)
    (hE : (Tm.dom f).den ρ = (Tm.id (A := A)).den ρ) (hS : (Tm.comp f.conv f).den ρ ⊑ (Tm.id (A := B)).den ρ) :
    (Tm.lam f).den ρ = (Tm.comp f (Tm.lam (Tm.id (A := B)))).den ρ :=
  Core.Rel.ext fun a ys => by
    obtain ⟨b, hb⟩ := Tm.entire_of_dom hE a
    have one : ∀ c, f.den ρ a c → c = b := fun c hc => fun_of_simple hS a c b hc hb
    change lamDen (f.den ρ) a ys ↔ ∃ b', f.den ρ a b' ∧ lamDen (𝟙 B.El) b' ys
    refine ⟨fun hl => let ⟨hp, h⟩ := (lamDen_iff _ _ _).1 hl
        ⟨b, hb, (lamDen_iff _ _ _).2 ⟨hp, fun c => (h c).trans ⟨fun hc => (one c hc).symm, fun e => e ▸ hb⟩⟩⟩,
      fun ⟨b', hb', hl⟩ => ?_⟩
    obtain ⟨hp, h⟩ := (lamDen_iff _ _ _).1 hl
    obtain rfl := one b' hb'
    exact (lamDen_iff _ _ _).2 ⟨hp, fun c => (h c).trans ⟨fun e => e ▸ hb', fun hc => (one c hc).symm⟩⟩

end Rel.Lang
