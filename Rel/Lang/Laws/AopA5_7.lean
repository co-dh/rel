import Rel.Lang.Laws.Map
import Rel.Lang.Laws.AopS2_10

/-! # Lax squares of freyd §5.7 `AOP/A5_7.lean`, on the concrete core

`Ta X ⊑ X' Tb` is a lax square; `Tm.comp_slides_den` pastes two along `≫`, `Tm.union_slides_den` along `∪`. -/

namespace Rel.Lang
open Tab Rel.Rep
open scoped Rel.Core.Rel
open Rel.Core.Rel hiding id comp recip inter union zero le inl inr junc

theorem Tm.comp_slides_den {A₁ A₂ B₁ B₂ C₁ C₂ : Obj} {Ta : Tm A₁ A₂} {Tb : Tm B₁ B₂} {Tc : Tm C₁ C₂}
    {X : Tm A₂ B₂} {X' : Tm A₁ B₁} {Y : Tm B₂ C₂} {Y' : Tm B₁ C₁} (ρ : Val)
    (hX : (Tm.comp Ta X).den ρ ⊑ (Tm.comp X' Tb).den ρ) (hY : (Tm.comp Tb Y).den ρ ⊑ (Tm.comp Y' Tc).den ρ) :
    (Tm.comp Ta (Tm.comp X Y)).den ρ ⊑ (Tm.comp (Tm.comp X' Y') Tc).den ρ :=
  Core.Rel.le_iff.2 fun a c ⟨b, hb, e, hx, hy⟩ =>
    let ⟨b', hx', hb'⟩ := Core.Rel.le_iff.1 hX a e ⟨b, hb, hx⟩
    let ⟨c', hy', hc'⟩ := Core.Rel.le_iff.1 hY b' c ⟨e, hb', hy⟩
    ⟨c', ⟨b', hx', hy'⟩, hc'⟩

theorem Tm.union_slides_den {A₁ A₂ B₁ B₂ : Obj} {Ta : Tm A₁ A₂} {Tb : Tm B₁ B₂} {X Y : Tm A₂ B₂}
    {X' Y' : Tm A₁ B₁} (ρ : Val)
    (hX : (Tm.comp Ta X).den ρ ⊑ (Tm.comp X' Tb).den ρ) (hY : (Tm.comp Ta Y).den ρ ⊑ (Tm.comp Y' Tb).den ρ) :
    (Tm.comp Ta (Tm.join X Y)).den ρ ⊑ (Tm.comp (Tm.join X' Y') Tb).den ρ :=
  Core.Rel.le_iff.2 fun a b ⟨e, ha, hxy⟩ =>
    hxy.elim
      (fun h => let ⟨c, hc, hb⟩ := Core.Rel.le_iff.1 hX a b ⟨e, ha, h⟩; ⟨c, .inl hc, hb⟩)
      (fun h => let ⟨c, hc, hb⟩ := Core.Rel.le_iff.1 hY a b ⟨e, ha, h⟩; ⟨c, .inr hc, hb⟩)

end Rel.Lang
