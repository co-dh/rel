import Rel.Lang.Laws.AopS2_10

/-! # Product laws of freyd `AOP/A5_2.lean` (relational product `⟨R,S⟩`, `π₁`, `π₂`, `R × S`), on the concrete core

Each `Rel.Lang.Tm.<name>_den` is the law of the freyd declaration `<name>` read off `Tm.den`, so that
`Rel/Programs/Aop/A5_2.lean` states it as `theorem <name> … by Rel.Lang.Tm.<name>_den`. -/

namespace Rel.Lang
open Tab Rel.Rep
open scoped Rel.Core.Rel
open Rel.Core.Rel hiding id comp recip inter union zero le inl inr junc

theorem Tm.pair_outl_le_den {A B C : Obj} {R : Tm A B} {S : Tm A C} (ρ : Val) :
    (Tm.comp (Tm.pair R S) Tm.outl).den ρ ⊑ R.den ρ :=
  Core.Rel.le_iff.2 fun _ _ ⟨_, ⟨h, _⟩, e⟩ => e ▸ h

theorem Tm.pair_outr_le_den {A B C : Obj} {R : Tm A B} {S : Tm A C} (ρ : Val) :
    (Tm.comp (Tm.pair R S) Tm.outr).den ρ ⊑ S.den ρ :=
  Core.Rel.le_iff.2 fun _ _ ⟨_, ⟨_, h⟩, e⟩ => e ▸ h

theorem Tm.pair_outl_den {A B C : Obj} {R : Tm A B} {S : Tm A C} (ρ : Val) :
    (Tm.comp (Tm.pair R S) Tm.outl).den ρ = (Tm.comp (Tm.dom S) R).den ρ := by
  simp only [Tm.dom_den, Tm.den]
  exact Core.Rel.ext fun a b => ⟨fun ⟨p, ⟨h, hs⟩, e⟩ => ⟨a, ⟨rfl, p.2, hs, hs⟩, e ▸ h⟩,
    fun ⟨d, ⟨e, c, hc, _⟩, h⟩ => ⟨(b, c), ⟨e ▸ h, hc⟩, rfl⟩⟩

theorem Tm.pair_outr_den {A B C : Obj} {R : Tm A B} {S : Tm A C} (ρ : Val) :
    (Tm.comp (Tm.pair R S) Tm.outr).den ρ = (Tm.comp (Tm.dom R) S).den ρ := by
  simp only [Tm.dom_den, Tm.den]
  exact Core.Rel.ext fun a b => ⟨fun ⟨p, ⟨hr, h⟩, e⟩ => ⟨a, ⟨rfl, p.1, hr, hr⟩, e ▸ h⟩,
    fun ⟨d, ⟨e, c, hc, _⟩, h⟩ => ⟨(c, b), ⟨hc, e ▸ h⟩, rfl⟩⟩

theorem Tm.pair_prodMap_den {A B C D E : Obj} {X : Tm A B} {Y : Tm A C} {R : Tm B D} {S : Tm C E} (ρ : Val) :
    (Tm.comp (Tm.pair X Y) (Tm.pair (Tm.comp Tm.outl R) (Tm.comp Tm.outr S))).den ρ = (Tm.pair (Tm.comp X R) (Tm.comp Y S)).den ρ := by
  simp only [Tm.den, Core.Rel.graph]
  exact Core.Rel.ext fun a q => ⟨fun ⟨p, ⟨hx, hy⟩, ⟨_, ex, hr⟩, ⟨_, ey, hs⟩⟩ => ⟨⟨p.1, hx, ex ▸ hr⟩, ⟨p.2, hy, ey ▸ hs⟩⟩,
    fun ⟨⟨b, hx, hr⟩, ⟨c, hy, hs⟩⟩ => ⟨(b, c), ⟨hx, hy⟩, ⟨b, rfl, hr⟩, ⟨c, rfl, hs⟩⟩⟩

theorem Tm.pair_recip_pair_den {A B C D : Obj} {X : Tm A B} {Y : Tm A C} {R : Tm D B} {S : Tm D C} (ρ : Val) :
    (Tm.comp (Tm.pair X Y) (Tm.conv (Tm.pair R S))).den ρ =
      (Tm.meet (Tm.comp X (Tm.conv R)) (Tm.comp Y (Tm.conv S))).den ρ := by
  simp only [Tm.den]
  exact Core.Rel.ext fun a d => ⟨fun ⟨p, ⟨hx, hy⟩, hr, hs⟩ => ⟨⟨p.1, hx, hr⟩, ⟨p.2, hy, hs⟩⟩,
    fun ⟨⟨b, hx, hr⟩, ⟨c, hy, hs⟩⟩ => ⟨(b, c), ⟨hx, hy⟩, hr, hs⟩⟩

theorem Tm.recip_pair_pair_le_den {A B C D E : Obj} {R : Tm A B} {S : Tm A C} {U : Tm A D} {V : Tm A E} (ρ : Val) :
    (Tm.comp (Tm.conv (Tm.pair R S)) (Tm.pair U V)).den ρ ⊑
      (Tm.pair (Tm.comp Tm.outl (Tm.comp (Tm.conv R) U)) (Tm.comp Tm.outr (Tm.comp (Tm.conv S) V))).den ρ := by
  simp only [Tm.den, Core.Rel.graph]
  exact Core.Rel.le_iff.2 fun _ _ ⟨c, ⟨hr, hs⟩, hu, hv⟩ => ⟨⟨_, rfl, c, hr, hu⟩, ⟨_, rfl, c, hs, hv⟩⟩

theorem Tm.comp_pair_le_den {A B C D : Obj} {X : Tm A B} {R : Tm B C} {S : Tm B D} (ρ : Val) :
    (Tm.comp X (Tm.pair R S)).den ρ ⊑ (Tm.pair (Tm.comp X R) (Tm.comp X S)).den ρ := by
  simp only [Tm.den]
  exact Core.Rel.le_iff.2 fun _ _ ⟨c, hx, hr, hs⟩ => ⟨⟨c, hx, hr⟩, ⟨c, hx, hs⟩⟩

-- only the simple half of `Map f` is used
theorem Tm.map_comp_pair_den {A B C D : Obj} {f : Tm A B} {R : Tm B C} {S : Tm B D} (ρ : Val)
    (hf : (Tm.comp f.conv f).den ρ ⊑ (Tm.id (A := B)).den ρ) :
    (Tm.comp f (Tm.pair R S)).den ρ = (Tm.pair (Tm.comp f R) (Tm.comp f S)).den ρ := by
  have sf := fun_of_simple hf
  simp only [Tm.den] at hf ⊢
  exact Core.Rel.ext fun a q => ⟨fun ⟨c, hx, hr, hs⟩ => ⟨⟨c, hx, hr⟩, ⟨c, hx, hs⟩⟩,
    fun ⟨⟨c, hx, hr⟩, ⟨c', hx', hs⟩⟩ => ⟨c, hx, hr, sf a c' c hx' hx ▸ hs⟩⟩

theorem Tm.prodMap_outl_le_den {A B C D : Obj} {R : Tm A C} {S : Tm B D} (ρ : Val) :
    (Tm.comp (Tm.pair (Tm.comp Tm.outl R) (Tm.comp Tm.outr S)) Tm.outl).den ρ ⊑ (Tm.comp Tm.outl R).den ρ := by
  simp only [Tm.den, Core.Rel.graph]
  exact Core.Rel.le_iff.2 fun _ _ ⟨_, ⟨⟨x, ex, hr⟩, _⟩, e⟩ => ⟨x, ex, e ▸ hr⟩

theorem Tm.prodMap_outr_le_den {A B C D : Obj} {R : Tm A C} {S : Tm B D} (ρ : Val) :
    (Tm.comp (Tm.pair (Tm.comp Tm.outl R) (Tm.comp Tm.outr S)) Tm.outr).den ρ ⊑ (Tm.comp Tm.outr S).den ρ := by
  simp only [Tm.den, Core.Rel.graph]
  exact Core.Rel.le_iff.2 fun _ _ ⟨_, ⟨_, ⟨y, ey, hs⟩⟩, e⟩ => ⟨y, ey, e ▸ hs⟩

end Rel.Lang
