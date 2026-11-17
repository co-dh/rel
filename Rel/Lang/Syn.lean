/-
  The syntactic category `Syn` (`doc/rel-denotation-design.md` §4): the objects are `Obj`, a hom `A ⟶ B` is a term
  modulo `Tm.Eqv`, one meaning under every valuation. `⟦−⟧ρ` is then a functor `Syn ⟶ Rel(Set)`; rel has no category
  class (decision A of the split), so the category laws and the functor laws are theorems here over `Core.Rel`, and
  `RelAop.Syn` makes them freyd's `Cat Syn` and `Functor Syn RelSet`. The rest is the §4.2 table of laws.
-/
import Rel.Lang.Den
import Rel.Run.Lang.Elab

namespace Rel.Lang

open Rel.Core.Rel hiding id comp recip inter union zero le inl inr junc
open scoped Rel.Core.Rel

/-! ### The syntactic category -/

/-- Two terms with one meaning under every valuation. -/
def Tm.Eqv {A B : Obj} (s t : (d : Bool) × Tm A B d) : Prop := ∀ ρ, s.2.den ρ = t.2.den ρ

/-- `Tm.Eqv` is an equivalence: equality of meanings, pointwise in `ρ`. -/
def Tm.setoid (A B : Obj) : Setoid ((d : Bool) × Tm A B d) :=
  ⟨Tm.Eqv, ⟨fun _ _ => rfl, fun h ρ => (h ρ).symm, fun h h' ρ => (h ρ).trans (h' ρ)⟩⟩

/-- The objects of the syntactic category. -/
def Syn := Obj

namespace Syn

/-- A hom `A ⟶ B`: a term `A ⟶ B` of either demand bit, modulo its meaning. -/
def Hom (A B : Syn) := Quotient (Tm.setoid A B)

/-- `𝟙`, the term `id`. -/
def id (A : Syn) : Hom A A := Quotient.mk _ ⟨true, .id⟩

/-- `f g`, diagram order: the term `comp`. -/
def comp {A B C : Syn} : Hom A B → Hom B C → Hom A C :=
  Quotient.lift₂ (s₁ := Tm.setoid A B) (s₂ := Tm.setoid B C) (fun R S => Quotient.mk _ ⟨R.1, .comp R.2 S.2⟩)
    fun _ _ _ _ hR hS => Quotient.sound fun ρ => show _ ≫ _ = _ ≫ _ by rw [hR ρ, hS ρ]

/-- `⟦f⟧ρ`, the meaning of a hom: the one meaning its terms share. -/
def Hom.den {A B : Syn} (ρ : Val) : Hom A B → Den A B := Quotient.lift (s := Tm.setoid A B) (·.2.den ρ) fun _ _ h => h ρ

variable {A B C D : Syn}

theorem Hom.den_mk {d : Bool} (t : Tm A B d) (ρ : Val) : Hom.den ρ (Quotient.mk (Tm.setoid A B) ⟨d, t⟩) = t.den ρ :=
  rfl

/-- `⟦−⟧ρ` keeps `𝟙`. -/
theorem Hom.den_id (ρ : Val) : Hom.den ρ (id A) = 𝟙 _ := rfl

/-- `⟦−⟧ρ` keeps composition: `⟦f g⟧ = ⟦f⟧ ⟦g⟧`. -/
theorem Hom.den_comp (ρ : Val) (f : Hom A B) (g : Hom B C) : Hom.den ρ (comp f g) = Hom.den ρ f ≫ Hom.den ρ g :=
  Quotient.inductionOn₂ f g fun _ _ => rfl

/-- `⟦−⟧` is faithful jointly over the valuations: two homs with one meaning under every `ρ` are one. -/
theorem Hom.ext {f g : Hom A B} (h : ∀ ρ, Hom.den ρ f = Hom.den ρ g) : f = g := by
  induction f using Quotient.inductionOn; induction g using Quotient.inductionOn
  exact Quotient.sound h

theorem id_comp (f : Hom A B) : comp (id A) f = f :=
  Hom.ext fun ρ => (Hom.den_comp ρ _ f).trans (Core.Rel.id_comp _)

theorem comp_id (f : Hom A B) : comp f (id B) = f :=
  Hom.ext fun ρ => (Hom.den_comp ρ f _).trans (Core.Rel.comp_id _)

theorem assoc (f : Hom A B) (g : Hom B C) (h : Hom C D) : comp (comp f g) h = comp f (comp g h) :=
  Hom.ext fun ρ => calc
    Hom.den ρ (comp (comp f g) h) = (Hom.den ρ f ≫ Hom.den ρ g) ≫ Hom.den ρ h := by
      rw [Hom.den_comp, Hom.den_comp]
    _ = Hom.den ρ f ≫ (Hom.den ρ g ≫ Hom.den ρ h) := Core.Rel.comp_assoc _ _ _
    _ = Hom.den ρ (comp f (comp g h)) := by rw [Hom.den_comp, Hom.den_comp]

end Syn

/-! ### The laws (§4.2) -/

namespace Tm

variable {A B C : Obj} {d e : Bool} (ρ : Val)

theorem den_comp (R : Tm A B d) (S : Tm B C e) : (comp R S).den ρ = R.den ρ ≫ S.den ρ := rfl
theorem den_id : (id : Tm A A true).den ρ = 𝟙 _ := rfl
theorem den_zero : (zero : Tm A B false).den ρ = 𝟘 := rfl
theorem den_conv (R : Tm A B false) : (conv R).den ρ = (R.den ρ)° := rfl
theorem den_meet (R : Tm A B d) (S : Tm A B e) : (meet R S).den ρ = R.den ρ ∩ S.den ρ := rfl
theorem den_join (R : Tm A B d) (S : Tm A B e) : (join R S).den ρ = R.den ρ ∪ S.den ρ := rfl
theorem den_pair (R : Tm A B d) (S : Tm A C e) : (pair R S).den ρ = rpair (R.den ρ) (S.den ρ) := rfl
theorem den_prod {D : Obj} (R : Tm A B false) (S : Tm C D false) :
    (prod R S).den ρ = rprodMap (R.den ρ) (S.den ρ) := rfl
theorem den_junc (R : Tm A C false) (S : Tm B C false) : (junc R S).den ρ = Core.Rel.junc (R.den ρ) (S.den ρ) := rfl
theorem den_dom (R : Tm A B d) : (dom R).den ρ = 𝟙 _ ∩ R.den ρ ≫ (R.den ρ)° := rfl
theorem den_ran (R : Tm A B false) : (ran R).den ρ = 𝟙 _ ∩ (R.den ρ)° ≫ R.den ρ := rfl
theorem den_share (k : Nat) (R : Tm A B d) : (share k R).den ρ = R.den Val.empty := rfl
theorem den_own (R : Tm A A d) : (own R).den ρ = R.den ρ := rfl

/-! The fixed points unfold where their variable occurs only positively: `Core.Rel.mu_fix`, `nu_fix` with the
    monotonicity `den_mono` gives. -/

theorem den_mu {k cap : Nat} {what : String} {b : Tm A B false} (h : b.pol true k = true) :
    (mu k what cap b).den ρ = b.den (ρ.bind k ((mu k what cap b).den ρ)) :=
  (Core.Rel.mu_fix fun _ _ hXY => den_mono h hXY).symm

theorem den_nu {k : Nat} {S b : Tm A B false} (h : b.pol true k = true) :
    (nu k S b).den ρ = b.den (ρ.bind k ((nu k S b).den ρ)) :=
  (Core.Rel.nu_fix fun _ _ hXY => den_mono h hXY).symm

theorem den_refold {k : Nat} {what : String} {ch : Tm A A d} {b : Tm A B e} (h : b.pol true k = true) :
    (refold k what ch b).den ρ = b.den (ρ.bind k ((refold k what ch b).den ρ)) :=
  (Core.Rel.mu_fix fun _ _ hXY => den_mono h hXY).symm

end Tm

end Rel.Lang
