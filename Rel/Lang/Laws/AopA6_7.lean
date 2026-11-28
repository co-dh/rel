import Rel.Lang.Laws.Map
import Rel.Lang.PreludeStar

/-! # Closure laws of freyd §6.7 `AOP/A6_7.lean`, on the concrete core

`star T = μX : 𝟙 ∪ T X` is `Core.Rel.mu`; the laws are about any `T`, then `Rel.Lang.Tm.<name>_den` reads each off
`Tm.den`, where `star(R)` is the row `star` given `R` (`Tm.star_den`), so that `Rel/Programs/Aop/A6_7.lean` states
it as `theorem <name> … by Rel.Lang.Tm.<name>_den`. -/

namespace Rel.Lang
open Tab Rel.Rep
open scoped Rel.Core.Rel
open Rel.Core.Rel hiding id comp recip inter union zero le inl inr junc

section Core
variable {α β : Type}

/-- `R*` of a relation `T`: the prelude's `star`. -/
abbrev cstar (T : Core.Rel α α) : Core.Rel α α := mu fun X => 𝟙 α ∪ T ≫ X

theorem id_le_cstar (T : Core.Rel α α) : 𝟙 α ⊑ cstar T :=
  Core.Rel.le_iff.2 fun a b (e : a = b) Y hY => Core.Rel.le_iff.1 hY a b (Or.inl e)

theorem comp_cstar_le (T : Core.Rel α α) : T ≫ cstar T ⊑ cstar T :=
  Core.Rel.le_iff.2 fun a b ⟨c, hT, hS⟩ Y hY => Core.Rel.le_iff.1 hY a b (Or.inr ⟨c, hT, hS Y hY⟩)

theorem le_cstar (T : Core.Rel α α) : T ⊑ cstar T :=
  Core.Rel.le_iff.2 fun a b h Y hY =>
    Core.Rel.le_iff.1 hY a b (Or.inr ⟨b, h, Core.Rel.le_iff.1 hY b b (Or.inl rfl)⟩)

theorem cstar_trans (T : Core.Rel α α) : cstar T ≫ cstar T ⊑ cstar T :=
  Core.Rel.le_iff.2 fun a b ⟨c, h1, h2⟩ => by
    refine h1 (fun a c => ∀ b, cstar T c b → cstar T a b) (Core.Rel.le_iff.2 fun a c h b hb => ?_) b h2
    rcases h with rfl | ⟨d, hT, hd⟩
    · exact hb
    · exact Core.Rel.le_iff.1 (comp_cstar_le T) a b ⟨d, hT, hd b hb⟩

theorem cstar_comp_le (T : Core.Rel α α) : cstar T ≫ T ⊑ cstar T :=
  Core.Rel.le_iff.2 fun a b ⟨c, hs, hT⟩ =>
    Core.Rel.le_iff.1 (cstar_trans T) a b ⟨c, hs, Core.Rel.le_iff.1 (le_cstar T) c b hT⟩

theorem preorder_prefixed {T X : Core.Rel α α} (hr : 𝟙 α ⊑ X) (ht : X ≫ X ⊑ X) (hT : T ⊑ X) :
    𝟙 α ∪ T ≫ X ⊑ X :=
  Core.Rel.le_iff.2 fun a b h => by
    rcases h with e | ⟨c, h1, h2⟩
    · exact Core.Rel.le_iff.1 hr a b e
    · exact Core.Rel.le_iff.1 ht a b ⟨c, Core.Rel.le_iff.1 hT a c h1, h2⟩

theorem cstar_le_of_preorder {T X : Core.Rel α α} (hr : 𝟙 α ⊑ X) (ht : X ≫ X ⊑ X) (hT : T ⊑ X) : cstar T ⊑ X :=
  mu_le (preorder_prefixed hr ht hT)

theorem cstar_simulation {A : Core.Rel β β} {B : Core.Rel α β} {C : Core.Rel α α} (h : B ≫ A ⊑ C ≫ B) :
    B ≫ cstar A ⊑ cstar C ≫ B :=
  Core.Rel.le_iff.2 fun a b ⟨c, hB, hs⟩ => by
    refine hs (fun c b => ∀ a, B a c → (cstar C ≫ B) a b) (Core.Rel.le_iff.2 fun c b h' a hB => ?_) a hB
    · rcases h' with rfl | ⟨d, hA, hd⟩
      · exact ⟨a, Core.Rel.le_iff.1 (id_le_cstar C) a a rfl, hB⟩
      · obtain ⟨e, hC, hBe⟩ := Core.Rel.le_iff.1 h a d ⟨c, hB, hA⟩
        obtain ⟨f, hs, hBf⟩ := hd e hBe
        exact ⟨f, Core.Rel.le_iff.1 (comp_cstar_le C) a f ⟨e, hC, hs⟩, hBf⟩

theorem cstar_simulation_step {A : Core.Rel β β} {B : Core.Rel α β} {C : Core.Rel α α} (h : B ≫ A ⊑ C ≫ B) :
    (cstar C ≫ B) ≫ A ⊑ cstar C ≫ B :=
  Core.Rel.le_iff.2 fun a x ⟨d, ⟨c, hs, hB⟩, hA⟩ =>
    let ⟨e, hC, hBe⟩ := Core.Rel.le_iff.1 h c x ⟨d, hB, hA⟩
    ⟨e, Core.Rel.le_iff.1 (cstar_comp_le C) a e ⟨c, hs, hC⟩, hBe⟩

theorem comp_star_body_le {A : Core.Rel β β} {B : Core.Rel α β} {C : Core.Rel α α} (h : B ≫ A ⊑ C ≫ B)
    (Z : Core.Rel β β) : B ≫ (𝟙 β ∪ A ≫ Z) ⊑ B ∪ C ≫ (B ≫ Z) :=
  Core.Rel.le_iff.2 fun a b ⟨c, hB, h'⟩ => by
    rcases h' with rfl | ⟨d, hA, hZ⟩
    · exact Or.inl hB
    · obtain ⟨e, hC, hBe⟩ := Core.Rel.le_iff.1 h a d ⟨c, hB, hA⟩
      exact Or.inr ⟨e, hC, d, hBe, hZ⟩

/-- `μX : S ∪ X T = S T*`: the linear recursion with the closure on the right. -/
theorem mu_comp_cstar (T : Core.Rel α α) (S : Core.Rel β α) :
    mu (fun X => S ∪ X ≫ T) = S ≫ cstar T :=
  le_antisymm
    (mu_le (Core.Rel.le_iff.2 fun a b h => by
      rcases h with h | ⟨d, ⟨c, hS, hs⟩, hT⟩
      · exact ⟨b, h, Core.Rel.le_iff.1 (id_le_cstar T) b b rfl⟩
      · exact ⟨c, hS, Core.Rel.le_iff.1 (cstar_comp_le T) c b ⟨d, hs, hT⟩⟩))
    (Core.Rel.le_iff.2 fun a b ⟨c, hS, hs⟩ => by
      refine hs (fun c b => mu (fun X => S ∪ X ≫ T) a c → mu (fun X => S ∪ X ≫ T) a b)
        (Core.Rel.le_iff.2 fun c b h hM => ?_) (fun Y hY => Core.Rel.le_iff.1 hY a c (Or.inl hS))
      rcases h with rfl | ⟨d, hT, hd⟩
      · exact hM
      · exact hd fun Y hY => Core.Rel.le_iff.1 hY a d (Or.inr ⟨c, hM Y hY, hT⟩))

/-- `θ(𝟘,S) = 𝟘 ∪ (μX : S ∪ (X T − 𝟘)) = S T*`: `− 𝟘` and `𝟘 ∪` change nothing, then `mu_comp_cstar`. -/
theorem theta_zero_left (T : Core.Rel α α) (S : Core.Rel β α) :
    𝟘 ∪ mu (fun X => S ∪ Core.Rel.diff (X ≫ T) 𝟘) = S ≫ cstar T := by
  have : (fun X : Core.Rel β α => S ∪ Core.Rel.diff (X ≫ T) 𝟘) = fun X => S ∪ X ≫ T :=
    funext fun X => Core.Rel.ext fun a b => ⟨Or.imp id (·.1), Or.imp id (fun h => ⟨h, id⟩)⟩
  rw [this, ← mu_comp_cstar]
  exact Core.Rel.ext fun a b => ⟨fun h => h.elim False.elim id, Or.inr⟩

/-- `θ(P,𝟘) = P ∪ (μX : 𝟘 ∪ (X T − P)) = P`: `𝟘` is a prefixed point, as `𝟘 T − P = 𝟘`. -/
theorem theta_zero_right (T : Core.Rel α α) (P : Core.Rel β α) :
    P ∪ mu (fun X => 𝟘 ∪ Core.Rel.diff (X ≫ T) P) = P := by
  have : mu (fun X : Core.Rel β α => 𝟘 ∪ Core.Rel.diff (X ≫ T) P) = 𝟘 :=
    le_antisymm (mu_le (Core.Rel.le_iff.2 fun a b h => h.elim id fun ⟨⟨c, f, _⟩, _⟩ => f)) (Core.Rel.le_iff.2 fun _ _ h => h.elim)
  rw [this]
  exact Core.Rel.ext fun a b => ⟨fun h => h.elim id False.elim, Or.inl⟩

end Core

theorem Tm.star_den {A : Obj} (T : Core.Rel (Obj.El A) (Obj.El A)) (ρ : Val) :
    Tm.argDen ρ (Tm.prim (rowOf "star") : Tm A A) [⟨A, A, T⟩] = cstar T := by
  simp only [Tm.argDen, Prim.den_star]

/-- `star(R)` as a term. -/
abbrev Tm.star {A : Obj} (R : Tm A A) : Tm A A := Tm.arg (Tm.prim (rowOf "star") : Tm A A) R

theorem Tm.id_le_star_den {A : Obj} {R : Tm A A} (ρ : Val) : (Tm.id (A := A)).den ρ ⊑ (Tm.star R).den ρ := by
  simp only [Tm.den, Tm.star_den]; exact id_le_cstar _

theorem Tm.le_star_den {A : Obj} {R : Tm A A} (ρ : Val) : R.den ρ ⊑ (Tm.star R).den ρ := by
  simp only [Tm.den, Tm.star_den]; exact le_cstar _

theorem Tm.star_trans_den {A : Obj} {R : Tm A A} (ρ : Val) :
    (Tm.comp (Tm.star R) (Tm.star R)).den ρ ⊑ (Tm.star R).den ρ := by
  simp only [Tm.den]; simp only [Tm.star_den]; exact cstar_trans _

theorem Tm.preorder_prefixed_den {A : Obj} {R X : Tm A A} (ρ : Val) (hr : (Tm.id (A := A)).den ρ ⊑ X.den ρ)
    (ht : (Tm.comp X X).den ρ ⊑ X.den ρ) (hR : R.den ρ ⊑ X.den ρ) :
    (Tm.join Tm.id (Tm.comp R X)).den ρ ⊑ X.den ρ :=
  preorder_prefixed hr ht hR

theorem Tm.star_le_of_preorder_den {A : Obj} {R X : Tm A A} (ρ : Val) (hr : (Tm.id (A := A)).den ρ ⊑ X.den ρ)
    (ht : (Tm.comp X X).den ρ ⊑ X.den ρ) (hR : R.den ρ ⊑ X.den ρ) : (Tm.star R).den ρ ⊑ X.den ρ := by
  simp only [Tm.den, Tm.star_den]; exact cstar_le_of_preorder hr ht hR

theorem Tm.star_simulation_den {X Y : Obj} {A : Tm Y Y} {B : Tm X Y} {C : Tm X X} (ρ : Val)
    (h : (Tm.comp B A).den ρ ⊑ (Tm.comp C B).den ρ) :
    (Tm.comp B (Tm.star A)).den ρ ⊑ (Tm.comp (Tm.star C) B).den ρ := by
  simp only [Tm.den] at h ⊢; simp only [Tm.star_den]; exact cstar_simulation h

theorem Tm.star_simulation_step_den {X Y : Obj} {A : Tm Y Y} {B : Tm X Y} {C : Tm X X} (ρ : Val)
    (h : (Tm.comp B A).den ρ ⊑ (Tm.comp C B).den ρ) :
    (Tm.comp (Tm.comp (Tm.star C) B) A).den ρ ⊑ (Tm.comp (Tm.star C) B).den ρ := by
  simp only [Tm.den] at h ⊢; simp only [Tm.star_den]; exact cstar_simulation_step h

theorem Tm.comp_star_body_le_den {X Y : Obj} {A : Tm Y Y} {B : Tm X Y} {C : Tm X X} {Z : Tm Y Y} (ρ : Val)
    (h : (Tm.comp B A).den ρ ⊑ (Tm.comp C B).den ρ) :
    (Tm.comp B (Tm.join Tm.id (Tm.comp A Z))).den ρ ⊑ (Tm.join B (Tm.comp C (Tm.comp B Z))).den ρ := by
  simp only [Tm.den] at h ⊢; exact comp_star_body_le h _

theorem Tm.theta_zero_left_den {A B : Obj} {what : String} {cap : Nat} (ρ : Val) :
    (Tm.join Tm.zero (Tm.mu 2 what cap (Tm.join (.var 1 : Tm B A) (Tm.diff (Tm.comp (.var 2 : Tm B A) (.var 0 : Tm A A)) Tm.zero))) : Tm B A).den ρ =
      (Tm.comp (.var 1 : Tm B A) (Tm.star (.var 0 : Tm A A))).den ρ := by
  simp only [Tm.den, Tm.star_den, Val.bind, if_true]
  exact theta_zero_left _ _

theorem Tm.theta_zero_right_den {A B : Obj} {what : String} {cap : Nat} (ρ : Val) :
    (Tm.join (.var 1 : Tm B A) (Tm.mu 2 what cap (Tm.join Tm.zero (Tm.diff (Tm.comp (.var 2 : Tm B A) (.var 0 : Tm A A)) (.var 1 : Tm B A)))) : Tm B A).den ρ =
      (.var 1 : Tm B A).den ρ := by
  simp only [Tm.den, Val.bind, if_true]
  exact theta_zero_right _ _

end Rel.Lang
