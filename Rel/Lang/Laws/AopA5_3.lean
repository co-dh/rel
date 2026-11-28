import Rel.Lang.Laws.Map
import Rel.Lang.Laws.Eunion

/-! # Sum laws of freyd §5.3 `AOP/A5_3.lean`, on the concrete core

`[R,S]` is `inl°R ∪ inr°S` (`Pre.junc`, a term of its own here: `Tm.junc`). Each `Rel.Lang.Tm.<name>_den` is the law
of one freyd declaration, read off `Tm.den`; `Rel/Programs/Aop/A5_3.lean` states it as a `rel_program` theorem. -/

namespace Rel.Lang
open Tab Rel.Rep
open scoped Rel.Core.Rel
open Rel.Core.Rel hiding id comp recip inter union zero le inl inr junc

/-- `[R,S] : A + B ⟶ C` as the elaborator builds it (`Pre.junc`). -/
abbrev Tm.junc {A B C : Obj} (R : Tm A C) (S : Tm B C) : Tm (.sum A B) C :=
  .join (.comp (.conv .inl) R) (.comp (.conv .inr) S)

section core
variable {α β γ : Type} {R : Core.Rel α γ} {S : Core.Rel β γ}

theorem junc_inl {a : α} {c : γ} : Core.Rel.junc R S (Sum.inl a) c ↔ R a c := by
  simp [Core.Rel.junc, Core.Rel.union, Core.Rel.comp, Core.Rel.recip, Core.Rel.inl, Core.Rel.inr, Core.Rel.graph]

theorem junc_inr {b : β} {c : γ} : Core.Rel.junc R S (Sum.inr b) c ↔ S b c := by
  simp [Core.Rel.junc, Core.Rel.union, Core.Rel.comp, Core.Rel.recip, Core.Rel.inl, Core.Rel.inr, Core.Rel.graph]

/-- A relation out of a sum is determined by its two restrictions. -/
theorem junc_eta (T : Core.Rel (α ⊕ β) γ) :
    T = Core.Rel.junc (Core.Rel.inl ≫ T) (Core.Rel.inr ≫ T) :=
  Core.Rel.ext fun x c => by
    cases x <;> simp [junc_inl, junc_inr, Core.Rel.comp, Core.Rel.inl, Core.Rel.inr, Core.Rel.graph]

theorem inl_junc : Core.Rel.inl ≫ Core.Rel.junc R S = R :=
  Core.Rel.ext fun a c => by simp [Core.Rel.comp, Core.Rel.inl, Core.Rel.graph, junc_inl]

theorem inr_junc : Core.Rel.inr ≫ Core.Rel.junc R S = S :=
  Core.Rel.ext fun b c => by simp [Core.Rel.comp, Core.Rel.inr, Core.Rel.graph, junc_inr]

/-- `Λ(T) ∋ = T` where `Λ(T)` has an array at every point. -/
theorem lamDen_memDen {A B : Obj} {T : Core.Rel (Obj.El A) (Obj.El B)} (h : ∀ a, ∃ ys, lamDen T a ys) :
    lamDen T ≫ memDen = T :=
  Core.Rel.ext fun a b => by
    obtain ⟨ys, hy⟩ := h a
    have := (lamDen_iff T a ys).1 hy
    exact ⟨fun ⟨g, hg, hb⟩ => by rw [lamDen_unique T hg hy] at hb; exact (this.2 b).1 hb,
      fun hT => ⟨ys, hy, (this.2 b).2 hT⟩⟩

/-- `(R ⊕ S) ∩ ([P,Q] [U,V]°) = (R ∩ P U°) ⊕ (S ∩ Q V°)`, `⊕` the sum of relations `[R inl, S inr]`. -/
theorem sumMap_inter_junc_recip {α α' β β' δ : Type} (R : Core.Rel α β) (S : Core.Rel α' β') (P : Core.Rel α δ)
    (Q : Core.Rel α' δ) (U : Core.Rel β δ) (V : Core.Rel β' δ) :
    Core.Rel.junc (R ≫ Core.Rel.inl) (S ≫ Core.Rel.inr) ∩ (Core.Rel.junc P Q ≫ (Core.Rel.junc U V)°) =
      Core.Rel.junc ((R ∩ P ≫ U°) ≫ Core.Rel.inl) ((S ∩ Q ≫ V°) ≫ Core.Rel.inr) :=
  Core.Rel.ext fun x y => by
    cases x <;> cases y <;>
      simp [junc_inl, junc_inr, Core.Rel.inter, Core.Rel.comp, Core.Rel.recip, Core.Rel.inl, Core.Rel.inr, Core.Rel.graph]

end core

theorem Tm.junc_comp_den {A B C D : Obj} {R : Tm A C} {S : Tm B C} {Z : Tm C D} (ρ : Val) :
    (Tm.comp (Tm.junc R S) Z).den ρ = (Tm.junc (Tm.comp R Z) (Tm.comp S Z)).den ρ := by
  simp only [Tm.den, Core.Rel.union_comp, Core.Rel.comp_assoc]

theorem Tm.u1_junc_den {A B C : Obj} {R : Tm A C} {S : Tm B C} (ρ : Val) :
    (Tm.comp (Tm.inl (A := A) (B := B)) (Tm.junc R S)).den ρ = R.den ρ := inl_junc

theorem Tm.u2_junc_den {A B C : Obj} {R : Tm A C} {S : Tm B C} (ρ : Val) :
    (Tm.comp (Tm.inr (A := A) (B := B)) (Tm.junc R S)).den ρ = S.den ρ := inr_junc

theorem Tm.junc_unique_den {A B C : Obj} {R : Tm A C} {S : Tm B C} {T : Tm (.sum A B) C} (ρ : Val)
    (h₁ : (Tm.comp Tm.inl T).den ρ = R.den ρ) (h₂ : (Tm.comp Tm.inr T).den ρ = S.den ρ) :
    T.den ρ = (Tm.junc R S).den ρ := by
  simp only [Tm.den] at h₁ h₂ ⊢
  rw [← h₁, ← h₂]; exact junc_eta _

/-- `[U,V]° = U° inl ∪ V° inr` as the elaborator builds it (it pushes a converse through `∪` and `≫`). -/
abbrev Tm.juncConv {A B C : Obj} (U : Tm A C) (V : Tm B C) : Tm C (.sum A B) :=
  .join (.comp U.conv .inl) (.comp V.conv .inr)

theorem Tm.juncConv_den {A B C : Obj} {U : Tm A C} {V : Tm B C} (ρ : Val) :
    (Tm.juncConv U V).den ρ = ((Tm.junc U V).den ρ)° :=
  Core.Rel.ext fun d x => by
    change ((U.den ρ)° ≫ Core.Rel.inl ∪ (V.den ρ)° ≫ Core.Rel.inr) d x ↔ Core.Rel.junc (U.den ρ) (V.den ρ) x d
    cases x <;> simp [junc_inl, junc_inr, Core.Rel.union, Core.Rel.comp, Core.Rel.recip, Core.Rel.inl, Core.Rel.inr,
      Core.Rel.graph]

theorem Tm.junc_recip_junc_den {A B D E : Obj} {U : Tm A D} {V : Tm B D} {R : Tm A E} {S : Tm B E} (ρ : Val) :
    (Tm.comp (Tm.juncConv U V) (Tm.junc R S)).den ρ = (Tm.join (Tm.comp U.conv R) (Tm.comp V.conv S)).den ρ := by
  have : (Tm.comp (Tm.juncConv U V) (Tm.junc R S)).den ρ = ((Tm.junc U V).den ρ)° ≫ (Tm.junc R S).den ρ := by
    change (Tm.juncConv U V).den ρ ≫ _ = _
    rw [Tm.juncConv_den]
  rw [this]
  refine Core.Rel.ext fun d e => ?_
  change (∃ x, Core.Rel.junc (U.den ρ) (V.den ρ) x d ∧ Core.Rel.junc (R.den ρ) (S.den ρ) x e) ↔
    ((∃ a, U.den ρ a d ∧ R.den ρ a e) ∨ ∃ b, V.den ρ b d ∧ S.den ρ b e)
  constructor
  · rintro ⟨x | x, hx, hy⟩
    · exact Or.inl ⟨x, junc_inl.1 hx, junc_inl.1 hy⟩
    · exact Or.inr ⟨x, junc_inr.1 hx, junc_inr.1 hy⟩
  · rintro (⟨a, hu, hr⟩ | ⟨b, hv, hs⟩)
    · exact ⟨Sum.inl a, junc_inl.2 hu, junc_inl.2 hr⟩
    · exact ⟨Sum.inr b, junc_inr.2 hv, junc_inr.2 hs⟩

theorem Tm.Λ_junc_den {A B C : Obj} {R : Tm A C} {S : Tm B C} (ρ : Val) :
    (Tm.lam (Tm.junc R S)).den ρ = (Tm.junc (Tm.lam R) (Tm.lam S)).den ρ := by
  refine Core.Rel.ext fun x g => ?_
  change lamDen (A := .sum A B) (B := C) (Core.Rel.junc (R.den ρ) (S.den ρ)) x g ↔ Core.Rel.junc (lamDen (R.den ρ)) (lamDen (S.den ρ)) x g
  cases x with
  | inl a => rw [junc_inl, lamDen_iff, lamDen_iff]; simp [junc_inl]
  | inr b => rw [junc_inr, lamDen_iff, lamDen_iff]; simp [junc_inr]

theorem Tm.junc_eq_Λ_junc_eps_den {A B C : Obj} {R : Tm A C} {S : Tm B C} (ρ : Val)
    (hR : (Tm.dom (Tm.lam R)).den ρ = (Tm.id (A := A)).den ρ) (hS : (Tm.dom (Tm.lam S)).den ρ = (Tm.id (A := B)).den ρ) :
    (Tm.junc R S).den ρ = (Tm.comp (Tm.junc (Tm.lam R) (Tm.lam S)) Tm.mem).den ρ := by
  rw [Tm.junc_comp_den]
  change Core.Rel.junc (R.den ρ) (S.den ρ) = Core.Rel.junc (lamDen (R.den ρ) ≫ memDen) (lamDen (S.den ρ) ≫ memDen)
  rw [lamDen_memDen (Tm.entire_of_dom hR), lamDen_memDen (Tm.entire_of_dom hS)]

theorem Tm.u1_junc_Λ_eps_den {A B C : Obj} {R : Tm A C} {S : Tm B C} (ρ : Val)
    (hR : (Tm.dom (Tm.lam R)).den ρ = (Tm.id (A := A)).den ρ) :
    (Tm.comp (Tm.comp Tm.inl (Tm.junc (Tm.lam R) (Tm.lam S))) Tm.mem).den ρ = R.den ρ := by
  change (Core.Rel.inl ≫ Core.Rel.junc (lamDen (R.den ρ)) (lamDen (S.den ρ))) ≫ memDen = R.den ρ
  rw [inl_junc, lamDen_memDen (Tm.entire_of_dom hR)]

theorem Tm.u2_junc_Λ_eps_den {A B C : Obj} {R : Tm A C} {S : Tm B C} (ρ : Val)
    (hS : (Tm.dom (Tm.lam S)).den ρ = (Tm.id (A := B)).den ρ) :
    (Tm.comp (Tm.comp Tm.inr (Tm.junc (Tm.lam R) (Tm.lam S))) Tm.mem).den ρ = S.den ρ := by
  change (Core.Rel.inr ≫ Core.Rel.junc (lamDen (R.den ρ)) (lamDen (S.den ρ))) ≫ memDen = S.den ρ
  rw [inr_junc, lamDen_memDen (Tm.entire_of_dom hS)]

theorem Tm.sumMap_inter_junc_recip_den {A A' B B' C : Obj} {R : Tm A B} {S : Tm A' B'} {P : Tm A C} {Q : Tm A' C}
    {U : Tm B C} {V : Tm B' C} (ρ : Val) :
    (Tm.meet (Tm.junc (Tm.comp R Tm.inl) (Tm.comp S Tm.inr)) (Tm.comp (Tm.junc P Q) (Tm.juncConv U V))).den ρ =
      (Tm.junc (Tm.comp (Tm.meet R (Tm.comp P U.conv)) Tm.inl) (Tm.comp (Tm.meet S (Tm.comp Q V.conv)) Tm.inr)).den ρ := by
  change _ ∩ ((Tm.junc P Q).den ρ ≫ (Tm.juncConv U V).den ρ) = _
  rw [Tm.juncConv_den]
  exact sumMap_inter_junc_recip _ _ _ _ _ _

end Rel.Lang
