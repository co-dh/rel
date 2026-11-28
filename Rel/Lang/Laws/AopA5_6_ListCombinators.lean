import Rel.Lang.Laws.AopS2_10
import Rel.Lang.Laws.LamTotal
import Rel.Lang.Laws.AopA4_6
import Rel.Lang.Laws.AopA5_3

/-! # List-combinator laws of freyd `AOP/A5_6_ListCombinators.lean`, on the concrete core

`Rel/Programs/Aop/A5_6_ListCombinators.lean` states each as `theorem <name> … by Rel.Lang.Tm.<name>_den`. -/

namespace Rel.Lang
open Tab Rel.Rep
open scoped Rel.Core.Rel
open Rel.Core.Rel hiding id comp recip inter union zero le inl inr junc

/-- `Λ(R S) = Λ(R) E(S)`, `E(S) = Λ(∋ S)`: the image of the set `Λ(R)` under `S`, when `Λ(R)` has a set at every point
    (`dom(Λ(R)) = 𝟙`). `Tm.Ecomp_den` is the case `R = ∋ R'`. -/
theorem Tm.lamE_den {A B C : Obj} {R : Tm A B} {S : Tm B C} (ρ : Val)
    (h : (Tm.dom (.lam R)).den ρ = (Tm.id (A := A)).den ρ) :
    (Tm.lam (.comp R S)).den ρ = (Tm.comp (.lam R) (.lam (.comp .mem S))).den ρ :=
  (lamDen_absorb (R.den ρ) (S.den ρ) (Tm.entire_of_dom h)).symm

/-- `Λ(nil) = nil Λ(𝟙)`: `nil` is a map at every source, so `Tm.singleton_natural_den` needs no premise. -/
theorem Tm.lamNilSingleton_den {A B : Obj} (ρ : Val) :
    (Tm.comp (Tm.nil (A := A) (B := B)) (Tm.lam Tm.id)).den ρ = (Tm.lam (Tm.nil (A := A) (B := B))).den ρ :=
  Tm.singleton_natural_den ρ
    (Core.Rel.ext fun a b => by
      rw [Tm.dom_den]
      simp only [Tm.den, Tm.nil, Prim.den_nilRow, nilDen, Core.Rel.id]
      exact ⟨fun h => h.1, fun h => by subst h; exact ⟨rfl, [], rfl, rfl⟩⟩)
    (Core.Rel.le_iff.2 fun a b h => by
      simp only [Tm.den, Tm.nil, Prim.den_nilRow, nilDen, Core.Rel.graph, Core.Rel.id, Core.Rel.comp, Core.Rel.recip] at h ⊢
      obtain ⟨_, rfl, rfl⟩ := h; rfl)

/-- The same after any prefix `P` (the elaborator puts the closed source `uni(1)` in front of a closed `nil`). -/
theorem Tm.lamNilSingletonPre_den {D A B : Obj} {P : Tm D A} (ρ : Val) :
    (Tm.comp P (Tm.comp (Tm.nil (A := A) (B := B)) (Tm.lam Tm.id))).den ρ
      = (Tm.comp P (Tm.lam (Tm.nil (A := A) (B := B)))).den ρ := by
  have := Tm.lamNilSingleton_den (A := A) (B := B) ρ
  simp only [Tm.den] at this ⊢
  rw [this]

/-- Composition distributes over `∪` on the right. -/
theorem Tm.compJoin_den {A B C : Obj} {P : Tm A B} {S T : Tm B C} (ρ : Val) :
    (Tm.comp P (Tm.join S T)).den ρ = (Tm.join (Tm.comp P S) (Tm.comp P T)).den ρ := by
  simp only [Tm.den]
  exact Core.Rel.ext fun a c => ⟨fun ⟨b, hb, h⟩ => h.elim (fun h => Or.inl ⟨b, hb, h⟩) (fun h => Or.inr ⟨b, hb, h⟩),
    fun h => h.elim (fun ⟨b, hb, h⟩ => ⟨b, hb, Or.inl h⟩) (fun ⟨b, hb, h⟩ => ⟨b, hb, Or.inr h⟩)⟩

/-- `⟨π₁,S⟩ π₂ = S`: the first component is total. -/
theorem Tm.pairOutr_den {B C D : Obj} {S : Tm (.prod B C) D} (ρ : Val) :
    (Tm.comp (Tm.pair Tm.outl S) Tm.outr).den ρ = S.den ρ := by
  simp only [Tm.den]
  exact Core.Rel.ext fun a d => ⟨fun ⟨y, ⟨_, hy⟩, hd⟩ => by subst hd; exact hy, fun h => ⟨(a.1, d), ⟨rfl, h⟩, rfl⟩⟩

/-- `⟨π₁,S⟩ (U ∪ π₂) ∪`-slide: replacing the second operand `⟨π₁,S⟩ π₂` of a union by `S`. -/
theorem Tm.joinSlideOutr_den {B C D : Obj} {S : Tm (.prod B C) D} {U : Tm (.prod B C) D} (ρ : Val) :
    (Tm.join U (Tm.comp (Tm.pair Tm.outl S) Tm.outr)).den ρ = (Tm.join U S).den ρ := by
  have := Tm.pairOutr_den (S := S) ρ
  simp only [Tm.den] at this ⊢
  rw [this]

/-- `Λ(π₂ R) = π₂ Λ(R)`: the second projection is a map, so `Tm.lam_fusion_den` needs no premise. -/
theorem Tm.lamOutr_den {B C D : Obj} {R : Tm C D} (ρ : Val) :
    (Tm.lam (Tm.comp (Tm.outr (A := B) (B := C)) R)).den ρ = (Tm.comp Tm.outr (Tm.lam R)).den ρ :=
  Tm.lam_fusion_den ρ
    (Core.Rel.ext fun a b => by
      simp only [Tm.dom_den, Tm.den]
      exact ⟨fun h => h.1, fun h => by subst h; exact ⟨rfl, a.2, rfl, rfl⟩⟩)
    (Core.Rel.le_iff.2 fun a b h => by
      simp only [Tm.den, Core.Rel.comp, Core.Rel.recip, Core.Rel.graph, Core.Rel.id] at h ⊢
      obtain ⟨_, rfl, rfl⟩ := h; rfl)

/-- `Λ(⟨π₁,π₂ R⟩ π₂) = π₂ Λ(R)`: `⟨π₁,S⟩ π₂ = S`, then `Tm.lamOutr_den`. -/
theorem Tm.lamPairOutr_den {B C D : Obj} {R : Tm C D} (ρ : Val) :
    (Tm.lam (Tm.comp (Tm.pair (Tm.outl (A := B) (B := C)) (Tm.comp Tm.outr R)) Tm.outr)).den ρ
      = (Tm.comp Tm.outr (Tm.lam R)).den ρ := by
  have h := Tm.pairOutr_den (S := Tm.comp (Tm.outr (A := B) (B := C)) R) ρ
  have := Tm.lamOutr_den (B := B) (R := R) ρ
  simp only [Tm.den] at h this ⊢
  rw [h]; exact this

/-- `[R inl, S inr] [P, Q] = [R P, S Q]`: a sum map before a junction is the junction of the branches. -/
theorem Tm.sumMapJunc_den {A A' B B' C : Obj} {R : Tm A B} {S : Tm A' B'} {P : Tm B C} {Q : Tm B' C} (ρ : Val) :
    (Tm.comp (Tm.junc (Tm.comp R Tm.inl) (Tm.comp S Tm.inr)) (Tm.junc P Q)).den ρ
      = (Tm.junc (Tm.comp R P) (Tm.comp S Q)).den ρ := by
  rw [Tm.junc_comp_den]
  have h1 := Tm.u1_junc_den (R := P) (S := Q) ρ
  have h2 := Tm.u2_junc_den (R := P) (S := Q) ρ
  simp only [Tm.den, Core.Rel.comp_assoc] at h1 h2 ⊢
  rw [h1, h2]

/-- `Λ([𝟙 inl, X inr] [nil, S]) = [nil Λ(𝟙), Λ(X S)]`: `sumMapJunc`, `Λ` of a junction (`Tm.Λ_junc_den`) and
    `Λ(nil) = nil Λ(𝟙)` (`Tm.lamNilSingleton_den`). -/
theorem Tm.subseqAlgLam_den {C D E : Obj} {X : Tm C D} {S : Tm D (.arr E)} (ρ : Val) :
    (Tm.lam (Tm.comp (Tm.junc (Tm.comp Tm.id Tm.inl) (Tm.comp X Tm.inr))
        (Tm.junc (Tm.nil (A := .one) (B := E)) S))).den ρ
      = (Tm.junc (Tm.comp (Tm.nil (A := .one) (B := E)) (Tm.lam Tm.id)) (Tm.lam (Tm.comp X S))).den ρ := by
  have e := Tm.sumMapJunc_den (R := (Tm.id (A := .one))) (S := X) (P := (Tm.nil (A := .one) (B := E))) (Q := S) ρ
  have l := Tm.Λ_junc_den (R := Tm.comp (Tm.id (A := .one)) (Tm.nil (A := .one) (B := E))) (S := Tm.comp X S) ρ
  have hn : (Tm.lam (Tm.comp (Tm.id (A := .one)) (Tm.nil (A := .one) (B := E)))).den ρ
      = (Tm.comp (Tm.nil (A := .one) (B := E)) (Tm.lam Tm.id)).den ρ := by
    rw [Tm.lamNilSingleton_den]; simp only [Tm.den, Core.Rel.id_comp]
  change lamDen _ = _
  rw [e]
  change (Tm.lam (Tm.junc (Tm.comp (Tm.id (A := .one)) (Tm.nil (A := .one) (B := E))) (Tm.comp X S))).den ρ = _
  rw [l]
  change Core.Rel.junc _ _ = Core.Rel.junc _ _
  rw [hn]

/-- `[Λ(nil), U] = [nil Λ(𝟙), U]`: `Tm.lamNilSingleton_den` in the first arm of a junction. -/
theorem Tm.lamNilJunc_den {D E : Obj} {U : Tm D (.arr (.arr E))} (ρ : Val) :
    (Tm.junc (Tm.lam (Tm.nil (A := .one) (B := E))) U).den ρ
      = (Tm.junc (Tm.comp (Tm.nil (A := .one) (B := E)) (Tm.lam Tm.id)) U).den ρ := by
  have h := Tm.lamNilSingleton_den (A := .one) (B := E) ρ
  change Core.Rel.junc (Tm.den ρ (Tm.lam Tm.nil)) _ = Core.Rel.junc (Tm.den ρ (Tm.comp Tm.nil (Tm.lam Tm.id))) _
  rw [h]

end Rel.Lang
