import Rel.Lang.Laws.Map
import Rel.Lang.PreludeRows

/-! # Laws of freyd §8.1 `AOP/A8_1.lean` (thinning), on the concrete core

`Rel.Lang.Tm.<name>_den` is the law of the freyd declaration `<name>` read off `Tm.den`; `Rel/Programs/Aop/A8_1.lean`
states it as `theorem <name> … by Rel.Lang.Tm.<name>_den`. A thinning is not a definition of the program (the converse
of `∋` it contains runs only after a relation that supplies its keys), so each statement writes it inline after `X`. -/

namespace Rel.Lang
open Tab Rel.Rep
open scoped Rel.Core.Rel
open Rel.Core.Rel hiding id comp recip inter union zero le inl inr junc

/-- `τ ∋ = 𝟙`: the one-element list of `a` has `a` as its only member. -/
theorem Tm.singleton_comp_eps_den {A : Obj} (ρ : Val) :
    (Tm.comp (Tm.prim (rowOf "τ") : Tm A (.arr A)) Tm.mem).den ρ = (Tm.id (A := A)).den ρ := by
  simp only [Tm.den, Prim.den_tau]
  refine Core.Rel.ext fun a b => ⟨fun ⟨Y, hY, hb⟩ => ?_, fun h => ⟨[a], rfl, ?_⟩⟩
  · subst hY; exact (by simpa [memDen] using hb : b = a).symm
  · subst h; simp [memDen]

/-- `T° Λ(T) ⊑ ∈`: an image `a` of `c` under `T` is a member of the set `Λ(T) c` of all of them. -/
theorem Tm.recip_comp_lam_le_den {A B : Obj} {T : Tm B A} (ρ : Val) :
    (Tm.comp T.conv T.lam).den ρ ⊑ (Tm.comp Tm.id Tm.mem).conv.den ρ := by
  simp only [Tm.den]
  refine Core.Rel.le_iff.2 fun a ys ⟨c, hT, hl⟩ => ?_
  have h := ((lamDen_iff _ c ys).1 hl).2 a
  exact ⟨ys, rfl, h.2 hT⟩

/-- Thinning only shrinks: `X thin(Q) ∋ ⊑ X ∋`, `thin(Q) = (∋/∋) ∩ (∋° \ (Q° ∋°))`. -/
theorem Tm.thin_comp_eps_le_den {A B : Obj} {X : Tm B (.arr A)} {Q : Tm A A} (ρ : Val) :
    (Tm.comp (Tm.comp X (Tm.meet (Tm.ldiv (Tm.comp Tm.id Tm.mem).conv (Tm.comp Tm.id Tm.mem).conv Tm.id Tm.id).conv
        (Tm.ldiv (Tm.comp Tm.id Tm.mem).conv (Tm.comp Q.conv (Tm.comp Tm.id Tm.mem).conv) Tm.id Tm.id))) Tm.mem).den ρ ⊑
      (Tm.comp X Tm.mem).den ρ := by
  simp only [Tm.den]
  refine Core.Rel.le_iff.2 fun b a ⟨z, ⟨x, hX, hM⟩, ha⟩ => ?_
  have h1 := (ldivDen_iff.1 hM.1).1 a ⟨z, rfl, ha⟩
  obtain ⟨_, rfl, hx⟩ := h1
  exact ⟨x, hX, hx⟩

/-- `thin` is monotone: `Q ⊑ R → X thin(Q) ⊑ X thin(R)`. -/
theorem Tm.thin_mono_den {A B : Obj} {X : Tm B (.arr A)} {Q R : Tm A A} (ρ : Val) (h : Q.den ρ ⊑ R.den ρ) :
    (Tm.comp X (Tm.meet (Tm.ldiv (Tm.comp Tm.id Tm.mem).conv (Tm.comp Tm.id Tm.mem).conv Tm.id Tm.id).conv
        (Tm.ldiv (Tm.comp Tm.id Tm.mem).conv (Tm.comp Q.conv (Tm.comp Tm.id Tm.mem).conv) Tm.id Tm.id))).den ρ ⊑
      (Tm.comp X (Tm.meet (Tm.ldiv (Tm.comp Tm.id Tm.mem).conv (Tm.comp Tm.id Tm.mem).conv Tm.id Tm.id).conv
        (Tm.ldiv (Tm.comp Tm.id Tm.mem).conv (Tm.comp R.conv (Tm.comp Tm.id Tm.mem).conv) Tm.id Tm.id))).den ρ := by
  simp only [Tm.den]
  refine Core.Rel.le_iff.2 fun b y ⟨z, hX, hM1, hM2⟩ => ⟨z, hX, hM1, ?_⟩
  obtain ⟨hall, hg⟩ := ldivDen_iff.1 hM2
  refine ldivDen_iff.2 ⟨fun a hR => ?_, hg⟩
  obtain ⟨w, hq, hw⟩ := hall a hR
  exact ⟨w, Core.Rel.le_iff.1 h w a hq, hw⟩

/-- `𝟙 ⊑ Q → X ⊑ X thin(Q)`: a reflexive `Q` lets a thinning keep the whole set. -/
theorem Tm.refl_le_thin_den {A B : Obj} {X : Tm B (.arr A)} {Q : Tm A A} (ρ : Val)
    (h : (Tm.id (A := A)).den ρ ⊑ Q.den ρ) :
    X.den ρ ⊑ (Tm.comp X (Tm.meet (Tm.ldiv (Tm.comp Tm.id Tm.mem).conv (Tm.comp Tm.id Tm.mem).conv Tm.id Tm.id).conv
        (Tm.ldiv (Tm.comp Tm.id Tm.mem).conv (Tm.comp Q.conv (Tm.comp Tm.id Tm.mem).conv) Tm.id Tm.id))).den ρ := by
  simp only [Tm.den]
  refine Core.Rel.le_iff.2 fun b y hX => ⟨y, hX, ?_, ?_⟩
  · exact ldivDen_iff.2 ⟨fun a ⟨_, rfl, ha⟩ => ⟨_, rfl, ha⟩, .inr ⟨⟨y, rfl⟩, ⟨y, rfl⟩⟩⟩
  · exact ldivDen_iff.2 ⟨fun a ⟨_, rfl, ha⟩ => ⟨a, Core.Rel.le_iff.1 h a a rfl, ⟨y, rfl, ha⟩⟩, .inr ⟨⟨y, rfl⟩, ⟨y, rfl⟩⟩⟩

end Rel.Lang
