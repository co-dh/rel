import Rel.Lang.Laws.FoldUP

/-! # Catamorphism laws of freyd §5.5 `AOP/A5_5.lean`, at the list datatype, on the concrete core

freyd's `InitialAlgebra F` is the left-fold list (`α = [nil, snoc]`, `F X = 1 + X × A`); its relational catamorphism
`⦇R⦈` is the prelude's `⦇[e, S]⦈` (`Tm.fold (Tm.ran e) S`), `R = [e, S]`. -/

namespace Rel.Lang
open Tab Rel.Rep
open scoped Rel.Core.Rel
open Rel.Core.Rel hiding id comp recip inter union zero le inl inr junc

/-- (5.12) at `X := ⦇R⦈`, the converse of `Tm.foldUP_den`: `⦇[e,S]⦈` satisfies its own defining equation
    (`α ≫ ⦇R⦈ = F(⦇R⦈) ≫ R`, read through `α° `). -/
theorem Tm.fold_cancel_den {E V : Obj} {e : Tm .one V} {S : Tm (.prod V E) V} (ρ : Val) :
    (Tm.fold (Tm.ran e) S).den ρ = (Tm.join (.comp (Tm.closedNil E).conv e)
      (.comp (.comp (.prim (rowOf "unsnoc")) (.pair (.comp .outl (Tm.fold (Tm.ran e) S)) (.comp .outr .id))) S)).den ρ := by
  have h := ((foldUP (E := E) (V := V) ((Tm.ran e).den ρ) (S.den ρ) _).2 rfl)
  simpa only [foldStep, ↓foldSeed_den, ↓pairComp_den, Tm.den, Prim.den_unsnoc, Core.Rel.comp_assoc] using h

theorem rprodMap_comp_id {α β γ δ : Type} (A : Core.Rel α β) (T : Core.Rel β γ) :
    Core.Rel.rprodMap A (𝟙 δ) ≫ Core.Rel.rprodMap T (𝟙 δ) = Core.Rel.rprodMap (A ≫ T) (𝟙 δ) :=
  Core.Rel.ext fun p q => by
    constructor
    · rintro ⟨r, ⟨h1, h2⟩, h3, h4⟩; exact ⟨⟨r.1, h1, h3⟩, h2.trans h4⟩
    · rintro ⟨⟨b, h1, h3⟩, h2⟩; exact ⟨(b, p.2), ⟨h1, rfl⟩, h3, h2⟩

/-- Fusion (B&dM 2.x, (5.14) at lists): `⦇[e,f]⦈ T = ⦇[e',g]⦈` when `[e,f] T = (𝟙+T×𝟙) [e',g]`. -/
theorem Tm.fold_fusion_den {E V W : Obj} {e : Tm .one V} {f : Tm (.prod V E) V} {e' : Tm .one W}
    {g : Tm (.prod W E) W} {T : Tm V W} (ρ : Val) (he : (Tm.comp e T).den ρ = e'.den ρ)
    (hf : (Tm.comp f T).den ρ = (Tm.comp (Tm.pair (.comp .outl T) (.comp .outr .id)) g).den ρ) :
    (Tm.comp (Tm.fold (Tm.ran e) f) T).den ρ = (Tm.fold (Tm.ran e') g).den ρ := by
  refine Tm.foldUP_den (X := Tm.comp (Tm.fold (Tm.ran e) f) T) ρ ?_
  refine (congrArg (· ≫ T.den ρ) (Tm.fold_cancel_den (e := e) (S := f) ρ)).trans ?_
  have hf' : f.den ρ ≫ T.den ρ = rprodMap (T.den ρ) (𝟙 _) ≫ g.den ρ := by
    have h : f.den ρ ≫ T.den ρ = (Tm.pair (.comp .outl T) (.comp .outr .id)).den ρ ≫ g.den ρ := hf
    rw [pairComp_den] at h; exact h
  simp only [↓pairComp_den, Tm.den, Core.Rel.union_comp, Core.Rel.comp_assoc] at he ⊢
  rw [hf', he, ← Core.Rel.comp_assoc (rprodMap _ _), rprodMap_comp_id]

end Rel.Lang
