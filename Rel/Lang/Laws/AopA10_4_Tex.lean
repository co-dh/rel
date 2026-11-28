import Rel.Lang.Laws.Map
import Rel.Lang.Laws.FoldUP

/-! # Laws of freyd §10.4 `AOP/A10_4_Tex.lean`, on the concrete core

`Rel.Lang.Tm.<name>_den` is the law of the freyd declaration `<name>` read off `Tm.den`; `Rel/Programs/Aop/A10_4_Tex.lean`
states it as `theorem <name> … by Rel.Lang.Tm.<name>_den`. -/

namespace Rel.Lang
open Tab Rel.Rep
open scoped Rel.Core.Rel
open Rel.Core.Rel hiding id comp recip inter union zero le inl inr junc

/-- Fusion of a right fold into a fold (B&dM p.260): a seed of the first fold is `R` of a seed of the second, and a step
    of the first from an `R`-image is `R` of a step of the second, so each value of the first fold is `R` of the second's. -/
theorem foldrDen_fusion {E V W : Obj} {Te : Core.Rel (Obj.El V) (Obj.El V)} {TS : Core.Rel (Obj.El (.prod E V)) (Obj.El V)}
    {Te' : Core.Rel (Obj.El W) (Obj.El W)} {TS' : Core.Rel (Obj.El (.prod E W)) (Obj.El W)} {R : Core.Rel (Obj.El W) (Obj.El V)}
    (he : ∀ v, (∃ a, Te a v) → ∃ w, (∃ a, Te' a w) ∧ R w v)
    (hS : ∀ x w u v, R w u → TS (x, u) v → ∃ w', TS' (x, w) w' ∧ R w' v) :
    ∀ (xs : List E.El) v, foldrDen Te TS xs v → ∃ w, foldrDen Te' TS' xs w ∧ R w v
  | [], v, h => by
    obtain ⟨w, hw, hR⟩ := he v ((foldrDen_empty Te TS v).1 h)
    exact ⟨w, (foldrDen_empty Te' TS' w).2 hw, hR⟩
  | x :: xs, v, h => by
    obtain ⟨u, hu, hs⟩ := (foldrDen_cons Te TS x xs v).1 h
    obtain ⟨w, hw, hR⟩ := foldrDen_fusion he hS xs u hu
    obtain ⟨w', hs', hR'⟩ := hS x w u v hR hs
    exact ⟨w', (foldrDen_cons Te' TS' x xs w').2 ⟨w, hw, hs'⟩, hR'⟩

/-- `ran(e)` as a seed: `ran(e) a w` iff `a = w` and `w` is an image of `e`. -/
theorem ranArg_den {A B : Obj} (ρ : Val) (e : Tm A B) (a w : Obj.El B) :
    ((Tm.prim ranRow).arg e).den ρ a w ↔ a = w ∧ ∃ m, e.den ρ m a := by
  show Prim.den ranRow _ _ [⟨_, _, e.den ρ⟩] a w ↔ _
  rw [Prim.den_ranRow]
  simp only [Core.Rel.inter, Core.Rel.id, Core.Rel.comp, Core.Rel.recip]
  constructor
  · rintro ⟨rfl, m, h, -⟩; exact ⟨rfl, m, h⟩
  · rintro ⟨rfl, m, h⟩; exact ⟨rfl, m, h, h⟩

/-- Fusion of a fold into a fold: `⦇[e,S]⦈ʳ ⊑ ⦇[e',S']⦈ʳ R` when `e ⊑ e' R` and `⟨π₁,π₂R⟩S ⊑ S' R`. -/
theorem Tm.tex_fusion_den {O D B C : Obj} {e : Tm O B} {S : Tm (.prod D B) B} {e' : Tm O C} {S' : Tm (.prod D C) C}
    {R : Tm C B} (ρ : Val) (he : e.den ρ ⊑ (Tm.comp e' R).den ρ)
    (hS : (Tm.comp (Tm.pair Tm.outl (Tm.comp Tm.outr R)) S).den ρ ⊑ (Tm.comp S' R).den ρ) :
    (Tm.foldr ((Tm.prim ranRow).arg e) S).den ρ ⊑ (Tm.comp (Tm.foldr ((Tm.prim ranRow).arg e') S') R).den ρ := by
  refine Core.Rel.le_iff.2 fun xs v h => ?_
  simp only [Tm.den, Core.Rel.comp] at h hS ⊢
  refine foldrDen_fusion (R := R.den ρ) ?_ ?_ xs v h
  · rintro v ⟨a, ha⟩
    obtain ⟨rfl, m, hm⟩ := (ranArg_den ρ e a v).1 ha
    obtain ⟨w, hw, hR⟩ := Core.Rel.le_iff.1 he m a hm
    exact ⟨w, ⟨w, (ranArg_den ρ e' w w).2 ⟨rfl, m, hw⟩⟩, hR⟩
  · intro x w u v hR hs
    have hp : (Tm.pair Tm.outl (Tm.comp Tm.outr R)).den ρ (x, w) (x, u) := by
      simp only [Tm.den]
      exact ⟨rfl, w, rfl, hR⟩
    obtain ⟨w', hw', hR'⟩ := Core.Rel.le_iff.1 hS (x, w) v ⟨(x, u), hp, hs⟩
    exact ⟨w', hw', hR'⟩

/-- The fusion condition `F(R)[e,S] ⊑ [e',S'] R` from its two branches. -/
theorem Tm.tex_fusion_condition_den {O D B C : Obj} {e : Tm O B} {S : Tm (.prod D B) B} {e' : Tm O C} {S' : Tm (.prod D C) C}
    {R : Tm C B} (ρ : Val) (he : e.den ρ ⊑ (Tm.comp e' R).den ρ)
    (hS : (Tm.comp (Tm.pair Tm.outl (Tm.comp Tm.outr R)) S).den ρ ⊑ (Tm.comp S' R).den ρ) :
    (Tm.join (Tm.comp Tm.inl.conv e) (Tm.comp Tm.inr.conv (Tm.comp (Tm.pair Tm.outl (Tm.comp Tm.outr R)) S))).den ρ ⊑
      (Tm.comp (Tm.join (Tm.comp Tm.inl.conv e') (Tm.comp Tm.inr.conv S')) R).den ρ := by
  refine Core.Rel.le_iff.2 fun a b h => ?_
  simp only [Tm.den, Core.Rel.union, Core.Rel.comp, Core.Rel.recip, Core.Rel.inl, Core.Rel.inr] at h hS he ⊢
  rcases h with ⟨m, hm, hb⟩ | ⟨m, hm, hb⟩
  · obtain ⟨c, hc, hR⟩ := Core.Rel.le_iff.1 he m b hb
    exact ⟨c, Or.inl ⟨m, hm, hc⟩, hR⟩
  · obtain ⟨c, hc, hR⟩ := Core.Rel.le_iff.1 hS m b hb
    exact ⟨c, Or.inr ⟨m, hm, hc⟩, hR⟩

end Rel.Lang
