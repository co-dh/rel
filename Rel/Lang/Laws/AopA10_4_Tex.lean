import Rel.Lang.Laws.Map
import Rel.Lang.Laws.FoldUP
import Rel.Lang.PreludeOplus
import Rel.Lang.PreludeRows

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

/-- `F(X) = 𝟙 ⊕ (𝟙×X)` of the functor `1 + E×−`, as the elaborator builds it: the prelude `⊕` called on `𝟙` and `⟨π₁𝟙,π₂X⟩`. -/
abbrev Tm.texF {E A : Obj} (k : Nat) (cv : Option Lean.Name) (os : List Obj) (X : Tm A (.arr E)) :
    Tm (.sum .one (.prod E A)) (.sum .one (.prod E (.arr E))) :=
  (Tm.arg (Tm.arg (Tm.call [k, k + 1] `«_⊕_» cv os (Tm.oplusDef k (k + 1) .one .one (.prod E A) (.prod E (.arr E)))) (Tm.id : Tm .one .one))
    ((Tm.outl.comp (Tm.id : Tm E E)).pair (Tm.outr.comp X)))

/-- `inl° ⊤ inr ∪ 𝟙` on `1 + E×A`: `⊤` as the elaborator builds it, `top ⟨π₁𝟙,π₂𝟙⟩`. -/
abbrev Tm.texL {E A : Obj} : Tm (.sum .one (.prod E A)) (.sum .one (.prod E A)) :=
  ((Tm.inl.conv.comp (Tm.top ((Tm.outl.comp Tm.id).pair (Tm.outr.comp Tm.id) : Tm (.prod E A) (.prod E A)))).comp
    Tm.inr).join Tm.id

/-- The algebra `[nil, cons]` of lists, `1 + E×[E] ⟶ [E]`. -/
abbrev Tm.texAlg {E : Obj} : Tm (.sum .one (.prod E (.arr E))) (.arr E) :=
  (Tm.inl.conv.comp (Tm.prim (rowOf "nil"))).join (Tm.inr.conv.comp (Tm.prim (rowOf "cons")))

/-- **Greedy** (`tex_greedy`): `(inl° ⊤ inr ∪ 𝟙) F(X) [nil,cons] ⊑ F(X) [nil,cons] R` when `𝟙 ⊑ R` and `nil ⊤ ⊑ nil R`. -/
theorem Tm.texGreedy_den {E E' A : Obj} {k k' : Nat} {cv cv' : Option Lean.Name}
    {os os' : List Obj} {U : Vals .one (USize.ofNat 1)} {h : Tm .one .one = Tm .one .one} (ρ : Val)
    (hid : (Tm.id : Tm (.arr E) (.arr E)).den ρ ⊑ (Tm.var 1 : Tm (.arr E) (.arr E)).den ρ)
    (hnil : ((cast h (Tm.uni U)).comp ((Tm.prim (rowOf "nil") : Tm .one (.arr E')).comp (Tm.top (Tm.id : Tm (.arr E) (.arr E)) : Tm (.arr E') (.arr E)))).den ρ ⊑
      ((cast h (Tm.uni U)).comp ((Tm.prim (rowOf "nil") : Tm .one (.arr E)).comp
        (Tm.var 1 : Tm (.arr E) (.arr E)))).den ρ) :
    (((Tm.texL (E := E) (A := A)).comp (Tm.texF k cv os (Tm.var 0))).comp Tm.texAlg).den ρ ⊑
    (((Tm.texF k' cv' os' (Tm.var 0)).comp Tm.texAlg).comp (Tm.var 1)).den ρ := by
  rw [Tm.uni_cast_comp_den U (by simp) rfl h, Tm.uni_cast_comp_den U (by simp) rfl h] at hnil
  refine Core.Rel.le_iff.2 fun x z hx => ?_
  simp only [Tm.den, Core.Rel.comp, Core.Rel.union, Core.Rel.recip, Core.Rel.inl, Core.Rel.inr, Core.Rel.graph,
    Core.Rel.top, Core.Rel.id, Core.Rel.rpair, Tm.oplusCall_den (by omega : k + 1 ≠ k),
    Tm.oplusCall_den (by omega : k' + 1 ≠ k'), Prim.den_cons] at hx ⊢
  have hn : ∀ {B : Obj} (a b), (rowOf "nil").den Obj.one B.arr [] a b ↔ b = [] := fun a b => by
    rw [show rowOf "nil" = nilRow from rfl, Prim.den_nilRow]; simp [nilDen, Core.Rel.graph]
  have hR : ∀ z, ρ 1 E.arr E.arr [] z := fun z => by
    have := Core.Rel.le_iff.1 hnil ⟨⟩ z
    simp only [Tm.den, Core.Rel.comp, Core.Rel.top, Core.Rel.id, hn] at this
    obtain ⟨b, rfl, h⟩ := this ⟨[], rfl, z, trivial, rfl⟩
    exact h
  obtain ⟨w, ⟨y, hy, hF⟩, hw⟩ := hx
  rcases hy with ⟨c, ⟨u, rfl, -⟩, rfl⟩ | rfl
  · exact ⟨[], ⟨Sum.inl u, Or.inl ⟨u, u, rfl, rfl, trivial⟩, Or.inl ⟨u, rfl, (hn _ _).2 rfl⟩⟩, hR z⟩
  · exact ⟨z, ⟨w, hF, hw⟩, Core.Rel.le_iff.1 hid z z rfl⟩

end Rel.Lang
