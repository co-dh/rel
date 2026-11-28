import Rel.Lang.Laws.Map
import Rel.Lang.PreludeRows
import Rel.Lang.Laws.Cylinder

/-! # The list type functor `F(R)` of B&dM §2.7 (`AOP/A5_5_TypeFunctor.lean`), on the concrete core

`F(R) : [A] ⟶ [B]` is `mapDen (R.den ρ)`: equal lengths, related elementwise (`Rel.Lang.mapDen_iff`).
`Rel/Programs/Aop/A5_5_TypeFunctor.lean` states each law as `theorem <name> … by Rel.Lang.Tm.<name>_den`. -/

namespace Rel.Lang
open Tab Rel.Rep
open scoped Rel.Core.Rel
open Rel.Core.Rel hiding id comp recip inter union zero le inl inr junc

theorem Tm.fmap_den (ρ : Val) {A B : Obj} (R : Tm A B) :
    (Tm.arg (Tm.prim mapRow : Tm (.arr A) (.arr B)) R).den ρ = mapDen (R.den ρ) := by
  simp only [Tm.den, Tm.argDen]; exact Prim.den_mapRow _

theorem mapDen_id (A : Obj) : mapDen (𝟙 (Obj.El A)) = 𝟙 (Obj.El (.arr A)) :=
  Core.Rel.ext fun xs ys => by
    rw [mapDen_iff]
    constructor
    · rintro ⟨hl, h⟩
      exact List.ext_getElem hl.symm fun t h1 h2 => h t h1 h2
    · rintro (rfl : xs = ys); exact ⟨rfl, fun t _ _ => rfl⟩

theorem mapDen_recip {A B : Obj} (T : Core.Rel (Obj.El A) (Obj.El B)) : (mapDen T)° = mapDen T° :=
  Core.Rel.ext fun ys xs => by
    show mapDen T xs ys ↔ mapDen T° ys xs; rw [mapDen_iff, mapDen_iff]; exact ⟨fun ⟨hl, h⟩ => ⟨hl.symm, fun t h1 h2 => h t h2 h1⟩,
      fun ⟨hl, h⟩ => ⟨hl.symm, fun t h1 h2 => h t h2 h1⟩⟩

theorem Tm.fmap_id_den {A : Obj} (ρ : Val) :
    (Tm.arg (Tm.prim mapRow : Tm (.arr A) (.arr A)) (Tm.id (A := A))).den ρ = (Tm.id (A := .arr A)).den ρ := by
  rw [Tm.fmap_den]; exact mapDen_id A

theorem Tm.fmap_comp_den {A B C : Obj} {R : Tm A B} {S : Tm B C} (ρ : Val) :
    (Tm.comp (Tm.arg (Tm.prim mapRow : Tm (.arr A) (.arr B)) R) (Tm.arg (Tm.prim mapRow : Tm (.arr B) (.arr C)) S)).den ρ =
      (Tm.arg (Tm.prim mapRow : Tm (.arr A) (.arr C)) (Tm.comp R S)).den ρ := by
  show (Tm.arg (Tm.prim mapRow : Tm (.arr A) (.arr B)) R).den ρ ≫ (Tm.arg (Tm.prim mapRow : Tm (.arr B) (.arr C)) S).den ρ =
    (Tm.arg (Tm.prim mapRow : Tm (.arr A) (.arr C)) (Tm.comp R S)).den ρ
  rw [Tm.fmap_den, Tm.fmap_den, Tm.fmap_den]; exact mapDen_comp _ _

theorem Tm.fmap_recip_den {A B : Obj} {R : Tm A B} (ρ : Val) :
    (Tm.conv (Tm.comp Tm.id (Tm.arg (Tm.prim mapRow : Tm (.arr A) (.arr B)) R))).den ρ =
      (Tm.arg (Tm.prim mapRow : Tm (.arr B) (.arr A)) (Tm.conv R)).den ρ := by
  show ((𝟙 _ ≫ (Tm.arg (Tm.prim mapRow : Tm (.arr A) (.arr B)) R).den ρ))° = (Tm.arg (Tm.prim mapRow : Tm (.arr B) (.arr A)) (Tm.conv R)).den ρ
  rw [Tm.fmap_den, Tm.fmap_den, Core.Rel.id_comp]; exact mapDen_recip _


theorem mapDen_snoc {A B : Obj} (T : Core.Rel (Obj.El A) (Obj.El B)) (xs : List A.El) (x : A.El) (zs : List B.El) :
    mapDen T (xs ++ [x]) zs ↔ ∃ ws y, zs = ws ++ [y] ∧ mapDen T xs ws ∧ T x y := by
  unfold mapDen; rw [foldDen_snoc]
  simp only [Core.Rel.comp, Core.Rel.rpair, Core.Rel.graph]
  constructor
  · rintro ⟨u, hu, ⟨p1, p2⟩, ⟨h1, c, h2, h3⟩, rfl⟩
    cases h1; cases h2; exact ⟨_, p2, rfl, hu, h3⟩
  · rintro ⟨ws, y, rfl, hw, hy⟩; exact ⟨ws, hw, (ws, y), ⟨rfl, x, rfl, hy⟩, rfl⟩

/-- Type functor fusion (2.14) on lists: `F(T) ⦇Te,TS⦈ = ⦇Te, ⟨π₁, π₂ T⟩ TS⦈`. -/
theorem mapDen_foldDen {A B V : Obj} (T : Core.Rel (Obj.El A) (Obj.El B)) (Te : Core.Rel (Obj.El V) (Obj.El V))
    (TS : Core.Rel (Obj.El (.prod V B)) (Obj.El V)) :
    mapDen T ≫ foldDen Te TS = foldDen Te (Core.Rel.rpair (Core.Rel.graph Prod.fst ≫ 𝟙 _) (Core.Rel.graph Prod.snd ≫ T) ≫ TS) := by
  refine Core.Rel.ext fun xs w => ?_
  induction h : xs.length generalizing xs w with
  | zero =>
    obtain rfl := List.length_eq_zero_iff.1 h
    rw [foldDen_empty]
    constructor
    · rintro ⟨ys, h, hf⟩
      obtain ⟨hl, -⟩ := (mapDen_iff _ _ _).1 h
      obtain rfl := List.length_eq_zero_iff.1 hl
      exact (foldDen_empty _ _ _).1 hf
    · intro h; exact ⟨[], (mapDen_iff _ _ _).2 ⟨rfl, fun t ht => absurd ht (by simp)⟩, (foldDen_empty _ _ _).2 h⟩
  | succ n ih =>
    obtain ⟨xs, x, rfl⟩ := List.eq_nil_or_concat xs |>.resolve_left (by rintro rfl; simp at h)
    rw [List.concat_eq_append] at *
    have ih := fun w => ih xs w (by simpa using h)
    rw [foldDen_snoc]
    simp only [Core.Rel.comp, Core.Rel.rpair, Core.Rel.graph, Core.Rel.id] at ih ⊢
    constructor
    · rintro ⟨ys', h, hf⟩
      obtain ⟨ws, y, rfl, hw, hy⟩ := (mapDen_snoc _ _ _ _).1 h
      obtain ⟨u, hu, hs⟩ := (foldDen_snoc _ _ _ _ _).1 hf
      exact ⟨u, (ih u).1 ⟨ws, hw, hu⟩, (u, y), ⟨⟨u, rfl, rfl⟩, ⟨x, rfl, hy⟩⟩, hs⟩
    · rintro ⟨u, hu, ⟨a, y⟩, ⟨⟨c, rfl, rfl⟩, ⟨c', rfl, hy⟩⟩, hs⟩
      obtain ⟨ws, hw, hu'⟩ := (ih _).2 hu
      exact ⟨ws ++ [y], (mapDen_snoc _ _ _ _).2 ⟨ws, y, rfl, hw, hy⟩, (foldDen_snoc _ _ _ _ _).2 ⟨_, hu', hs⟩⟩

theorem Tm.fmap_fold_den {A B V : Obj} {f : Tm A B} {e : Tm .one V} {S : Tm (.prod V B) V} (ρ : Val) :
    (Tm.comp (Tm.arg (Tm.prim mapRow : Tm (.arr A) (.arr B)) f) (Tm.fold (Tm.ran e) S)).den ρ =
      (Tm.fold (Tm.ran e) (Tm.comp (Tm.pair (Tm.comp Tm.outl Tm.id) (Tm.comp Tm.outr f)) S)).den ρ := by
  show (Tm.arg (Tm.prim mapRow : Tm (.arr A) (.arr B)) f).den ρ ≫ foldDen ((Tm.ran e).den ρ) (S.den ρ) = _
  rw [Tm.fmap_den]; exact mapDen_foldDen _ _ _

theorem Tm.fmap_nil_den {X A B : Obj} {U : Tm X X} {f : Tm A B} (ρ : Val) :
    (Tm.comp (U.comp (Tm.nil : Tm X (.arr A))) (Tm.arg (Tm.prim mapRow : Tm (.arr A) (.arr B)) f)).den ρ =
      (U.comp (Tm.nil : Tm X (.arr B))).den ρ := by
  show (U.den ρ ≫ Prim.den nilRow X (.arr A) []) ≫ (Tm.arg (Tm.prim mapRow : Tm (.arr A) (.arr B)) f).den ρ = U.den ρ ≫ Prim.den nilRow X (.arr B) []
  rw [Tm.fmap_den, Prim.den_nilRow, Prim.den_nilRow, Core.Rel.comp_assoc]; congr 1
  refine Core.Rel.ext fun x zs => ?_
  constructor
  · rintro ⟨ys, hy, h⟩
    have : ys = [] := by simpa [nilDen] using hy
    subst this
    simpa [nilDen] using (mapDen_iff _ _ _).1 h |>.1
  · intro h
    have : zs = [] := by simpa [nilDen] using h
    subst this
    exact ⟨[], rfl, (mapDen_iff _ _ _).2 ⟨rfl, fun t ht => absurd ht (by simp)⟩⟩

theorem Tm.fmap_snoc_den {A B : Obj} {f : Tm A B} (ρ : Val) :
    (Tm.comp (Tm.prim (rowOf "snoc") : Tm (.prod (.arr A) A) (.arr A)) (Tm.arg (Tm.prim mapRow : Tm (.arr A) (.arr B)) f)).den ρ =
      (Tm.comp (Tm.pair (Tm.comp Tm.outl (Tm.arg (Tm.prim mapRow : Tm (.arr A) (.arr B)) f)) (Tm.comp Tm.outr f))
        (Tm.prim (rowOf "snoc") : Tm (.prod (.arr B) B) (.arr B))).den ρ := by
  show Prim.den (rowOf "snoc") (.prod (.arr A) A) (.arr A) [] ≫ (Tm.arg (Tm.prim mapRow : Tm (.arr A) (.arr B)) f).den ρ =
    Core.Rel.rpair (Core.Rel.graph Prod.fst ≫ (Tm.arg (Tm.prim mapRow : Tm (.arr A) (.arr B)) f).den ρ)
      (Core.Rel.graph Prod.snd ≫ f.den ρ) ≫ Prim.den (rowOf "snoc") (.prod (.arr B) B) (.arr B) []
  rw [Tm.fmap_den, Prim.den_snoc, Prim.den_snoc]
  refine Core.Rel.ext fun p zs => ?_
  obtain ⟨xs, x⟩ := p
  simp only [Core.Rel.comp, Core.Rel.rpair, Core.Rel.graph]
  constructor
  · rintro ⟨ys, rfl, h⟩
    obtain ⟨ws, y, rfl, hw, hy⟩ := (mapDen_snoc _ _ _ _).1 h
    exact ⟨(ws, y), ⟨⟨xs, rfl, hw⟩, ⟨x, rfl, hy⟩⟩, rfl⟩
  · rintro ⟨⟨ws, y⟩, ⟨⟨c, rfl, hw⟩, ⟨c', rfl, hy⟩⟩, rfl⟩
    exact ⟨_, rfl, (mapDen_snoc _ _ _ _).2 ⟨ws, y, rfl, hw, hy⟩⟩

end Rel.Lang
