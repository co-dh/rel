module

public import Rel.Lang.Den
public import Rel.Lang.PreludeRows

public section

namespace Rel.Lang
open Rel.Kernel Tab Rel.Rep
open scoped Rel.Core.Rel
open Rel.Core.Rel hiding id comp recip inter union zero le inl inr junc

/-- B&dM (5.12), the fold's universal property on arrays: `foldStep` has the one fixed point `foldDen`.
    Any fixed point `X` meets `foldDen_empty`/`foldDen_snoc`'s equations, so it agrees with `foldDen` by length. -/
theorem foldUP {E V : Obj} (Te : Core.Rel (Obj.El V) (Obj.El V)) (TS : Core.Rel (Obj.El (.prod V E)) (Obj.El V))
    (X : Core.Rel (Obj.El (.arr E)) (Obj.El V)) : X = foldStep Te TS X ↔ X = foldDen Te TS := by
  refine ⟨fun hX => ?_, fun hX => hX ▸ (mu_fix (foldStep_mono Te TS)).symm⟩
  have Xe (w : V.El) : X [] w ↔ ∃ a, Te a w := by
    refine (Iff.of_eq (congrFun (congrFun hX _) _)).trans ?_
    simp only [foldStep, Core.Rel.union_apply, Core.Rel.comp_apply, Core.Rel.corefl, Core.Rel.inter_apply, Core.Rel.id,
      Core.Rel.top, Core.Rel.recip, Core.Rel.graph, Core.Rel.rprodMap]
    constructor
    · rintro (⟨_, ⟨-, -⟩, _, -, rfl, e, he, -⟩ | ⟨p, hp, -⟩)
      · exact ⟨e, he⟩
      · exact absurd (List.append_eq_nil_iff.1 hp.symm).2 (List.cons_ne_nil _ _)
    · rintro ⟨a, ha⟩
      exact Or.inl ⟨[], ⟨rfl, trivial⟩, w, trivial, rfl, a, ha, trivial⟩
  have Xs (xs : List E.El) (x : E.El) (w : V.El) : X (xs ++ [x]) w ↔ ∃ u, X xs u ∧ TS (u, x) w := by
    refine (Iff.of_eq (congrFun (congrFun hX _) _)).trans ?_
    simp only [foldStep, Core.Rel.union_apply, Core.Rel.comp_apply, Core.Rel.corefl, Core.Rel.recip, Core.Rel.graph,
      Core.Rel.rprodMap, Core.Rel.id]
    constructor
    · rintro (⟨_, ⟨-, h⟩, -⟩ | ⟨⟨ys, y⟩, hp, ⟨u, z⟩, ⟨hu, hz⟩, hS⟩)
      · exact absurd (List.append_eq_nil_iff.1 h.symm).2 (List.cons_ne_nil _ _)
      · obtain ⟨rfl, h⟩ := List.append_inj' hp rfl
        obtain rfl := (List.cons.inj h).1
        obtain rfl := hz
        exact ⟨u, hu, hS⟩
    · rintro ⟨u, hu, hS⟩
      exact Or.inr ⟨(xs, x), rfl, (u, x), ⟨hu, rfl⟩, hS⟩
  funext xs w
  refine propext ?_
  induction h : xs.length generalizing xs w with
  | zero => obtain rfl := List.length_eq_zero_iff.1 h; exact (Xe w).trans (foldDen_empty Te TS w).symm
  | succ n ih =>
    obtain ⟨L, x, rfl⟩ := List.eq_nil_or_concat xs |>.resolve_left (by rintro rfl; simp at h)
    rw [List.concat_eq_append]
    exact (Xs L x w).trans (Iff.trans (exists_congr fun u => and_congr_left' (ih L u (by simpa using h)))
      (foldDen_snoc Te TS L x w).symm)

/-- Universal property of `fold(e, S)` over `[nil, cons]`: `foldrStep` has the one fixed point `foldrDen`. -/
theorem foldrUP {E V : Obj} (Te : Core.Rel (Obj.El V) (Obj.El V)) (TS : Core.Rel (Obj.El (.prod E V)) (Obj.El V))
    (X : Core.Rel (Obj.El (.arr E)) (Obj.El V)) : X = foldrStep Te TS X ↔ X = foldrDen Te TS := by
  refine ⟨fun hX => ?_, fun hX => hX ▸ (mu_fix (foldrStep_mono Te TS)).symm⟩
  have Xe (w : V.El) : X [] w ↔ ∃ a, Te a w := by
    refine (Iff.of_eq (congrFun (congrFun hX _) _)).trans ?_
    simp only [foldrStep, Core.Rel.union_apply, Core.Rel.comp_apply, Core.Rel.corefl, Core.Rel.inter_apply, Core.Rel.id,
      Core.Rel.top, Core.Rel.recip, Core.Rel.graph, Core.Rel.rprodMap]
    constructor
    · rintro (⟨_, ⟨-, -⟩, _, -, rfl, e, he, -⟩ | ⟨p, hp, -⟩)
      · exact ⟨e, he⟩
      · exact absurd hp.symm (List.cons_ne_nil _ _)
    · rintro ⟨a, ha⟩
      exact Or.inl ⟨[], ⟨rfl, trivial⟩, w, trivial, rfl, a, ha, trivial⟩
  have Xc (x : E.El) (xs : List E.El) (w : V.El) : X (x :: xs) w ↔ ∃ u, X xs u ∧ TS (x, u) w := by
    refine (Iff.of_eq (congrFun (congrFun hX _) _)).trans ?_
    simp only [foldrStep, Core.Rel.union_apply, Core.Rel.comp_apply, Core.Rel.corefl, Core.Rel.recip, Core.Rel.graph,
      Core.Rel.rprodMap, Core.Rel.id]
    constructor
    · rintro (⟨_, ⟨-, h⟩, -⟩ | ⟨⟨y, ys⟩, hp, ⟨z, u⟩, ⟨hz, hu⟩, hS⟩)
      · exact absurd h.symm (List.cons_ne_nil _ _)
      · obtain ⟨rfl, rfl⟩ := List.cons.inj hp
        obtain rfl := hz
        exact ⟨u, hu, hS⟩
    · rintro ⟨u, hu, hS⟩
      exact Or.inr ⟨(x, xs), rfl, (x, u), ⟨rfl, hu⟩, hS⟩
  funext xs w
  refine propext ?_
  induction xs generalizing w with
  | nil => exact (Xe w).trans (foldrDen_empty Te TS w).symm
  | cons x xs ih =>
    exact (Xc x xs w).trans (Iff.trans (exists_congr fun u => and_congr_left' (ih u)) (foldrDen_cons Te TS x xs w).symm)

/-- `nil` closed over the singleton source universe, as built before taking its converse. -/
abbrev Tm.closedNil (E : Obj) : Tm .one (.arr E) :=
  .comp (.uni (Gen.oneV false 1).1) .nil

private theorem foldSeed_den {E V : Obj} (ρ : Val) (e : Tm .one V) :
    (Tm.comp (Tm.closedNil E).conv e).den ρ =
      corefl (Eq ([] : List E.El)) ≫ top ≫ (𝟙 _ ∩ ((Tm.ran e).den ρ)° ≫ top) := by
  have hnil : (Tm.closedNil E).den ρ = nilDen (A := .one) (B := E) := by
    funext u xs
    apply propext
    simp only [Tm.nil, Tm.den, Prim.den_nilRow, nilDen, Core.Rel.comp, Core.Rel.recip, Core.Rel.graph]
    constructor
    · rintro ⟨_, _, h⟩
      exact h
    · intro h
      exact ⟨(), ⟨⟨0, by simp⟩, trivial, trivial⟩, h⟩
  change ((Tm.closedNil E).den ρ)° ≫ e.den ρ = _
  rw [hnil, Tm.ran_den]
  funext xs w
  apply propext
  constructor
  · rintro ⟨u, rfl, h⟩
    exact ⟨[], ⟨rfl, rfl⟩, w, trivial, rfl, w, ⟨rfl, u, h, h⟩, trivial⟩
  · rintro ⟨_, ⟨rfl, rfl⟩, _, _, rfl, _, ⟨rfl, u, hu, _⟩, _⟩
    exact ⟨u, rfl, hu⟩

private theorem pairComp_den {A B C D : Obj} (ρ : Val) (R : Tm A C) (S : Tm B D) :
    (Tm.pair (.comp .outl R) (.comp .outr S)).den ρ = rprodMap (R.den ρ) (S.den ρ) := by
  funext p q
  simp [Tm.den, rpair, rprodMap, Core.Rel.comp, graph]

/-- The denotation of the prelude's left fold equation is the fixed-point premise of `foldUP`. -/
theorem Tm.foldUP_den {E V : Obj} {e : Tm .one V} {S : Tm (.prod V E) V} {X : Tm (.arr E) V}
    (ρ : Val)
    (h : X.den ρ = (Tm.join (.comp (Tm.closedNil E).conv e)
      (.comp (.comp (.prim (rowOf "unsnoc")) (.pair (.comp .outl X) (.comp .outr .id))) S)).den ρ) :
    X.den ρ = (Tm.fold (Tm.ran e) S).den ρ := by
  refine (foldUP (E := E) (V := V) ((Tm.ran e).den ρ) (S.den ρ) (X.den ρ)).1 ?_
  simpa only [foldStep, ↓foldSeed_den, ↓pairComp_den, Tm.den, Prim.den_unsnoc, Core.Rel.comp_assoc] using h

/-- The denotation of the prelude's right fold equation is the fixed-point premise of `foldrUP`. -/
theorem Tm.foldrUP_den {E V : Obj} {e : Tm .one V} {S : Tm (.prod E V) V} {X : Tm (.arr E) V}
    (ρ : Val)
    (h : X.den ρ = (Tm.join (.comp (Tm.closedNil E).conv e)
      (.comp (.comp (.prim (rowOf "uncons")) (.pair (.comp .outl .id) (.comp .outr X))) S)).den ρ) :
    X.den ρ = (Tm.foldr (Tm.ran e) S).den ρ := by
  refine (foldrUP (E := E) (V := V) ((Tm.ran e).den ρ) (S.den ρ) (X.den ρ)).1 ?_
  simpa only [foldrStep, ↓foldSeed_den, ↓pairComp_den, Tm.den, Prim.den_uncons, Core.Rel.comp_assoc] using h

end Rel.Lang
