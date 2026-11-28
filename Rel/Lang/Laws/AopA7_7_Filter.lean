import Rel.Lang.Laws.AopA10_4_Tex
import Rel.Lang.Laws.AopA5_5_TypeFunctor

/-! # Laws of freyd `AOP/A7_7_Filter.lean` (B&dM Ex 7.41), at the list datatype, on the concrete core

freyd's `α subseq list(p) = F(subseq list(p)) S` with `S = [nil, (p×𝟙)cons ∪ π₂]` is `X = nil°nil ∪ cons°(𝟙×X)S'` for
`X = subseq F(p)` and `S' = ⟨π₁p, π₂⟩cons ∪ π₂`, the premise of `foldrUP`. `subseq = ⦇[nil, cons ∪ π₂]⦈ʳ` is freyd's
`subseq` on cons lists. `Rel/Programs/Aop/A7_7_Filter.lean` states each law as `theorem <name> … by Rel.Lang.Tm.<name>_den`. -/

namespace Rel.Lang
open Tab Rel.Rep
open scoped Rel.Core.Rel
open Rel.Core.Rel hiding id comp recip inter union zero le inl inr junc

/-- One unfolding of the right fold at `[]`: the seed. -/
theorem filtStepNil {E V : Obj} (Te : Core.Rel (Obj.El V) (Obj.El V)) (TS : Core.Rel (Obj.El (.prod E V)) (Obj.El V))
    (X : Core.Rel (Obj.El (.arr E)) (Obj.El V)) (w : V.El) : foldrStep Te TS X [] w ↔ ∃ a, Te a w := by
  simp only [foldrStep, Core.Rel.union_apply, Core.Rel.comp_apply, Core.Rel.corefl, Core.Rel.inter_apply, Core.Rel.id,
    Core.Rel.top, Core.Rel.recip, Core.Rel.graph, Core.Rel.rprodMap]
  constructor
  · rintro (⟨_, ⟨-, -⟩, _, -, rfl, e, he, -⟩ | ⟨p, hp, -⟩)
    · exact ⟨e, he⟩
    · exact absurd hp.symm (List.cons_ne_nil _ _)
  · rintro ⟨a, ha⟩
    exact Or.inl ⟨[], ⟨rfl, trivial⟩, w, trivial, rfl, a, ha, trivial⟩

/-- One unfolding of the right fold at `x :: xs`: the step. -/
theorem filtStepCons {E V : Obj} (Te : Core.Rel (Obj.El V) (Obj.El V)) (TS : Core.Rel (Obj.El (.prod E V)) (Obj.El V))
    (X : Core.Rel (Obj.El (.arr E)) (Obj.El V)) (x : E.El) (xs : List E.El) (w : V.El) :
    foldrStep Te TS X (x :: xs) w ↔ ∃ u, X xs u ∧ TS (x, u) w := by
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

theorem filtMapNil {A B : Obj} (T : Core.Rel (Obj.El A) (Obj.El B)) (w : List B.El) :
    mapDen T ([] : List A.El) w ↔ w = [] := by
  rw [mapDen_iff]
  constructor
  · rintro ⟨hl, -⟩; exact List.length_eq_zero_iff.1 (by simpa using hl)
  · rintro rfl; exact ⟨rfl, fun t ht => absurd ht (by simp)⟩

theorem filtMapCons {A B : Obj} (T : Core.Rel (Obj.El A) (Obj.El B)) (x : A.El) (xs : List A.El) (w : List B.El) :
    mapDen T (x :: xs) w ↔ ∃ a ws, w = a :: ws ∧ T x a ∧ mapDen T xs ws := by
  cases w with
  | nil =>
    rw [mapDen_iff]
    constructor
    · rintro ⟨hl, -⟩
      exact absurd hl (by simp)
    · rintro ⟨_, _, h, -⟩
      exact absurd h (by simp)
  | cons a ws =>
    rw [mapDen_iff]
    constructor
    · rintro ⟨hl, h⟩
      refine ⟨a, ws, rfl, h 0 (by simp) (by simp), (mapDen_iff _ _ _).2 ⟨by simpa using hl, fun t ht ht' => ?_⟩⟩
      simpa using h (t + 1) (by simpa using ht) (by simpa using ht')
    · rintro ⟨a', ws', h, hT, hm⟩
      obtain ⟨rfl, rfl⟩ := List.cons.inj h
      obtain ⟨hl, hm⟩ := (mapDen_iff _ _ _).1 hm
      refine ⟨by simpa using hl, fun t ht ht' => ?_⟩
      cases t with
      | zero => simpa using hT
      | succ t => simpa using hm t (by simpa using ht) (by simpa using ht')

/-- The fixed-point equation of `⦇[nil, cons ∪ π₂]⦈ʳ ≫ F(P)` at the step `⟨π₁P, π₂⟩cons ∪ π₂`, for any `P`: the
cons list `x :: xs` keeps its head (which `P` must relate to its image) or drops it. -/
theorem filtSubseq_fix {E : Obj} {P : Core.Rel E.El E.El} {Te Te' : Core.Rel (Obj.El (.arr E)) (Obj.El (.arr E))}
    {Ssub S' : Core.Rel (Obj.El (.prod E (.arr E))) (Obj.El (.arr E))}
    (hTe : ∀ v, (∃ a, Te a v) ↔ v = []) (hTe' : ∀ v, (∃ a, Te' a v) ↔ v = [])
    (hSub : ∀ x u v, Ssub (x, u) v ↔ v = x :: u ∨ v = u)
    (hS' : ∀ x u w, S' (x, u) w ↔ (∃ a, P x a ∧ w = a :: u) ∨ w = u) :
    foldrStep Te' S' (foldrDen Te Ssub ≫ mapDen P) = foldrDen Te Ssub ≫ mapDen P := by
  funext xs w
  refine propext ?_
  cases xs with
  | nil =>
    rw [filtStepNil, hTe']
    constructor
    · rintro rfl
      exact ⟨[], (foldrDen_empty Te Ssub []).2 ((hTe []).2 rfl), (filtMapNil P []).2 rfl⟩
    · rintro ⟨v, hv, hm⟩
      obtain rfl := (hTe v).1 ((foldrDen_empty Te Ssub v).1 hv)
      exact (filtMapNil P w).1 hm
  | cons x xs =>
    rw [filtStepCons]
    constructor
    · rintro ⟨u, ⟨v, hv, hm⟩, hS⟩
      rcases (hS' x u w).1 hS with ⟨a, hP, rfl⟩ | rfl
      · exact ⟨x :: v, (foldrDen_cons Te Ssub x xs _).2 ⟨v, hv, (hSub x v _).2 (Or.inl rfl)⟩,
          (filtMapCons P x v _).2 ⟨a, u, rfl, hP, hm⟩⟩
      · exact ⟨v, (foldrDen_cons Te Ssub x xs _).2 ⟨v, hv, (hSub x v _).2 (Or.inr rfl)⟩, hm⟩
    · rintro ⟨v, hv, hm⟩
      obtain ⟨y, hy, hS⟩ := (foldrDen_cons Te Ssub x xs v).1 hv
      rcases (hSub x y v).1 hS with rfl | rfl
      · obtain ⟨a, ws, rfl, hP, hws⟩ := (filtMapCons P x y w).1 hm
        exact ⟨ws, ⟨y, hy, hws⟩, (hS' x ws _).2 (Or.inl ⟨a, hP, rfl⟩)⟩
      · exact ⟨w, ⟨v, hy, hm⟩, (hS' x w w).2 (Or.inr rfl)⟩

/-- A seed `ran e` with `e` the one value `[]` reaches exactly `[]`. -/
theorem filtRanNil {E : Obj} (ρ : Val) (e : Tm .one (.arr E)) (he : ∀ m w, e.den ρ m w ↔ w = []) (v : List E.El) :
    (∃ a, (Tm.ran e).den ρ a v) ↔ v = [] := by
  constructor
  · rintro ⟨a, ha⟩
    obtain ⟨rfl, m, hm⟩ := (ranArg_den ρ e a v).1 ha
    exact (he m a).1 hm
  · rintro rfl
    exact ⟨[], (ranArg_den ρ e [] []).2 ⟨rfl, (), (he _ _).2 rfl⟩⟩

/-- freyd's `subseq` on cons lists, `⦇[nil, cons ∪ π₂]⦈ʳ`, as the program's `subseqC` elaborates. -/
abbrev Tm.subseqC (E : Obj) : Tm (.arr E) (.arr E) :=
  Tm.foldr (Tm.ran (Tm.closedNil E)) (Tm.join (Tm.prim (rowOf "cons")) Tm.outr)

/-- `⟨π₁ p, π₂⟩cons ∪ π₂`, the step of `subseq list(p)`. -/
abbrev Tm.filtStep {E : Obj} (p : Tm E E) : Tm (.prod E (.arr E)) (.arr E) :=
  Tm.join (Tm.comp (Tm.pair (Tm.comp Tm.outl p) Tm.outr) (Tm.prim (rowOf "cons"))) Tm.outr

theorem Tm.closedNil_iff {E : Obj} (ρ : Val) (m : Obj.El .one) (w : List E.El) : (Tm.closedNil E).den ρ m w ↔ w = [] := by
  rw [Tm.closedNil_den]; exact Iff.rfl

theorem Tm.nil_iff {E : Obj} (ρ : Val) (m : Obj.El .one) (w : List E.El) : (Tm.nil (A := .one) (B := E)).den ρ m w ↔ w = [] := by
  simp only [Tm.nil, Tm.den, Prim.den_nilRow]; exact Iff.rfl

theorem Tm.filtStep_iff {E : Obj} (ρ : Val) (p : Tm E E) (x : E.El) (u w : List E.El) :
    (Tm.filtStep p).den ρ (x, u) w ↔ (∃ a, p.den ρ x a ∧ w = a :: u) ∨ w = u := by
  simp only [Tm.den, Prim.den_cons, Core.Rel.union_apply, Core.Rel.comp_apply, Core.Rel.graph, rpair]
  constructor
  · rintro (⟨⟨a, u'⟩, ⟨⟨_, rfl, hp⟩, rfl⟩, rfl⟩ | h)
    · exact Or.inl ⟨a, hp, rfl⟩
    · exact Or.inr h
  · rintro (⟨a, hp, rfl⟩ | h)
    · exact Or.inl ⟨(a, u), ⟨⟨x, rfl, hp⟩, rfl⟩, rfl⟩
    · exact Or.inr h

theorem Tm.subseqStep_iff {E : Obj} (ρ : Val) (x : E.El) (u w : List E.El) :
    (Tm.join (Tm.prim (rowOf "cons")) Tm.outr : Tm (.prod E (.arr E)) (.arr E)).den ρ (x, u) w ↔ w = x :: u ∨ w = u := by
  simp only [Tm.den, Prim.den_cons, Core.Rel.union_apply, Core.Rel.graph]

/-- The fixed-point equation of `subseq F(p)` (`filter_alg_comm`), for any `p`: the premise of `foldrUP`. -/
theorem Tm.filterAlgComm_den {E : Obj} {p : Tm E E} (ρ : Val) :
    (Tm.comp (Tm.subseqC E) (Tm.arg (Tm.prim mapRow) p)).den ρ =
      (Tm.join (Tm.comp (Tm.closedNil E).conv Tm.nil)
        (Tm.comp (Tm.comp (Tm.prim (rowOf "uncons"))
          (Tm.pair (Tm.comp Tm.outl Tm.id) (Tm.comp Tm.outr (Tm.comp (Tm.subseqC E) (Tm.arg (Tm.prim mapRow) p)))))
          (Tm.filtStep p))).den ρ := by
  have h := filtSubseq_fix (E := E) (P := p.den ρ) (Te := (Tm.ran (Tm.closedNil E)).den ρ)
    (Te' := (Tm.ran Tm.nil).den ρ) (Ssub := (Tm.join (Tm.prim (rowOf "cons")) Tm.outr).den ρ) (S' := (Tm.filtStep p).den ρ)
    (filtRanNil ρ _ (Tm.closedNil_iff ρ)) (filtRanNil ρ _ (Tm.nil_iff ρ))
    (fun x u v => Tm.subseqStep_iff ρ x u v) (fun x u w => Tm.filtStep_iff ρ p x u w)
  simpa only [foldrStep, ↓foldSeed_den, ↓pairComp_den, Tm.subseqC, Tm.den, Tm.argDen, Prim.den_mapRow, Prim.den_uncons,
    Core.Rel.comp_assoc] using h.symm

/-- `subseq F(p) = ⦇[nil, ⟨π₁p, π₂⟩cons ∪ π₂]⦈ʳ` (`filter_alg`), by the universal property from the equation above. -/
theorem Tm.filterAlg_den {E : Obj} {p : Tm E E} (ρ : Val) :
    (Tm.comp (Tm.subseqC E) (Tm.arg (Tm.prim mapRow) p)).den ρ = (Tm.foldr (Tm.ran (Tm.closedNil E)) (Tm.filtStep p)).den ρ := by
  have h := filtSubseq_fix (E := E) (P := p.den ρ) (Te := (Tm.ran (Tm.closedNil E)).den ρ)
    (Te' := (Tm.ran (Tm.closedNil E)).den ρ) (Ssub := (Tm.join (Tm.prim (rowOf "cons")) Tm.outr).den ρ)
    (S' := (Tm.filtStep p).den ρ) (filtRanNil ρ _ (Tm.closedNil_iff ρ)) (filtRanNil ρ _ (Tm.closedNil_iff ρ))
    (fun x u v => Tm.subseqStep_iff ρ x u v) (fun x u w => Tm.filtStep_iff ρ p x u w)
  simpa only [Tm.subseqC, Tm.den, Tm.argDen, Prim.den_mapRow] using
    (foldrUP ((Tm.ran (Tm.closedNil E)).den ρ) ((Tm.filtStep p).den ρ) _).1 h.symm

/-- `⟨π₁, π₂Q⟩ = 𝟙×Q` on `α×[α]`, as the program elaborates it. -/
abbrev Tm.keepFst {E : Obj} (Q : Tm (.arr E) (.arr E)) : Tm (.prod E (.arr E)) (.prod E (.arr E)) :=
  Tm.pair Tm.outl (Tm.comp Tm.outr Q)

/-- `⟨π₁, π₂Q⟩` relates `(x, u)` to `(x', u')` iff `x' = x` and `Q u u'`. -/
theorem Tm.keepFst_iff {E : Obj} (ρ : Val) (Q : Tm (.arr E) (.arr E)) (x x' : E.El) (u u' : List E.El) :
    (Tm.keepFst Q).den ρ (x, u) (x', u') ↔
      x' = x ∧ Q.den ρ u u' := by
  simp only [Tm.den, rpair, Core.Rel.graph, Core.Rel.comp]
  exact and_congr_right fun _ => ⟨fun ⟨_, rfl, h⟩ => h, fun h => ⟨_, rfl, h⟩⟩

/-- `filter_mono`'s cons arm `F(R°) S ⊑ S R°` with `R°` any `Q` that `cons` commutes past (`⟨π₁, π₂Q⟩cons ⊑ cons Q`), and
`p` any relation: the `cons` branch keeps the head `x` and moves `Q` across, the `π₂` branch is natural. -/
theorem Tm.filterMono_den {E : Obj} {p : Tm E E} {Q : Tm (.arr E) (.arr E)} (ρ : Val)
    (hQ : (Tm.comp (Tm.keepFst Q) (Tm.prim (rowOf "cons"))).den ρ ⊑
      (Tm.comp (Tm.prim (rowOf "cons")) Q).den ρ) :
    (Tm.comp (Tm.keepFst Q) (Tm.filtStep p)).den ρ ⊑ (Tm.comp (Tm.filtStep p) Q).den ρ := by
  refine Core.Rel.le_iff.2 fun ⟨x, u⟩ w h => ?_
  obtain ⟨⟨x', u'⟩, hp, hs⟩ := h
  obtain ⟨rfl, hQu⟩ := (Tm.keepFst_iff ρ Q x x' u u').1 hp
  rcases (Tm.filtStep_iff ρ p x' u' w).1 hs with ⟨a, hpa, rfl⟩ | rfl
  · obtain ⟨y, hy, hQy⟩ := Core.Rel.le_iff.1 hQ (a, u) (a :: u')
      ⟨(a, u'), (Tm.keepFst_iff ρ Q a a u u').2 ⟨rfl, hQu⟩, by simp only [Tm.den, Prim.den_cons]⟩
    simp only [Tm.den, Prim.den_cons] at hy
    subst hy
    exact ⟨a :: u, (Tm.filtStep_iff ρ p x' u _).2 (Or.inl ⟨a, hpa, rfl⟩), hQy⟩
  · exact ⟨u, (Tm.filtStep_iff ρ p x' u u).2 (Or.inr rfl), hQu⟩

end Rel.Lang
