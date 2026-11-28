import Rel.Lang.Laws.AopA7_7_Filter
import Rel.Lang.Laws.AopA9_4_Code
import Rel.Lang.Laws.AopA7_1

/-! # Laws of freyd `AOP/A7_7_TakeWhile.lean` (B&dM Ex 7.39), at the list datatype, on the concrete core

`prefix = ⦇[nil, nil ∪ cons]⦈ʳ` (`prefC`) and `S = [nil, ⟨π₁p, π₂⟩cons ∪ nil]` (`twStep` is its step; `nil` at `α×[α]` is
freyd's `⊸ nil`). `prefC F(p) = nil°nil ∪ cons°(𝟙×(prefC F(p)))(twStep p)` for ANY `p` (freyd assumes `p` coreflexive):
a prefix `v` of `x :: xs` is `[]` or `x :: v'` with `v'` a prefix of `xs`, and `F(p)` maps `[]` to `[]` and `x :: v'` to
`a :: u` for `p x a`. -/

namespace Rel.Lang
open Tab Rel.Rep
open scoped Rel.Core.Rel
open Rel.Core.Rel hiding id comp recip inter union zero le inl inr junc

/-- The fixed-point equation of `⦇[nil, nil ∪ cons]⦈ʳ ≫ F(P)` at the step `⟨π₁P, π₂⟩cons ∪ nil`, for any `P`. -/
theorem twPrefix_fix {E : Obj} {P : Core.Rel E.El E.El} {Te Te' : Core.Rel (Obj.El (.arr E)) (Obj.El (.arr E))}
    {Spre S' : Core.Rel (Obj.El (.prod E (.arr E))) (Obj.El (.arr E))}
    (hTe : ∀ v, (∃ a, Te a v) ↔ v = []) (hTe' : ∀ v, (∃ a, Te' a v) ↔ v = [])
    (hSub : ∀ x u v, Spre (x, u) v ↔ v = [] ∨ v = x :: u)
    (hS' : ∀ x u w, S' (x, u) w ↔ (∃ a, P x a ∧ w = a :: u) ∨ w = []) :
    foldrStep Te' S' (foldrDen Te Spre ≫ mapDen P) = foldrDen Te Spre ≫ mapDen P := by
  have hnil : ∀ xs : List E.El, foldrDen Te Spre xs [] := by
    intro xs
    induction xs with
    | nil => exact (foldrDen_empty Te Spre []).2 ((hTe []).2 rfl)
    | cons x xs ih => exact (foldrDen_cons Te Spre x xs []).2 ⟨[], ih, (hSub x [] []).2 (Or.inl rfl)⟩
  funext xs w
  refine propext ?_
  cases xs with
  | nil =>
    rw [filtStepNil, hTe']
    constructor
    · rintro rfl
      exact ⟨[], (foldrDen_empty Te Spre []).2 ((hTe []).2 rfl), (filtMapNil P []).2 rfl⟩
    · rintro ⟨v, hv, hm⟩
      obtain rfl := (hTe v).1 ((foldrDen_empty Te Spre v).1 hv)
      exact (filtMapNil P w).1 hm
  | cons x xs =>
    rw [filtStepCons]
    constructor
    · rintro ⟨u, ⟨v, hv, hm⟩, hS⟩
      rcases (hS' x u w).1 hS with ⟨a, hP, rfl⟩ | rfl
      · exact ⟨x :: v, (foldrDen_cons Te Spre x xs _).2 ⟨v, hv, (hSub x v _).2 (Or.inr rfl)⟩,
          (filtMapCons P x v _).2 ⟨a, u, rfl, hP, hm⟩⟩
      · exact ⟨[], (foldrDen_cons Te Spre x xs _).2 ⟨v, hv, (hSub x v _).2 (Or.inl rfl)⟩, (filtMapNil P []).2 rfl⟩
    · rintro ⟨v, hv, hm⟩
      obtain ⟨y, hy, hS⟩ := (foldrDen_cons Te Spre x xs v).1 hv
      rcases (hSub x y v).1 hS with rfl | rfl
      · exact ⟨[], ⟨[], hnil xs, (filtMapNil P []).2 rfl⟩, (hS' x [] w).2 (Or.inr ((filtMapNil P w).1 hm))⟩
      · obtain ⟨a, ws, rfl, hP, hws⟩ := (filtMapCons P x y w).1 hm
        exact ⟨ws, ⟨y, hy, hws⟩, (hS' x ws _).2 (Or.inl ⟨a, hP, rfl⟩)⟩

/-- `⦇[nil, nil ∪ cons]⦈ʳ`, the prefixes, as the program's `prefC` elaborates. -/
abbrev Tm.prefC (E : Obj) : Tm (.arr E) (.arr E) :=
  Tm.foldr (Tm.ran (Tm.closedNil E)) (Tm.join Tm.nil (Tm.prim (rowOf "cons")))

/-- `⟨π₁ p, π₂⟩cons ∪ nil`, the step of `prefix list(p)`. -/
abbrev Tm.twStep {E : Obj} (p : Tm E E) : Tm (.prod E (.arr E)) (.arr E) :=
  Tm.join (Tm.comp (Tm.pair (Tm.comp Tm.outl p) Tm.outr) (Tm.prim (rowOf "cons"))) Tm.nil

theorem Tm.twStep_iff {E : Obj} (ρ : Val) (p : Tm E E) (x : E.El) (u w : List E.El) :
    (Tm.twStep p).den ρ (x, u) w ↔ (∃ a, p.den ρ x a ∧ w = a :: u) ∨ w = [] := by
  simp only [Tm.den, Tm.nil, Prim.den_nilRow, nilDen, Prim.den_cons, Core.Rel.union_apply, Core.Rel.comp_apply, Core.Rel.graph,
    rpair]
  constructor
  · rintro (⟨⟨a, u'⟩, ⟨⟨_, rfl, hp⟩, rfl⟩, rfl⟩ | h)
    · exact Or.inl ⟨a, hp, rfl⟩
    · exact Or.inr h
  · rintro (⟨a, hp, rfl⟩ | h)
    · exact Or.inl ⟨(a, u), ⟨⟨x, rfl, hp⟩, rfl⟩, rfl⟩
    · exact Or.inr h

theorem Tm.prefStep_iff {E : Obj} (ρ : Val) (x : E.El) (u w : List E.El) :
    (Tm.join Tm.nil (Tm.prim (rowOf "cons")) : Tm (.prod E (.arr E)) (.arr E)).den ρ (x, u) w ↔ w = [] ∨ w = x :: u := by
  simp only [Tm.den, Tm.nil, Prim.den_nilRow, nilDen, Prim.den_cons, Core.Rel.union_apply, Core.Rel.graph]

/-- The fixed-point equation of `prefix F(p)` (`takewhile_alg_comm`), for any `p`: the premise of `foldrUP`. -/
theorem Tm.takewhileAlgComm_den {E : Obj} {p : Tm E E} (ρ : Val) :
    (Tm.comp (Tm.prefC E) (Tm.arg (Tm.prim mapRow) p)).den ρ =
      (Tm.join (Tm.comp (Tm.closedNil E).conv Tm.nil)
        (Tm.comp (Tm.comp (Tm.prim (rowOf "uncons"))
          (Tm.pair (Tm.comp Tm.outl Tm.id) (Tm.comp Tm.outr (Tm.comp (Tm.prefC E) (Tm.arg (Tm.prim mapRow) p)))))
          (Tm.twStep p))).den ρ := by
  have h := twPrefix_fix (E := E) (P := p.den ρ) (Te := (Tm.ran (Tm.closedNil E)).den ρ)
    (Te' := (Tm.ran Tm.nil).den ρ) (Spre := (Tm.join Tm.nil (Tm.prim (rowOf "cons"))).den ρ) (S' := (Tm.twStep p).den ρ)
    (filtRanNil ρ _ (Tm.closedNil_iff ρ)) (filtRanNil ρ _ (Tm.nil_iff ρ))
    (fun x u v => Tm.prefStep_iff ρ x u v) (fun x u w => Tm.twStep_iff ρ p x u w)
  simpa only [foldrStep, ↓foldSeed_den, ↓pairComp_den, Tm.prefC, Tm.den, Tm.argDen, Prim.den_mapRow, Prim.den_uncons,
    Core.Rel.comp_assoc] using h.symm

/-- `prefix F(p) = ⦇[nil, ⟨π₁p, π₂⟩cons ∪ nil]⦈ʳ` (`takewhile_alg`), by the universal property from the equation above. -/
theorem Tm.takewhileAlg_den {E : Obj} {p : Tm E E} (ρ : Val) :
    (Tm.comp (Tm.prefC E) (Tm.arg (Tm.prim mapRow) p)).den ρ = (Tm.foldr (Tm.ran (Tm.closedNil E)) (Tm.twStep p)).den ρ := by
  have h := twPrefix_fix (E := E) (P := p.den ρ) (Te := (Tm.ran (Tm.closedNil E)).den ρ)
    (Te' := (Tm.ran (Tm.closedNil E)).den ρ) (Spre := (Tm.join Tm.nil (Tm.prim (rowOf "cons"))).den ρ)
    (S' := (Tm.twStep p).den ρ) (filtRanNil ρ _ (Tm.closedNil_iff ρ)) (filtRanNil ρ _ (Tm.closedNil_iff ρ))
    (fun x u v => Tm.prefStep_iff ρ x u v) (fun x u w => Tm.twStep_iff ρ p x u w)
  simpa only [Tm.prefC, Tm.den, Tm.argDen, Prim.den_mapRow] using
    (foldrUP ((Tm.ran (Tm.closedNil E)).den ρ) ((Tm.twStep p).den ρ) _).1 h.symm

/-- `nil` at `α×[α]` (freyd's `⊸ nil`) relates every pair to `[]` alone. -/
theorem Tm.nilPair_iff {E : Obj} (ρ : Val) (a : (Obj.prod E (.arr E)).El) (w : List E.El) :
    (Tm.nil : Tm (.prod E (.arr E)) (.arr E)).den ρ a w ↔ w = [] := by
  simp only [Tm.den, Tm.nil, Prim.den_nilRow, nilDen, Core.Rel.graph]

/-- `(𝟙×Q) ⊸ nil ⊑ ⊸ nil` (`takewhile_mono_disc`), for any `Q`: `⊸` discards the pair. -/
theorem Tm.takewhileMonoDisc_den {E : Obj} {Q : Tm (.arr E) (.arr E)} (ρ : Val) :
    (Tm.comp (Tm.keepFst Q) (Tm.nil : Tm (.prod E (.arr E)) (.arr E))).den ρ ⊑
      (Tm.nil : Tm (.prod E (.arr E)) (.arr E)).den ρ :=
  Core.Rel.le_iff.2 fun _ _ ⟨_, _, h⟩ => (Tm.nilPair_iff ρ _ _).2 ((Tm.nilPair_iff ρ _ _).1 h)

/-- `⟨π₁p, π₂Q⟩cons` relates `(x, u)` to `a :: u'` iff `p x a` and `Q u u'`. -/
theorem Tm.pconsQ_iff {E : Obj} (ρ : Val) (p : Tm E E) (Q : Tm (.arr E) (.arr E)) (x : E.El) (u w : List E.El) :
    (Tm.comp (Tm.pair (Tm.comp Tm.outl p) (Tm.comp Tm.outr Q)) (Tm.prim (rowOf "cons") : Tm (.prod E (.arr E)) (.arr E))).den ρ (x, u) w ↔
      ∃ a u', p.den ρ x a ∧ Q.den ρ u u' ∧ w = a :: u' := by
  simp only [Tm.den, Prim.den_cons, Core.Rel.comp_apply, Core.Rel.graph, rpair]
  constructor
  · rintro ⟨⟨a, u'⟩, ⟨⟨_, rfl, hp⟩, ⟨_, rfl, hQ⟩⟩, rfl⟩
    exact ⟨a, u', hp, hQ, rfl⟩
  · rintro ⟨a, u', hp, hQ, rfl⟩
    exact ⟨(a, u'), ⟨⟨x, rfl, hp⟩, ⟨u, rfl, hQ⟩⟩, rfl⟩

/-- `⟨π₁p, π₂⟩cons` is `⟨π₁p, π₂Q⟩cons` at `Q = 𝟙`-free form: relates `(x, u)` to `a :: u` iff `p x a`. -/
theorem Tm.pcons_iff {E : Obj} (ρ : Val) (p : Tm E E) (x : E.El) (u w : List E.El) :
    (Tm.comp (Tm.pair (Tm.comp Tm.outl p) Tm.outr) (Tm.prim (rowOf "cons") : Tm (.prod E (.arr E)) (.arr E))).den ρ (x, u) w ↔
      ∃ a, p.den ρ x a ∧ w = a :: u := by
  simp only [Tm.den, Prim.den_cons, Core.Rel.comp_apply, Core.Rel.graph, rpair]
  constructor
  · rintro ⟨⟨a, u'⟩, ⟨⟨_, rfl, hp⟩, rfl⟩, rfl⟩
    exact ⟨a, hp, rfl⟩
  · rintro ⟨a, hp, rfl⟩
    exact ⟨(a, u), ⟨⟨x, rfl, hp⟩, rfl⟩, rfl⟩

/-- `(𝟙×Q)(⟨π₁p, π₂⟩cons ∪ ⊸ nil) = ⟨π₁p, π₂Q⟩cons ∪ (𝟙×Q)⊸ nil` (`takewhile_mono_fork`), for any `p` and `Q`. -/
theorem Tm.takewhileMonoFork_den {E : Obj} {p : Tm E E} {Q : Tm (.arr E) (.arr E)} (ρ : Val) :
    (Tm.comp (Tm.keepFst Q) (Tm.twStep p)).den ρ =
      (Tm.join (Tm.comp (Tm.pair (Tm.comp Tm.outl p) (Tm.comp Tm.outr Q)) (Tm.prim (rowOf "cons")))
        (Tm.comp (Tm.keepFst Q) (Tm.nil : Tm (.prod E (.arr E)) (.arr E)))).den ρ := by
  funext q w; obtain ⟨x, u⟩ := q
  refine propext ?_
  have hc : ∀ q w', (Tm.comp (Tm.keepFst Q) (Tm.twStep p)).den ρ q w' ↔ ∃ b, (Tm.keepFst Q).den ρ q b ∧ (Tm.twStep p).den ρ b w' :=
    fun _ _ => Iff.rfl
  have hn : ∀ q w', (Tm.comp (Tm.keepFst Q) (Tm.nil : Tm (.prod E (.arr E)) (.arr E))).den ρ q w' ↔
      ∃ b, (Tm.keepFst Q).den ρ q b ∧ (Tm.nil : Tm (.prod E (.arr E)) (.arr E)).den ρ b w' := fun _ _ => Iff.rfl
  rw [hc]
  rw [show ∀ (A B : Tm (.prod E (.arr E)) (.arr E)) q w', (Tm.join A B).den ρ q w' ↔ A.den ρ q w' ∨ B.den ρ q w' from fun _ _ _ _ => Iff.rfl]
  rw [show (Tm.comp (Tm.pair (Tm.comp Tm.outl p) (Tm.comp Tm.outr Q)) (Tm.prim (rowOf "cons") : Tm (.prod E (.arr E)) (.arr E))).den ρ (x, u) w ↔ _ from
    Tm.pconsQ_iff ρ p Q x u w]
  constructor
  · rintro ⟨⟨x', u'⟩, hk, hs⟩
    obtain ⟨rfl, hQ⟩ := (Tm.keepFst_iff ρ Q x x' u u').1 hk
    rcases (Tm.twStep_iff ρ p x' u' w).1 hs with ⟨a, hp, rfl⟩ | h
    · exact Or.inl ⟨a, u', hp, hQ, rfl⟩
    · exact Or.inr ((hn _ _).2 ⟨(x', u'), (Tm.keepFst_iff ρ Q x' x' u u').2 ⟨rfl, hQ⟩, (Tm.nilPair_iff ρ _ _).2 h⟩)
  · rintro (⟨a, u', hp, hQ, rfl⟩ | h)
    · exact ⟨(x, u'), (Tm.keepFst_iff ρ Q x x u u').2 ⟨rfl, hQ⟩, (Tm.twStep_iff ρ p x u' _).2 (Or.inl ⟨a, hp, rfl⟩)⟩
    · obtain ⟨b, hb, hn'⟩ := (hn _ _).1 h
      exact ⟨b, hb, (Tm.twStep_iff ρ p b.1 b.2 w).2 (Or.inr ((Tm.nilPair_iff ρ _ _).1 hn'))⟩

/-- `⟨π₁p, π₂Q⟩cons ⊑ ⟨π₁p, π₂⟩cons Q` (`takewhile_mono_slide`), for any `p` and any `Q` that `cons` commutes past
(`⟨π₁, π₂Q⟩cons ⊑ cons Q`). -/
theorem Tm.takewhileMonoSlide_den {E : Obj} {p : Tm E E} {Q : Tm (.arr E) (.arr E)} (ρ : Val)
    (hQ : (Tm.comp (Tm.keepFst Q) (Tm.prim (rowOf "cons") : Tm (.prod E (.arr E)) (.arr E))).den ρ ⊑ (Tm.comp (Tm.prim (rowOf "cons") : Tm (.prod E (.arr E)) (.arr E)) Q).den ρ) :
    (Tm.comp (Tm.pair (Tm.comp Tm.outl p) (Tm.comp Tm.outr Q)) (Tm.prim (rowOf "cons"))).den ρ ⊑
      (Tm.comp (Tm.comp (Tm.pair (Tm.comp Tm.outl p) Tm.outr) (Tm.prim (rowOf "cons"))) Q).den ρ := by
  refine Core.Rel.le_iff.2 fun ⟨x, u⟩ w h => ?_
  obtain ⟨a, u', hp, hq, rfl⟩ := (Tm.pconsQ_iff ρ p Q x u w).1 h
  obtain ⟨y, hy, hQy⟩ := Core.Rel.le_iff.1 hQ (a, u) (a :: u')
    ⟨(a, u'), (Tm.keepFst_iff ρ Q a a u u').2 ⟨rfl, hq⟩, by simp only [Tm.den, Prim.den_cons]⟩
  simp only [Tm.den, Prim.den_cons] at hy
  subst hy
  exact ⟨a :: u, (Tm.pcons_iff ρ p x u _).2 ⟨a, hp, rfl⟩, hQy⟩

/-- `⊸ nil Q = ⊸ nil` (`takewhile_mono_nil`) for a `Q` that keeps `[]` as it is: `nil Q ⊑ nil` and `nil ⊑ nil Q`. -/
theorem Tm.takewhileMonoNil_den {E : Obj} {Q : Tm (.arr E) (.arr E)} (ρ : Val)
    (h1 : (Tm.comp (Tm.nil : Tm (.prod E (.arr E)) (.arr E)) Q).den ρ ⊑ (Tm.nil : Tm (.prod E (.arr E)) (.arr E)).den ρ)
    (h2 : (Tm.nil : Tm (.prod E (.arr E)) (.arr E)).den ρ ⊑ (Tm.comp (Tm.nil : Tm (.prod E (.arr E)) (.arr E)) Q).den ρ) :
    (Tm.comp (Tm.nil : Tm (.prod E (.arr E)) (.arr E)) Q).den ρ = (Tm.nil : Tm (.prod E (.arr E)) (.arr E)).den ρ :=
  Core.Rel.le_antisymm h1 h2

/-- `(𝟙×Q)(⟨π₁p, π₂⟩cons ∪ ⊸ nil) ⊑ (⟨π₁p, π₂⟩cons ∪ ⊸ nil)Q` (`takewhile_mono_cons`), for any `p` and any `Q` that `cons`
commutes past (`⟨π₁, π₂Q⟩cons ⊑ cons Q`) and keeps `[]` (`nil ⊑ nil Q`). -/
theorem Tm.takewhileMonoCons_den {E : Obj} {p : Tm E E} {Q : Tm (.arr E) (.arr E)} (ρ : Val)
    (hQ : (Tm.comp (Tm.keepFst Q) (Tm.prim (rowOf "cons") : Tm (.prod E (.arr E)) (.arr E))).den ρ ⊑
      (Tm.comp (Tm.prim (rowOf "cons") : Tm (.prod E (.arr E)) (.arr E)) Q).den ρ)
    (hN : (Tm.nil : Tm (.prod E (.arr E)) (.arr E)).den ρ ⊑ (Tm.comp (Tm.nil : Tm (.prod E (.arr E)) (.arr E)) Q).den ρ) :
    (Tm.comp (Tm.keepFst Q) (Tm.twStep p)).den ρ ⊑ (Tm.comp (Tm.twStep p) Q).den ρ := by
  refine Core.Rel.le_iff.2 fun ⟨x, u⟩ w h => ?_
  obtain ⟨⟨x', u'⟩, hk, hs⟩ := h
  obtain ⟨rfl, hQu⟩ := (Tm.keepFst_iff ρ Q x x' u u').1 hk
  rcases (Tm.twStep_iff ρ p x' u' w).1 hs with ⟨a, hpa, rfl⟩ | rfl
  · obtain ⟨y, hy, hQy⟩ := Core.Rel.le_iff.1 hQ (a, u) (a :: u')
      ⟨(a, u'), (Tm.keepFst_iff ρ Q a a u u').2 ⟨rfl, hQu⟩, by simp only [Tm.den, Prim.den_cons]⟩
    simp only [Tm.den, Prim.den_cons] at hy
    subst hy
    exact ⟨a :: u, (Tm.twStep_iff ρ p x' u _).2 (Or.inl ⟨a, hpa, rfl⟩), hQy⟩
  · obtain ⟨y, hy, hQy⟩ := Core.Rel.le_iff.1 hN (x', u) [] ((Tm.nilPair_iff ρ _ _).2 rfl)
    exact ⟨y, (Tm.twStep_iff ρ p x' u y).2 (Or.inr ((Tm.nilPair_iff ρ _ _).1 hy)), hQy⟩

/-- `[nil, ⟨π₁p, π₂⟩cons ∪ ⊸ nil]`, the algebra `S` of `prefix list(p)` on `1 + α×[α]`. -/
abbrev Tm.twAlg {E : Obj} (p : Tm E E) : Tm (.sum .one (.prod E (.arr E))) (.arr E) :=
  Tm.join (Tm.comp Tm.inl.conv Tm.nil) (Tm.comp Tm.inr.conv (Tm.twStep p))

theorem Tm.twAlg_inl_iff {E : Obj} (ρ : Val) (p : Tm E E) (a : Obj.one.El) (w : List E.El) :
    (Tm.twAlg p).den ρ (Sum.inl a) w ↔ w = [] := by
  simp only [Tm.den, Tm.nil, Prim.den_nilRow, nilDen, Core.Rel.union_apply, Core.Rel.comp_apply, Core.Rel.recip,
    Core.Rel.inl, Core.Rel.inr, Core.Rel.graph]
  constructor
  · rintro (⟨_, -, h⟩ | ⟨b, hb, -⟩)
    · exact h
    · exact absurd hb (by simp)
  · intro h
    exact Or.inl ⟨(), trivial, h⟩

theorem Tm.twAlg_inr_iff {E : Obj} (ρ : Val) (p : Tm E E) (q : (Obj.prod E (.arr E)).El) (w : List E.El) :
    (Tm.twAlg p).den ρ (Sum.inr q) w ↔ (Tm.twStep p).den ρ q w := by
  simp only [Tm.den, Tm.nil, Prim.den_nilRow, nilDen, Core.Rel.union_apply, Core.Rel.comp_apply, Core.Rel.recip,
    Core.Rel.inl, Core.Rel.inr, Core.Rel.graph]
  constructor
  · rintro (⟨b, hb, -⟩ | ⟨b, hb, h⟩)
    · exact absurd hb (by simp)
    · obtain rfl := Sum.inr.inj hb
      exact h
  · intro h
    exact Or.inr ⟨q, rfl, h⟩

theorem Tm.snocBiQ_inl_iff {E : Obj} (ρ : Val) (Q : Tm (.arr E) (.arr E)) (a : Obj.one.El) (v : (Obj.sum .one (.prod E (.arr E))).El) :
    (Tm.snocBi (O := .one) (Tm.id (A := E)) Q).den ρ (Sum.inl a) v ↔ v = Sum.inl a := by
  simp only [Tm.den, Core.Rel.union_apply, Core.Rel.comp_apply, Core.Rel.recip, Core.Rel.inl, Core.Rel.inr, Core.Rel.graph,
    Core.Rel.id]
  constructor
  · rintro (⟨_, -, b', -, rfl⟩ | ⟨b, hb, -⟩)
    · exact congrArg Sum.inl (Subsingleton.elim _ _)
    · exact absurd hb (by simp)
  · rintro rfl
    exact Or.inl ⟨(), trivial, a, trivial, rfl⟩

theorem Tm.snocBiQ_inr_iff {E : Obj} (ρ : Val) (Q : Tm (.arr E) (.arr E)) (x : E.El) (u : List E.El)
    (v : (Obj.sum .one (.prod E (.arr E))).El) :
    (Tm.snocBi (O := .one) (Tm.id (A := E)) Q).den ρ (Sum.inr (x, u)) v ↔ ∃ u', Q.den ρ u u' ∧ v = Sum.inr (x, u') := by
  simp only [Tm.den, Core.Rel.union_apply, Core.Rel.comp_apply, Core.Rel.recip, Core.Rel.inl, Core.Rel.inr, Core.Rel.graph,
    Core.Rel.id, rpair]
  constructor
  · rintro (⟨b, hb, -⟩ | ⟨b, hb, ⟨x1, u1⟩, ⟨⟨c, hc1, hc2⟩, ⟨d, hd, h⟩⟩, rfl⟩)
    · exact absurd hb (by simp)
    · obtain rfl := Sum.inr.inj hb
      simp only at hc1 hc2 hd h
      subst hc1 hd
      subst hc2
      exact ⟨u1, h, rfl⟩
  · rintro ⟨u', h, rfl⟩
    exact Or.inr ⟨(x, u), rfl, (x, u'), ⟨⟨x, rfl, rfl⟩, ⟨u, rfl, h⟩⟩, rfl⟩

/-- `F(Q)[nil, S] ⊑ [nil, S]Q` (`takewhile_mono`) for `S = ⟨π₁p, π₂⟩cons ∪ ⊸ nil`, any `p`, and any `Q` that `cons`
commutes past (`⟨π₁, π₂Q⟩cons ⊑ cons Q`) and keeps `[]` (`nil ⊑ nil Q`), with `F(Q) = [𝟙 inl, ⟨π₁𝟙, π₂Q⟩ inr]`. -/
theorem Tm.takewhileMono_den {E : Obj} {p : Tm E E} {Q : Tm (.arr E) (.arr E)} (ρ : Val)
    (hQ : (Tm.comp (Tm.keepFst Q) (Tm.prim (rowOf "cons") : Tm (.prod E (.arr E)) (.arr E))).den ρ ⊑
      (Tm.comp (Tm.prim (rowOf "cons") : Tm (.prod E (.arr E)) (.arr E)) Q).den ρ)
    (hE : (Tm.comp (Tm.closedNil E).conv (Tm.nil : Tm .one (.arr E))).den ρ ⊑ Q.den ρ) :
    (Tm.comp (Tm.snocBi (O := .one) (Tm.id (A := E)) Q) (Tm.twAlg p)).den ρ ⊑ (Tm.comp (Tm.twAlg p) Q).den ρ := by
  have hQ0 : Q.den ρ [] [] :=
    Core.Rel.le_iff.1 hE [] [] ⟨(), (Tm.closedNil_iff ρ () []).2 rfl, by simp only [Tm.den, Tm.nil, Prim.den_nilRow, nilDen, Core.Rel.graph]⟩
  have hN : (Tm.nil : Tm (.prod E (.arr E)) (.arr E)).den ρ ⊑ (Tm.comp (Tm.nil : Tm (.prod E (.arr E)) (.arr E)) Q).den ρ :=
    Core.Rel.le_iff.2 fun q w h => ⟨[], (Tm.nilPair_iff ρ _ _).2 rfl, by rw [(Tm.nilPair_iff ρ _ _).1 h]; exact hQ0⟩
  refine Core.Rel.le_iff.2 fun q w h => ?_
  obtain ⟨v, hv, hs⟩ := h
  cases q with
  | inl a =>
    obtain rfl := (Tm.snocBiQ_inl_iff ρ Q a v).1 hv
    rw [Tm.twAlg_inl_iff] at hs
    subst hs
    exact ⟨[], (Tm.twAlg_inl_iff ρ p a []).2 rfl, hQ0⟩
  | inr q =>
    obtain ⟨x, u⟩ := q
    obtain ⟨u', hQu, rfl⟩ := (Tm.snocBiQ_inr_iff ρ Q x u v).1 hv
    rw [Tm.twAlg_inr_iff] at hs
    obtain ⟨y, hy, hQy⟩ := Core.Rel.le_iff.1 (Tm.takewhileMonoCons_den (p := p) ρ hQ hN) (x, u) w ⟨(x, u'), (Tm.keepFst_iff ρ Q x x u u').2 ⟨rfl, hQu⟩, hs⟩
    exact ⟨y, (Tm.twAlg_inr_iff ρ p (x, u) y).2 hy, hQy⟩

/-- `takewhile(p) = Λ(X) est(Q)` is simple (`takewhile_simple`) for any `X` and `Q` such that two images of one point that
`Q ∪ 𝟙` orders both ways are equal (`X°X ∩ ((Q ∪ 𝟙) ∩ (Q ∪ 𝟙)°) ⊑ 𝟙`): the extreme of a set is unique. -/
theorem Tm.takewhileSimple_den {E : Obj} {X Q : Tm (.arr E) (.arr E)} (ρ : Val)
    (h : (Tm.meet (Tm.comp (Tm.comp Tm.id X).conv X) (Tm.meet (Tm.join Q Tm.id) (Tm.join Q.conv Tm.id))).den ρ ⊑ (Tm.id : Tm (.arr E) (.arr E)).den ρ) :
    (Tm.comp (Tm.comp Tm.id (Tm.comp (Tm.lam X) (Tm.est (pairTest Q)))).conv (Tm.comp (Tm.lam X) (Tm.est (pairTest Q)))).den ρ ⊑
      (Tm.id : Tm (.arr E) (.arr E)).den ρ := by
  refine Core.Rel.le_iff.2 fun ws zs hws => ?_
  obtain ⟨u, ⟨v, hv, ⟨ys, hy, he⟩⟩, ⟨ys', hy', he'⟩⟩ := hws
  obtain rfl := hv
  obtain rfl := lamDen_unique _ hy hy'
  rw [Tm.estPairTest_den] at he he'
  simp only [Core.Rel.inter, Core.Rel.ldiv_apply, Core.Rel.recip, Core.Rel.union, Core.Rel.id] at he he'
  obtain ⟨-, hmx⟩ := (lamDen_iff _ _ _).1 hy
  have hw : ws ∈ ys := he.1
  have hz : zs ∈ ys := he'.1
  refine Core.Rel.le_iff.1 h ws zs ⟨⟨u, ⟨u, rfl, (hmx ws).1 hw⟩, (hmx zs).1 hz⟩, ?_, ?_⟩
  · simp only [Tm.den, Core.Rel.union_apply, Core.Rel.id]
    exact (he.2 zs hz)
  · simp only [Tm.den, Core.Rel.union_apply, Core.Rel.recip, Core.Rel.id]
    exact (he'.2 ws hw).imp (fun h => h) (fun h => h.symm)

end Rel.Lang
