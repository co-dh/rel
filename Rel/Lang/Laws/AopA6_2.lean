import Rel.Lang.Laws.AopA10_4_Tex

/-! # Fixed-point laws (6.2)-(6.5) of freyd §6.2 `AOP/A6_2.lean`, at the list datatype, on the concrete core

freyd's `relCata R` over the initial algebra `α = [nil, snoc]` is the prelude's `⦇[e, S]⦈` (`Tm.fold (Tm.ran e) S`), and
its recursion body `α° ≫ F(X) ≫ R` is `nil°e ∪ (snoc°(X×𝟙)S)`, `foldStep` on the core. `Rel.Lang.Tm.<name>_den` is the
law of the freyd declaration `<name>`; the pointwise lemmas below are `Core.Rel` facts about `foldStep`/`foldDen`. -/

namespace Rel.Lang
open Tab Rel.Rep
open scoped Rel.Core.Rel
open Rel.Core.Rel hiding id comp recip inter union zero le inl inr junc

/-- Induction on the last element, the shape `foldDen_snoc` unfolds. -/
theorem snocInd {α : Type} {P : List α → Prop} (nil : P []) (snoc : ∀ L x, P L → P (L ++ [x])) (xs : List α) : P xs := by
  rw [← List.reverse_reverse xs]
  generalize xs.reverse = l
  induction l with
  | nil => exact nil
  | cons x l ih => simpa using snoc _ x ih

/-- (6.2) on the core: `foldDen` is the least fixed point of `foldStep`, so it is below every prefixed point. -/
theorem foldDen_le_of_prefixed {E V : Obj} {Te : Core.Rel (Obj.El V) (Obj.El V)} {TS : Core.Rel (Obj.El (.prod V E)) (Obj.El V)}
    {X : Core.Rel (Obj.El (.arr E)) (Obj.El V)} (h : foldStep Te TS X ⊑ X) : foldDen Te TS ⊑ X := mu_le h

/-- (6.3) on the core: a postfixed point `X ⊑ foldStep X` is below `foldDen`, by induction on the array. -/
theorem le_foldDen_of_postfixed {E V : Obj} {Te : Core.Rel (Obj.El V) (Obj.El V)} {TS : Core.Rel (Obj.El (.prod V E)) (Obj.El V)}
    {X : Core.Rel (Obj.El (.arr E)) (Obj.El V)} (hX : X ⊑ foldStep Te TS X) : X ⊑ foldDen Te TS := by
  refine Core.Rel.le_iff.2 fun xs w h => ?_
  induction xs using snocInd generalizing w with
  | nil =>
    have hx := Core.Rel.le_iff.1 hX _ w h
    simp only [foldStep, Core.Rel.union_apply, Core.Rel.comp_apply, Core.Rel.corefl, Core.Rel.inter_apply, Core.Rel.id,
      Core.Rel.top, Core.Rel.recip, Core.Rel.graph, Core.Rel.rprodMap] at hx
    rcases hx with ⟨_, ⟨-, -⟩, _, -, rfl, e, he, -⟩ | ⟨p, hp, -⟩
    · exact (foldDen_empty Te TS _).2 ⟨e, he⟩
    · exact absurd (List.append_eq_nil_iff.1 hp.symm).2 (List.cons_ne_nil _ _)
  | snoc L x ih =>
    have hx := Core.Rel.le_iff.1 hX _ w h
    simp only [foldStep, Core.Rel.union_apply, Core.Rel.comp_apply, Core.Rel.corefl, Core.Rel.recip, Core.Rel.graph,
      Core.Rel.rprodMap, Core.Rel.id] at hx
    rcases hx with ⟨_, ⟨-, h⟩, -⟩ | ⟨⟨ys, y⟩, hp, ⟨u, z⟩, ⟨hu, hz⟩, hS⟩
    · exact absurd (List.append_eq_nil_iff.1 h.symm).2 (List.cons_ne_nil _ _)
    · obtain ⟨rfl, h⟩ := List.append_inj' hp rfl
      obtain rfl := (List.cons.inj h).1
      obtain rfl := hz
      exact (foldDen_snoc Te TS _ _ _).2 ⟨u, ih u hu, hS⟩

/-- (6.4)'s prefix-point condition on the core: `⦇R⦈ S` is a prefix point of `T`'s body when `F(S) T ⊑ R S`, here
    seed `Te' ⊑ Te S` and step `(S×𝟙) G ⊑ F S`. -/
theorem foldDen_comp_prefixed {E V W : Obj} {Te : Core.Rel (Obj.El V) (Obj.El V)} {F : Core.Rel (Obj.El (.prod V E)) (Obj.El V)}
    {Te' : Core.Rel (Obj.El W) (Obj.El W)} {G : Core.Rel (Obj.El (.prod W E)) (Obj.El W)} {S : Core.Rel (Obj.El V) (Obj.El W)}
    (he : ∀ w, (∃ a, Te' a w) → ∃ v, (∃ a, Te a v) ∧ S v w)
    (hS : ∀ v u x w, S v u → G (u, x) w → ∃ v', F (v, x) v' ∧ S v' w) :
    foldStep Te' G (foldDen Te F ≫ S) ⊑ foldDen Te F ≫ S := by
  refine Core.Rel.le_iff.2 fun xs w h => ?_
  simp only [foldStep, Core.Rel.union_apply, Core.Rel.comp_apply, Core.Rel.corefl, Core.Rel.inter_apply, Core.Rel.id,
    Core.Rel.top, Core.Rel.recip, Core.Rel.graph, Core.Rel.rprodMap] at h
  rcases h with ⟨z, ⟨h1, h2⟩, _, -, rfl, e, he', -⟩ | ⟨⟨ys, y⟩, hp, ⟨u, z⟩, ⟨⟨v, hv, hSv⟩, hz⟩, hG⟩
  · subst h2; subst h1
    obtain ⟨v, hv, hSv⟩ := he _ ⟨e, he'⟩
    exact ⟨v, (foldDen_empty Te F v).2 hv, hSv⟩
  · obtain rfl := hz
    obtain ⟨v', hF, hS'⟩ := hS v u y w hSv hG
    subst hp
    exact ⟨v', (foldDen_snoc Te F ys y v').2 ⟨v, hv, hF⟩, hS'⟩

/-- (6.5)'s postfix-point condition on the core: `⦇R⦈ S` is a postfix point of `T`'s body when `R S ⊑ F(S) T`. -/
theorem foldDen_comp_postfixed {E V W : Obj} {Te : Core.Rel (Obj.El V) (Obj.El V)} {F : Core.Rel (Obj.El (.prod V E)) (Obj.El V)}
    {Te' : Core.Rel (Obj.El W) (Obj.El W)} {G : Core.Rel (Obj.El (.prod W E)) (Obj.El W)} {S : Core.Rel (Obj.El V) (Obj.El W)}
    (he : ∀ v w, (∃ a, Te a v) → S v w → ∃ a, Te' a w)
    (hS : ∀ v x v' w, F (v, x) v' → S v' w → ∃ u, S v u ∧ G (u, x) w) :
    foldDen Te F ≫ S ⊑ foldStep Te' G (foldDen Te F ≫ S) := by
  refine Core.Rel.le_iff.2 fun xs w ⟨v, hv, hSv⟩ => ?_
  simp only [foldStep, Core.Rel.union_apply, Core.Rel.comp_apply, Core.Rel.corefl, Core.Rel.inter_apply, Core.Rel.id,
    Core.Rel.top, Core.Rel.recip, Core.Rel.graph, Core.Rel.rprodMap]
  induction xs using snocInd generalizing v with
  | nil =>
    obtain ⟨a, ha⟩ := he v w ((foldDen_empty Te F v).1 hv) hSv
    exact Or.inl ⟨[], ⟨rfl, rfl⟩, w, trivial, rfl, a, ha, trivial⟩
  | snoc L x _ =>
    obtain ⟨v0, hv0, hF⟩ := (foldDen_snoc Te F L x v).1 hv
    obtain ⟨u, hSu, hG⟩ := hS v0 x v w hF hSv
    exact Or.inr ⟨(L, x), rfl, (u, x), ⟨⟨v0, hv0, hSu⟩, rfl⟩, hG⟩

/-- (6.4) on the core: fusion `⦇T⦈ ⊑ ⦇R⦈ S`, (6.2) at the prefixed point `⦇R⦈ S`. -/
theorem foldDen_le_comp {E V W : Obj} {Te : Core.Rel (Obj.El V) (Obj.El V)} {F : Core.Rel (Obj.El (.prod V E)) (Obj.El V)}
    {Te' : Core.Rel (Obj.El W) (Obj.El W)} {G : Core.Rel (Obj.El (.prod W E)) (Obj.El W)} {S : Core.Rel (Obj.El V) (Obj.El W)}
    (he : ∀ w, (∃ a, Te' a w) → ∃ v, (∃ a, Te a v) ∧ S v w)
    (hS : ∀ v u x w, S v u → G (u, x) w → ∃ v', F (v, x) v' ∧ S v' w) : foldDen Te' G ⊑ foldDen Te F ≫ S :=
  foldDen_le_of_prefixed (foldDen_comp_prefixed he hS)

/-- (6.5) on the core: `⦇R⦈ S ⊑ ⦇T⦈`, (6.3) at the postfixed point `⦇R⦈ S`. -/
theorem comp_le_foldDen {E V W : Obj} {Te : Core.Rel (Obj.El V) (Obj.El V)} {F : Core.Rel (Obj.El (.prod V E)) (Obj.El V)}
    {Te' : Core.Rel (Obj.El W) (Obj.El W)} {G : Core.Rel (Obj.El (.prod W E)) (Obj.El W)} {S : Core.Rel (Obj.El V) (Obj.El W)}
    (he : ∀ v w, (∃ a, Te a v) → S v w → ∃ a, Te' a w)
    (hS : ∀ v x v' w, F (v, x) v' → S v' w → ∃ u, S v u ∧ G (u, x) w) : foldDen Te F ≫ S ⊑ foldDen Te' G :=
  le_foldDen_of_postfixed (foldDen_comp_postfixed he hS)

/-- The recursion body `α° ≫ F(X) ≫ [e, S]` of `⦇[e,S]⦈`, as the program's `nil°e ∪ (snoc°(X×𝟙)S)` elaborates. -/
abbrev Tm.foldBody {E V : Obj} (e : Tm .one V) (S : Tm (.prod V E) V) (X : Tm (.arr E) V) : Tm (.arr E) V :=
  Tm.join (.comp (Tm.closedNil E).conv e)
    (.comp (.comp (.prim (rowOf "unsnoc")) (.pair (.comp .outl X) (.comp .outr .id))) S)

theorem Tm.foldBody_den {E V : Obj} (ρ : Val) (e : Tm .one V) (S : Tm (.prod V E) V) (X : Tm (.arr E) V) :
    (Tm.foldBody e S X).den ρ = foldStep ((Tm.ran e).den ρ) (S.den ρ) (X.den ρ) := by
  simp only [foldStep, ↓foldSeed_den, ↓pairComp_den, Tm.den, Prim.den_unsnoc, Core.Rel.comp_assoc]

/-- A seed `ran e`: some `a` reaches `w` iff `w` is an image of `e`. -/
theorem ranSeed_iff {A B : Obj} (ρ : Val) (e : Tm A B) (w : Obj.El B) :
    (∃ a, (Tm.ran e).den ρ a w) ↔ ∃ m, e.den ρ m w :=
  ⟨fun ⟨a, ha⟩ => by obtain ⟨rfl, m, hm⟩ := (ranArg_den ρ e a w).1 ha; exact ⟨m, hm⟩,
   fun ⟨m, hm⟩ => ⟨w, (ranArg_den ρ e w w).2 ⟨rfl, m, hm⟩⟩⟩

/-- (6.2): `⦇[e,S]⦈ ⊑ X ⟸ nil°e ∪ (snoc°(X×𝟙)S) ⊑ X`. -/
theorem Tm.relCata_le_of_prefixed_den {E V : Obj} {e : Tm .one V} {S : Tm (.prod V E) V} {X : Tm (.arr E) V} (ρ : Val)
    (h : (Tm.foldBody e S X).den ρ ⊑ X.den ρ) : (Tm.fold (Tm.ran e) S).den ρ ⊑ X.den ρ :=
  foldDen_le_of_prefixed (by rwa [Tm.foldBody_den] at h)

/-- (6.3): `X ⊑ ⦇[e,S]⦈ ⟸ X ⊑ nil°e ∪ (snoc°(X×𝟙)S)`. -/
theorem Tm.le_relCata_of_postfixed_den {E V : Obj} {e : Tm .one V} {S : Tm (.prod V E) V} {X : Tm (.arr E) V} (ρ : Val)
    (h : X.den ρ ⊑ (Tm.foldBody e S X).den ρ) : X.den ρ ⊑ (Tm.fold (Tm.ran e) S).den ρ :=
  le_foldDen_of_postfixed (by rwa [Tm.foldBody_den] at h)

/-- `he` of (6.4) read pointwise at the seeds `ran e'`, `ran e`: `e' ⊑ e S`. -/
theorem ranSeed_le_comp {V W : Obj} {e : Tm .one V} {e' : Tm .one W} {S : Tm V W} (ρ : Val)
    (he : e'.den ρ ⊑ (Tm.comp e S).den ρ) :
    ∀ w, (∃ a, (Tm.ran e').den ρ a w) → ∃ v, (∃ a, (Tm.ran e).den ρ a v) ∧ S.den ρ v w := fun w h => by
  obtain ⟨m, hm⟩ := (ranSeed_iff ρ e' w).1 h
  obtain ⟨v, hv, hS⟩ := Core.Rel.le_iff.1 he m w hm
  exact ⟨v, (ranSeed_iff ρ e v).2 ⟨m, hv⟩, hS⟩

/-- `he` of (6.5) read pointwise: `e S ⊑ e'`. -/
theorem comp_le_ranSeed {V W : Obj} {e : Tm .one V} {e' : Tm .one W} {S : Tm V W} (ρ : Val)
    (he : (Tm.comp e S).den ρ ⊑ e'.den ρ) :
    ∀ v w, (∃ a, (Tm.ran e).den ρ a v) → S.den ρ v w → ∃ a, (Tm.ran e').den ρ a w := fun v w h hS => by
  obtain ⟨m, hm⟩ := (ranSeed_iff ρ e v).1 h
  exact (ranSeed_iff ρ e' w).2 ⟨m, Core.Rel.le_iff.1 he m w ⟨v, hm, hS⟩⟩

/-- The step `(S×𝟙) G` of (6.4) read pointwise. -/
theorem prodComp_le {E V W : Obj} {F : Tm (.prod V E) V} {G : Tm (.prod W E) W} {S : Tm V W} (ρ : Val)
    (hS : (Tm.comp (Tm.pair (.comp .outl S) (.comp .outr .id)) G).den ρ ⊑ (Tm.comp F S).den ρ) :
    ∀ v u x w, S.den ρ v u → G.den ρ (u, x) w → ∃ v', F.den ρ (v, x) v' ∧ S.den ρ v' w := fun v u x w hu hG => by
  have hp : (Tm.pair (.comp .outl S) (.comp .outr .id) : Tm (.prod V E) (.prod W E)).den ρ (v, x) (u, x) := by
    rw [pairComp_den]; exact ⟨hu, rfl⟩
  obtain ⟨v', hF, hS'⟩ := Core.Rel.le_iff.1 hS (v, x) w ⟨(u, x), hp, hG⟩
  exact ⟨v', hF, hS'⟩

/-- The step `R S ⊑ (S×𝟙) G` of (6.5) read pointwise. -/
theorem le_prodComp {E V W : Obj} {F : Tm (.prod V E) V} {G : Tm (.prod W E) W} {S : Tm V W} (ρ : Val)
    (hS : (Tm.comp F S).den ρ ⊑ (Tm.comp (Tm.pair (.comp .outl S) (.comp .outr .id)) G).den ρ) :
    ∀ v x v' w, F.den ρ (v, x) v' → S.den ρ v' w → ∃ u, S.den ρ v u ∧ G.den ρ (u, x) w := fun v x v' w hF hu => by
  obtain ⟨⟨u, y⟩, hp, hG⟩ := Core.Rel.le_iff.1 hS (v, x) w ⟨v', hF, hu⟩
  rw [pairComp_den] at hp
  obtain ⟨hSu, rfl⟩ := hp
  exact ⟨u, hSu, hG⟩

/-- (6.4)'s prefix-point condition: `⦇R⦈S` is a prefix point of `T`'s body when `F(S)T ⊑ RS`. -/
theorem Tm.relCata_comp_prefixed_den {E V W : Obj} {e : Tm .one V} {f : Tm (.prod V E) V} {e' : Tm .one W}
    {g : Tm (.prod W E) W} {S : Tm V W} (ρ : Val) (he : e'.den ρ ⊑ (Tm.comp e S).den ρ)
    (hS : (Tm.comp (Tm.pair (.comp .outl S) (.comp .outr .id)) g).den ρ ⊑ (Tm.comp f S).den ρ) :
    (Tm.foldBody e' g (Tm.comp (Tm.fold (Tm.ran e) f) S)).den ρ ⊑ (Tm.comp (Tm.fold (Tm.ran e) f) S).den ρ := by
  rw [Tm.foldBody_den]
  exact foldDen_comp_prefixed (ranSeed_le_comp ρ he) (prodComp_le ρ hS)

/-- (6.4): `⦇T⦈ ⊑ ⦇R⦈S ⟸ F(S)T ⊑ RS`. -/
theorem Tm.relCata_le_comp_den {E V W : Obj} {e : Tm .one V} {f : Tm (.prod V E) V} {e' : Tm .one W}
    {g : Tm (.prod W E) W} {S : Tm V W} (ρ : Val) (he : e'.den ρ ⊑ (Tm.comp e S).den ρ)
    (hS : (Tm.comp (Tm.pair (.comp .outl S) (.comp .outr .id)) g).den ρ ⊑ (Tm.comp f S).den ρ) :
    (Tm.fold (Tm.ran e') g).den ρ ⊑ (Tm.comp (Tm.fold (Tm.ran e) f) S).den ρ :=
  foldDen_le_comp (ranSeed_le_comp ρ he) (prodComp_le ρ hS)

/-- (6.5)'s postfix-point condition: `⦇R⦈S` is a postfix point of `T`'s body when `RS ⊑ F(S)T`. -/
theorem Tm.relCata_comp_postfixed_den {E V W : Obj} {e : Tm .one V} {f : Tm (.prod V E) V} {e' : Tm .one W}
    {g : Tm (.prod W E) W} {S : Tm V W} (ρ : Val) (he : (Tm.comp e S).den ρ ⊑ e'.den ρ)
    (hS : (Tm.comp f S).den ρ ⊑ (Tm.comp (Tm.pair (.comp .outl S) (.comp .outr .id)) g).den ρ) :
    (Tm.comp (Tm.fold (Tm.ran e) f) S).den ρ ⊑ (Tm.foldBody e' g (Tm.comp (Tm.fold (Tm.ran e) f) S)).den ρ := by
  rw [Tm.foldBody_den]
  exact foldDen_comp_postfixed (comp_le_ranSeed ρ he) (le_prodComp ρ hS)

/-- (6.5): `⦇R⦈S ⊑ ⦇T⦈ ⟸ RS ⊑ F(S)T`. -/
theorem Tm.comp_le_relCata_den {E V W : Obj} {e : Tm .one V} {f : Tm (.prod V E) V} {e' : Tm .one W}
    {g : Tm (.prod W E) W} {S : Tm V W} (ρ : Val) (he : (Tm.comp e S).den ρ ⊑ e'.den ρ)
    (hS : (Tm.comp f S).den ρ ⊑ (Tm.comp (Tm.pair (.comp .outl S) (.comp .outr .id)) g).den ρ) :
    (Tm.comp (Tm.fold (Tm.ran e) f) S).den ρ ⊑ (Tm.fold (Tm.ran e') g).den ρ :=
  comp_le_foldDen (comp_le_ranSeed ρ he) (le_prodComp ρ hS)

end Rel.Lang
