import Rel.Lang.Laws.AopA6_2

/-! # Hylomorphisms (freyd §6.3, `AOP/A6_3.lean`) at the list datatype, on the concrete core

freyd's `H = ⦇T⦈°⦇h⦈` with `T = [e,S]`, `h = [e',S']` is `⦇[e,S]⦈° ⦇[e',S']⦈ : V ⟶ W`, and its recursion body
`T°F(X)h` is `e°e' ∪ (S°(X×𝟙)S')`, since `[e,S]° F(X) [e',S'] = e°e' ∪ S°(X×𝟙)S'`. -/

namespace Rel.Lang
open Tab Rel.Rep
open scoped Rel.Core.Rel
open Rel.Core.Rel hiding id comp recip inter union zero le inl inr junc

/-- The hylomorphism `⦇[e,S]⦈° ⦇[e',S']⦈` as the program elaborates it. -/
abbrev Tm.hyloL {E V W : Obj} (e : Tm .one V) (S : Tm (.prod V E) V) (e' : Tm .one W) (S' : Tm (.prod W E) W) : Tm V W :=
  Tm.comp (Tm.comp Tm.id (Tm.fold (Tm.ran e) S)).conv (Tm.fold (Tm.ran e') S')

/-- The hylomorphism body `e°e' ∪ (S°(X×𝟙)S')` as the program elaborates it. -/
abbrev Tm.hyloStep {E V W : Obj} (e : Tm .one V) (S : Tm (.prod V E) V) (e' : Tm .one W) (S' : Tm (.prod W E) W)
    (X : Tm V W) : Tm V W :=
  Tm.join (.comp e.conv e')
    (.comp (.comp S.conv (.pair (.comp .outl X) (.comp .outr .id))) S')

theorem Tm.hyloStep_iff {E V W : Obj} (ρ : Val) (e : Tm .one V) (S : Tm (.prod V E) V) (e' : Tm .one W)
    (S' : Tm (.prod W E) W) (X : Tm V W) (a : V.El) (b : W.El) :
    (Tm.hyloStep e S e' S' X).den ρ a b ↔
      (∃ m, e.den ρ m a ∧ e'.den ρ m b) ∨ ∃ a' x b', S.den ρ (a', x) a ∧ X.den ρ a' b' ∧ S'.den ρ (b', x) b := by
  simp only [Tm.den, ↓pairComp_den, Core.Rel.union_apply, Core.Rel.comp_apply, Core.Rel.recip_apply]
  simp only [Core.Rel.rprodMap, Core.Rel.id, Prod.exists]
  constructor
  · rintro (h | ⟨b', x, ⟨a', y, hS, hX, rfl⟩, hS'⟩)
    · exact Or.inl h
    · exact Or.inr ⟨a', y, b', hS, hX, hS'⟩
  · rintro (h | ⟨a', x, b', hS, hX, hS'⟩)
    · exact Or.inl h
    · exact Or.inr ⟨b', x, ⟨a', x, hS, hX, rfl⟩, hS'⟩

theorem Tm.hyloL_iff {E V W : Obj} (ρ : Val) (e : Tm .one V) (S : Tm (.prod V E) V) (e' : Tm .one W)
    (S' : Tm (.prod W E) W) (a : V.El) (b : W.El) :
    (Tm.hyloL e S e' S').den ρ a b ↔
      ∃ xs, foldDen ((Tm.ran e).den ρ) (S.den ρ) xs a ∧ foldDen ((Tm.ran e').den ρ) (S'.den ρ) xs b := by
  simp only [Tm.den, Core.Rel.comp_apply, Core.Rel.recip_apply, Core.Rel.id]
  constructor
  · rintro ⟨_, ⟨xs, hy, h1⟩, h2⟩
    exact ⟨xs, h1, hy ▸ h2⟩
  · rintro ⟨xs, h1, h2⟩
    exact ⟨xs, ⟨xs, rfl, h1⟩, h2⟩

/-- The two seeds of the hylomorphism step read at the empty array: `ran e` reaches `a` iff `e` does. -/
theorem hyloSeed_iff {E V W : Obj} (ρ : Val) (e : Tm .one V) (e' : Tm .one W) (S : Tm (.prod V E) V)
    (S' : Tm (.prod W E) W) (a : V.El) (b : W.El) :
    (foldDen ((Tm.ran e).den ρ) (S.den ρ) [] a ∧ foldDen ((Tm.ran e').den ρ) (S'.den ρ) [] b) ↔
      ∃ m, e.den ρ m a ∧ e'.den ρ m b := by
  rw [foldDen_empty, foldDen_empty, ranSeed_iff, ranSeed_iff]
  constructor
  · rintro ⟨⟨m, hm⟩, ⟨n, hn⟩⟩
    cases m; cases n
    exact ⟨_, hm, hn⟩
  · rintro ⟨m, hm, hn⟩
    exact ⟨⟨m, hm⟩, ⟨m, hn⟩⟩

/-- freyd `hylo_fixed`: `T°F(H)h = H` at `T = [e,S]`, `h = [e',S']`, `H = ⦇T⦈°⦇h⦈`. -/
theorem Tm.hylo_fixed_den {E V W : Obj} {e : Tm .one V} {S : Tm (.prod V E) V} {e' : Tm .one W}
    {S' : Tm (.prod W E) W} (ρ : Val) :
    (Tm.hyloStep e S e' S' (Tm.hyloL e S e' S')).den ρ = (Tm.hyloL e S e' S').den ρ := by
  funext a b
  apply propext
  simp only [Tm.hyloStep_iff, Tm.hyloL_iff]
  constructor
  · rintro (h | ⟨a', x, b', hS, ⟨xs, hA, hB⟩, hS'⟩)
    · exact ⟨[], (hyloSeed_iff ρ e e' S S' a b).2 h⟩
    · exact ⟨xs ++ [x], (foldDen_snoc _ _ _ _ _).2 ⟨a', hA, hS⟩, (foldDen_snoc _ _ _ _ _).2 ⟨b', hB, hS'⟩⟩
  · rintro ⟨xs, hA, hB⟩
    rcases List.eq_nil_or_concat xs with rfl | ⟨L, x, rfl⟩
    · exact Or.inl ((hyloSeed_iff ρ e e' S S' a b).1 ⟨hA, hB⟩)
    · rw [List.concat_eq_append] at hA hB
      obtain ⟨a', hA', hS⟩ := (foldDen_snoc _ _ _ _ _).1 hA
      obtain ⟨b', hB', hS'⟩ := (foldDen_snoc _ _ _ _ _).1 hB
      exact Or.inr ⟨a', x, b', hS, ⟨L, hA', hB'⟩, hS'⟩

/-- freyd `hylo_le_of_prefixed`: `T°F(X)h ⊑ X → ⦇T⦈°⦇h⦈ ⊑ X`, by induction on the array. -/
theorem Tm.hylo_le_of_prefixed_den {E V W : Obj} {e : Tm .one V} {S : Tm (.prod V E) V} {e' : Tm .one W}
    {S' : Tm (.prod W E) W} {X : Tm V W} (ρ : Val)
    (h : (Tm.hyloStep e S e' S' X).den ρ ⊑ X.den ρ) : (Tm.hyloL e S e' S').den ρ ⊑ X.den ρ := by
  refine Core.Rel.le_iff.2 fun a b hab => ?_
  obtain ⟨xs, hA, hB⟩ := (Tm.hyloL_iff ρ e S e' S' a b).1 hab
  clear hab
  induction xs using snocInd generalizing a b with
  | nil => exact Core.Rel.le_iff.1 h a b ((Tm.hyloStep_iff ρ e S e' S' X a b).2 (Or.inl ((hyloSeed_iff ρ e e' S S' a b).1 ⟨hA, hB⟩)))
  | snoc L x ih =>
    obtain ⟨a', hA', hS⟩ := (foldDen_snoc _ _ _ _ _).1 hA
    obtain ⟨b', hB', hS'⟩ := (foldDen_snoc _ _ _ _ _).1 hB
    exact Core.Rel.le_iff.1 h a b ((Tm.hyloStep_iff ρ e S e' S' X a b).2 (Or.inr ⟨a', x, b', hS, ih a' b' hA' hB', hS'⟩))


/-- freyd `relCata_alpha`: `⦇α⦈ = 𝟙` at `α = [nil, snoc]`, the seed `ran nil` the program elaborates for `nil`. -/
theorem Tm.fold_nil_snoc_den {E : Obj} (ρ : Val) :
    (Tm.fold (Tm.ran (Tm.closedNil E)) (Tm.prim (rowOf "snoc") : Tm (.prod (.arr E) E) (.arr E))).den ρ =
      (Tm.id : Tm (.arr E) (.arr E)).den ρ := by
  funext xs w
  apply propext
  simp only [Tm.den]
  rw [Prim.den_snoc]
  induction xs using snocInd generalizing w with
  | nil =>
    rw [foldDen_empty, ranSeed_iff, Tm.closedNil_den]
    simp only [nilDen, Core.Rel.id, Core.Rel.graph]
    exact ⟨fun ⟨_, h⟩ => h.symm, fun h => ⟨(), h.symm⟩⟩
  | snoc L x ih =>
    rw [foldDen_snoc]
    simp only [ih, Core.Rel.id]
    exact ⟨fun ⟨u, h1, h2⟩ => by subst h1; exact h2.symm, fun h => ⟨L, rfl, h.symm⟩⟩

end Rel.Lang
