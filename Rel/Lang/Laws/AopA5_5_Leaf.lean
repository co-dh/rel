import Rel.Lang.Laws.FoldUP

/-! # Laws of freyd §5.5 `AOP/A5_5_Leaf.lean` on the concrete core, at the left fold over `[nil, snoc]`

`Rel.Lang.Tm.<name>_den` is the law of the freyd declaration `<name>` read off `Tm.den`;
`Rel/Programs/Aop/A5_5_Leaf.lean` states it as `theorem <name> … by Rel.Lang.Tm.<name>_den`. -/

namespace Rel.Lang
open Tab Rel.Rep
open scoped Rel.Core.Rel
open Rel.Core.Rel hiding id comp recip inter union zero le inl inr junc

/-- Banana split: a fork of two left folds is one fold on the product carrier, each step seeing only its own
    component. By length: both sides start at the pair of the two ranges and take `u ↦ (S u₁ x, S' u₂ x)`. -/
theorem Tm.pair_relCata_eq_relCata_pair_den {E V W : Obj} {e : Tm .one V} {e' : Tm .one W} {S : Tm (.prod V E) V} {S' : Tm (.prod W E) W} (ρ : Val) :
    (Tm.pair (Tm.fold (Tm.ran e) S) (Tm.fold (Tm.ran e') S')).den ρ =
      (Tm.fold (Tm.ran (Tm.pair e e'))
        (Tm.pair (.comp (.pair (.comp .outl .outl) .outr) S) (.comp (.pair (.comp .outl .outr) .outr) S'))).den ρ := by
  funext xs p
  obtain ⟨x, y⟩ := p
  refine propext ?_
  show rpair (foldDen ((Tm.ran e).den ρ) (S.den ρ)) (foldDen ((Tm.ran e').den ρ) (S'.den ρ)) xs (x, y) ↔
    foldDen ((Tm.ran (Tm.pair e e')).den ρ) ((Tm.pair (.comp (.pair (.comp .outl .outl) .outr) S)
      (.comp (.pair (.comp .outl .outr) .outr) S')).den ρ) xs (x, y)
  induction h : xs.length generalizing xs x y with
  | zero =>
    obtain rfl := List.length_eq_zero_iff.1 h
    show foldDen _ _ [] x ∧ foldDen _ _ [] y ↔ _
    rw [foldDen_empty, foldDen_empty, foldDen_empty]
    simp only [Tm.ran_den, Tm.den, rpair, Core.Rel.comp, Core.Rel.inter, Core.Rel.id, Core.Rel.recip]
    constructor
    · rintro ⟨⟨_, rfl, b, hb, -⟩, ⟨_, rfl, b', hb', -⟩⟩
      cases b
      cases b'
      exact ⟨_, rfl, (), ⟨hb, hb'⟩, hb, hb'⟩
    · rintro ⟨_, rfl, b, -, h₃, h₄⟩
      exact ⟨⟨_, rfl, b, h₃, h₃⟩, _, rfl, b, h₄, h₄⟩
  | succ n ih =>
    obtain ⟨L, a, rfl⟩ := List.eq_nil_or_concat xs |>.resolve_left (by rintro rfl; simp at h)
    rw [List.concat_eq_append]
    show foldDen _ _ (L ++ [a]) x ∧ foldDen _ _ (L ++ [a]) y ↔ _
    rw [foldDen_snoc, foldDen_snoc, foldDen_snoc]
    constructor
    · rintro ⟨⟨u₁, h₁, s₁⟩, ⟨u₂, h₂, s₂⟩⟩
      refine ⟨(u₁, u₂), (ih L u₁ u₂ (by simpa using h)).1 ⟨h₁, h₂⟩, ?_⟩
      simp only [Tm.den, rpair, Core.Rel.comp, graph]
      exact ⟨⟨(u₁, a), ⟨⟨_, rfl, rfl⟩, rfl⟩, s₁⟩, ⟨(u₂, a), ⟨⟨_, rfl, rfl⟩, rfl⟩, s₂⟩⟩
    · rintro ⟨⟨u₁, u₂⟩, hu, hs⟩
      have := (ih L u₁ u₂ (by simpa using h)).2 hu
      simp only [Tm.den, rpair, Core.Rel.comp, graph] at hs
      obtain ⟨⟨⟨b₁, b₂⟩, ⟨⟨_, rfl, e₁⟩, e₂⟩, hS⟩, ⟨⟨c₁, c₂⟩, ⟨⟨_, rfl, f₁⟩, f₂⟩, hS'⟩⟩ := hs
      dsimp only at e₁ e₂ f₁ f₂
      subst e₁ e₂ f₁ f₂
      exact ⟨⟨_, this.1, hS⟩, ⟨_, this.2, hS'⟩⟩


/-- The fold's two equations at the initial algebra `[nil, snoc]`: `[nil, snoc] ⦇e,S⦈ = [e, (⦇e,S⦈ × 𝟙) S]`. The
    `inl` summand is `foldDen_empty` (`nil ≫ ⦇e,S⦈` is the range of `e`), the `inr` summand `foldDen_snoc`. -/
theorem Tm.relCata_mapAlg_cancel_den {E V : Obj} {e : Tm .one V} {S : Tm (.prod V E) V} (ρ : Val) :
    (Tm.comp (Tm.join (Tm.comp Tm.inl.conv (Tm.prim nilRow)) (Tm.comp Tm.inr.conv (Tm.prim (rowOf "snoc"))))
      (Tm.fold (Tm.ran e) S)).den ρ =
    (Tm.join (Tm.comp Tm.inl.conv e) (Tm.comp Tm.inr.conv (Tm.comp (Tm.pair (Tm.comp Tm.outl (Tm.fold (Tm.ran e) S))
      (Tm.comp Tm.outr Tm.id)) S))).den ρ := by
  funext s w
  refine propext ?_
  rcases s with u | ⟨xs, a⟩
  · simp [Tm.den, Core.Rel.comp, Core.Rel.recip, Core.Rel.inl, Core.Rel.inr, Core.Rel.graph, Prim.den_nilRow,
      nilDen, Tm.ran_den]
    rw [foldDen_empty]
    simp only [Core.Rel.inter_apply, Core.Rel.id, Core.Rel.comp_apply, Core.Rel.recip]
    constructor
    · rintro ⟨_, rfl, b, -, hb⟩
      exact ⟨b, hb⟩
    · rintro ⟨b, hb⟩
      exact ⟨w, rfl, b, hb, hb⟩
  · simp [Tm.den, Core.Rel.comp, Core.Rel.recip, Core.Rel.inl, Core.Rel.inr, Core.Rel.graph, Prim.den_snoc, rpair]
    rw [foldDen_snoc]
    constructor
    · rintro ⟨u, h, s⟩
      exact ⟨u, a, ⟨h, rfl⟩, s⟩
    · rintro ⟨u, b, ⟨h, rfl⟩, s⟩
      exact ⟨u, h, s⟩

/-- Banana split's first β-law `⟨R,S⟩ π₁ = R`: the fork loses nothing of `R` where `S` has an image everywhere
    (`dom(S) = 𝟙`), which is what totality of the folds `⦇h⦈`, `⦇k⦈` supplies. -/
theorem Tm.relCata_pair_beta_den {A B C : Obj} {R : Tm A B} {S : Tm A C} (ρ : Val)
    (h : (Tm.dom S).den ρ = (Tm.id (A := A)).den ρ) :
    (Tm.comp (Tm.pair R S) Tm.outl).den ρ = R.den ρ := by
  have eS := Tm.entire_of_dom h
  funext a b
  refine propext ⟨?_, fun hr => ?_⟩
  · rintro ⟨⟨b', c⟩, ⟨hr, -⟩, rfl⟩
    exact hr
  · obtain ⟨c, hc⟩ := eS a
    exact ⟨(b, c), ⟨hr, hc⟩, rfl⟩

/-- `Λ(T) ∋ = T` where `Λ(T)` is defined everywhere (`dom(Λ(T)) = 𝟙`, `Map f` of the freyd statement). -/
theorem Tm.lam_mem_den {A B : Obj} {T : Tm A B} (ρ : Val)
    (h : (Tm.dom (Tm.lam T)).den ρ = (Tm.id (A := A)).den ρ) :
    (Tm.comp (Tm.lam T) Tm.mem).den ρ = T.den ρ := by
  have eL := Tm.entire_of_dom h
  funext a b
  refine propext ⟨?_, fun hT => ?_⟩
  · rintro ⟨ys, hys, hb⟩
    exact (((lamDen_iff _ _ _).1 hys).2 b).1 hb
  · obtain ⟨ys, hys⟩ := eL a
    exact ⟨ys, hys, (((lamDen_iff _ _ _).1 hys).2 b).2 hT⟩

/-- The fork of two folds is a homomorphism `[nil, snoc] → [⟨e,e'⟩, ⟨⟨π₁π₁,π₂⟩S, ⟨π₁π₂,π₂⟩S'⟩]`: banana split
    rewrites the fork as one fold, whose unrolling is `relCata_mapAlg_cancel_den`. -/
theorem Tm.pair_relCata_hom_den {E V W : Obj} {e : Tm .one V} {e' : Tm .one W} {S : Tm (.prod V E) V}
    {S' : Tm (.prod W E) W} (ρ : Val) :
    (Tm.comp (Tm.join (Tm.comp Tm.inl.conv (Tm.prim nilRow)) (Tm.comp Tm.inr.conv (Tm.prim (rowOf "snoc"))))
      (Tm.pair (Tm.fold (Tm.ran e) S) (Tm.fold (Tm.ran e') S'))).den ρ =
    (Tm.join (Tm.comp Tm.inl.conv (Tm.pair e e')) (Tm.comp Tm.inr.conv (Tm.comp
      (Tm.pair (Tm.comp Tm.outl (Tm.pair (Tm.fold (Tm.ran e) S) (Tm.fold (Tm.ran e') S'))) (Tm.comp Tm.outr Tm.id))
      (Tm.pair (.comp (.pair (.comp .outl .outl) .outr) S) (.comp (.pair (.comp .outl .outr) .outr) S'))))).den ρ := by
  have h := Tm.pair_relCata_eq_relCata_pair_den (e := e) (e' := e') (S := S) (S' := S') ρ
  have u := Tm.relCata_mapAlg_cancel_den (e := Tm.pair e e')
    (S := Tm.pair (.comp (.pair (.comp .outl .outl) .outr) S) (.comp (.pair (.comp .outl .outr) .outr) S')) ρ
  simp only [Tm.den] at h u ⊢
  rw [h]
  exact u

end Rel.Lang
