import Rel.Lang.Laws.EstUnion
import Rel.Lang.PreludeConcat
import Rel.Lang.PreludeDfn
import Rel.Lang.PreludeLoop

/-! The two laws of B&dM §7.4 (pp.182-183) on the `Vec` model, over any element type and any pair test `TQ`:

* `estConcat_den`: a cheapest of each of the lists and then a cheapest of those is a cheapest of the lists laid end to
  end, `TQ` transitive (`F(est(S)) est(S) ⊑ concat est(S)`);
* `cons713_den`: the new element in front of every candidate and then a cheapest of them is beaten by a cheapest first
  and the element in front of that one, `TQ` monotone for `cons` (`(𝟙×est(R)) cons ⊑ cp F(cons) est(R)`). -/

namespace Rel.Lang
open scoped Rel.Core.Rel
open Rel.Core.Rel hiding id comp recip inter union zero le inl inr junc

variable {B : Obj}

/-- **`estConcat`**: with `TQ` transitive, a member `m` of each list `xss[t]` that no other member beats, then a member
    `b` of those `m` that no other beats, is a member of `xss.flatten` that no other beats. -/
theorem estConcat_den (TQ : Core.Rel (Obj.El (.prod B B)) (Obj.El (.prod B B)))
    (htr : ∀ b c d, TQ (b, c) (b, c) → TQ (c, d) (c, d) → TQ (b, d) (b, d)) :
    mapDen (estDen TQ) ≫ estDen TQ ⊑ graph (fun xss : List (List B.El) => xss.flatten) ≫ estDen TQ := by
  refine Core.Rel.le_iff.2 ?_
  rintro xss b ⟨ys, hmap, hb⟩
  obtain ⟨hl, hT⟩ := (mapDen_iff _ xss ys).1 hmap
  obtain ⟨hby, hbmax⟩ := (estDen_iff' TQ ys b).1 hb
  refine ⟨xss.flatten, rfl, (estDen_iff' _ _ _).2 ⟨?_, fun c hc hcb => ?_⟩⟩
  · obtain ⟨t, ht, rfl⟩ := List.getElem_of_mem hby
    exact List.mem_flatten.2 ⟨xss[t]'(by omega), List.getElem_mem _, ((estDen_iff' _ _ _).1 (hT t (by omega) ht)).1⟩
  · obtain ⟨xs, hxs, hcx⟩ := List.mem_flatten.1 hc
    obtain ⟨s, hs, rfl⟩ := List.getElem_of_mem hxs
    obtain ⟨hm, hmax⟩ := (estDen_iff' _ _ _).1 (hT s hs (by omega))
    have hmy : ys[s]'(by omega) ∈ ys := List.getElem_mem _
    by_cases hcm : c = ys[s]'(by omega)
    · exact hcm ▸ hbmax _ hmy (hcm ▸ hcb)
    · by_cases hmb : ys[s]'(by omega) = b
      · exact hmb ▸ hmax c hcx hcm
      · exact htr _ _ _ (hbmax _ hmy hmb) (hmax c hcx hcm)

/-- `F(T)` at `[A] ⟶ [B]`: `mapDen`. -/
theorem Prim.den_mapRow {A B : Obj} (T : Core.Rel (Obj.El A) (Obj.El B)) :
    Prim.den mapRow (.arr A) (.arr B) [⟨A, B, T⟩] = mapDen T := by
  have ho : ∀ ps, mapRow.objs (.arr A) (.arr B) ps = some [A, B] := by
    simp [Prim.objs, Option.orElse, mapRow, OExp.unify, Prim.vars, OExp.vars, List.eraseDups, List.eraseDupsBy,
      List.eraseDupsBy.loop, List.lookup]
  have hf : rowDens.find? (·.1.sym == mapRow.sym) =
      some ⟨RowCode.map, fun σ => Sem.one (X := σ₁ σ) (Y := σ₂ σ) mapDen⟩ := rfl
  unfold Prim.den; rw [hf, ho]; dsimp only; rw [dif_pos ⟨rfl, rfl⟩]
  simp only [Sem.one, σ₁, σ₂, List.headD, List.getD, List.getElem?_cons_succ, List.getElem?_cons_zero,
    Option.getD_some, dite_true, and_self]

/-- **`estConcat`** as the program elaborates it, `S` the variable `0` transitive: `F(est(S)) est(S) ⊑ concat est(S)`. -/
theorem Tm.estConcat_den {B : Obj} (ρ : Val)
    (h : Core.Rel.le (Tm.den ρ ((Tm.var 0 : Tm B B).comp (Tm.var 0))) (Tm.den ρ (Tm.var 0 : Tm B B))) :
    Core.Rel.le
      (Tm.den ρ ((((Tm.prim mapRow : Tm (.arr (.arr B)) (.arr B)).arg (Tm.est (pairTest (Tm.var 0 : Tm B B)))).comp
        (Tm.est (pairTest (Tm.var 0 : Tm B B))))))
      (Tm.den ρ (((Tm.prim (rowOf "concat") : Tm (.arr (.arr B)) (.arr B)).comp (Tm.est (pairTest (Tm.var 0 : Tm B B)))))) := by
  have htr : ∀ b c d, (pairTest (Tm.var 0 : Tm B B)).den ρ (b, c) (b, c) →
      (pairTest (Tm.var 0 : Tm B B)).den ρ (c, d) (c, d) → (pairTest (Tm.var 0 : Tm B B)).den ρ (b, d) (b, d) :=
    fun b c d h1 h2 => (Tm.pairTest_den ρ _ b d).2 (Core.Rel.le_iff.1 h b d
      ⟨c, (Tm.pairTest_den ρ _ b c).1 h1, (Tm.pairTest_den ρ _ c d).1 h2⟩)
  have key := Rel.Lang.estConcat_den ((pairTest (Tm.var 0 : Tm B B)).den ρ) htr
  simp only [Tm.den, Tm.argDen, Prim.den_mapRow, Tm.est_den, Prim.den_concat]
  refine Core.Rel.le_iff.2 fun xss b hxb => ?_
  obtain ⟨c, hc, hb⟩ := Core.Rel.le_iff.1 key xss b hxb
  subst hc
  exact ⟨_, rfl, hb⟩

/-- The step of the prelude's `cp`: `((a, acc), y) ↦ (a, acc ++ [(a, y)])`, as the program elaborates it. -/
abbrev cpStep (E : Obj) : Tm (.prod (.prod E (.arr (.prod E (.arr E)))) (.arr E)) (.prod E (.arr (.prod E (.arr E)))) :=
  (Tm.outl.comp Tm.outl).pair (((Tm.outl.comp Tm.outr).pair ((Tm.outl.comp Tm.outl).pair Tm.outr)).comp
    (Tm.prim (rowOf "snoc")))

/-- `cp : α×[β] ⟶ [α×β]` pairs `a` with every element: its body is `⟨⟨π₁,nil⟩,π₂⟩ loop(step) π₂`. -/
def cpTm (E : Obj) : Tm (.prod E (.arr (.arr E))) (.arr (.prod E (.arr E))) :=
  ((((Tm.outl : Tm (.prod E (.arr (.arr E))) E).pair (Tm.prim nilRow : Tm (.prod E (.arr (.arr E))) (.arr (.prod E (.arr E))))).pair Tm.outr).comp
    ((Tm.prim (rowOf "loop") : Tm (.prod (.prod E (.arr (.prod E (.arr E)))) (.arr (.arr E)))
      (.prod E (.arr (.prod E (.arr E))))).arg (cpStep E))).comp Tm.outr

theorem cp_den (ρ : Val) {E : Obj} (a : E.El) (xss : List (List E.El)) :
    (cpTm E).den ρ (a, xss) (xss.map fun x => (a, x)) := by
  simp only [cpTm, cpStep, Tm.den, Tm.argDen, Prim.den_loopRow, Prim.den_nilRow, nilDen, Prim.den_snoc]
  refine ⟨(a, xss.map fun x => (a, x)), ⟨((a, []), xss), ⟨⟨rfl, rfl⟩, rfl⟩, (loopDen_iff _ _ _).2
    ⟨fun t => (a, (xss.take t).map fun x => (a, x)), rfl, fun t ht => ?_, ?_⟩⟩, rfl⟩
  · simp only [Core.Rel.comp, Core.Rel.rpair, Core.Rel.graph]
    refine ⟨⟨_, rfl, rfl⟩, ((a, List.map (fun x => (a, x)) (List.take t xss)).2, (a, xss[t]'ht)),
      ⟨⟨⟨_, rfl, rfl⟩, ⟨_, rfl, rfl⟩, rfl⟩, ?_⟩⟩
    rw [List.take_succ_eq_append_getElem (show t < xss.length from ht), List.map_append]; rfl
  · simp

/-- **`cons713`** as the program elaborates it, `R` monotone for `cons`: the new element in front of the cheapest of the
    candidates is beaten by the cheapest of the candidates with the element in front of each. -/
theorem Tm.cons713_den {E : Obj} {R : Tm (.arr E) (.arr E)} (ρ : Val)
    (hmono : Core.Rel.le
      (Tm.den ρ ((Tm.outl.comp Tm.id).pair (Tm.outr.comp R) : Tm (.prod E (.arr E)) (.prod E (.arr E))))
      (Tm.den ρ (((Tm.prim (rowOf "cons") : Tm (.prod E (.arr E)) (.arr E)).comp R).comp
        (Tm.prim (rowOf "uncons") : Tm (.arr E) (.prod E (.arr E)))))) :
    Core.Rel.le
      (Tm.den ρ (((Tm.outl.comp Tm.id).pair (Tm.outr.comp (Tm.est (pairTest R)))).comp
        (Tm.prim (rowOf "cons") : Tm (.prod E (.arr E)) (.arr E)) : Tm (.prod E (.arr (.arr E))) (.arr E)))
      (Tm.den ρ (((cpTm E).comp ((Tm.prim mapRow : Tm (.arr (.prod E (.arr E))) (.arr (.arr E))).arg
        (Tm.prim (rowOf "cons") : Tm (.prod E (.arr E)) (.arr E)))).comp (Tm.est (pairTest R)))) := by
  refine Core.Rel.le_iff.2 fun ⟨a, xss⟩ c hc => ?_
  simp only [Tm.den, Tm.argDen, Tm.est_den, Prim.den_cons, Prim.den_mapRow, Core.Rel.comp, Core.Rel.rpair,
    Core.Rel.graph] at hc ⊢
  have hmo : ∀ (a : E.El) (m x : E.arr.El), R.den ρ m x → R.den ρ (a :: m) (a :: x) := by
    intro a m x h
    have h' := Core.Rel.le_iff.1 hmono (a, m) (a, x) (by
      simp only [Tm.den, Core.Rel.rpair, Core.Rel.comp, Core.Rel.graph, Core.Rel.id]
      exact ⟨⟨a, rfl, rfl⟩, m, rfl, h⟩)
    simp only [Tm.den, Prim.den_cons, Prim.den_uncons, Core.Rel.comp, Core.Rel.graph, Core.Rel.recip] at h'
    obtain ⟨_, ⟨_, rfl, hR⟩, rfl⟩ := h'
    exact hR
  obtain ⟨⟨a', m⟩, ⟨⟨b1, h1, h2⟩, ⟨b2, h3, hm⟩⟩, rfl⟩ := hc
  have ha : a = a' := h1.symm.trans h2
  subst ha
  obtain ⟨hmx, hmax⟩ := (estDen_iff' _ _ _).1 (h3 ▸ hm : estDen _ xss m)
  refine ⟨xss.map (a :: ·), ⟨xss.map fun x => (a, x), cp_den ρ a xss,
    (mapDen_iff _ _ _).2 ⟨by simp, fun t ht ht' => by simp⟩⟩, (estDen_iff' _ _ _).2 ⟨List.mem_map.2 ⟨m, hmx, rfl⟩, ?_⟩⟩
  intro d hd hne
  obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hd
  exact (Tm.pairTest_den ρ R _ _).2 (hmo a m x ((Tm.pairTest_den ρ R _ _).1
    (hmax x hx fun e => hne (e ▸ rfl))))

/-- `F` is a functor on `mapDen`: `F(T) F(U) = F(T U)`. -/
theorem mapDen_comp {A B C : Obj} (T : Core.Rel (Obj.El A) (Obj.El B)) (U : Core.Rel (Obj.El B) (Obj.El C)) :
    mapDen T ≫ mapDen U = mapDen (T ≫ U) := by
  funext xs zs; apply propext
  show (∃ ys, mapDen T xs ys ∧ mapDen U ys zs) ↔ mapDen (T ≫ U) xs zs
  constructor
  · rintro ⟨ys, h1, h2⟩
    obtain ⟨hl, hT⟩ := (mapDen_iff _ _ _).1 h1
    obtain ⟨hl', hU⟩ := (mapDen_iff _ _ _).1 h2
    exact (mapDen_iff _ _ _).2 ⟨hl'.trans hl, fun t ht ht' =>
      ⟨ys[t]'(by omega), hT t ht (by omega), hU t (by omega) ht'⟩⟩
  · intro h0
    obtain ⟨hl, h⟩ := (mapDen_iff _ _ _).1 h0
    have h' := fun t : Fin xs.length => h t t.2 (by omega)
    obtain ⟨f, hf⟩ : ∃ f : Fin xs.length → B.El, ∀ t : Fin xs.length,
        T (xs[t.1]'t.2) (f t) ∧ U (f t) (zs[t.1]'(by omega)) :=
      ⟨fun t => Classical.choose (h' t), fun t => Classical.choose_spec (h' t)⟩
    refine ⟨List.ofFn f, (mapDen_iff _ _ _).2 ⟨by simp, fun t ht ht' => ?_⟩,
      (mapDen_iff _ _ _).2 ⟨by simp [hl], fun t ht ht' => ?_⟩⟩
    · simpa using (hf ⟨t, ht⟩).1
    · simpa using (hf ⟨t, by omega⟩).2

/-- `F(T) F(U) = F(T U)` as the program elaborates it. -/
theorem Tm.Fcomp_den {A B C : Obj} (ρ : Val) :
    Tm.den ρ (((Tm.prim mapRow : Tm (.arr A) (.arr B)).arg (Tm.var 0 : Tm A B)).comp
      ((Tm.prim mapRow : Tm (.arr B) (.arr C)).arg (Tm.var 1 : Tm B C))) =
    Tm.den ρ ((Tm.prim mapRow : Tm (.arr A) (.arr C)).arg ((Tm.var 0 : Tm A B).comp (Tm.var 1 : Tm B C))) := by
  simp only [Tm.den, Tm.argDen, Prim.den_mapRow]; exact mapDen_comp _ _

/-- `(𝟙×T)(𝟙×U) = (𝟙×(T U))` as the program elaborates it. -/
theorem Tm.prodComp_den {E A B C : Obj} (ρ : Val) :
    Tm.den ρ (((Tm.outl.comp Tm.id : Tm (.prod E A) E).pair (Tm.outr.comp (Tm.var 0 : Tm A B))).comp
      ((Tm.outl.comp Tm.id : Tm (.prod E B) E).pair (Tm.outr.comp (Tm.var 1 : Tm B C)))) =
    Tm.den ρ ((Tm.outl.comp Tm.id : Tm (.prod E A) E).pair (Tm.outr.comp ((Tm.var 0 : Tm A B).comp (Tm.var 1 : Tm B C)))) := by
  funext p q; apply propext
  obtain ⟨e, a⟩ := p; obtain ⟨e', c⟩ := q
  simp only [Tm.den, Core.Rel.comp, Core.Rel.rpair, Core.Rel.graph, Core.Rel.id]
  constructor
  · rintro ⟨⟨e1, b⟩, ⟨⟨_, rfl, rfl⟩, ⟨_, rfl, hb⟩⟩, ⟨_, rfl, rfl⟩, ⟨_, rfl, hc⟩⟩
    exact ⟨⟨_, rfl, rfl⟩, ⟨_, rfl, _, hb, hc⟩⟩
  · rintro ⟨⟨_, rfl, rfl⟩, ⟨_, rfl, b, hb, hc⟩⟩
    exact ⟨⟨_, b⟩, ⟨⟨_, rfl, rfl⟩, ⟨_, rfl, hb⟩⟩, ⟨_, rfl, rfl⟩, ⟨_, rfl, hc⟩⟩

theorem Prim.den_zip {A B : Obj} :
    Prim.den (rowOf "zip") (.prod (.arr A) (.arr B)) (.arr (.prod A B)) [] =
      Core.Rel.graph fun p : List A.El × List B.El => p.1.zip p.2 := by
  have hs : (rowOf "zip").sig = ([], .prod (.list (.var {} "A")) (.list (.var {} "B")),
      .list (.prod (.var {} "A") (.var {} "B"))) := rfl
  have ho : (rowOf "zip").objs (.prod (.arr A) (.arr B)) (.arr (.prod A B)) [] = some [A, B] := by
    simp [Prim.objs, Prim.vars, hs, Option.orElse, OExp.unify, OExp.vars, List.eraseDups, List.eraseDupsBy,
      List.eraseDupsBy.loop, List.lookup]
  have hf : rowDens.find? (·.1.sym == (rowOf "zip").sym) =
      some ⟨RowCode.zip, fun _ _ => Core.Rel.graph fun p => p.1.zip p.2⟩ := rfl
  unfold Prim.den; simp only [List.map_nil]
  rw [hf, ho]; dsimp only; rw [dif_pos ⟨rfl, rfl⟩]; rfl

/-- `(𝟙×F(S)) zip ⊑ zip F(𝟙×S)` as the program elaborates it: `zip` truncates to the shorter list and `F(S)` keeps
    the length, so `S` moves along. -/
theorem Tm.zipLax_den {A B C : Obj} (ρ : Val) :
    Core.Rel.le
      (Tm.den ρ (((Tm.outl.comp Tm.id : Tm (.prod (.arr A) (.arr B)) (.arr A)).pair
        (Tm.outr.comp ((Tm.prim mapRow : Tm (.arr B) (.arr C)).arg (Tm.var 0 : Tm B C)))).comp
        (Tm.prim (rowOf "zip") : Tm (.prod (.arr A) (.arr C)) (.arr (.prod A C)))))
      (Tm.den ρ ((Tm.prim (rowOf "zip") : Tm (.prod (.arr A) (.arr B)) (.arr (.prod A B))).comp
        ((Tm.prim mapRow : Tm (.arr (.prod A B)) (.arr (.prod A C))).arg
          ((Tm.outl.comp Tm.id : Tm (.prod A B) A).pair (Tm.outr.comp (Tm.var 0 : Tm B C)))))) := by
  refine Core.Rel.le_iff.2 fun ⟨xs, ys⟩ zs h => ?_
  simp only [Tm.den, Tm.argDen, Prim.den_mapRow, Prim.den_zip, Core.Rel.comp, Core.Rel.rpair, Core.Rel.graph,
    Core.Rel.id] at h ⊢
  obtain ⟨⟨a, b⟩, ⟨⟨_, rfl, rfl⟩, ⟨_, rfl, hys⟩⟩, rfl⟩ := h
  obtain ⟨hl, hS⟩ := (mapDen_iff _ _ _).1 hys
  refine ⟨_, rfl, (mapDen_iff _ _ _).2 ⟨by simp [hl], fun t ht ht' => ?_⟩⟩
  obtain ⟨h1, h2⟩ := Nat.lt_min.1 (List.length_zip ▸ ht)
  simp only [List.getElem_zip]
  exact ⟨⟨_, rfl, rfl⟩, ⟨_, rfl, hS t h2 (by omega)⟩⟩

end Rel.Lang

namespace Rel.Lang
open scoped Rel.Core.Rel
open Rel.Core.Rel hiding id comp recip inter union zero le inl inr junc

/-- Fold fusion for `⊑` (B&dM 7.13): if the step `S₂` followed by `T` covers `T` followed by the step `S₁`, and the
    bases agree, then the fold of `S₁` is covered by the fold of `S₂` followed by `T`. -/
theorem foldrDen_fuse {E V W : Obj} (Te₁ : Core.Rel (Obj.El V) (Obj.El V)) (Te₂ : Core.Rel (Obj.El W) (Obj.El W))
    (S₁ : Core.Rel (Obj.El (.prod E V)) (Obj.El V)) (S₂ : Core.Rel (Obj.El (.prod E W)) (Obj.El W))
    (T : Core.Rel (Obj.El W) (Obj.El V))
    (h0 : ∀ a w, Te₁ a w → ∃ w', (∃ a', Te₂ a' w') ∧ T w' w)
    (h1 : ∀ x g q r, T g q → S₁ (x, q) r → ∃ g', S₂ (x, g) g' ∧ T g' r) (xs : List E.El) (r : V.El) :
    foldrDen Te₁ S₁ xs r → ∃ g, foldrDen Te₂ S₂ xs g ∧ T g r := by
  induction xs generalizing r with
  | nil =>
    intro h
    obtain ⟨a, ha⟩ := (foldrDen_empty _ _ _).1 h
    obtain ⟨w', ⟨a', ha'⟩, hT⟩ := h0 a r ha
    exact ⟨w', (foldrDen_empty _ _ _).2 ⟨a', ha'⟩, hT⟩
  | cons x xs ih =>
    intro h
    obtain ⟨u, hu, hS⟩ := (foldrDen_cons _ _ _ _ _).1 h
    obtain ⟨g, hg, hTg⟩ := ih u hu
    obtain ⟨g', hS2, hT'⟩ := h1 x g u r hTg hS
    exact ⟨g', (foldrDen_cons _ _ _ _ _).2 ⟨g, hg, hS2⟩, hT'⟩

/-- `ran(⟨⟩ nil)` at `[V]`: the base `[nil, S]` of a fold over `[nil, cons]` as the program elaborates it. -/
abbrev ranNil (V : Obj) : Tm (.arr V) (.arr V) :=
  (Tm.prim ranRow : Tm (.arr V) (.arr V)).arg (((Tm.uni (Gen.oneV false (USize.ofNat 1)).fst : Tm .one .one).comp
    (Tm.prim nilRow : Tm .one (.arr V))))

/-- `qfoldLe` as the program elaborates it: with the step of `qFold` followed-by-covered by the step of `genFold`
    after `T = F(U)` (`(𝟙×T) S₁ ⊑ S₂ T`), `⦇nil, S₁⦈ ⊑ ⦇nil, S₂⦈ T`. -/
theorem Tm.qfoldLe_den {E X Y : Obj} {S₁ : Tm (.prod E (.arr X)) (.arr X)} {S₂ : Tm (.prod E (.arr Y)) (.arr Y)}
    {U : Tm Y X} (ρ : Val)
    (h : Core.Rel.le
      (Tm.den ρ (((Tm.outl.comp Tm.id).pair (Tm.outr.comp ((Tm.prim mapRow : Tm (.arr Y) (.arr X)).arg U))).comp S₁))
      (Tm.den ρ (S₂.comp ((Tm.prim mapRow : Tm (.arr Y) (.arr X)).arg U)))) :
    Core.Rel.le (Tm.den ρ ((ranNil X).foldr S₁))
      (Tm.den ρ (((ranNil Y).foldr S₂).comp ((Tm.prim mapRow : Tm (.arr Y) (.arr X)).arg U))) := by
  refine Core.Rel.le_iff.2 fun xs r hr => ?_
  simp only [Tm.den, Tm.argDen, Prim.den_mapRow, Core.Rel.comp, Core.Rel.rpair, Core.Rel.graph, Core.Rel.id] at h ⊢
  have key := foldrDen_fuse (Tm.den ρ (ranNil X)) (Tm.den ρ (ranNil Y)) (Tm.den ρ S₁) (Tm.den ρ S₂) (mapDen (U.den ρ))
    ?_ ?_ xs r hr
  · exact key
  · intro a w ha
    simp only [Tm.den, Tm.argDen, Prim.den_ranRow, Prim.den_nilRow, Core.Rel.comp, Core.Rel.inter, Core.Rel.recip,
      Core.Rel.id] at ha ⊢
    obtain ⟨rfl, b, ⟨b1, hb, hn⟩, -⟩ := ha
    have h0 : a = [] := hn
    subst h0
    exact ⟨[], ⟨[], rfl, b, ⟨b1, hb, rfl⟩, b1, hb, rfl⟩, (mapDen_iff _ _ _).2 ⟨rfl, fun t ht => absurd ht (by simp)⟩⟩
  · intro x g q r hT hS
    exact Core.Rel.le_iff.1 h (x, g) r ⟨(x, q), ⟨⟨x, rfl, rfl⟩, ⟨g, rfl, hT⟩⟩, hS⟩

end Rel.Lang
