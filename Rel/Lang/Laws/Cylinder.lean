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

end Rel.Lang
