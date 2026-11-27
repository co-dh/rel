import Rel.Lang.Laws.EstUnion
import Rel.Lang.PreludeConcat
import Rel.Lang.PreludeDfn
import Rel.Lang.PreludeLoop
import Rel.Lang.PreludeEnds

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

/-- `moves` of the cylinder program as it elaborates (`moves(x) = (up(x), x, down(x))`, `up = ⟨tail, head τ⟩cat`,
    `down = ⟨last τ, init⟩cat`), the four calls each at the object instantiation `os`. -/
def Tm.movesCall (B : Obj) (os : List Obj) : Tm (.arr B) (.arr (.arr B)) :=
  .comp (B := .prod (.arr (.arr B)) (.arr (.arr B)))
    (.pair
      (.comp (B := .arr B) (.comp (B := .prod (.arr B) (.arr B))
        (.pair (Tm.tailCall B os) (.comp (B := B) (Tm.headCall B os) (.prim (rowOf "τ")))) (.prim (rowOf "cat")))
        (.prim (rowOf "τ")))
      (.comp (B := .prod (.arr (.arr B)) (.arr (.arr B)))
        (.pair (.prim (rowOf "τ"))
          (.comp (B := .arr B) (.comp (B := .prod (.arr B) (.arr B))
            (.pair (.comp (B := B) (Tm.lastCall B os) (.prim (rowOf "τ"))) (Tm.initCall B os)) (.prim (rowOf "cat")))
            (.prim (rowOf "τ"))))
        (.prim (rowOf "cat"))))
    (.prim (rowOf "cat"))

theorem Tm.movesCall_den (ρ : Val) {B : Obj} {os : List Obj} (xs : Obj.El (.arr B)) (zs : Obj.El (.arr (.arr B))) :
    (Tm.movesCall B os).den ρ xs zs ↔
      ∃ a as bs c, xs = a :: as ∧ xs = bs ++ [c] ∧ zs = [as ++ [a], xs, c :: bs] := by
  simp only [Tm.movesCall, Tm.den, Core.Rel.comp, Core.Rel.rpair, Prim.den_tau, Prim.den_cat,
    Tm.tailCall_den, Tm.headCall_den, Tm.lastCall_den, Tm.initCall_den]
  constructor
  · rintro ⟨p, ⟨⟨u, ⟨q, ⟨⟨a, hxa⟩, c', ⟨h, hc'⟩, hq2⟩, hu⟩, hpu⟩,
      ⟨r, ⟨hr1, d, ⟨s, ⟨⟨e, ⟨ys, hys⟩, hs1⟩, ⟨f, hf⟩⟩, hd⟩, hr2⟩, hpr⟩⟩, hz⟩
    have hc : c' = a := by subst hxa; simpa using hc'
    obtain ⟨-, he⟩ := List.append_inj' (hys.symm.trans hf) (by simp)
    have he' : e = f := List.singleton_inj.1 he
    refine ⟨a, q.1, s.2, f, hxa, hf, ?_⟩
    rw [hz, hpu, hpr, hr1, hr2, hd, hs1, hu, hq2, hc]
    simp [he']
  · rintro ⟨a, as, bs, c, h1, h2, rfl⟩
    exact ⟨([as ++ [a]], [xs, c :: bs]), ⟨⟨as ++ [a], ⟨(as, [a]), ⟨⟨a, h1⟩, a, ⟨by simp [h1], by simp [h1]⟩, rfl⟩, rfl⟩, rfl⟩,
      ⟨([xs], [c :: bs]), ⟨rfl, c :: bs, ⟨([c], bs), ⟨⟨c, ⟨bs, h2⟩, rfl⟩, ⟨c, h2⟩⟩, rfl⟩, rfl⟩, rfl⟩⟩, rfl⟩

/-- Two lists related elementwise (Mathlib's `List.Forall₂`, which this repository does not import). -/
inductive All2 {α β : Type} (R : α → β → Prop) : List α → List β → Prop
  | nil : All2 R [] []
  | cons {a b l l'} : R a b → All2 R l l' → All2 R (a :: l) (b :: l')

theorem All2.append {α β : Type} {R : α → β → Prop} {l₁ l₁' l₂ l₂'} (h1 : All2 R l₁ l₁') (h2 : All2 R l₂ l₂') :
    All2 R (l₁ ++ l₂) (l₁' ++ l₂') := by
  induction h1 with
  | nil => simpa using h2
  | cons h _ ih => exact .cons h ih

theorem All2.snoc_right {α β : Type} {R : α → β → Prop} :
    ∀ {bs : List β} {xs : List α} {c : β}, All2 R xs (bs ++ [c]) → ∃ ys d, xs = ys ++ [d] ∧ All2 R ys bs ∧ R d c := by
  intro bs
  induction bs with
  | nil => intro xs c h; cases h with | cons hr ht => cases ht; exact ⟨[], _, rfl, .nil, hr⟩
  | cons b bs ih =>
    intro xs c h
    cases h with | cons hr ht => obtain ⟨ys, d, rfl, h1, h2⟩ := ih ht; exact ⟨_ :: ys, d, rfl, .cons hr h1, h2⟩

/-- `F(T)` relates two lists exactly when they are `All2 T`. -/
theorem mapDen_all2 {A B : Obj} (T : Core.Rel (Obj.El A) (Obj.El B)) :
    ∀ (xs : List A.El) (ys : List B.El), mapDen T xs ys ↔ All2 T xs ys := by
  intro xs
  induction xs with
  | nil =>
    intro ys; rw [mapDen_iff]; constructor
    · rintro ⟨hl, -⟩; cases ys with | nil => exact .nil | cons => simp at hl
    · intro h; cases h; exact ⟨rfl, fun t ht => absurd ht (by simp)⟩
  | cons x xs ih =>
    intro ys; rw [mapDen_iff]; constructor
    · rintro ⟨hl, h⟩
      cases ys with
      | nil => simp at hl
      | cons y ys =>
        exact .cons (h 0 (by simp) (by simp)) ((ih ys).1 ((mapDen_iff _ _ _).2 ⟨by simpa using hl,
          fun t ht ht' => h (t + 1) (by simpa using ht) (by simpa using ht')⟩))
    · intro h
      cases h with
      | cons hr ht =>
        obtain ⟨hl, h'⟩ := (mapDen_iff _ _ _).1 ((ih _).2 ht)
        exact ⟨by simp [hl], fun t ht ht' => by
          cases t with
          | zero => exact hr
          | succ t => exact h' t (by simpa using ht) (by simpa using ht')⟩

/-- `F(S) moves ⊑ moves F(F(S))` as the program elaborates it, `S` the variable `0`, the calls of `moves` at the object
    instantiations `os` (of `S`'s target) and `os'` (of its source). -/
theorem Tm.movesLax_den {A B : Obj} {os os' : List Obj} (ρ : Val) :
    Core.Rel.le
      (Tm.den ρ (((Tm.prim mapRow : Tm (.arr A) (.arr B)).arg (Tm.var 0 : Tm A B)).comp (Tm.movesCall B os)))
      (Tm.den ρ ((Tm.movesCall A os').comp ((Tm.prim mapRow : Tm (.arr (.arr A)) (.arr (.arr B))).arg
        ((Tm.prim mapRow : Tm (.arr A) (.arr B)).arg (Tm.var 0 : Tm A B))))) := by
  refine Core.Rel.le_iff.2 fun xs zs h => ?_
  simp only [Tm.den, Tm.argDen, Prim.den_mapRow, Core.Rel.comp] at h ⊢
  obtain ⟨ys, hxy, hm⟩ := h
  obtain ⟨a', as', bs', c', hy1, hy2, rfl⟩ := (Tm.movesCall_den ρ _ _).1 hm
  subst hy1
  rw [mapDen_all2] at hxy
  obtain ⟨bs, c, hxs, hb, hSc⟩ := All2.snoc_right (hy2 ▸ hxy)
  cases hxy with
  | cons hSa hSas =>
    refine ⟨[_ ++ [_], _ :: _, c :: bs], (Tm.movesCall_den ρ _ _).2 ⟨_, _, bs, c, rfl, hxs, rfl⟩, ?_⟩
    rw [mapDen_all2]
    exact .cons ((mapDen_all2 _ _ _).2 (All2.append hSas (.cons hSa .nil)))
      (.cons ((mapDen_all2 _ _ _).2 (.cons hSa hSas)) (.cons ((mapDen_all2 _ _ _).2 (.cons hSc hb)) .nil))

theorem All2.mono {α β : Type} {R R' : α → β → Prop} (hR : ∀ a b, R a b → R' a b) {l : List α} {l' : List β}
    (h : All2 R l l') : All2 R' l l' := by
  induction h with
  | nil => exact .nil
  | cons h _ ih => exact .cons (hR _ _ h) ih

/-- `F` of a function `f` maps it over the list. -/
theorem mapDen_graph {A B : Obj} (f : A.El → B.El) (m : List A.El) (w : List B.El) :
    mapDen (fun p ys => ys = f p : Core.Rel (Obj.El A) (Obj.El B)) m w ↔ w = m.map f := by
  rw [mapDen_iff]
  constructor
  · rintro ⟨hl, h⟩
    refine List.ext_getElem (by simp [hl]) fun t h1 h2 => ?_
    rw [List.getElem_map]; exact h t (by simpa using h2) h1
  · rintro rfl; exact ⟨by simp, fun t ht ht' => by simp⟩

/-- The left fold `loop(T)` of a step `T` that is the function `f` on (acc, y) is `List.foldl f`. -/
theorem loopDen_foldl {X Y : Obj} (T : Core.Rel (Obj.El (.prod X Y)) (Obj.El X)) (f : X.El → Y.El → X.El)
    (hT : ∀ acc y w, T (acc, y) w ↔ w = f acc y) (a : X.El) (l : List Y.El) (c : X.El) :
    loopDen T (a, l) c ↔ c = l.foldl f a := by
  rw [loopDen_iff]
  have tk : ∀ t (h : t < l.length), l.take (t + 1) = l.take t ++ [l[t]] := fun t h => by
    rw [List.take_add_one, List.getElem?_eq_getElem h]; rfl
  have key : ∀ g : Nat → X.El, g 0 = a → (∀ t (ht : t < l.length), T (g t, l[t]'ht) (g (t + 1))) →
      ∀ t, t ≤ l.length → g t = (l.take t).foldl f a := by
    intro g h0 hg t
    induction t with
    | zero => intro _; simpa using h0
    | succ t ih =>
      intro ht
      rw [(hT _ _ _).1 (hg t (by omega)), ih (by omega), tk t (by omega), List.foldl_append]; rfl
  constructor
  · rintro ⟨g, h0, hg, rfl⟩
    rw [key g h0 hg _ (Nat.le_refl _)]; simp
  · rintro rfl
    refine ⟨fun t => (l.take t).foldl f a, by simp, fun t ht => (hT _ _ _).2 ?_, by simp⟩
    dsimp only
    rw [tk t ht, List.foldl_append]; rfl

/-- The step of `trans`, `zip F(snoc)`: `(acc, y) ↦ (acc zip y).map (++ [·])`. -/
def Tm.transStep (B : Obj) : Tm (.prod (.arr (.arr B)) (.arr B)) (.arr (.arr B)) :=
  .comp (B := .arr (.prod (.arr B) B)) (.prim (rowOf "zip"))
    ((Tm.prim mapRow : Tm (.arr (.prod (.arr B) B)) (.arr (.arr B))).arg (.prim (rowOf "snoc") : Tm (.prod (.arr B) B) (.arr B)))

/-- `loop(zip F(snoc))`, the left fold of `Tm.transStep` over the rows. -/
def Tm.transLoop (B : Obj) : Tm (.prod (.arr (.arr B)) (.arr (.arr B))) (.arr (.arr B)) :=
  (Tm.prim (rowOf "loop") : Tm (.prod (.arr (.arr B)) (.arr (.arr B))) (.arr (.arr B))).arg (Tm.transStep B)

/-- `trans : [[α]] ⟶ [[α]] ≜ ⟨head F(τ), tail⟩loop(zip F(snoc))` as it elaborates, the calls at `os`. -/
def Tm.transCall (B : Obj) (os : List Obj) : Tm (.arr (.arr B)) (.arr (.arr B)) :=
  .comp (B := .prod (.arr (.arr B)) (.arr (.arr B)))
    (.pair (.comp (B := .arr B) (Tm.headCall (.arr B) os)
      ((Tm.prim mapRow : Tm (.arr B) (.arr (.arr B))).arg (.prim (rowOf "τ") : Tm B (.arr B)))) (Tm.tailCall (.arr B) os))
    (Tm.transLoop B)

/-- One row `y` laid under the columns `acc`. -/
def snocRow {α : Type} (acc : List (List α)) (y : List α) : List (List α) := (acc.zip y).map fun p => p.1 ++ [p.2]

theorem Tm.transStep_den (ρ : Val) {B : Obj} (acc : List (List B.El)) (y : List B.El) (w : List (List B.El)) :
    (Tm.transStep B).den ρ (acc, y) w ↔ w = snocRow acc y := by
  simp only [Tm.transStep, Tm.den, Tm.argDen, Core.Rel.comp, Prim.den_zip, Prim.den_mapRow, Prim.den_snoc,
    Core.Rel.graph, exists_eq_left, snocRow]
  exact mapDen_graph (A := .prod (.arr B) B) (B := .arr B) (fun p => p.1 ++ [p.2]) _ _

theorem Tm.transCall_den (ρ : Val) {B : Obj} {os : List Obj} (xss : List (List B.El)) (zss : List (List B.El)) :
    (Tm.transCall B os).den ρ xss zss ↔
      ∃ r rs, xss = r :: rs ∧ zss = rs.foldl snocRow (r.map fun a => [a]) := by
  have hl : ∀ (p : List (List B.El) × List (List B.El)) zs, (Tm.transLoop B).den ρ p zs ↔ zs = p.2.foldl snocRow p.1 := by
    intro p zs
    simp only [Tm.transLoop, Tm.den, Tm.argDen, Prim.den_loopRow]
    exact loopDen_foldl (X := .arr (.arr B)) (Y := .arr B) _ snocRow (fun acc y w => Tm.transStep_den ρ acc y w) p.1 p.2 zs
  simp only [Tm.transCall, Tm.den, Tm.argDen, Core.Rel.comp, Core.Rel.rpair, hl, Tm.headCall_den, Tm.tailCall_den, Prim.den_mapRow,
    Prim.den_tau]
  constructor
  · rintro ⟨⟨c, rs⟩, ⟨⟨b1, ⟨h, hb1⟩, hm⟩, ⟨a, hx⟩⟩, hz⟩
    have hb : b1 = a := by subst hx; simpa using hb1
    subst hb
    rw [mapDen_graph (A := B) (B := .arr B) (fun a => [a])] at hm
    exact ⟨_, rs, hx, by rw [hz, hm]⟩
  · rintro ⟨r, rs, rfl, rfl⟩
    exact ⟨(r.map fun a => [a], rs), ⟨⟨r, ⟨by simp, rfl⟩, (mapDen_graph (A := B) (B := .arr B) (fun a => [a]) _ _).2 rfl⟩, ⟨r, rfl⟩⟩, rfl⟩

theorem snocRow_all2 {α β : Type} {S : α → β → Prop} {acc : List (List α)} {acc' : List (List β)}
    (h : All2 (All2 S) acc acc') : ∀ {y y'}, All2 S y y' → All2 (All2 S) (snocRow acc y) (snocRow acc' y') := by
  induction h with
  | nil => intro y y' _; exact .nil
  | cons hl _ ih =>
    intro y y' hy
    cases hy with
    | nil => exact .nil
    | cons hx hys => exact .cons (All2.append hl (.cons hx .nil)) (ih hys)

theorem foldl_snocRow_all2 {α β : Type} {S : α → β → Prop} {rs : List (List α)} {rs' : List (List β)}
    (h : All2 (All2 S) rs rs') : ∀ {acc acc'}, All2 (All2 S) acc acc' →
      All2 (All2 S) (rs.foldl snocRow acc) (rs'.foldl snocRow acc') := by
  induction h with
  | nil => intro acc acc' ha; exact ha
  | cons hy _ ih => intro acc acc' ha; exact ih (snocRow_all2 ha hy)

theorem singleton_all2 {α β : Type} {S : α → β → Prop} {r : List α} {r' : List β} (h : All2 S r r') :
    All2 (All2 S) (r.map fun a => [a]) (r'.map fun a => [a]) := by
  induction h with
  | nil => exact .nil
  | cons hx _ ih => exact .cons (.cons hx .nil) ih

/-- `F(F(S)) trans ⊑ trans F(F(S))` as the program elaborates it, `S` the variable `0`, the calls of `trans` at the object
    instantiations `os` (of `S`'s target) and `os'` (of its source). -/
theorem Tm.transLax_den {A B : Obj} {os os' : List Obj} (ρ : Val) :
    Core.Rel.le
      (Tm.den ρ (((Tm.prim mapRow : Tm (.arr (.arr A)) (.arr (.arr B))).arg
        ((Tm.prim mapRow : Tm (.arr A) (.arr B)).arg (Tm.var 0 : Tm A B))).comp (Tm.transCall B os)))
      (Tm.den ρ ((Tm.transCall A os').comp ((Tm.prim mapRow : Tm (.arr (.arr A)) (.arr (.arr B))).arg
        ((Tm.prim mapRow : Tm (.arr A) (.arr B)).arg (Tm.var 0 : Tm A B))))) := by
  refine Core.Rel.le_iff.2 fun xss zss h => ?_
  simp only [Tm.den, Tm.argDen, Prim.den_mapRow, Core.Rel.comp] at h ⊢
  obtain ⟨yss, hxy, ht⟩ := h
  obtain ⟨r', rs', rfl, rfl⟩ := (Tm.transCall_den ρ _ _).1 ht
  rw [mapDen_all2] at hxy
  cases hxy with
  | cons hr hrs =>
    have hr' := (mapDen_all2 _ _ _).1 hr
    have hrs' := hrs.mono fun a b h => (mapDen_all2 _ a b).1 h
    exact ⟨_, (Tm.transCall_den ρ _ _).2 ⟨_, _, rfl, rfl⟩, (mapDen_all2 _ _ _).2
      ((foldl_snocRow_all2 hrs' (singleton_all2 hr')).mono fun a b h => (mapDen_all2 _ a b).2 h)⟩

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

namespace Rel.Lang
open scoped Rel.Core.Rel
open Rel.Core.Rel hiding id comp recip inter union zero le inl inr junc

/-- Composition distributes over `∪` on the right: `X (A ∪ B) = X A ∪ X B`, as the program elaborates it. -/
theorem Tm.compUnion_den {A B C : Obj} (ρ : Val) :
    Tm.den ρ ((Tm.var 0 : Tm A B).comp ((Tm.var 1 : Tm B C).join (Tm.var 2 : Tm B C))) =
    Tm.den ρ (((Tm.var 0 : Tm A B).comp (Tm.var 1 : Tm B C)).join ((Tm.var 0 : Tm A B).comp (Tm.var 2 : Tm B C))) := by
  simp only [Tm.den]; exact Core.Rel.comp_union _ _ _

/-- ... and on the left: `(A ∪ B) X = A X ∪ B X`. -/
theorem Tm.unionComp_den {A B C : Obj} (ρ : Val) :
    Tm.den ρ (((Tm.var 0 : Tm A B).join (Tm.var 1 : Tm A B)).comp (Tm.var 2 : Tm B C)) =
    Tm.den ρ (((Tm.var 0 : Tm A B).comp (Tm.var 2 : Tm B C)).join ((Tm.var 1 : Tm A B).comp (Tm.var 2 : Tm B C))) := by
  simp only [Tm.den]; exact Core.Rel.union_comp _ _ _

/-- `(𝟙×T) π₁ ⊑ π₁`: `T` is only read, so the left component passes through. -/
theorem Tm.pi1Lax_den {E A B : Obj} (ρ : Val) :
    Core.Rel.le
      (Tm.den ρ (((Tm.outl.comp Tm.id : Tm (.prod E A) E).pair (Tm.outr.comp (Tm.var 0 : Tm A B))).comp
        (Tm.outl : Tm (.prod E B) E)))
      (Tm.den ρ (Tm.outl : Tm (.prod E A) E)) := by
  refine Core.Rel.le_iff.2 fun ⟨e, a⟩ e' h => ?_
  simp only [Tm.den, Core.Rel.comp, Core.Rel.rpair, Core.Rel.graph, Core.Rel.id] at h ⊢
  obtain ⟨⟨e1, b⟩, ⟨⟨_, rfl, rfl⟩, ⟨_, rfl, hb⟩⟩, rfl⟩ := h
  rfl

/-- `dom(π₂ head)` is the coreflexive of the pairs whose list is non-empty. -/
theorem Tm.dom_head_iff {E A : Obj} (ρ : Val) (e : E.El) (xs : A.arr.El) (q : (Obj.prod E A.arr).El) :
    (Tm.dom (Tm.outr.comp Tm.at0 : Tm (.prod E A.arr) A)).den ρ (e, xs) q ↔ q = (e, xs) ∧ 0 < xs.length := by
  have hR : ∀ (q : (Obj.prod E A.arr).El) b, (Tm.outr.comp Tm.at0 : Tm (.prod E A.arr) A).den ρ q b ↔
      ∃ h : 0 < q.2.length, b = q.2[0]'h := fun q b => by
    simp only [Tm.den, Core.Rel.comp, Core.Rel.graph]
    exact ⟨fun ⟨_, h1, h2⟩ => h1 ▸ (Tm.at0_den ρ _ _).1 h2, fun h => ⟨_, rfl, (Tm.at0_den ρ _ _).2 h⟩⟩
  simp only [Tm.dom_den, Core.Rel.comp, Core.Rel.inter, Core.Rel.id, Core.Rel.recip, hR]
  constructor
  · rintro ⟨rfl, b, ⟨h, rfl⟩, h', -⟩
    exact ⟨rfl, h⟩
  · rintro ⟨rfl, h⟩
    exact ⟨rfl, _, ⟨h, rfl⟩, h, rfl⟩

/-- `(𝟙×F(S)) dom(π₂ head) ⊑ dom(π₂ head) (𝟙×F(S))`: `F(S)` keeps the length, so a non-empty image has a non-empty
    source. -/
theorem Tm.domLax_den {E A B : Obj} (ρ : Val) :
    Core.Rel.le
      (Tm.den ρ (((Tm.outl.comp Tm.id : Tm (.prod E A.arr) E).pair
        (Tm.outr.comp ((Tm.prim mapRow : Tm A.arr B.arr).arg (Tm.var 0 : Tm A B)))).comp
        (Tm.dom (Tm.outr.comp Tm.at0 : Tm (.prod E B.arr) B))))
      (Tm.den ρ ((Tm.dom (Tm.outr.comp Tm.at0 : Tm (.prod E A.arr) A)).comp
        ((Tm.outl.comp Tm.id : Tm (.prod E A.arr) E).pair
          (Tm.outr.comp ((Tm.prim mapRow : Tm A.arr B.arr).arg (Tm.var 0 : Tm A B)))))) := by
  refine Core.Rel.le_iff.2 fun p q h => ?_
  simp only [Tm.den, Tm.argDen, Prim.den_mapRow, Core.Rel.comp, Core.Rel.rpair, Core.Rel.graph, Core.Rel.id] at h ⊢
  obtain ⟨⟨e1, ys⟩, ⟨⟨_, rfl, rfl⟩, ⟨_, rfl, hm⟩⟩, hd⟩ := h
  obtain ⟨rfl, hl⟩ := (Tm.dom_head_iff ρ _ _ _).1 hd
  have hlen := ((mapDen_iff _ _ _).1 hm).1
  exact ⟨p, (Tm.dom_head_iff ρ p.1 p.2 _).2 ⟨rfl, by dsimp only at hlen hl ⊢; omega⟩, ⟨_, rfl, rfl⟩, ⟨_, rfl, hm⟩⟩

/-- `(𝟙×F(S)) (𝟙 − dom(π₂ head)) ⊑ (𝟙 − dom(π₂ head)) (𝟙×F(S))`: an empty image has an empty source. -/
theorem Tm.diffLax_den {E A B : Obj} (ρ : Val) :
    Core.Rel.le
      (Tm.den ρ (((Tm.outl.comp Tm.id : Tm (.prod E A.arr) E).pair
        (Tm.outr.comp ((Tm.prim mapRow : Tm A.arr B.arr).arg (Tm.var 0 : Tm A B)))).comp
        (Tm.diff Tm.id (Tm.dom (Tm.outr.comp Tm.at0 : Tm (.prod E B.arr) B)))))
      (Tm.den ρ ((Tm.diff Tm.id (Tm.dom (Tm.outr.comp Tm.at0 : Tm (.prod E A.arr) A))).comp
        ((Tm.outl.comp Tm.id : Tm (.prod E A.arr) E).pair
          (Tm.outr.comp ((Tm.prim mapRow : Tm A.arr B.arr).arg (Tm.var 0 : Tm A B)))))) := by
  refine Core.Rel.le_iff.2 fun p q h => ?_
  simp only [Tm.den, Tm.argDen, Prim.den_mapRow, Core.Rel.comp, Core.Rel.rpair, Core.Rel.graph, Core.Rel.id,
    Core.Rel.diff_apply] at h ⊢
  obtain ⟨⟨e1, ys⟩, ⟨⟨_, rfl, rfl⟩, ⟨_, rfl, hm⟩⟩, hq, hd⟩ := h
  have hlen := ((mapDen_iff _ _ _).1 hm).1
  subst hq
  exact ⟨p, ⟨rfl, fun h => hd ((Tm.dom_head_iff ρ _ _ _).2
    ⟨rfl, by have := ((Tm.dom_head_iff ρ _ _ _).1 h).2; dsimp only at hlen this ⊢; omega⟩)⟩, ⟨_, rfl, rfl⟩, ⟨_, rfl, hm⟩⟩

/-- `F(τ) ⊑ F(τ τ) F(est(S))`: `est(S)` of a one-element list is its element. -/
theorem Tm.tauEst_den {A : Obj} (ρ : Val) :
    Core.Rel.le
      (Tm.den ρ ((Tm.prim mapRow : Tm A.arr A.arr.arr).arg (Tm.prim (rowOf "τ") : Tm A A.arr)))
      (Tm.den ρ (((Tm.prim mapRow : Tm A.arr A.arr.arr.arr).arg
          ((Tm.prim (rowOf "τ") : Tm A A.arr).comp (Tm.prim (rowOf "τ") : Tm A.arr A.arr.arr))).comp
        ((Tm.prim mapRow : Tm A.arr.arr.arr A.arr.arr).arg
          (Tm.est (pairTest (Tm.var 0 : Tm A.arr A.arr)))))) := by
  refine Core.Rel.le_iff.2 fun xs ys h => ?_
  simp only [Tm.den, Tm.argDen, Prim.den_mapRow, Core.Rel.comp, Tm.est_den, Prim.den_tau, Core.Rel.graph] at h ⊢
  obtain ⟨hl, hT⟩ := (mapDen_iff _ _ _).1 h
  refine ⟨xs.map fun a => [[a]], (mapDen_iff _ _ _).2 ⟨by simp, fun t ht ht' => ⟨[xs[t]'ht], rfl, by simp⟩⟩,
    (mapDen_iff _ _ _).2 ⟨by simp [hl], fun t ht ht' => ?_⟩⟩
  have hy := hT t (by omega) (by omega)
  refine (estDen_iff _ _ _).2 ⟨by simp [hy], ?_⟩
  rintro ⟨c, hc, hne, -⟩
  simp at hc hy
  exact hne (by simp [hc, hy])

end Rel.Lang
