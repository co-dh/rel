import Rel.RepWF
import Rel.Run.Cast
import Rel.Run.Where

/-! **`Tab.WF` kept by the rounds, `thin`, the value verbs, `$` and the folds on cells** (PLAN 8.5), on the
lemmas of `Rel/RepWF.lean` (`Tab.pack_wf` and the List ops'). `positions` is `positions_spec` (`Rel/RepWhere.lean`). -/

namespace Rel
open Rel.Ext Rel.Kernel Rel.Verify

namespace Tab

/-- **`foldRounds` keeps `Tab.WF`** where `peel` and `step` do: each round's `P` and `out` are `pack`, `step`, `∪`,
`−`, `≫`, `dom` of `Tab.WF` tables. -/
theorem foldRounds_wf {K E V : Obj} {peel : Tab K (.arr E) → Except String (Tab K E × Tab K (.arr E))}
    {step : Tab K V → Tab K E → Except String (Tab K V)}
    (hpeel : ∀ r p, peel r = .ok p → r.WF → p.1.WF ∧ p.2.WF)
    (hstep : ∀ P el t, step P el = .ok t → P.WF → el.WF → t.WF) :
    ∀ {f : Nat} {rest : Tab K (.arr E)} {P out t : Tab K V}, foldRounds peel step f rest P out = .ok t →
      rest.WF → P.WF → out.WF → t.WF
  | 0, _, _, _, _, h, _, _, _ => by simp [foldRounds, throw, throwThe, MonadExceptOf.throw] at h
  | f + 1, rest, P, out, t, h, hr, hP, hw => by
    simp only [foldRounds] at h
    split at h
    · simp only [pure, Except.pure, Except.ok.injEq] at h; exact h ▸ hw
    simp only [bind, Except.bind_eq_ok'] at h
    obtain ⟨_, -, p, hp, s1, hs1, s2, hs2, d, hd, c, hc, x, hx, u, hu, o, ho, h⟩ := h
    obtain ⟨wel, wr⟩ := hpeel _ _ hp hr
    exact foldRounds_wf hpeel hstep h wr (Tab.pack_wf hs2 (hstep _ _ _ hs1 hP wel))
      (Tab.pack_wf ho (union_wf hu hw (diff_wf hx hP (comp_wf hc (dom_wf hd wel) hP))))

theorem peelL_wf {K E : Obj} {rest : Tab K (.arr E)} {p : Tab K E × Tab K (.arr E)}
    (h : peelL rest = .ok p) (hr : rest.WF) : p.1.WF ∧ p.2.WF := by
  simp only [peelL, bind, Except.bind_eq_ok', pure, Except.pure, Except.ok.injEq] at h
  obtain ⟨u, hu, c, hc, a, ha, x, hx, b, hb, y, hy, rfl⟩ := h
  have wc := comp_wf hc hr (uncons_wf hu hr.2)
  exact ⟨comp_wf hx wc (outl_wf ha wc.2), comp_wf hy wc (outr_wf hb wc.2)⟩

theorem peelR_wf {K E : Obj} {rest : Tab K (.arr E)} {p : Tab K E × Tab K (.arr E)}
    (h : peelR rest = .ok p) (hr : rest.WF) : p.1.WF ∧ p.2.WF := by
  simp only [peelR, bind, Except.bind_eq_ok', pure, Except.pure, Except.ok.injEq] at h
  obtain ⟨u, hu, c, hc, a, ha, x, hx, b, hb, y, hy, rfl⟩ := h
  have wc := comp_wf hc hr (unsnoc_wf hu hr.2)
  exact ⟨comp_wf hx wc (outr_wf ha wc.2), comp_wf hy wc (outl_wf hb wc.2)⟩

/-- **`P ≫ loop(F)` keeps `Tab.WF`** where `F` does (`foldRounds_wf`, `peelL_wf`). -/
theorem loop_wf {K X Y : Obj}
    {F : Tab (.prod X Y) (.prod X Y) → Except String (Tab (.prod X Y) X)}
    (hF : ∀ D t, F D = .ok t → D.WF → t.WF) {P : Tab K (.prod X (.arr Y))} {t : Tab K X} (h : loop F P = .ok t)
    (hP : P.WF) : t.WF := by
  simp only [loop, bind, Except.bind_eq_ok'] at h
  obtain ⟨D, hD, a, ha, r, hr, b, hb, o, ho, z, hz, R, hR, h⟩ := h
  have wD := ran_wf hD hP
  refine comp_wf h hP (foldRounds_wf (fun _ _ => peelL_wf) (fun S el t hs wS wel => ?_) hR
    (comp_wf hr wD (outr_wf ha wD.2)) (comp_wf ho wD (outl_wf hb wD.2)) (zero_wf hz))
  simp only [Except.bind_eq_ok'] at hs
  obtain ⟨p, hp, e, he, f, hf, hs⟩ := hs
  have wp := pair_wf hp wS wel
  exact comp_wf hs wp (hF _ _ hf (ran_wf he wp))

/-- **`P ≫ merge(Q)` keeps `Tab.WF`** where `q` does: a round's state is `≫`, `pair`, `∪`, `−`, `dom`, `snoc` of the
state before (`foldRounds_wf`, `peelL_wf`). -/
theorem mergeRound_wf {K B : Obj}
    {q : Tab (.prod B B) (.prod B B) → Except String (Tab (.prod B B) (.prod B B))}
    (hq : ∀ D t, q D = .ok t → D.WF → t.WF) {S T : Tab K (.prod (.prod (.arr B) (.arr B)) (.arr B))} {el : Tab K B}
    (hs : mergeRound q S el = .ok T) (wS : S.WF) : T.WF := by
  simp only [mergeRound, bind, Except.bind_eq_ok'] at hs
  obtain ⟨o1, h1, xy, hxy, o2, h2, acc, hacc, o3, h3, x, hx, o4, h4, y, hy, u1, hu1, ux, hux, u2, hu2, uy, huy,
    o5, h5, a, ha, o6, h6, b, hb, ab, hab, r1, hr1, dg, hdg, cm, hcm, l, hl, dy, hdy, dx, hdx, df, hdf, tx, htx,
    ty, hty, o7, h7, c7, hc7, p1, hp1, q1, hq1, s1, hs1, sx, hsx, o8, h8, c8, hc8, p2, hp2, q2, hq2, s2, hs2, sy, hsy,
    c1, hc1, c2, hc2, hs⟩ := hs
  have wxy := comp_wf hxy wS (outl_wf h1 wS.2)
  have wacc := comp_wf hacc wS (outr_wf h2 wS.2)
  have wx := comp_wf hx wxy (outl_wf h3 wxy.2)
  have wy := comp_wf hy wxy (outr_wf h4 wxy.2)
  have wux := comp_wf hux wx (uncons_wf hu1 wx.2)
  have wuy := comp_wf huy wy (uncons_wf hu2 wy.2)
  have wa := comp_wf ha wux (outl_wf h5 wux.2)
  have wb := comp_wf hb wuy (outl_wf h6 wuy.2)
  have wab := pair_wf hab wa wb
  have wl := dom_wf hl (comp_wf hcm wab (diag_wf hq hdg (ran_wf hr1 wab)))
  have wdy := dom_wf hdy wuy
  have wtx := union_wf htx wl (diff_wf hdf (dom_wf hdx wux) wdy)
  have wty := diff_wf hty wdy wl
  have wsx := pair_wf hsx (pair_wf hp1 (comp_wf hc7 wux (outr_wf h7 wux.2)) wy) (snoc_wf hs1 (pair_wf hq1 wacc wa))
  have wsy := pair_wf hsy (pair_wf hp2 wx (comp_wf hc8 wuy (outr_wf h8 wuy.2))) (snoc_wf hs2 (pair_wf hq2 wacc wb))
  exact union_wf hs (comp_wf hc1 wtx wsx) (comp_wf hc2 wty wsy)

theorem merge_wf {K B : Obj}
    {q : Tab (.prod B B) (.prod B B) → Except String (Tab (.prod B B) (.prod B B))}
    (hq : ∀ D t, q D = .ok t → D.WF → t.WF) {P : Tab K (.prod (.arr B) (.arr B))} {t : Tab K (.arr B)}
    (h : merge q P = .ok t) (hP : P.WF) : t.WF := by
  simp only [merge, bind, Except.bind_eq_ok'] at h
  obtain ⟨D, hD, c, hc, nl, hnl, I, hI, z, hz, out, hout, a, ha, o, ho, h⟩ := h
  have wD := ran_wf hD hP
  have wout : out.WF := foldRounds_wf (fun _ _ => peelL_wf) (fun _ _ _ hs wS _ => mergeRound_wf hq hs wS) hout
    (cat_wf hc wD) (pair_wf hI wD (nil_wf hnl wD.1)) (zero_wf hz)
  exact comp_wf h hP (comp_wf ho wout (outr_wf ha wout.2))

/-- **`bump(Q)` keeps `Tab.WF`** where `q` does: its answer is `≫`, `pair`, `∪`, `−`, `dom`, `cons` of the round's
pairs. -/
theorem bump_wf {B : Obj} {q : Tab (.prod B B) (.prod B B) → Except String (Tab (.prod B B) (.prod B B))}
    (hq : ∀ D t, q D = .ok t → D.WF → t.WF) {p : Tab (.arr B) (.prod B (.arr B))} {t : Tab (.arr B) (.arr B)}
    (hs : bump q p = .ok t) (wp : p.WF) : t.WF := by
  simp only [bump, bind, Except.bind_eq_ok'] at hs
  obtain ⟨E, hE, o1, h1, x, hx, o2, h2, ys, hys, u0, hu0, u, hu, o3, h3, b, hb, ab, hab, ba, hba,
    r1, hr1, d1, hd1, c1, hc1, up, hup, r2, hr2, d2, hd2, c2, hc2, down, hdown, du, hdu, e1, he1, e2, he2, e3, he3,
    lone, hlone, o4, h4, bs, hbs, k1, hk1, xb, hxb, k2, hk2, c3, hc3, v1, hv1, c4, hc4, r, hr, hs⟩ := hs
  have wE := ran_wf hE wp
  have wx := comp_wf hx wE (outl_wf h1 wE.2)
  have wys := comp_wf hys wE (outr_wf h2 wE.2)
  have wu := comp_wf hu wys (uncons_wf hu0 wys.2)
  have wb := comp_wf hb wu (outl_wf h3 wu.2)
  have wab := pair_wf hab wx wb
  have wba := pair_wf hba wb wx
  have wup := dom_wf hup (comp_wf hc1 wab (diag_wf hq hd1 (ran_wf hr1 wab)))
  have wdown := dom_wf hdown (comp_wf hc2 wba (diag_wf hq hd2 (ran_wf hr2 wba)))
  have wdu := dom_wf hdu wu
  have wlone := union_wf hlone (diff_wf he1 wE wdu) (diff_wf he3 (diff_wf he2 wdu wup) wdown)
  have wbs := comp_wf hbs wu (outr_wf h4 wu.2)
  have wr := union_wf hr (union_wf hv1 (cons_wf hk1 wlone) (comp_wf hc3 wup (cons_wf hk2 (pair_wf hxb wx wbs))))
    (comp_wf hc4 wdown wys)
  exact comp_wf hs wp wr

/-- **`thinL(Q)` keeps `Tab.WF`** where `q` does: a round is `bump(Q)` of the round's pairs (`foldRounds_wf`,
`peelR_wf`, `bump_wf`). -/
theorem thinL_wf {B : Obj} {n : USize}
    {q : Tab (.prod B B) (.prod B B) → Except String (Tab (.prod B B) (.prod B B))}
    (hq : ∀ D t, q D = .ok t → D.WF → t.WF) {X : Vals (.arr B) n} {t : Tab (.arr B) (.arr B)}
    (h : thinL q X = .ok t) (hX : Vals.WF X) : t.WF := by
  simp only [thinL, bind, Except.bind_eq_ok'] at h
  obtain ⟨I, hI, N, hN, z, hz, h⟩ := h
  refine foldRounds_wf (fun _ _ => peelR_wf) (fun P el t hs wP wel => ?_) h (idU_wf hI hX)
    (nil_wf hN hX) (zero_wf hz)
  simp only [Except.bind_eq_ok'] at hs
  obtain ⟨p, hp, hs⟩ := hs
  exact bump_wf hq hs (pair_wf hp wel wP)

/-- **`thin(Q)` keeps `Tab.WF`** where `q` does: `mem`, `pair`, `ran`, `diag`, `−`, `≫`, then `lam`. -/
theorem thin_wf {B : Obj} {n : USize} {q : Tab (.prod B B) (.prod B B) → Except String (Tab (.prod B B) (.prod B B))}
    (hq : ∀ D t, q D = .ok t → D.WF → t.WF) {X : Vals (.arr B) n} {t : Tab (.arr B) (.arr B)}
    (h : thin q X = .ok t) (hX : Vals.WF X) : t.WF := by
  simp only [thin, bind, Except.bind_eq_ok'] at h
  obtain ⟨G, hG, P, hP, D, hD, Δ, hΔ, a, ha, b, hb, w, hw, c, hc, d, hd, Y, hY, e, he, f, hf, g, hg, h⟩ := h
  have wG := mem_wf hG hX
  have wP := pair_wf hP wG wG
  have wD := ran_wf hD wP
  have wΔ := diag_wf hq hΔ wD
  have wY := diff_wf hY wΔ (dom_wf hd (comp_wf hc (pair_wf hw (outr_wf ha wD.1) (outl_wf hb wD.1)) wΔ))
  exact lam_wf h hX (diff_wf hg wG (comp_wf hf wP (outr_wf he wY.1)))

/-- **`est q X` denotes `estDen`** (`Tab.est`), its test `q` agreeing with `TQ` on the diagonal of the pairs it is
given (`QDiag`): `(xs, b)` of `G = ∋` dropped exactly where some `(b, c)` of `ran ⟨G, G⟩` off the diagonal fails
`TQ`. -/
theorem est_holds {B : Obj} {q : Tab (.prod B B) (.prod B B) → Except String (Tab (.prod B B) (.prod B B))}
    {TQ : Core.Rel (Obj.El (.prod B B)) (Obj.El (.prod B B))} (hq : QDiag q TQ) (hqw : ∀ D t, q D = .ok t → D.WF → t.WF)
    {n : USize} {X : Vals (.arr B) n} {T : Tab (.arr B) B} (h : Tab.est q X = .ok T)
    (hX : Vals.WF X) (xs : List B.El) (b : B.El) :
    T.Holds xs b ↔ (∃ i, X.row i = xs) ∧ Lang.estDen TQ xs b := by
  unfold Tab.est at h; simp only [bind] at h
  rw [Except.bind_eq_ok'] at h; obtain ⟨G, hG, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨P, hP, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨D, hD, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨V, hV, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨T1, hT1, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨Y1, hY1, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨W, hW, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨RW, hRW, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨Y, hY, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨O, hO, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨PO, hPO, h⟩ := h
  have wG := mem_wf hG hX
  have wP := pair_wf hP wG wG
  have wD := ran_wf hD wP
  have wV := ran_wf hV wG
  have wY1 := diff_wf hY1 wD (hqw _ _ hT1 wD)
  have wRW := ran_wf hRW (pair_wf hW wV wV)
  have wY := diff_wf hY wY1 wRW
  have wPO := comp_wf hPO wP (outl_wf hO wY.1)
  have eP : ∀ xs p, P.Holds xs p ↔ ((∃ i, X.row i = xs) ∧ p.1 ∈ xs) ∧ ((∃ i, X.row i = xs) ∧ p.2 ∈ xs) :=
    fun xs p => (pair_holds hP wG wG xs p).trans (and_congr (mem_holds hG hX _ _) (mem_holds hG hX _ _))
  -- a pair of one array's elements is a row of `D`, so `q D` agrees with `TQ` there
  have hQ : ∀ xs p, P.Holds xs p → (T1.Holds p p ↔ TQ p p) := fun xs p hx =>
    hq D T1 (ran_wf hD (pair_wf hP (mem_wf hG hX) (mem_wf hG hX))) hT1 p
      (let ⟨i, _, e⟩ := (ran_holds hD p p).2 ⟨rfl, xs, hx⟩; ⟨i, e⟩)
  -- `Y`: the pairs `q` is asked about, off the diagonal, failing `TQ`
  have eY : ∀ p p', Y.Holds p p' ↔ p = p' ∧ (∃ xs, P.Holds xs p) ∧ ¬TQ p p ∧ p.1 ≠ p.2 := by
    intro p p'
    rw [diff_holds hY wY1 wRW, diff_holds hY1 wD (hqw _ _ hT1 wD), ran_holds hD, ran_holds hRW]
    constructor
    · rintro ⟨⟨⟨rfl, xs, hx⟩, hq'⟩, hr⟩
      refine ⟨rfl, ⟨xs, hx⟩, fun t => hq' ((hQ xs p hx).2 t), fun e => hr ⟨rfl, p.1, ?_⟩⟩
      have hb := (mem_holds hG hX xs p.1).2 ((eP xs p).1 hx).1
      rw [pair_holds hW wV wV]
      exact ⟨(ran_holds hV _ _).2 ⟨rfl, xs, hb⟩, (ran_holds hV _ _).2 ⟨e, xs, hb⟩⟩
    · rintro ⟨rfl, ⟨xs, hx⟩, hq', hne⟩
      refine ⟨⟨⟨rfl, xs, hx⟩, fun t => hq' ((hQ xs p hx).1 t)⟩, ?_⟩
      rintro ⟨-, a, hw⟩
      obtain ⟨h1, h2⟩ := (pair_holds hW wV wV a p).1 hw
      exact hne (((ran_holds hV _ _).1 h1).1.symm.trans ((ran_holds hV _ _).1 h2).1)
  rw [diff_holds h wG wPO, mem_holds hG hX, comp_holds hPO wP (outl_wf hO wY.1)]
  constructor
  · rintro ⟨⟨hx, hb⟩, hno⟩
    refine ⟨hx, hb, fun ⟨c, hc, hne, hq'⟩ => hno ⟨(b, c), (eP xs (b, c)).2 ⟨⟨hx, hb⟩, hx, hc⟩, ?_⟩⟩
    refine (outl_holds hO _ b).2 ⟨(Rep.keyRowRep Y _).2 ⟨(b, c), (eY _ _).2 ⟨rfl, ⟨xs, ?_⟩, hq', fun e => hne e.symm⟩⟩, rfl⟩
    exact (eP xs (b, c)).2 ⟨⟨hx, hb⟩, hx, hc⟩
  · rintro ⟨hx, hb, hno⟩
    refine ⟨⟨hx, hb⟩, fun ⟨p, hp, ho⟩ => ?_⟩
    obtain ⟨hk, hb1⟩ := (outl_holds hO p b).1 ho
    obtain ⟨p', hy⟩ := (Rep.keyRowRep Y p).1 hk
    obtain ⟨rfl, -, hq', hne⟩ := (eY p p').1 hy
    obtain ⟨b', c⟩ := p
    obtain rfl : b = b' := hb1
    exact hno ⟨c, ((eP xs _).1 hp).2.2, fun e => hne e.symm, hq'⟩

/-- **`thin q X` denotes `thinDen`** (`Tab.thin`), its test `q` agreeing with `TQ` on the diagonal of the pairs it is
given: `(xs, c)` of `G = ∋` dropped exactly where some `(b, c)` of `D = ran ⟨G, G⟩` has `TQ (b, c) (b, c)` and its
swap has not; then `lam_den`. -/
theorem thin_den {B : Obj} {q : Tab (.prod B B) (.prod B B) → Except String (Tab (.prod B B) (.prod B B))}
    {TQ : Core.Rel (Obj.El (.prod B B)) (Obj.El (.prod B B))} (hq : QDiag q TQ) (hqw : ∀ D t, q D = .ok t → D.WF → t.WF)
    {n : USize} {X : Vals (.arr B) n} {T : Tab (.arr B) (.arr B)} (h : Tab.thin q X = .ok T) (hX : Vals.WF X)
    (xs ys : List B.El) : T.Holds xs ys ↔ (∃ i, X.row i = xs) ∧ Lang.thinDen TQ xs ys := by
  unfold Tab.thin at h; simp only [bind] at h
  rw [Except.bind_eq_ok'] at h; obtain ⟨G, hG, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨P, hP, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨D, hD, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨Dg, hDg, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨o1, ho1, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨o2, ho2, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨w, hw, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨WD, hWD, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨S, hS, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨Y, hY, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨O, hO, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨PO, hPO, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨Gd, hGd, h⟩ := h
  have wG := mem_wf hG hX
  have wP := pair_wf hP wG wG
  have wD := ran_wf hD wP
  have wDg := diag_wf hqw hDg wD
  have ww := pair_wf hw (outr_wf ho1 wD.1) (outl_wf ho2 wD.1)
  have wWD := comp_wf hWD ww wDg
  have wS := dom_wf hS wWD
  have wY := diff_wf hY wDg wS
  have wPO := comp_wf hPO wP (outr_wf hO wY.1)
  have wGd := diff_wf hGd wG wPO
  have eP : ∀ xs p, P.Holds xs p ↔ ((∃ i, X.row i = xs) ∧ p.1 ∈ xs) ∧ ((∃ i, X.row i = xs) ∧ p.2 ∈ xs) :=
    fun xs p => (pair_holds hP wG wG xs p).trans (and_congr (mem_holds hG hX _ _) (mem_holds hG hX _ _))
  -- `Δ = diag q D`: the pairs of one array on whose diagonal `TQ` holds
  have eD : ∀ p p', Dg.Holds p p' ↔ p = p' ∧ (∃ xs, P.Holds xs p) ∧ TQ p p := fun p p' => by
    rw [diag_holds hq hqw (fun p p' hd => ((ran_holds hD p p').1 hd).1)
      (ran_wf hD (pair_wf hP (mem_wf hG hX) (mem_wf hG hX))) hDg]
    simp only [ran_holds hD, true_and]
  -- the keys of `Y` among the pairs of one array: `TQ` on their diagonal, not on their swap's
  have eY : ∀ p p', Y.Holds p p' ↔ p = p' ∧ (∃ xs, P.Holds xs p) ∧ TQ p p ∧ ¬TQ (p.2, p.1) (p.2, p.1) :=
    fun p p' => by
      rw [diff_holds hY wDg wS, eD, dom_holds hS]
      constructor
      · rintro ⟨⟨rfl, ⟨xs, hx⟩, t⟩, hn⟩
        obtain ⟨i, hk, -⟩ := (ran_holds hD p p).2 ⟨rfl, xs, hx⟩
        refine ⟨rfl, ⟨xs, hx⟩, t, fun t' => hn ⟨rfl, (p.2, p.1), (comp_holds hWD ww wDg _ _).2 ⟨(p.2, p.1), ?_, ?_⟩⟩⟩
        · exact (pair_holds hw (outr_wf ho1 wD.1) (outl_wf ho2 wD.1) p _).2 ⟨(outr_holds ho1 p _).2 ⟨⟨i, hk⟩, rfl⟩, (outl_holds ho2 p _).2 ⟨⟨i, hk⟩, rfl⟩⟩
        · obtain ⟨⟨h1, h2⟩, h3, h4⟩ := (eP xs p).1 hx
          exact (eD _ _).2 ⟨rfl, ⟨xs, (eP xs _).2 ⟨⟨h1, h4⟩, h3, h2⟩⟩, t'⟩
      · rintro ⟨rfl, hp, t, hn⟩
        refine ⟨⟨rfl, hp, t⟩, fun ⟨_, y, hy⟩ => hn ?_⟩
        obtain ⟨s, hs, hd⟩ := (comp_holds hWD ww wDg _ _).1 hy
        obtain ⟨h1, h2⟩ := (pair_holds hw (outr_wf ho1 wD.1) (outl_wf ho2 wD.1) p s).1 hs
        obtain rfl : s = (p.2, p.1) := Prod.ext ((outr_holds ho1 p _).1 h1).2 ((outl_holds ho2 p _).1 h2).2
        exact ((eD _ _).1 hd).2.2
  rw [lam_den h hX wGd]
  refine and_congr_right fun hx => ?_
  simp only [Lang.thinDen, Lang.lamDen]
  refine and_congr_right fun _ => forall_congr' fun c => iff_congr Iff.rfl ?_
  rw [diff_holds hGd wG wPO, mem_holds hG hX xs c, comp_holds hPO wP (outr_wf hO wY.1), and_iff_right hx]
  refine and_congr_right fun hc => not_congr ⟨fun ⟨p, hp, ho⟩ => ?_, fun ⟨b, hb, hbt, hn⟩ => ?_⟩
  · obtain ⟨hk, hc'⟩ := (outr_holds hO p c).1 ho
    obtain ⟨p', hy⟩ := (Rep.keyRowRep Y p).1 hk
    obtain ⟨-, -, hbt, hn⟩ := (eY p p').1 hy
    obtain ⟨b, c'⟩ := p
    subst hc'
    exact ⟨b, ((eP xs _).1 hp).1.2, hbt, hn⟩
  · have hp := (eP xs (b, c)).2 ⟨⟨hx, hb⟩, hx, hc⟩
    exact ⟨(b, c), hp, (outr_holds hO _ c).2 ⟨(Rep.keyRowRep Y _).2 ⟨(b, c), (eY _ _).2 ⟨rfl, ⟨xs, hp⟩, hbt, hn⟩⟩, rfl⟩⟩

/-! ### The value verbs and `$`: their tables are atoms keyed by the input, `Tab.keep` and `≫` -/

/-- **`D ≫ arithDen k U` keeps `Tab.WF`** where `U` does: `≫ dom U` twice, `keep`, `≫ U`. -/
theorem arith_wf {K : Obj} {t : QAtomicType} {k : UInt8} {D : Tab K (.prod (.atom t) (.atom t))}
    {U : {n : USize} → Vals (.atom t) n → Except String (Tab (.atom t) (.atom t))}
    (hU : ∀ {n : USize} (X : Vals (.atom t) n) T, U X = .ok T → Vals.WF X → T.WF) {T : Tab K (.atom t)}
    (h : arith t k D U = .ok T) (hD : D.WF) : T.WF := by
  simp only [arith, bind, Except.bind_eq_ok'] at h
  obtain ⟨u1, hu1, d1, hd1, E₁, hE₁, u2, hu2, d2, hd2, E, hE, ⟨w, b⟩, -, P, hP, u3, hu3, h⟩ := h
  have wE₁ := comp_wf hE₁ ⟨⟨hD.1, hD.2⟩, trivial⟩ (dom_wf hd1 (hU _ _ hu1 trivial))
  have wE := comp_wf hE ⟨wE₁.1, trivial⟩ (dom_wf hd2 (hU _ _ hu2 trivial))
  exact comp_wf h (keep_wf hP ⟨wE.1.1, trivial⟩) (hU _ _ hu3 trivial)

/-- **`D ≫ succDen U` keeps `Tab.WF`** where `U` does: `≫ dom U` on both sides of the step. -/
theorem succ_wf {K : Obj} {D : Tab K .long} {U : {n : USize} → Vals .long n → Except String (Tab .long .long)}
    (hU : ∀ {n : USize} (X : Vals .long n) T, U X = .ok T → Vals.WF X → T.WF) {T : Tab K .long}
    (h : succ D U = .ok T) (hD : D.WF) : T.WF := by
  simp only [succ, bind, Except.bind_eq_ok'] at h
  obtain ⟨u1, hu1, d1, hd1, E, hE, ne, -, s, -, u2, hu2, d2, hd2, h⟩ := h
  exact comp_wf h ⟨(comp_wf hE hD (dom_wf hd1 (hU _ _ hu1 trivial))).1, trivial⟩ (dom_wf hd2 (hU _ _ hu2 trivial))

/-- **`$` keeps `Tab.WF`**: `X` keyed to the cast words, `keep`. -/
theorem cast_wf {A B : Obj} {n : USize} {X : Vals A n} {t : Tab A B} (h : Tab.cast X = .ok t) (hX : Vals.WF X) :
    t.WF := by
  unfold Tab.cast at h
  split at h
  · split at h
    · simp only [bind, Except.bind_eq_ok'] at h
      obtain ⟨w, -, f, -, h⟩ := h
      exact keep_wf h ⟨hX, trivial⟩
    · cases h
  · cases h

set_option hygiene false in
/-- `floatOp_wf` at fixed constructors of `A` and `B`: the `lookup` split, each `keep` branch `keep_wf`. -/
local macro "floatOpFin" : tactic => `(tactic| (
  rcases hl : List.lookup s floatOps with _ | ⟨o, x⟩ <;> simp only [Tab.floatOp, hl] at h <;>
  first
    | (simp at h; done)
    | (split at h
       · simp only [bind, Except.bind_eq_ok'] at h; obtain ⟨⟨w, f⟩, -, h⟩ := h; exact keep_wf h ⟨hX, trivial⟩
       · simp at h)))

/-- **A row of `floatOps` keeps `Tab.WF`**: `X` keyed to the answer words, `keep`. -/
theorem floatOp_wf {s : String} {A B : Obj} {n : USize} {X : Vals A n} {t : Tab A B} (h : Tab.floatOp s X = .ok t)
    (hX : Vals.WF X) : t.WF := by
  -- `split` cannot generalize `A`, `B` under `X`: fix their constructors first, then the match is on `lookup` alone
  cases A
  case prod a1 a2 => cases a1 <;> cases a2 <;> cases B <;> floatOpFin
  all_goals cases B <;> floatOpFin

/-! ### The folds of `Rel/Run/Fix.lean` on cells: `foldRounds` from `nil X` -/

/-- **`flatten` keeps `Tab.WF`**: a round's step is `cat` of `(acc, xs)` (`foldRounds_wf`). -/
theorem flatten_wf {B : Obj} {n : USize} {X : Vals (.arr (.arr B)) n} {t : Tab (.arr (.arr B)) (.arr B)}
    (h : flatten X = .ok t) (hX : Vals.WF X) : t.WF := by
  simp only [flatten, bind, Except.bind_eq_ok'] at h
  obtain ⟨I, hI, N, hN, z, hz, h⟩ := h
  refine foldRounds_wf (fun _ _ => peelL_wf) (fun acc el t hs wa wel => ?_) h (idU_wf hI hX) (nil_wf hN hX)
    (zero_wf hz)
  simp only [Except.bind_eq_ok'] at hs
  obtain ⟨p, hp, hs⟩ := hs
  exact cat_wf hs (pair_wf hp wa wel)

/-- **`filter(p)` keeps `Tab.WF`**: a round's step is `snoc`, `pair`, `≫`, `dom`, `−`, `∪` (`foldRounds_wf`). -/
theorem filter_wf {B : Obj} {n : USize} {P : Tab B B} {X : Vals (.arr B) n} {t : Tab (.arr B) (.arr B)}
    (h : filter P X = .ok t) (hP : P.WF) (hX : Vals.WF X) : t.WF := by
  simp only [filter, bind, Except.bind_eq_ok'] at h
  obtain ⟨D, hD, I, hI, N, hN, z, hz, h⟩ := h
  have wD := dom_wf hD hP
  refine foldRounds_wf (fun _ _ => peelL_wf) (fun acc el t hs wa wel => ?_) h (idU_wf hI hX) (nil_wf hN hX)
    (zero_wf hz)
  simp only [Except.bind_eq_ok'] at hs
  obtain ⟨k, hk, p, hp, s, hs1, d1, hd1, d2, hd2, e, he, c, hc, hs⟩ := hs
  have wk := comp_wf hk wel wD
  exact union_wf hs (snoc_wf hs1 (pair_wf hp wa wk)) (comp_wf hc (diff_wf he (dom_wf hd1 wel) (dom_wf hd2 wk)) wa)

/-- **`takewhile(p)` keeps `Tab.WF`**: a round's step is `cons`, `pair`, `≫`, `dom`, `−`, `nil`, `∪`
(`foldRounds_wf`, `peelR_wf`). -/
theorem takewhile_wf {B : Obj} {n : USize} {P : Tab B B} {X : Vals (.arr B) n} {t : Tab (.arr B) (.arr B)}
    (h : takewhile P X = .ok t) (hP : P.WF) (hX : Vals.WF X) : t.WF := by
  simp only [takewhile, bind, Except.bind_eq_ok'] at h
  obtain ⟨D, hD, I, hI, N, hN, z, hz, h⟩ := h
  have wD := dom_wf hD hP
  refine foldRounds_wf (fun _ _ => peelR_wf) (fun acc el t hs wa wel => ?_) h (idU_wf hI hX) (nil_wf hN hX)
    (zero_wf hz)
  simp only [Except.bind_eq_ok'] at hs
  obtain ⟨k, hk, p, hp, s, hs1, d1, hd1, d2, hd2, e, he, c, hc, nl, hnl, c2, hc2, hs⟩ := hs
  have wk := comp_wf hk wel wD
  have wc := comp_wf hc (diff_wf he (dom_wf hd1 wel) (dom_wf hd2 wk)) wa
  exact union_wf hs (cons_wf hs1 (pair_wf hp wk wa)) (comp_wf hc2 wc (nil_wf hnl wa.2))

/-- **`F(R)` keeps `Tab.WF`** where `R` does: the one pass is `Vals.cells` over the EXPAND of `X`'s widths, each at
most `m` (`Vals.cells_expand_wf`, `cellSpan_width`); the relator a left fold, its step `snoc`, `pair`, `≫`. -/
theorem map_wf {A B : Obj} {n : USize} {R : Tab A B} {X : Vals (.arr A) n} {t : Tab (.arr A) (.arr B)}
    (h : map R X = .ok t) (hR : R.WF) (hX : Vals.WF X) : t.WF := by
  obtain ⟨m, lo, hi, f⟩ := X
  simp only [map] at h
  split at h; · cases h
  rename_i hb
  simp only [bind] at h
  rw [Except.bind_eq_ok'] at h; obtain ⟨_, -, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨w, hw, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨⟨T, G, u⟩, hex, h⟩ := h; try dsimp only at h
  rw [Except.bind_eq_ok'] at h; obtain ⟨sg, -, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨ix, -, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨v, hv, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨ps, -, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨C, hC, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨dC, -, h⟩ := h
  split at h
  · rename_i hc
    simp only [Bool.and_eq_true, beq_iff_eq] at hc
    obtain ⟨CN, Ck, Cv⟩ := C
    obtain rfl : CN = T := hc.1
    rw [Except.bind_eq_ok'] at h; obtain ⟨Y, hY, h⟩ := h
    have hm63 : m.toNat < 2 ^ 63 := by omega
    obtain ⟨SN, EN, hse', hb1, -⟩ := cellSpan_spec hX.1 hm63 f
    have wC := comp_wf hC ⟨trivial, Vals.gather_wf hv hX.2⟩ hR
    refine canon_wf h ⟨hX, Vals.cells_expand_wf hex hY m.toNat (fun i hi => ?_) (by dsimp only; omega) (by dsimp only; omega) wC.2⟩
    obtain ⟨e1, b1⟩ := cellSpan_width hse' hb1 hw i hi
    rw [e1, toNat_toUInt64 (by omega)]; exact b1
  simp only [Except.bind_eq_ok'] at h
  obtain ⟨I, hI, N, hN, z, hz, h⟩ := h
  refine foldRounds_wf (fun _ _ => peelL_wf) (fun acc el t hs wa wel => ?_) h (idU_wf hI hX) (nil_wf hN hX)
    (zero_wf hz)
  simp only [Except.bind_eq_ok'] at hs
  obtain ⟨c, hc, p, hp, hs⟩ := hs
  exact snoc_wf hs (pair_wf hp wa (comp_wf hc wel hR))

/-- **The rounds of `Tab.mu`**, its step `f` acting on relations as `F`: the table it returns satisfies every
property `S` that `𝟘` has and each round `X ↦ X ∪ F(X)` keeps (`fixOn_inv`), and is a prefixed point of `F`: the
last round keeps the row count of the table before it, so it keeps the relation (`holds_of_n`). -/
theorem mu_holds {A B : Obj} {what : String} {cap : Nat} {f : Tab A B → Except String (Tab A B)}
    {F : Core.Rel A.El B.El → Core.Rel A.El B.El} (hf : ∀ X T, X.WF → f X = .ok T → ∀ a b, T.Holds a b ↔ F X.Holds a b)
    (hfw : ∀ X t, f X = .ok t → X.WF → t.WF)
    (S : Core.Rel A.El B.El → Prop) (h0 : S fun _ _ => False) (hS : ∀ X, S X → S fun a b => X a b ∨ F X a b)
    {Y : Tab A B} (h : Tab.mu what cap f = .ok Y) : S Y.Holds ∧ ∀ a b, F Y.Holds a b → Y.Holds a b := by
  unfold Tab.mu at h; simp only [bind] at h
  rw [Except.bind_eq_ok'] at h; obtain ⟨Z, hZ, h⟩ := h
  -- a round: `X ∪ f(X)`, then `pack`
  have round : ∀ X U U', X.WF → (f X >>= X.union) = .ok U → U.pack = .ok U' →
      U'.toList.Nodup ∧ U'.Holds = (fun a b => X.Holds a b ∨ F X.Holds a b) ∧ U'.WF := by
    intro X U U' wX hU hp
    simp only [bind] at hU; rw [Except.bind_eq_ok'] at hU; obtain ⟨T, hT, hu⟩ := hU
    have wU := union_wf hu wX (hfw _ _ hT wX)
    refine ⟨(pack_toList hp wU).2 ▸ union_nodup hu, funext fun a => funext fun b => propext ?_, pack_wf hp wU⟩
    rw [pack_holds hp wU, union_holds hu wX (hfw _ _ hT wX), hf X T wX hT]
  have eZ : Z.Holds = fun _ _ => False := funext fun a => funext fun b => propext (zero_holds hZ a b)
  obtain ⟨X, U, ⟨dX, sX, wX⟩, hU, hp, hn⟩ := fixOn_inv (fun X : Tab A B => X.toList.Nodup ∧ S X.Holds ∧ X.WF)
    (fun X U U' ⟨_, sX, wX⟩ hU hp => by
      obtain ⟨d, e, w⟩ := round X U U' wX hU hp
      rw [e]; exact ⟨d, hS _ sX, w⟩) _ _ _
    ⟨by
      rw [show Z.toList = [] from List.eq_nil_iff_forall_not_mem.2 fun p hp => by
        have := (holds_iff_mem_toList Z p.1 p.2).2 hp; rw [eZ] at this; exact this]
      exact List.nodup_nil, by rw [eZ]; exact h0, zero_wf hZ⟩ h
  obtain ⟨dY, eY, -⟩ := round X U Y wX hU hp
  have hY : ∀ a b, Y.Holds a b ↔ X.Holds a b ∨ F X.Holds a b := fun a b => by rw [eY]
  have hX := holds_of_n dX dY (fun a b hab => (hY a b).2 (.inl hab)) hn.symm
  have eXY : Y.Holds = X.Holds := funext fun a => funext fun b => propext ⟨hX a b, fun hx => (hY a b).2 (.inl hx)⟩
  refine ⟨by rw [eXY]; exact sX, fun a b hF => (hY a b).2 (.inr ?_)⟩
  rw [eXY] at hF; exact hF

open Core.Rel in
/-- **`P ≫ star(R)`** (`Tab.star`), its step given the coreflexive `D` acting as `D ≫ R`: the table it returns is
`P ≫ μX : 𝟙 ∪ R X`. Each round keeps `X ⊑ P μ`, `P ⊑ X`, `Δ ⊑ X`, and `k X b`, `b R c` give `k X c` or `k Δ b`; the
last round adds no row, so its `Δ'` is empty and `X` is closed under `R`, which puts `P μ` inside it (`mu_le`). -/
theorem star_holds {K B : Obj} {step : Tab B B → Except String (Tab B B)} {R : Core.Rel B.El B.El}
    (hs : ∀ D T, step D = .ok T → D.WF → ∀ a c, T.Holds a c ↔ ∃ b, D.Holds a b ∧ R b c)
    (hsw : ∀ D T, step D = .ok T → D.WF → T.WF)
    {P Y : Tab K B} (hPw : P.WF) (h : Tab.star step P = .ok Y) (k : K.El) (c : B.El) :
    Y.Holds k c ↔ ∃ a, P.Holds k a ∧ Core.Rel.mu (fun X => 𝟙 _ ∪ R ≫ X) a c := by
  have hm : Monotonic fun X : Core.Rel B.El B.El => 𝟙 _ ∪ R ≫ X := fun X Y hXY =>
    le_iff.2 fun a c h => h.elim .inl fun ⟨b, hb, hx⟩ => .inr ⟨b, hb, le_iff.1 hXY _ _ hx⟩
  have pre := le_iff.1 (mu_prefixed hm)
  -- `μ ≫ R ⊑ μ`: `μ` lies in `{(a, b) | ∀ c, b R c → a μ c}`
  have muR : ∀ a b c, Core.Rel.mu (fun X => 𝟙 _ ∪ R ≫ X) a b → R b c → Core.Rel.mu (fun X => 𝟙 _ ∪ R ≫ X) a c :=
    fun a b c hab hbc => le_iff.1 (mu_le (φ := fun X => 𝟙 _ ∪ R ≫ X)
      (Y := fun a b => ∀ c, R b c → Core.Rel.mu (fun X => 𝟙 _ ∪ R ≫ X) a c) (le_iff.2 fun a b h c hbc => h.elim
        (fun e => pre a c (.inr ⟨c, (e : a = b) ▸ hbc, pre c c (.inl rfl)⟩))
        fun ⟨a', ha, hz⟩ => pre a c (.inr ⟨a', ha, hz c hbc⟩))) a b hab c hbc
  simp only [Tab.star, bind] at h
  rw [Except.bind_eq_ok'] at h; obtain ⟨P', hP', h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨r, hr, h⟩ := h
  obtain rfl : r.1 = Y := Except.ok.inj h
  have hP : ∀ k a, P'.Holds k a ↔ P.Holds k a := canon_holds hP'
  -- a round from `s`: `X' = X ∪ Δ'`, `Δ' = Δ R − X`, both packed
  have round : ∀ (s Z Z' : Tab K B × Tab K B), s.1.WF → s.2.WF →
      (do let D ← (← s.2.comp (← step (← s.2.ran))).diff s.1; pure (← s.1.union D, D) :
        Except String (Tab K B × Tab K B)) = .ok Z →
      (do pure (← Z.1.pack, ← Z.2.pack) : Except String (Tab K B × Tab K B)) = .ok Z' →
      Z'.1.toList.Nodup ∧ (∀ k c, Z'.2.Holds k c ↔ (∃ b, s.2.Holds k b ∧ R b c) ∧ ¬s.1.Holds k c) ∧
        (∀ k c, Z'.1.Holds k c ↔ s.1.Holds k c ∨ Z'.2.Holds k c) ∧ Z'.1.WF ∧ Z'.2.WF := by
    intro s Z Z' w1 w2 hZ hp
    simp only [bind] at hZ hp
    rw [Except.bind_eq_ok'] at hZ; obtain ⟨Dr, hDr, hZ⟩ := hZ
    rw [Except.bind_eq_ok'] at hZ; obtain ⟨T, hT, hZ⟩ := hZ
    rw [Except.bind_eq_ok'] at hZ; obtain ⟨N, hN, hZ⟩ := hZ
    rw [Except.bind_eq_ok'] at hZ; obtain ⟨D, hD, hZ⟩ := hZ
    rw [Except.bind_eq_ok'] at hZ; obtain ⟨U, hU, hZ⟩ := hZ
    obtain rfl : (U, D) = Z := Except.ok.inj hZ
    rw [Except.bind_eq_ok'] at hp; obtain ⟨U', hU', hp⟩ := hp
    rw [Except.bind_eq_ok'] at hp; obtain ⟨D', hD', hp⟩ := hp
    obtain rfl : (U', D') = Z' := Except.ok.inj hp
    have wN := comp_wf hN w2 (hsw _ _ hT (ran_wf hDr w2))
    have wD := diff_wf hD wN w1
    have wU := union_wf hU w1 wD
    have eD : ∀ k c, D'.Holds k c ↔ (∃ b, s.2.Holds k b ∧ R b c) ∧ ¬s.1.Holds k c := fun k c => by
      rw [pack_holds hD' wD, diff_holds hD wN w1, comp_holds hN w2 (hsw _ _ hT (ran_wf hDr w2))]
      refine and_congr_left fun _ => ⟨fun ⟨b, hb, hbc⟩ => ?_, fun ⟨b, hb, hbc⟩ => ⟨b, hb, ?_⟩⟩
      · obtain ⟨b', hb', hbc'⟩ := (hs _ _ hT (ran_wf hDr w2) b c).1 hbc
        obtain ⟨rfl, -⟩ := (ran_holds hDr b b').1 hb'
        exact ⟨b, hb, hbc'⟩
      · exact (hs _ _ hT (ran_wf hDr w2) b c).2 ⟨b, (ran_holds hDr b b).2 ⟨rfl, k, hb⟩, hbc⟩
    refine ⟨(pack_toList hU' wU).2 ▸ union_nodup hU, eD, fun k c => ?_, pack_wf hU' wU, pack_wf hD' wD⟩
    rw [pack_holds hU' wU, union_holds hU w1 wD, ← pack_holds hD' wD]
  let I : Tab K B × Tab K B → Prop := fun s => s.1.toList.Nodup ∧ (∀ k b, s.2.Holds k b → s.1.Holds k b) ∧
    (∀ k b, s.1.Holds k b → ∃ a, P'.Holds k a ∧ Core.Rel.mu (fun X => 𝟙 _ ∪ R ≫ X) a b) ∧
    (∀ k a, P'.Holds k a → s.1.Holds k a) ∧
    (∀ k b c, s.1.Holds k b → R b c → s.1.Holds k c ∨ s.2.Holds k b) ∧ s.1.WF ∧ s.2.WF
  obtain ⟨X, Z, ⟨dX, -, sX, pX, cX, wX1, wX2⟩, hZ, hp, hn⟩ := fixOn_inv I
    (fun s Z Z' ⟨_, dsub, sX, pX, cX, w1, w2⟩ hZ hp => by
      obtain ⟨d, eD, eX, w1', w2'⟩ := round s Z Z' w1 w2 hZ hp
      refine ⟨d, fun k b hb => (eX k b).2 (.inr hb), fun k b hb => ((eX k b).1 hb).elim (sX k b) fun hD => ?_,
        fun k a ha => (eX k a).2 (.inl (pX k a ha)), fun k b c hb hbc => ?_, w1', w2'⟩
      · obtain ⟨⟨b', hb', hbc⟩, -⟩ := (eD k b).1 hD
        obtain ⟨a, ha, hab⟩ := sX k b' (dsub k b' hb')
        exact ⟨a, ha, muR a b' b hab hbc⟩
      · rcases (eX k b).1 hb with hb | hb
        · rcases cX k b c hb hbc with hc | hd
          · exact .inl ((eX k c).2 (.inl hc))
          · by_cases hc : s.1.Holds k c
            · exact .inl ((eX k c).2 (.inl hc))
            · exact .inl ((eX k c).2 (.inr ((eD k c).2 ⟨⟨b, hd, hbc⟩, hc⟩)))
        · exact .inr hb)
    _ _ _ ⟨toList_nodup fun _ _ => canon_distinct hP', fun _ _ h => h,
      fun k b hb => ⟨b, hb, pre b b (.inl rfl)⟩, fun _ _ h => h, fun _ _ _ _ _ => .inr ‹_›, canon_wf hP' hPw, canon_wf hP' hPw⟩ hr
  obtain ⟨dr, eD, eX, -, -⟩ := round X Z r wX1 wX2 hZ hp
  -- the last round kept the row count, so it added nothing: `X` is closed under `R`
  have hX := holds_of_n dX dr (fun k c h => (eX k c).2 (.inl h)) hn.symm
  have cl : ∀ k b c, X.1.Holds k b → R b c → X.1.Holds k c := fun k b c hb hbc =>
    (cX k b c hb hbc).elim id fun hd => by
      by_cases hc : X.1.Holds k c
      · exact hc
      · exact hX k c ((eX k c).2 (.inr ((eD k c).2 ⟨⟨b, hd, hbc⟩, hc⟩)))
  rw [show r.1.Holds k c ↔ X.1.Holds k c from ⟨hX k c, fun h => (eX k c).2 (.inl h)⟩]
  refine ⟨fun h => ?_, fun ⟨a, ha, hac⟩ => ?_⟩
  · obtain ⟨a, ha, hac⟩ := sX k c h; exact ⟨a, (hP k a).1 ha, hac⟩
  · exact le_iff.1 (mu_le (φ := fun X => 𝟙 _ ∪ R ≫ X) (Y := fun a c => ∀ k, X.1.Holds k a → X.1.Holds k c)
      (le_iff.2 fun a c h k hk => h.elim (fun e => (e : a = c) ▸ hk)
        fun ⟨a', ha, hz⟩ => hz k (cl k a a' hk ha))) a c hac k (pX k a ((hP k a).2 ha))

end Tab

end Rel
