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
theorem merge_wf {K B : Obj}
    {q : Tab (.prod B B) (.prod B B) → Except String (Tab (.prod B B) (.prod B B))}
    (hq : ∀ D t, q D = .ok t → D.WF → t.WF) {P : Tab K (.prod (.arr B) (.arr B))} {t : Tab K (.arr B)}
    (h : merge q P = .ok t) (hP : P.WF) : t.WF := by
  simp only [merge, bind, Except.bind_eq_ok'] at h
  obtain ⟨D, hD, c, hc, nl, hnl, I, hI, z, hz, out, hout, a, ha, o, ho, h⟩ := h
  have wD := ran_wf hD hP
  have wout : out.WF := foldRounds_wf (fun _ _ => peelL_wf) (fun S el T hs wS _ => ?_) hout
    (cat_wf hc wD) (pair_wf hI wD (nil_wf hnl wD.1)) (zero_wf hz)
  · exact comp_wf h hP (comp_wf ho wout (outr_wf ha wout.2))
  simp only [Except.bind_eq_ok'] at hs
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

/-- **`thinL(Q)` keeps `Tab.WF`** where `q` does: `bump`'s answer is `≫`, `pair`, `∪`, `−`, `dom`, `cons` of the
round's pairs (`foldRounds_wf`, `peelR_wf`). -/
theorem thinL_wf {B : Obj} {n : USize}
    {q : Tab (.prod B B) (.prod B B) → Except String (Tab (.prod B B) (.prod B B))}
    (hq : ∀ D t, q D = .ok t → D.WF → t.WF) {X : Vals (.arr B) n} {t : Tab (.arr B) (.arr B)}
    (h : thinL q X = .ok t) (hX : Vals.WF X) : t.WF := by
  simp only [thinL, bind, Except.bind_eq_ok'] at h
  obtain ⟨I, hI, N, hN, z, hz, h⟩ := h
  refine foldRounds_wf (fun _ _ => peelR_wf) (fun P el t hs wP wel => ?_) h (idU_wf hI hX)
    (nil_wf hN hX) (zero_wf hz)
  simp only [Except.bind_eq_ok'] at hs
  obtain ⟨p, hp, E, hE, o1, h1, x, hx, o2, h2, ys, hys, u0, hu0, u, hu, o3, h3, b, hb, ab, hab, ba, hba,
    r1, hr1, d1, hd1, c1, hc1, up, hup, r2, hr2, d2, hd2, c2, hc2, down, hdown, du, hdu, e1, he1, e2, he2, e3, he3,
    lone, hlone, o4, h4, bs, hbs, k1, hk1, xb, hxb, k2, hk2, c3, hc3, v1, hv1, c4, hc4, r, hr, hs⟩ := hs
  have wp := pair_wf hp wel wP
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
  obtain ⟨u1, hu1, d1, hd1, E, hE, c, -, ne, -, s, -, u2, hu2, d2, hd2, h⟩ := h
  exact comp_wf h ⟨(comp_wf hE hD (dom_wf hd1 (hU _ _ hu1 trivial))).1, trivial⟩ (dom_wf hd2 (hU _ _ hu2 trivial))

/-- **`$` keeps `Tab.WF`**: `X` keyed to the cast words, `keep`. -/
theorem cast_wf {A B : Obj} {n : USize} {X : Vals A n} {t : Tab A B} (h : Tab.cast X = .ok t) (hX : Vals.WF X) :
    t.WF := by
  unfold Tab.cast at h
  split at h
  · split at h
    · simp only [bind, Except.bind_eq_ok'] at h
      obtain ⟨w, -, c, -, f, -, h⟩ := h
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
  rw [Except.bind_eq_ok'] at h; obtain ⟨⟨s, e⟩, hse, h⟩ := h; try dsimp only at h
  rw [Except.bind_eq_ok'] at h; obtain ⟨w, hw, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨⟨T, G, u⟩, hex, h⟩ := h; try dsimp only at h
  rw [Except.bind_eq_ok'] at h; obtain ⟨sg, -, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨ix, -, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨v, hv, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨ps, -, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨C, hC, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨dC, -, h⟩ := h
  split at h
  · rw [Except.bind_eq_ok'] at h; obtain ⟨Y, hY, h⟩ := h
    have hm63 : m.toNat < 2 ^ 63 := by omega
    obtain ⟨SN, EN, hse', hb1, -⟩ := cellSpan_spec hse hm63 f
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

end Tab

end Rel
