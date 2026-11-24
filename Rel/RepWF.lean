module

public import Rel.RepCols
public import Rel.Run.Bits
public import Rel.Run.Power
public import Rel.Run.Asc
public import Rel.Run.Fix
public import Rel.RepTabDiv

-- exposed: every def body is a spec a downstream `rfl`/`decide`/`simp` may unfold (PLAN W.8)
@[expose] public section

/-! **`Tab.WF` kept by each `Tab` op** (PLAN 8.5): an op's output sides are `ValsB.gather`ed, `ValsB.concat`ed or
`Vals.nub`bed from its inputs' sides (`Vals.gather_wf`, `Vals.concat_wf`, `Tab.canon_wf`), or are sides of no row
(`Vals.none_wf`), so a cell of its output is a cell of an input. These are the base the switch of `Rel.Wf`'s `tab`
case to `Tab.WF` stands on: each op's `_wf` lemma there is one of these. -/

namespace Rel
open Rel.Ext Rel.Kernel Rel.Verify Ext.Enc

/-! ### The bit-matrix and division ops -/

/-- **`Vals.code2`'s joined side keeps `Vals.WF`**: the concatenation of the two (`Vals.concat_wf`). -/
theorem Vals.code2_wf {n₁ n₂ : USize} {x : Vals A n₁} {y : Vals A n₂}
    {r : USize × Enc × Enc × ((N : USize) × Vals A N × Enc)} (h : Vals.code2 x y = .ok r) (hx : Vals.WF x)
    (hy : Vals.WF y) : Vals.WF r.2.2.2.2.1 := by
  simp only [Vals.code2, bind, Except.bind, pure, Except.pure] at h
  split at h; · cases h
  rename_i p hp
  have hn := catRows_ok hp
  split at h; · cases h
  rename_i sh hsh
  split at h; · cases h
  rename_i z hz
  okSplit
  cases h; exact Vals.concat_wf hn hz hx hy

namespace Tab


/-- A table `compSelM` answers is `compFrom`'s (`compFrom_wf`). -/
theorem compSelM_inl_wf {bits : Nat} {R : Tab A B} {S : Tab B C} {t : Tab A C}
    (h : compSelM bits R S = .ok (.inl t)) (hR : R.WF) (hS : S.WF) : t.WF := by
  simp only [Tab.compSelM, bind, Except.bind, pure, Except.pure] at h
  okSplit
  all_goals first | (cases h; exact compFrom_wf ‹_› hR hS) | cases h

/-- **`compSel` keeps `Tab.WF`**: `compFrom`'s table or the matrix read back (`ofBits_wf`). -/
theorem compSel_wf {bits : Nat} {R : Tab A B} {S : Tab B C} {t : Tab A C} (h : compSel bits R S = .ok t)
    (hR : R.WF) (hS : S.WF) : t.WF := by
  simp only [Tab.compSel, bind, Except.bind, pure, Except.pure] at h
  okSplit
  all_goals first | (cases h; exact compSelM_inl_wf ‹_› hR hS) | exact ofBits_wf h hR.1 hS.2

/-- **`keepBits` keeps `Tab.WF`**: rows of `T.canon` kept twice (`keep_wf`). -/
theorem keepBits_wf {T t : Tab A C} {n m : USize} {g w : USize} {o ra rc : Enc} {x : Vals A n} {y : Vals C m}
    (h : T.keepBits g w o x ra y rc = .ok t) (hT : T.WF) : t.WF := by
  simp only [Tab.keepBits, bind, Except.bind, pure, Except.pure] at h
  okSplit
  exact keep_wf h (keep_wf ‹_› (canon_wf ‹_› hT))

/-- **`ldivBits` keeps `Tab.WF`**: its matrix read back over the joined sides of `Vals.code2` (`code2_wf`). -/
theorem ldivBits_wf {R : Tab A B} {S : Tab A C} {UB : Tab B B} {UC : Tab C C} {t : Tab B C}
    (h : ldivBits R S UB UC = .ok t) (hR : R.WF) (hS : S.WF) (hB : UB.WF) (hC : UC.WF) : t.WF := by
  simp only [Tab.ldivBits, bind, Except.bind, pure, Except.pure] at h
  okSplit
  exact ofBits_wf h (Vals.code2_wf ‹_› hR.2 hB.2) (Vals.code2_wf ‹_› hS.2 hC.2)





theorem ldiv_wf {R : Tab A B} {S : Tab A C} {UB : Tab B B} {UC : Tab C C} {t : Tab B C}
    (h : ldiv R S UB UC = .ok t) (hR : R.WF) (hS : S.WF) (hB : UB.WF) (hC : UC.WF) : t.WF := by
  simp only [Tab.ldiv, bind, Except.bind] at h
  split at h; · cases h
  rename_i r hr; split at h; · cases h
  rename_i s hs
  exact ldivOf_wf h (canon_wf hr hR) (canon_wf hs hS) hB hC

/-- **`ldivSel d` keeps `Tab.WF`** where its division `d` does at these arguments (`ldiv_wf`, `ldivOf_wf`), with
`ldivBits_wf`. -/
theorem ldivSel_wf {d : Tab A B → Tab A C → Tab B B → Tab C C → Except String (Tab B C)} {bits : Nat}
    {R : Tab A B} {S : Tab A C} {UB : Tab B B} {UC : Tab C C} {t : Tab B C}
    (hd : ∀ {t}, d R S UB UC = .ok t → t.WF) (h : ldivSel d bits R S UB UC = .ok t) (hR : R.WF) (hS : S.WF)
    (hB : UB.WF) (hC : UC.WF) : t.WF := by
  simp only [Tab.ldivSel, bind, Except.bind, pure, Except.pure] at h
  okSplit
  all_goals first | exact hd h | exact ldivBits_wf h hR hS hB hC

theorem rdiv_wf {R : Tab A C} {S : Tab B C} {UA : Tab A A} {UB : Tab B B} {t : Tab A B}
    (h : rdiv R S UA UB = .ok t) (hR : R.WF) (hS : S.WF) (hA : UA.WF) (hB : UB.WF) : t.WF := by
  simp only [Tab.rdiv, bind, Except.bind] at h
  okSplit
  exact conv_wf h (ldivOf_wf ‹_› (conv_wf ‹_› hS) (conv_wf ‹_› hR) hB hA)

/-- **`ldivTabMat`'s two sides keep `Vals.WF`**: each the joined side of a `Vals.code2` (`code2_wf`). -/
theorem ldivTabMat_sides_wf {R : Tab A B} {UB : Tab B B} {UC : Tab C C} {n m g w : USize} {o ra rc : Enc}
    {x : Vals A n} {y : Vals C m} {kb kc N N' : USize} {o' rb rc' : Enc} {zb : Vals B N} {zc : Vals C N'}
    (h : ldivTabMat R UB UC g w o x ra y rc = .ok (some (kb, kc, o', ⟨N, zb⟩, rb, ⟨N', zc⟩, rc')))
    (hR : R.WF) (hB : UB.WF) (hC : UC.WF) (hy : Vals.WF y) : Vals.WF zb ∧ Vals.WF zc := by
  simp only [Tab.ldivTabMat, bind, Except.bind, pure, Except.pure] at h
  okSplit
  cases h
  exact ⟨Vals.code2_wf ‹_› hR.2 hB.2, Vals.code2_wf ‹_› (Vals.gather_wf ‹_› hy) hC.2⟩

/-- **`compTabMat`'s key side keeps `Vals.WF`**: rows of `R.key` gathered. -/
theorem compTabMat_key_wf {R : Tab A B} {n g w ka M : USize} {o o' ra ra' : Enc} {x : Vals B n} {key : Vals A M}
    (h : compTabMat R g w o x ra = .ok (ka, o', ⟨M, key⟩, ra')) (hR : R.WF) : Vals.WF key := by
  simp only [Tab.compTabMat, bind, Except.bind, pure, Except.pure] at h
  okSplit
  cases h; exact Vals.gather_wf ‹_› hR.1

theorem inlConv_wf {n : USize} {X : Vals (.sum A B) n} {t : Tab (.sum A B) A} (h : Tab.inlConv X = .ok t)
    (hX : Vals.WF X) : t.WF := by
  rcases hv : X.view with ⟨hb, x⟩ | ⟨hb, tag, x, y⟩ <;> unfold Tab.inlConv at h <;> simp only [hv] at h
  · obtain ⟨rfl, rfl⟩ := Obj.band_some hb
    simp only [bind, Except.bind] at h
    okSplit
    exact comp_wf h (idU_wf ‹_› hX) (conv_wf ‹_› (inl_wf ‹_› trivial))
  have hXw := hX
  simp only [Vals.WF, ValsB.WFOn, hv] at hX
  simp only [bind, Except.bind] at h
  split at h; · cases h
  rename_i b hbm
  split at h; · cases h
  rename_i ws hws; obtain ⟨M, sel⟩ := ws
  split at h; · cases h
  rename_i G hG
  split at h; · cases h
  rename_i g hg
  split at h; · cases h
  rename_i u hu
  exact canon_wf h (selConv_holds (p := fun i => !tag.get i) (Arr.not_mask hbm) hws hG hg hu h hXw
    ((ValsB.WFOn_congr x fun i => by simp).1 hX.2.1)).1

theorem inrConv_wf {n : USize} {X : Vals (.sum A B) n} {t : Tab (.sum A B) B} (h : Tab.inrConv X = .ok t)
    (hX : Vals.WF X) : t.WF := by
  rcases hv : X.view with ⟨hb, x⟩ | ⟨hb, tag, x, y⟩ <;> unfold Tab.inrConv at h <;> simp only [hv] at h
  · -- a band column: both sides are gathers, whose `Vals.WF` is `Vals.gather_wf`'s, and a band side's is `True`
    unfold Tab.inrConvBand at h
    obtain ⟨rfl, rfl⟩ := Obj.band_some hb
    simp only [bind, Except.bind, pure, Except.pure, cast_eq, eq_mpr_eq_cast] at h
    -- UNBUILT: the splits are kscan, whereCol, ValsB.gather, Opt.gather, Arr.of; adjust to the goal state
    repeat (split at h; · cases h)
    cases h
    exact ⟨Vals.gather_wf ‹_› (by simp only [ValsB.WFOn, ValsB.view_ofOpt]; exact fun _ h => absurd trivial h), trivial⟩
  have hXw := hX
  simp only [Vals.WF, ValsB.WFOn, hv] at hX
  simp only [bind, Except.bind] at h
  split at h; · cases h
  rename_i ws hws; obtain ⟨M, sel⟩ := ws
  split at h; · cases h
  rename_i G hG
  split at h; · cases h
  rename_i g hg
  split at h; · cases h
  rename_i u hu
  exact canon_wf h (selConv_holds (p := fun i => tag.get i) (Arr.u1_mask tag) hws hG hg hu h hXw
    ((ValsB.WFOn_congr y fun i => by simp).1 hX.2.2)).1

/-! ### The power operators that build no cell -/

theorem length_wf {n : USize} {X : Vals (.arr B) n} {t : Tab (.arr B) .long} (h : Tab.length X = .ok t)
    (hX : Vals.WF X) : t.WF := by
  obtain ⟨m, lo, hi, f⟩ := X
  simp only [Tab.length, bind, Except.bind] at h
  okSplit
  exact canon_wf h ⟨hX, trivial⟩

theorem atIx_wf {n : USize} {X : Vals (.prod (.arr B) .long) n} {t : Tab (.prod (.arr B) .long) B}
    (h : Tab.atIx X = .ok t) (hX : Vals.WF X) : t.WF := by
  obtain ⟨⟨m, lo, hi, f⟩, k⟩ := X
  simp only [Tab.atIx, bind, Except.bind] at h
  okSplit
  exact canon_wf h ⟨Vals.gather_wf ‹_› hX, Vals.gather_wf ‹_› hX.1.2.2.2⟩

/-- **The row `at` keeps `Tab.WF`**: `atIx` at the `i64` index, no table elsewhere. -/
theorem atRow_wf {N : Obj} {n : USize} {X : Vals (.prod (.arr B) N) n} {t : Tab (.prod (.arr B) N) B}
    (h : Tab.atRow X = .ok t) (hX : Vals.WF X) : t.WF := by
  cases N
  case atom a => cases a <;> first | exact atIx_wf h hX | simp [Tab.atRow] at h
  all_goals simp [Tab.atRow] at h

/-- **`asc` keeps `Tab.WF`**: the value side of a `canon` of `P.key`. -/
theorem asc_wf {P : Tab B B} {t : Tab .long B} (h : Tab.asc P = .ok t) (hP : P.WF) : t.WF := by
  simp only [Tab.asc, bind, Except.bind, pure, Except.pure] at h
  split at h; · cases h
  split at h; · cases h
  split at h; · cases h
  rename_i U hU; split at h; · cases h
  cases h; exact ⟨trivial, (canon_wf hU ⟨trivial, hP.1⟩).2⟩

/-- **`est` keeps `Tab.WF`** where the test `q` does: every table it builds is `mem X`, `pair`, `ran`, `−`, `≫` of
`Tab.WF` ones. -/
theorem est_wf {n : USize} {q : Tab (.prod B B) (.prod B B) → Except String (Tab (.prod B B) (.prod B B))}
    (hq : ∀ D t, q D = .ok t → D.WF → t.WF) {X : Vals (.arr B) n} {t : Tab (.arr B) B} (h : Tab.est q X = .ok t)
    (hX : Vals.WF X) : t.WF := by
  simp only [Tab.est, bind, Except.bind] at h
  split at h; · cases h
  rename_i G hG; split at h; · cases h
  rename_i P hP; split at h; · cases h
  rename_i D hD; split at h; · cases h
  rename_i V hV; split at h; · cases h
  rename_i a ha; split at h; · cases h
  rename_i b hb; split at h; · cases h
  rename_i c hc; split at h; · cases h
  rename_i d hd; split at h; · cases h
  rename_i Y hY; split at h; · cases h
  rename_i e he; split at h; · cases h
  rename_i f hf
  have wG := mem_wf hG hX
  have wP := pair_wf hP wG wG
  have wD := ran_wf hD wP
  have wV := ran_wf hV wG
  have wY := diff_wf hY (diff_wf hb wD (hq _ _ ha wD)) (ran_wf hd (pair_wf hc wV wV))
  exact diff_wf h wG (comp_wf hf wP (outl_wf he wY.1))

end Tab

/-! ### `pack` and the fixed points -/

/-- **`ValsB.pack` keeps `ValsB.WFOn`**: a cut payload (`o = false`, every row owned) is the input's gathered and
packed, laid out by `Vals.cells` over the EXPAND of the cells' own widths, each at most `m` (`cellSpan_width`,
`Vals.cells_expand_wf`); a summand keeps its tag and cells and packs its payload. -/
theorem ValsB.pack_wf {k : Nat} : {o : Bool} → {A : Obj} → {n : USize} → {x y : ValsB o A n} → ValsB.pack k x = .ok y →
    {P : Fin n.toNat → Prop} → ValsB.WFOn x P → (o = false → ∀ i, P i) → ValsB.WFOn y P
  | _, .atom _, _, _, _, h, _, hx, _ => by
    simp only [ValsB.pack, pure, Except.pure, Except.ok.injEq] at h; cases h; exact hx
  | _, .one, _, _, _, _, _, _, _ => trivial
  | _, .prod _ _, _, x, _, h, _, hx, hall => by
    simp only [ValsB.pack, bind, Except.bind, pure, Except.pure] at h
    split at h; · cases h
    rename_i y1 h1
    split at h; · cases h
    rename_i y2 h2
    cases h; exact ⟨ValsB.pack_wf h1 hx.1 hall, ValsB.pack_wf h2 hx.2 hall⟩
  | _, .sum _ _, _, s, _, h, _, hx, _ => by
    rcases hv : s.view with ⟨hb, x⟩ | ⟨hb, tag, x, y⟩ <;> simp only [ValsB.pack, hv] at h
    · simp only [pure, Except.pure, Except.ok.injEq] at h; cases h; exact hx
    simp only [bind, Except.bind, pure, Except.pure] at h
    split at h; · cases h
    rename_i x' h1
    split at h; · cases h
    rename_i y' h2
    cases h
    simp only [ValsB.WFOn, hv] at hx
    simp only [ValsB.WFOn, ValsB.view_ofGen]
    exact ⟨hx.1, ValsB.pack_wf h1 hx.2.1 (fun h => nomatch h), ValsB.pack_wf h2 hx.2.2 (fun h => nomatch h)⟩
  | true, .arr B, n, ⟨m, lo, up, f⟩, y, h, P, hx, _ => by
    simp only [ValsB.pack] at h
    split at h; · cases h
    rename_i hb
    simp only [bind] at h
    rw [Except.bind_eq_ok'] at h; obtain ⟨_, -, h⟩ := h
    rw [Except.bind_eq_ok'] at h; obtain ⟨z, hz, h⟩ := h
    rw [Except.bind_eq_ok'] at h; obtain ⟨s, hs, h⟩ := h
    rw [Except.bind_eq_ok'] at h; obtain ⟨e, he, h⟩ := h
    rw [Except.bind_eq_ok'] at h; obtain ⟨w, hw, h⟩ := h
    split at h; · cases h
    split at h
    case isFalse =>
      rw [Except.bind_eq_ok'] at h; obtain ⟨f', hf', h⟩ := h
      cases h; exact ⟨hx.1, hx.2.1, hx.2.2.1, ValsB.pack_wf hf' hx.2.2.2 fun _ _ => trivial⟩
    rw [Except.bind_eq_ok'] at h; obtain ⟨⟨T, G, u⟩, hex, h⟩ := h; try dsimp only at h
    rw [Except.bind_eq_ok'] at h; obtain ⟨sg, hsg, h⟩ := h
    rw [Except.bind_eq_ok'] at h; obtain ⟨ix, hix, h⟩ := h
    rw [Except.bind_eq_ok'] at h; obtain ⟨g', hg', h⟩ := h
    rw [Except.bind_eq_ok'] at h; obtain ⟨p, hpk, h⟩ := h
    rw [Except.bind_eq_ok'] at h; obtain ⟨⟨T', lo', hi', f'⟩, hY, h⟩ := h; try dsimp only at h
    rw [Except.bind_eq_ok'] at h; obtain ⟨big, hbig, h⟩ := h
    rw [Except.bind_eq_ok'] at h; obtain ⟨y1, h1, h⟩ := h
    rw [Except.bind_eq_ok'] at h; obtain ⟨y2, h2, h⟩ := h
    cases h
    obtain ⟨sA, rfl, hsA⟩ := Opt.maxZero lo hz hs
    obtain ⟨eA, rfl, heA⟩ := Opt.maxZero up hz he
    have hse : ∀ i : Fin n.toNat, 0 ≤ (sA.get i).toInt ∧ (sA.get i).toInt ≤ (eA.get i).toInt ∧
        (eA.get i).toInt ≤ (m.toNat : Int) := fun i => by
      by_cases hp : P i
      · have := hx.2.2.1 i hp; rw [hsA i, heA i]; omega
      · rw [hsA i, heA i, ColB.get_unowned hx.1 hp, ColB.get_unowned hx.2.1 hp]; omega
    obtain ⟨hbW, hbk⟩ := Opt.bigOf lo hbig
    have hbw : ∀ j < n.toNat, (foRNuls n big)[j]? = some 0 → (raw .i64 n big)[j]? = some 0x7fffffffffffffff :=
      fun j hj h0 => (hbk j hj).2 ((hbk j hj).1.symm.trans h0)
    have hY' := Vals.cells_dense_wf (f := f) hb hse hw hex hY
      (ValsB.pack_wf hpk (Vals.gather_wf hg' hx.2.2.2) fun _ _ => trivial)
    refine ⟨Opt.ownedOn_flags hx.1 y1 fun j => ((Opt.maskWith_get hbW hbw h1 j).1).trans (hbk j.1 j.2).1,
      Opt.ownedOn_flags hx.1 y2 fun j => ((Opt.maskWith_get hbW hbw h2 j).1).trans (hbk j.1 j.2).1, fun j hj => ?_,
      hY'.2.2.2⟩
    have hb0 : (foRNuls n big)[j.1]? = some 0 := by
      rw [(hbk j.1 j.2).1]; exact ColB.flag_of_owned (o := true) lo hx.1 j hj
    have e3 : ColB.get (o := true) y1 j = ColB.get (o := false) lo' j := (Opt.maskWith_get hbW hbw h1 j).2 hb0
    have e4 : ColB.get (o := true) y2 j = ColB.get (o := false) hi' j := (Opt.maskWith_get hbW hbw h2 j).2 hb0
    rw [e3, e4]; exact hY'.2.2.1 j trivial
  | false, .arr B, n, ⟨m, lo, up, f⟩, y, h, P, hx, hall => by
    have hse := fun i => hx.2.2.1 i (hall rfl i)
    simp only [ValsB.pack] at h
    split at h; · cases h
    rename_i hb
    simp only [bind] at h
    rw [Except.bind_eq_ok'] at h; obtain ⟨_, -, h⟩ := h
    rw [Except.bind_eq_ok'] at h; obtain ⟨w, hw, h⟩ := h
    split at h; · cases h
    split at h
    case isFalse =>
      rw [Except.bind_eq_ok'] at h; obtain ⟨f', hf', h⟩ := h
      cases h; exact ⟨hx.1, hx.2.1, hx.2.2.1, ValsB.pack_wf hf' hx.2.2.2 fun _ _ => trivial⟩
    rw [Except.bind_eq_ok'] at h; obtain ⟨⟨T, G, u⟩, hex, h⟩ := h; try dsimp only at h
    rw [Except.bind_eq_ok'] at h; obtain ⟨sg, hsg, h⟩ := h
    rw [Except.bind_eq_ok'] at h; obtain ⟨ix, hix, h⟩ := h
    rw [Except.bind_eq_ok'] at h; obtain ⟨g', hg', h⟩ := h
    rw [Except.bind_eq_ok'] at h; obtain ⟨p, hp, h⟩ := h
    have hm63 : m.toNat < 2 ^ 63 := by omega
    obtain ⟨SN, EN, hse', hb1, -⟩ := cellSpan_spec hse hm63 f
    refine (ValsB.WFOn_congr y fun i => ⟨fun _ => hall rfl i, fun _ => trivial⟩).1
      (Vals.cells_expand_wf hex h m.toNat (fun i hi => ?_) (by omega) (by omega)
        (ValsB.pack_wf hp (Vals.gather_wf hg' hx.2.2.2) fun _ _ => trivial))
    obtain ⟨e1, b1⟩ := cellSpan_width hse' hb1 hw i hi
    rw [e1, toNat_toUInt64 (by omega)]; exact b1

/-- **`Tab.pack` keeps `Tab.WF`** (`ValsB.pack_wf` on both sides). -/
theorem Tab.pack_wf {R t : Tab A B} (h : R.pack = .ok t) (hR : R.WF) : t.WF := by
  simp only [Tab.pack, bind, Except.bind, pure, Except.pure] at h
  split at h; · cases h
  rename_i x hx; split at h; · cases h
  rename_i y hy; cases h
  exact ⟨ValsB.pack_wf hx hR.1 fun _ _ => trivial, ValsB.pack_wf hy hR.2 fun _ _ => trivial⟩

namespace Tab

/-- A property `W` that `pack` and every round of `step` keep holds of `fixOn`'s answer (`fixOn_inv`), whatever the
state: the table (`nu`, `mu`) or the table with its frontier (`star`). -/
theorem fixOn_wf {σ : Type} {size : σ → USize} {pack : σ → Except String σ} {out : String}
    {step : σ → Except String σ} (W : σ → Prop) (hp : ∀ X t, pack X = .ok t → W X → W t)
    (hs : ∀ X t, step X = .ok t → W X → W t) {k : Nat} {X t : σ} (h : fixOn size pack out step k X = .ok t)
    (hX : W X) : W t :=
  let ⟨_, _, wX, hY, hT, _⟩ := fixOn_inv W (fun _ _ _ wX hY hY' => hp _ _ hY' (hs _ _ hY wX)) k X t hX h
  hp _ _ hT (hs _ _ hY wX)

theorem mu_wf {what : String} {cap : Nat} {f : Tab A B → Except String (Tab A B)}
    (hf : ∀ X t, f X = .ok t → X.WF → t.WF) {t : Tab A B} (h : mu what cap f = .ok t) : t.WF := by
  simp only [mu, bind, Except.bind] at h
  split at h; · cases h
  refine fixOn_wf Tab.WF (fun _ _ => pack_wf) (fun X t hX wX => ?_) h (zero_wf ‹_›)
  simp only [bind, Except.bind] at hX
  split at hX; · cases hX
  exact union_wf hX wX (hf _ _ ‹_› wX)

theorem nu_wf {f : Tab A B → Except String (Tab A B)} {top : Tab A B}
    (hf : ∀ X t, f X = .ok t → X.WF → t.WF) {t : Tab A B} (h : nu f top = .ok t) (hT : top.WF) : t.WF := by
  simp only [nu, bind, Except.bind] at h
  split at h; · cases h
  refine fixOn_wf Tab.WF (fun _ _ => pack_wf) (fun X t hX wX => ?_) h (canon_wf ‹_› hT)
  simp only [bind, Except.bind] at hX
  split at hX; · cases hX
  exact inter_wf hX wX (hf _ _ ‹_› wX)

/-! ### `Λ`: `nil`, `lamOf`, `lam`, `E` -/

theorem nil_wf {n : USize} {D : Vals A n} {t : Tab A (.arr B)} (h : Tab.nil D = .ok t) (hD : Vals.WF D) :
    t.WF := by
  unfold Tab.nil at h; simp only [bind, Except.bind] at h
  split at h; · cases h
  rename_i z hz; split at h; · cases h
  refine canon_wf h ⟨hD, trivial, trivial, fun i _ => ?_, Vals.none_wf _ ‹_›⟩
  simp [ColB.get, Arr.zeros_get hz]

/-- **`lamOf` keeps `Tab.WF`**: `nil` at an `r` of no rows, else `lamOf_canon`'s cells inside the `N` sorted rows. -/
theorem lamOf_wf {n : USize} {D : Vals A n} {r : Tab A B} {t : Tab A (.arr B)} (h : Tab.lamOf D r = .ok t)
    (hD : Vals.WF D) (hr : r.WF) : t.WF := by
  obtain ⟨U, hU, wU, -⟩ := lamOf_canon h hD hr
  exact canon_wf hU wU

theorem lam_wf {n : USize} {D : Vals A n} {R : Tab A B} {t : Tab A (.arr B)} (h : Tab.lam D R = .ok t)
    (hD : Vals.WF D) (hR : R.WF) : t.WF := by
  simp only [Tab.lam, bind, Except.bind] at h
  split at h; · cases h
  exact lamOf_wf h hD (canon_wf ‹_› hR)

theorem tau_wf {n : USize} {X : Vals A n} {t : Tab A (.arr A)} (h : Tab.tau X = .ok t) (hX : Vals.WF X) : t.WF := by
  simp only [Tab.tau, bind, Except.bind] at h
  split at h; · cases h
  exact lam_wf h hX (idU_wf ‹_› hX)

end Tab

/-! ### The list ops (`Rel/Run/List.lean`)

A new cell is laid out by `Vals.cells` over the EXPAND of its own widths (`Vals.cells_expand_wf`, each width bounded
by the payload sizes), or is a slice `[a, b)` of an input cell `[SN, EN)` with `SN ≤ a ≤ b ≤ EN ≤ m` (`cell_wf_nat`). -/
namespace Tab

theorem cat_wf {K : Obj} {P : Tab K (.prod (.arr B) (.arr B))} {t : Tab K (.arr B)} (h : Tab.cat P = .ok t)
    (hP : P.WF) : t.WF := by
  simp only [Tab.cat, bind, Except.bind] at h
  split at h; · cases h
  exact canon_wf h ⟨hP.1, Vals.cat_wf ‹_› hP.2.1 hP.2.2⟩

/-- **`snoc` keeps `Tab.WF`**: `cat` after `τ`, whose `n < 2^63` is `cat`'s guard (`Vals.cat_lt`). -/
theorem snoc_wf {K : Obj} {P : Tab K (.prod (.arr B) B)} {t : Tab K (.arr B)} (h : Tab.snoc P = .ok t)
    (hP : P.WF) : t.WF := by
  simp only [Tab.snoc, bind, Except.bind] at h
  split at h; · cases h
  rename_i y hy; split at h; · cases h
  rename_i z hz
  exact canon_wf h ⟨hP.1, Vals.cat_wf hz hP.2.1 (Vals.tau_wf hy (Vals.cat_lt hz) hP.2.2)⟩

theorem cons_wf {K : Obj} {P : Tab K (.prod B (.arr B))} {t : Tab K (.arr B)} (h : Tab.cons P = .ok t)
    (hP : P.WF) : t.WF := by
  simp only [Tab.cons, bind, Except.bind] at h
  split at h; · cases h
  rename_i y hy; split at h; · cases h
  rename_i z hz
  exact canon_wf h ⟨hP.1, Vals.cat_wf hz (Vals.tau_wf hy (Vals.cat_lt hz) hP.2.1) hP.2.2⟩

theorem zip_wf {K : Obj} {P : Tab K (.prod (.arr A) (.arr B))} {t : Tab K (.arr (.prod A B))}
    (h : Tab.zip P = .ok t) (hP : P.WF) : t.WF := by
  simp only [Tab.zip, bind, Except.bind] at h
  split at h; · cases h
  exact canon_wf h ⟨hP.1, Vals.zip_wf ‹_› hP.2.1 hP.2.2⟩

theorem prefix_wf {n : USize} {X : Vals (.arr B) n} {t : Tab (.arr B) (.arr B)} (h : Tab.«prefix» X = .ok t)
    (hX : Vals.WF X) : t.WF := by
  simp only [Tab.«prefix», bind, Except.bind] at h
  split at h; · cases h
  rename_i u hu; split at h; · cases h
  have wu := uncat_wf hu hX
  exact comp_wf h wu (outl_wf ‹_› wu.2)

theorem suffix_wf {n : USize} {X : Vals (.arr B) n} {t : Tab (.arr B) (.arr B)} (h : Tab.suffix X = .ok t)
    (hX : Vals.WF X) : t.WF := by
  simp only [Tab.suffix, bind, Except.bind] at h
  split at h; · cases h
  rename_i u hu; split at h; · cases h
  have wu := uncat_wf hu hX
  exact comp_wf h wu (outr_wf ‹_› wu.2)

theorem inits_wf {n : USize} {X : Vals (.arr B) n} {t : Tab (.arr B) (.arr (.arr B))} (h : Tab.inits X = .ok t)
    (hX : Vals.WF X) : t.WF := by
  simp only [Tab.inits, bind, Except.bind] at h
  split at h; · cases h
  exact lamOf_wf h hX (prefix_wf ‹_› hX)

/-- **`tails` keeps `Tab.WF`**: `Λ(cat°)`'s cells kept, over the second column of their payload. -/
theorem tails_wf {n : USize} {X : Vals (.arr B) n} {t : Tab (.arr B) (.arr (.arr B))} (h : Tab.tails X = .ok t)
    (hX : Vals.WF X) : t.WF := by
  simp only [Tab.tails, bind, Except.bind] at h
  split at h; · cases h
  rename_i U hU; split at h; · cases h
  rename_i L hL
  have wL := lamOf_wf hL hX (uncat_wf hU hX)
  obtain ⟨Ln, Lk, m, lo, hi, f⟩ := L
  simp only [pure, Except.pure, Except.ok.injEq] at h; subst h
  exact ⟨wL.1, wL.2.1, wL.2.2.1, wL.2.2.2.1, wL.2.2.2.2.2⟩

theorem sumOn_wf {u : QAtomicType} {n : USize} {X : Vals (.arr (.atom u)) n} {t : Tab (.arr (.atom u)) (.atom u)}
    (h : Tab.sumOn X = .ok t) (hX : Vals.WF X) : t.WF := by
  obtain ⟨m, lo, hi, f⟩ := X
  simp only [Tab.sumOn, bind, Except.bind] at h
  okSplit
  exact canon_wf h (keep_wf ‹_› ⟨hX, trivial⟩)

theorem sum_wf : {V : Obj} → {n : USize} → {X : Vals (.arr V) n} → {t : Tab (.arr V) V} → Tab.sum X = .ok t →
    Vals.WF X → t.WF
  | .atom _, _, _, _, h, hX => sumOn_wf h hX
  | .prod _ _, _, _, _, h, _ | .arr _, _, _, _, h, _ | .sum _ _, _, _, _, h, _ => by
    simp [Tab.sum, throw, throwThe, MonadExceptOf.throw] at h

theorem setify_wf {n : USize} {X : Vals (.arr B) n} {t : Tab (.arr B) (.arr B)} (h : Tab.setify X = .ok t)
    (hX : Vals.WF X) : t.WF := by
  simp only [Tab.setify, bind, Except.bind] at h
  split at h; · cases h
  exact lamOf_wf h hX (mem_wf ‹_› hX)

end Tab

end Rel
