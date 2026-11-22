import Rel.RepCols
import Rel.Run.Bits
import Rel.Run.Power
import Rel.Run.Asc
import Rel.Run.Fix
import Rel.RepTabDiv

/-! **`Tab.WF` kept by each `Tab` op** (PLAN 8.5): an op's output sides are `Vals.gather`ed, `Vals.concat`ed or
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
  obtain ⟨hn, ho⟩ := catPlan_ok (show catPlan n₁ n₂ = .ok (p.1, p.2) from hp)
  split at h; · cases h
  rename_i z hz
  okSplit
  cases h; exact Vals.concat_wf hn ho hz hx hy

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

theorem cmpPairs_wf {op : Op} {t : QAtomicType} {T u : Tab (.atom t) (.atom t)} (h : cmpPairs op T = .ok u)
    (hT : T.WF) : u.WF := by
  simp only [Tab.cmpPairs, bind, Except.bind] at h
  okSplit
  exact keep_wf h hT

theorem cmpOn_wf {op : Op} {t : QAtomicType} {n m : USize} {K : Vals (.atom t) n} {L : Vals (.atom t) m}
    {u : Tab (.atom t) (.atom t)} (h : cmpOn op K L = .ok u) (hK : Vals.WF K) (hL : Vals.WF L) : u.WF := by
  simp only [Tab.cmpOn, bind, Except.bind] at h
  okSplit
  exact cmpPairs_wf h (cross_wf ‹_› hK hL)



/-- **`r \ s` keeps `Tab.WF`**: the groups of `Q = r° ≫ ⟨𝟙, s⟩` gathered (`compOne_wf`), `∪` the vacuous part
(`cross_wf` of `ran`s). -/
theorem ldivOf_wf {r : Tab A B} {s : Tab A C} {UB : Tab B B} {UC : Tab C C} {t : Tab B C}
    (h : ldivOf r s UB UC = .ok t) (hr : r.WF) (hs : s.WF) (hB : UB.WF) (hC : UC.WF) : t.WF := by
  simp only [Tab.ldivOf, bind, Except.bind, pure, Except.pure] at h
  split at h; · cases h
  rename_i Q hQ
  have wQ := compOne_wf hQ ⟨hr.2, hr.1⟩ ⟨hs.1, hs.1, hs.2⟩
  okSplit
  exact union_wf h ⟨Vals.gather_wf ‹_› wQ.1, Vals.gather_wf ‹_› wQ.2.2⟩
    (cross_wf ‹_› (diff_wf ‹_› (ran_wf ‹_› hB) (ran_wf ‹_› hr)).1 (ran_wf ‹_› hC).1)

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
  obtain ⟨l, r, tag, idx, x, y⟩ := X
  simp only [Tab.inlConv, bind, Except.bind] at h
  okSplit
  all_goals first | exact zero_wf h | exact comp_wf h (idU_wf ‹_› hX) (conv_wf ‹_› (inl_wf ‹_› hX.1))

theorem inrConv_wf {n : USize} {X : Vals (.sum A B) n} {t : Tab (.sum A B) B} (h : Tab.inrConv X = .ok t)
    (hX : Vals.WF X) : t.WF := by
  obtain ⟨l, r, tag, idx, x, y⟩ := X
  simp only [Tab.inrConv, bind, Except.bind] at h
  okSplit
  all_goals first | exact zero_wf h | exact comp_wf h (idU_wf ‹_› hX) (conv_wf ‹_› (inr_wf ‹_› hX.2))

/-! ### The power operators that build no cell -/

theorem length_wf {n : USize} {X : Vals (.arr B) n} {t : Tab (.arr B) .long} (h : Tab.length X = .ok t)
    (hX : Vals.WF X) : t.WF := by
  obtain ⟨m, lo, hi, f⟩ := X
  simp only [Tab.length, bind, Except.bind] at h
  okSplit
  exact canon_wf h ⟨hX, trivial⟩

theorem atPos_wf {n : USize} {k : Nat} {X : Vals (.arr B) n} {t : Tab (.arr B) B} (h : Tab.atPos k X = .ok t)
    (hX : Vals.WF X) : t.WF := by
  obtain ⟨m, lo, hi, f⟩ := X
  simp only [Tab.atPos, bind, Except.bind] at h
  okSplit
  exact canon_wf h ⟨Vals.gather_wf ‹_› hX, Vals.gather_wf ‹_› hX.2⟩

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

/-- **`Vals.pack` keeps `Vals.WF`**: a cut payload is the input's gathered and packed, laid out by `Vals.cells` over
the EXPAND of the cells' own widths, each at most `m` (`cellSpan_width`, `Vals.cells_expand_wf`). -/
theorem Vals.pack_wf : {A : Obj} → {n : USize} → {x y : Vals A n} → Vals.pack x = .ok y → Vals.WF x → Vals.WF y
  | .atom _, _, _, _, _, _ => trivial
  | .one, _, _, _, _, _ => trivial
  | .prod _ _, _, x, _, h, hx => by
    simp only [Vals.pack, bind, Except.bind, pure, Except.pure] at h
    split at h; · cases h
    rename_i y1 h1
    split at h; · cases h
    rename_i y2 h2
    cases h; exact ⟨Vals.pack_wf h1 hx.1, Vals.pack_wf h2 hx.2⟩
  | .sum _ _, _, ⟨l, r, tag, idx, x, y⟩, _, h, hx => by
    simp only [Vals.pack, bind, Except.bind, pure, Except.pure] at h
    split at h; · cases h
    rename_i x' h1
    split at h; · cases h
    rename_i y' h2
    cases h; exact ⟨Vals.pack_wf h1 hx.1, Vals.pack_wf h2 hx.2⟩
  | .arr B, n, ⟨m, lo, up, f⟩, y, h, hx => by
    simp only [Vals.pack] at h
    split at h; · cases h
    rename_i hb
    simp only [bind] at h
    rw [Except.bind_eq_ok'] at h; obtain ⟨_, -, h⟩ := h
    rw [Except.bind_eq_ok'] at h; obtain ⟨⟨s, e⟩, hse, h⟩ := h; try dsimp only at h
    rw [Except.bind_eq_ok'] at h; obtain ⟨w, hw, h⟩ := h
    split at h; · cases h
    split at h
    case isFalse =>
      rw [Except.bind_eq_ok'] at h; obtain ⟨f', hf', h⟩ := h
      cases h; exact ⟨hx.1, Vals.pack_wf hf' hx.2⟩
    rw [Except.bind_eq_ok'] at h; obtain ⟨⟨T, G, u⟩, hex, h⟩ := h; try dsimp only at h
    rw [Except.bind_eq_ok'] at h; obtain ⟨sg, hsg, h⟩ := h
    rw [Except.bind_eq_ok'] at h; obtain ⟨ix, hix, h⟩ := h
    rw [Except.bind_eq_ok'] at h; obtain ⟨g', hg', h⟩ := h
    rw [Except.bind_eq_ok'] at h; obtain ⟨p, hp, h⟩ := h
    have hm63 : m.toNat < 2 ^ 63 := by omega
    obtain ⟨SN, EN, hse', hb1, -⟩ := cellSpan_spec hse hm63 f
    refine Vals.cells_expand_wf hex h m.toNat (fun i hi => ?_) (by omega) (by omega)
      (Vals.pack_wf hp (Vals.gather_wf hg' hx.2))
    obtain ⟨e1, b1⟩ := cellSpan_width hse' hb1 hw i hi
    rw [e1, toNat_toUInt64 (by omega)]; exact b1

/-- **`Tab.pack` keeps `Tab.WF`** (`Vals.pack_wf` on both sides). -/
theorem Tab.pack_wf {R t : Tab A B} (h : R.pack = .ok t) (hR : R.WF) : t.WF := by
  simp only [Tab.pack, bind, Except.bind, pure, Except.pure] at h
  split at h; · cases h
  rename_i x hx; split at h; · cases h
  rename_i y hy; cases h
  exact ⟨Vals.pack_wf hx hR.1, Vals.pack_wf hy hR.2⟩

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

/-- `P ≫ star(R)` on a `WF` `P`, `step` keeping `WF`: each round's `X` and `Δ` stay `WF` (`fixOn_wf` on the pair). -/
theorem star_wf {K B : Obj} {step : Tab B B → Except String (Tab B B)} (hf : ∀ D t, step D = .ok t → D.WF → t.WF)
    {P t : Tab K B} (h : star step P = .ok t) (hP : P.WF) : t.WF := by
  simp only [star, bind] at h
  rw [Except.bind_eq_ok'] at h; obtain ⟨P', hP', h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨r, hr, h⟩ := h
  obtain rfl : r.1 = t := Except.ok.inj h
  refine (fixOn_wf (fun s : Tab K B × Tab K B => s.1.WF ∧ s.2.WF) (fun s t hs ws => ?_) (fun s t hs ws => ?_) hr
    ⟨canon_wf hP' hP, canon_wf hP' hP⟩).1
  · simp only [bind] at hs
    rw [Except.bind_eq_ok'] at hs; obtain ⟨U, hU, hs⟩ := hs
    rw [Except.bind_eq_ok'] at hs; obtain ⟨D, hD, hs⟩ := hs
    obtain rfl : (U, D) = t := Except.ok.inj hs
    exact ⟨pack_wf hU ws.1, pack_wf hD ws.2⟩
  · simp only [bind] at hs
    rw [Except.bind_eq_ok'] at hs; obtain ⟨Dr, hDr, hs⟩ := hs
    rw [Except.bind_eq_ok'] at hs; obtain ⟨T, hT, hs⟩ := hs
    rw [Except.bind_eq_ok'] at hs; obtain ⟨N, hN, hs⟩ := hs
    rw [Except.bind_eq_ok'] at hs; obtain ⟨D, hD, hs⟩ := hs
    rw [Except.bind_eq_ok'] at hs; obtain ⟨U, hU, hs⟩ := hs
    obtain rfl : (U, D) = t := Except.ok.inj hs
    have wD := diff_wf hD (comp_wf hN ws.2 (hf _ _ hT (ran_wf hDr ws.2))) ws.1
    exact ⟨union_wf hU ws.1 wD, wD⟩

/-! ### `Λ`: `nil`, `lamOf`, `lam`, `E` -/

theorem nil_wf {n : USize} {D : Vals A n} {t : Tab A (.arr B)} (h : Tab.nil D = .ok t) (hD : Vals.WF D) :
    t.WF := by
  unfold Tab.nil at h; simp only [bind, Except.bind] at h
  split at h; · cases h
  rename_i z hz; split at h; · cases h
  refine canon_wf h ⟨hD, fun i => ?_, Vals.none_wf ‹_›⟩
  rw [Arr.zeros_get hz]; simp

/-- **`lamOf` keeps `Tab.WF`**: `nil` at an `r` of no rows, else `lamOf_canon`'s cells inside the `N` sorted rows. -/
theorem lamOf_wf {n : USize} {D : Vals A n} {r : Tab A B} {t : Tab A (.arr B)} (h : Tab.lamOf D r = .ok t)
    (hD : Vals.WF D) (hr : r.WF) : t.WF := by
  by_cases h0 : r.n.toNat = 0
  · simp only [Tab.lamOf, if_pos h0] at h; exact nil_wf h hD
  · obtain ⟨U, hU, wU, -⟩ := lamOf_canon h hD hr
    exact canon_wf hU (wU h0 hD hr)

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

/-- **`Vals.cat` keeps `Vals.WF`**: widths `w₁ + w₂ ≤ m₁ + m₂` over the joined payloads gathered. -/
theorem Vals.cat_wf {B : Obj} {n : USize} {X Y Z : Vals (.arr B) n} (h : Vals.cat X Y = .ok Z) (hX : Vals.WF X)
    (hY : Vals.WF Y) : Vals.WF Z := by
  obtain ⟨m₁, lo₁, up₁, f₁⟩ := X
  obtain ⟨m₂, lo₂, up₂, f₂⟩ := Y
  simp only [Vals.cat] at h
  split at h; · cases h
  rename_i hb
  simp only [bind] at h
  rw [Except.bind_eq_ok'] at h; obtain ⟨_, -, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨⟨N, off⟩, hpl, h⟩ := h; try dsimp only at h
  rw [Except.bind_eq_ok'] at h; obtain ⟨F, hF, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨⟨s₁, e₁⟩, hse₁, h⟩ := h; try dsimp only at h
  rw [Except.bind_eq_ok'] at h; obtain ⟨⟨s₂, e₂⟩, hse₂, h⟩ := h; try dsimp only at h
  rw [Except.bind_eq_ok'] at h; obtain ⟨w₁, hw₁, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨w₂, hw₂, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨w, hw, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨⟨T, G, u⟩, hex, h⟩ := h; try dsimp only at h
  rw [Except.bind_eq_ok'] at h; obtain ⟨ga, hga, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨a, ha, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨cm, hcm, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨sm, hsm, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨dd, hdd, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨gd, hgd, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨b, hbb, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨gw, hgw, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨c, hc, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨ab, hab, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨cab, hcab, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨ix, hix, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨g, hg, h⟩ := h
  obtain ⟨hNn, hoff⟩ := catPlan_ok hpl
  have hm₁ : m₁.toNat < 2 ^ 63 := by omega
  have hm₂ : m₂.toNat < 2 ^ 63 := by omega
  obtain ⟨S₁, E₁, hse₁', hb₁, -⟩ := cellSpan_spec hse₁ hm₁ f₁
  obtain ⟨S₂, E₂, hse₂', hb₂, -⟩ := cellSpan_spec hse₂ hm₂ f₂
  refine Vals.cells_expand_wf hex h (m₁.toNat + m₂.toNat) (fun i hi => ?_) (by omega) (by omega)
    (Vals.gather_wf hg (Vals.concat_wf hNn hoff hF hX.2 hY.2))
  obtain ⟨x₁, y₁⟩ := cellSpan_width hse₁' hb₁ hw₁ i hi
  obtain ⟨x₂, y₂⟩ := cellSpan_width hse₂' hb₂ hw₂ i hi
  have es := (colMap_raw hw).2.2.2 i hi
  rw [x₁, x₂] at es; simp only [Op.eval, Except.ok.injEq] at es
  rw [← es, ← UInt64.ofNat_add, toNat_toUInt64 (by omega)]; omega

/-- **`Vals.zip` keeps `Vals.WF`**: widths `min w₁ w₂`, each one of `w₁ ≤ m₁`, `w₂ ≤ m₂`, over both payloads
gathered. -/
theorem Vals.zip_wf {A B : Obj} {n : USize} {X : Vals (.arr A) n} {Y : Vals (.arr B) n}
    {Z : Vals (.arr (.prod A B)) n} (h : Vals.zip X Y = .ok Z) (hX : Vals.WF X) (hY : Vals.WF Y) : Vals.WF Z := by
  obtain ⟨m₁, lo₁, up₁, f₁⟩ := X
  obtain ⟨m₂, lo₂, up₂, f₂⟩ := Y
  simp only [Vals.zip] at h
  split at h; · cases h
  rename_i hb
  simp only [bind] at h
  rw [Except.bind_eq_ok'] at h; obtain ⟨_, -, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨⟨s₁, e₁⟩, hse₁, h⟩ := h; try dsimp only at h
  rw [Except.bind_eq_ok'] at h; obtain ⟨⟨s₂, e₂⟩, hse₂, h⟩ := h; try dsimp only at h
  rw [Except.bind_eq_ok'] at h; obtain ⟨w₁, hw₁, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨w₂, hw₂, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨w, hw, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨⟨T, G, u⟩, hex, h⟩ := h; try dsimp only at h
  rw [Except.bind_eq_ok'] at h; obtain ⟨g₁, hg₁, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨a₁, ha₁, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨x, hx, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨g₂, hg₂, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨a₂, ha₂, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨y, hy, h⟩ := h
  have hm₁ : m₁.toNat < 2 ^ 63 := by omega
  have hm₂ : m₂.toNat < 2 ^ 63 := by omega
  obtain ⟨S₁, E₁, hse₁', hb₁, -⟩ := cellSpan_spec hse₁ hm₁ f₁
  obtain ⟨S₂, E₂, hse₂', hb₂, -⟩ := cellSpan_spec hse₂ hm₂ f₂
  refine Vals.cells_expand_wf hex h (m₁.toNat + m₂.toNat) (fun i hi => ?_) (by omega) (by omega)
    ⟨Vals.gather_wf hx hX.2, Vals.gather_wf hy hY.2⟩
  obtain ⟨x₁, y₁⟩ := cellSpan_width hse₁' hb₁ hw₁ i hi
  obtain ⟨x₂, y₂⟩ := cellSpan_width hse₂' hb₂ hw₂ i hi
  have es := (colMap_raw hw).2.2.2 i hi
  rw [x₁, x₂] at es; simp only [Op.eval, Except.ok.injEq] at es
  rw [← es]; split <;> rw [toNat_toUInt64 (by omega)] <;> omega

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

/-- **`uncat` keeps `Tab.WF`**: split `d ≤ EN - SN` of cell `[SN, EN)` (`expand_spec` of the counts `EN - SN + 1`) is
`[SN, SN + d)` and `[SN + d, EN)`, inside `m` (`cellSpan_start_le` where the cell is empty). -/
theorem uncat_wf {n : USize} {X : Vals (.arr B) n} {t : Tab (.arr B) (.prod (.arr B) (.arr B))}
    (h : Tab.uncat X = .ok t) (hX : Vals.WF X) : t.WF := by
  obtain ⟨m, lo, up, f⟩ := X
  dsimp only [Tab.uncat] at h
  split at h; · cases h
  rename_i hb
  simp only [bind] at h
  rw [Except.bind_eq_ok'] at h; obtain ⟨_, -, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨⟨s, e⟩, hse, h⟩ := h; try dsimp only at h
  rw [Except.bind_eq_ok'] at h; obtain ⟨wd, hwd, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨c1, hc1, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨w, hw, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨⟨Tn, G, u⟩, hex, h⟩ := h; try dsimp only at h
  rw [Except.bind_eq_ok'] at h; obtain ⟨sG, hsG, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨mid, hmid, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨K, hK, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨eG, heG, h⟩ := h
  have hm63 : m.toNat < 2 ^ 63 := by omega
  have hn63 : n.toNat < 2 ^ 63 := by omega
  obtain ⟨SN, EN, hse', hb1, -⟩ := cellSpan_spec hse hm63 f
  obtain ⟨wN, hwN⟩ : ∃ F : Nat → Nat, ∀ i, F i = EN i - SN i + 1 := ⟨_, fun _ => rfl⟩
  have hww : ∀ i < n.toNat, (raw .i64 n w)[i]?.getD 0 = (wN i).toUInt64 := fun i hi => by
    have e2 := (colMap_raw hw).2.2.2 i hi
    rw [colConst_raw hc1, Array.getElem?_replicate, if_pos hi, Option.getD_some,
      (cellSpan_width hse' hb1 hwd i hi).1] at e2
    simp only [Op.eval, Except.ok.injEq] at e2
    rw [← e2, hwN]; exact (UInt64.ofNat_add _ _).symm
  have hsn : ((List.range n.toNat).map wN).sum < 2 ^ 63 := by
    have := sum_range_le_mul (wN := wN) (k := n.toNat) (c := m.toNat + 1) fun i _ => by have := hb1 i; rw [hwN]; omega
    omega
  obtain ⟨hTn, hrun⟩ := expand_spec hex wN hww hsn hn63
  -- row `t` is split `d` of its cell `g`: `sG = SN g`, `mid = SN g + d`, `eG = EN g`, `SN g + d ≤ EN g ≤ m`
  have hJ : ∀ t : Fin Tn.toNat, ∃ a d b : Nat, (raw .i64 Tn sG.enc)[t.1]?.getD 0 = a.toUInt64 ∧
      (raw .i64 Tn mid.enc)[t.1]?.getD 0 = (a + d).toUInt64 ∧ (raw .i64 Tn eG.enc)[t.1]?.getD 0 = b.toUInt64 ∧
      a + d ≤ b ∧ b ≤ m.toNat := fun t => by
    obtain ⟨g, hg, h1, h2⟩ := exists_group wN n.toNat t (by rw [← hTn]; exact t.2)
    obtain ⟨hG, hu⟩ := hrun g hg t h1 h2
    have hGg : ((raw .i64 Tn G)[t.1]?.getD 0).toNat = g := by rw [hG, toNat_toUInt64 (by omega)]
    obtain ⟨i2, hi2, hs2⟩ := Arr.gather_raw s hsG t
    obtain ⟨i3, hi3, he3⟩ := Arr.gather_raw e heG t
    obtain rfl : i2 = ⟨g, hg⟩ := Fin.ext (hi2.symm.trans hGg)
    obtain rfl : i3 = ⟨g, hg⟩ := Fin.ext (hi3.symm.trans hGg)
    rw [(hse' g hg).1] at hs2
    rw [(hse' g hg).2] at he3
    have hd : t.1 - ((List.range g).map wN).sum ≤ EN g - SN g := by rw [hwN] at h2; omega
    have hmw : (raw .i64 Tn mid.enc)[t.1]?.getD 0 = (SN g + (t.1 - ((List.range g).map wN).sum)).toUInt64 := by
      have es := (colMap_raw (colArr_ok hmid)).2.2.2 _ t.2
      rw [hs2, hu] at es; simp only [Op.eval, Except.ok.injEq] at es
      rw [← es, ← UInt64.ofNat_add]
    have hSm := cellSpan_start_le hse hX.1 ⟨g, hg⟩
    rw [(hse' g hg).1, toNat_toUInt64 (by have := hb1 g; omega)] at hSm
    have hd' : SN g + (t.1 - ((List.range g).map wN).sum) ≤ EN g := by have := hb1 g; omega
    refine ⟨SN g, _, EN g, hs2, hmw, he3, hd', ?_⟩
    have := hb1 g; omega
  refine canon_wf h ⟨Vals.gather_wf hK hX, ⟨fun t => ?_, hX.2⟩, ⟨fun t => ?_, hX.2⟩⟩
  · obtain ⟨a, d, b, ha, hd, -, hab, hbm⟩ := hJ t
    exact cell_wf_nat ha hd (by omega) (by omega) hm63
  · obtain ⟨a, d, b, -, hd, hb', hab, hbm⟩ := hJ t
    exact cell_wf_nat hd hb' hab hbm hm63

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
  have wL := lam_wf hL hX (uncat_wf hU hX)
  obtain ⟨Ln, Lk, m, lo, hi, f⟩ := L
  simp only [pure, Except.pure, Except.ok.injEq] at h; subst h
  exact ⟨wL.1, wL.2.1, wL.2.2.2⟩

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
