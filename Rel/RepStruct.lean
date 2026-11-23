module

public import Rel.Run.Struct
public import Rel.RepTabComp
public import Rel.RepSetOps
public import Rel.Core.Rel

-- exposed: every def body is a spec a downstream `rfl`/`decide`/`simp` may unfold (PLAN W.8)
@[expose] public section

/-! The laws of the structural operators (`Rel/Run/Struct.lean`), each with its `Tm` constructor's denotation
(`Tm.den`, `Rel/Lang/Den.lean`) as the right-hand side, and their checks against their denotations as sets. -/

namespace Rel
open Rel.Ext Rel.Kernel Rel.Verify Ext.Enc
open scoped Rel.Core.Rel
/-- `Arr.zeros` holds `0` at every row. -/
theorem Arr.zeros_get {n : USize} {z : Arr .i64 n} (h : Arr.zeros .i64 n = .ok z) (i : Fin n.toNat) : z.get i = 0 := by
  unfold Arr.zeros at h
  obtain ⟨w, hw, es⟩ := colMap_first_chain (colArr_ok h) i.1 i.2
  simp [chain, Op.eval] at hw
  have e0 : (raw .i64 n z.enc)[i.1]?.getD 0 = 0 := by simp [es, ← hw]
  rw [Arr.get_i64, e0]; rfl

/-- **Every row of `Opt.nuls t n` is the null** (`wordsFoR` of `n` zero words with every row flagged). -/
theorem Opt.nuls_get {t : QAtomicType} {n : USize} {x : Opt t n} (h : Opt.nuls t n = .ok x) (i : Fin n.toNat) :
    x.get i = none := by
  unfold Opt.nuls at h
  dsimp only at h
  split at h
  rotate_left; · cases h
  cases h
  have hf := foRNuls_wordsFoR (Array.replicate n.toNat 0) (nulMap (Array.replicate n.toNat 1)) (n := n) (by simp) i.1
    (by simpa using i.2)
  have hb : Column.bitAt (nulMap (Array.replicate n.toNat 1)) i.1 = true := by
    simp only [nulMap, Array.size_replicate]
    rw [bitAt_packOf _ _ _ i.2]; simp
  rw [hb, if_pos rfl] at hf
  have hn : Opt.isNul ⟨wordsFoR (Array.replicate n.toNat 0) (nulMap (Array.replicate n.toNat 1)), ‹_›⟩ i = true := by
    cases hc : Opt.isNul ⟨wordsFoR (Array.replicate n.toNat 0) (nulMap (Array.replicate n.toNat 1)), ‹_›⟩ i
    · exact absurd (Option.some.inj (((Opt.isNul_eq_false _ i).1 hc).symm.trans hf)) (by decide)
    · rfl
  simp only [Opt.get, hn, if_true]

/-- **Every row of `tagCol n s` is `s`**: the positions through `[(.and, 0), (.or, s)]`, cut to the bit. -/
theorem tagCol_get {n : USize} {s : Bool} {tag : Arr .u1 n} (h : tagCol n s = .ok tag) (k : Fin n.toNat) :
    tag.get k = s := by
  have hc := colArr_ok h
  obtain ⟨a, ha, he⟩ := Arr.get_u1 tag (colMap_closed (by lockstep) hc).1 k
  obtain ⟨v, ev, hv⟩ := colMap_first_chain hc k.1 k.2
  rw [ha] at hv
  simp [chain, Op.eval, bind, Except.bind, pure, Except.pure] at ev
  simp only [if_true, Option.some.injEq] at hv
  subst ev; subst hv
  cases s <;> cases hg : tag.get k <;> rw [hg] at he <;> revert he <;> decide

/-- **Every row of `Arr.dflts t n` is `t`'s `default`**: the stored word of the null read back at `t` (`ofBits_word`); a
`general` payload is no column of words (`Enc.WF`), so `Arr.dflts` never answers there. -/
theorem Arr.dflts_get {t : QAtomicType} {n : USize} {z : Arr t n} (h : Arr.dflts t n = .ok z) (i : Fin n.toNat) :
    z.get i = @default (Dep.Carrier t) Dep.instInhabitedCarrier := by
  have hc := colArr_ok h
  have hcl := colMap_closed (by lockstep) hc
  have ht : t ≠ .general := by
    rintro rfl
    obtain ⟨hv, hw⟩ := hcl
    revert hv hw; cases z.enc <;> simp [Kernel.Enc.Valid, Ext.Enc.WF, QAtomicType.width]
  have hgo : ∀ a, (Dep.Carrier.of? t (.atom (Column.atomOfBits t a ht))).getD default = QAtomicType.ofBits t a := by
    cases t <;> first | exact absurd rfl ht | (intro a; rfl)
  have hdw : QAtomicType.ofBits t (QAtomicType.word t (@default (Dep.Carrier t) Dep.instInhabitedCarrier)) =
      @default (Dep.Carrier t) Dep.instInhabitedCarrier := by
    cases t <;> first | exact absurd rfl ht | decide
  obtain ⟨a, ha, -, hg⟩ := Arr.get_raw_atom z hcl.1 ht i
  obtain ⟨v, ev, hv⟩ := colMap_first_chain hc i.1 i.2
  rw [ha] at hv
  simp only [chain, Op.eval, List.foldlM_cons, List.foldlM_nil, bind, Except.bind, pure, Except.pure,
    Except.ok.injEq] at ev
  rw [hg, hgo]
  have hv' := Option.some.inj hv
  subst ev
  try simp only [UInt64.zero_and, UInt64.zero_or, UInt64.and_zero, UInt64.or_zero] at hv'
  by_cases hu : t = .u1
  · subst hu; simp only [if_true] at hv'; subst hv'; decide
  · simp only [hu, if_false] at hv'; subst hv'; exact hdw

/-- **`Vals.zeros A n` is `Vals.WF` and every row is `A.dflt`**, by induction on `A`: `Arr.dflts_get` at an atom, an
`arr` side's empty cells, a band column's nulls (`Opt.nuls_get`), a dense sum's tag `false` over two such summands. -/
theorem Vals.zeros_ok : (A : Obj) → (n : USize) → (x : Vals A n) → Vals.zeros A n = .ok x →
    Vals.WF x ∧ ∀ i, Vals.row x i = A.dflt
  | .atom _, _, _, h => ⟨trivial, fun i => Arr.dflts_get h i⟩
  | .one, _, _, _ => ⟨trivial, fun _ => rfl⟩
  | .prod a b, n, x, h => by
    simp only [Vals.zeros, bind, Except.bind, pure, Except.pure] at h
    split at h; · cases h
    rename_i p hp; split at h; · cases h
    rename_i q hq; cases h
    obtain ⟨wp, rp⟩ := Vals.zeros_ok a n _ hp
    obtain ⟨wq, rq⟩ := Vals.zeros_ok b n _ hq
    exact ⟨⟨wp, wq⟩, fun i => by simp only [Vals.row, rp, rq, Obj.dflt]⟩
  | .arr b, n, x, h => by
    simp only [Vals.zeros, bind, Except.bind, pure, Except.pure] at h
    cases hlo : Arr.zeros .i64 n with
    | error e => simp [hlo] at h
    | ok lo =>
    cases hf : Vals.zeros b 0 with
    | error e => simp [hlo, hf] at h
    | ok f =>
    simp only [hlo, hf] at h
    cases h
    refine ⟨⟨fun i => ?_, (Vals.zeros_ok b 0 _ hf).1⟩, fun i => ?_⟩
    · simp [Arr.zeros_get hlo]
    · simp [Vals.row, Obj.dflt]
  | .sum a b, n, x, h => by
    unfold Vals.zeros at h
    split at h
    · rename_i t ht
      simp only [bind, Except.bind, pure, Except.pure] at h
      split at h; · cases h
      rename_i z hz; cases h
      refine ⟨by simp only [Vals.WF, Vals.view_ofOpt], fun i => ?_⟩
      simp only [Vals.row, Vals.view_ofOpt, Opt.nuls_get hz i]
      obtain ⟨rfl, rfl⟩ := Obj.band_some ht
      unfold Obj.optEl; generalize Obj.band_some ht = p; obtain ⟨p1, p2⟩ := p; rfl
    · simp only [bind, Except.bind, pure, Except.pure] at h
      split at h; · cases h
      rename_i tg htg; split at h; · cases h
      rename_i p hp; split at h; · cases h
      rename_i q hq; cases h
      obtain ⟨wp, rp⟩ := Vals.zeros_ok a n _ hp
      obtain ⟨wq, rq⟩ := Vals.zeros_ok b n _ hq
      refine ⟨?_, fun i => ?_⟩
      · simp only [Vals.WF, Vals.view_ofGen]
        exact ⟨wp, wq, fun i _ => rq i, fun i hi => by rw [tagCol_get htg i] at hi; cases hi⟩
      · simp only [Vals.row, Vals.view_ofGen, tagCol_get htg i, Bool.false_eq_true, if_false, rp, Obj.dflt]

/-- **`Vals.ofGen` is `Vals.WF`** on `WF` summands holding `dflt` in the summand the tag does not name. -/
theorem Vals.ofGen_wf {a b : Obj} {n : USize} {h : Obj.band a b = Option.none} {tag : Arr .u1 n} {x : Vals a n}
    {y : Vals b n} (hx : Vals.WF x) (hy : Vals.WF y) (h0 : ∀ i, tag.get i = false → Vals.row y i = b.dflt)
    (h1 : ∀ i, tag.get i = true → Vals.row x i = a.dflt) : Vals.WF (Vals.ofGen h tag x y) := by
  simp only [Vals.WF, Vals.view_ofGen]; exact ⟨hx, hy, h0, h1⟩

/-- **A side of no rows is `Vals.WF`**: an `arr` side of it has no cell. -/
theorem Vals.none_wf {A : Obj} {x : Vals A 0} (h : Vals.none A = .ok x) : Vals.WF x := (Vals.zeros_ok A 0 x h).1

namespace Tab
variable {A B C D I : Obj}

/-- **`𝟘` is `Tab.WF`**: both sides `Vals.none`. -/
theorem zero_wf {t : Tab A B} (h : (Tab.zero : Except String (Tab A B)) = .ok t) : t.WF := by
  simp only [Tab.zero, bind, Except.bind, pure, Except.pure] at h
  split at h; · cases h
  rename_i x hx; split at h; · cases h
  rename_i y hy; cases h
  exact ⟨Vals.none_wf hx, Vals.none_wf hy⟩

/-- **`dom` keeps `Tab.WF`**: `Vals.nub` of the key side, on both sides. -/
theorem dom_wf {R : Tab A B} {t : Tab A A} (h : R.dom = .ok t) (hR : R.WF) : t.WF := by
  unfold Tab.dom at h
  cases hn : Vals.nub R.key with
  | error e => simp [hn, Functor.map, Except.map] at h
  | ok y =>
    simp only [hn, Functor.map, Except.map, Except.ok.injEq] at h; subst h
    exact ⟨Vals.nub_wf hn hR.1, Vals.nub_wf hn hR.1⟩

/-- **`ran` keeps `Tab.WF`**: `Vals.nub` of the value side, on both sides. -/
theorem ran_wf {R : Tab A B} {t : Tab B B} (h : R.ran = .ok t) (hR : R.WF) : t.WF := by
  unfold Tab.ran at h
  cases hn : Vals.nub R.val with
  | error e => simp [hn, Functor.map, Except.map] at h
  | ok y =>
    simp only [hn, Functor.map, Except.map, Except.ok.injEq] at h; subst h
    exact ⟨Vals.nub_wf hn hR.2, Vals.nub_wf hn hR.2⟩

/-- **`idU X` is `Tab.WF`** on a `Vals.WF` `X` (`dom_wf`). -/
theorem idU_wf {n : USize} {X : Vals A n} {t : Tab A A} (h : Tab.idU X = .ok t) (hX : Vals.WF X) : t.WF :=
  dom_wf h ⟨hX, hX⟩

/-- **`R°` keeps `Tab.WF`**: the two sides swapped, `canon`. -/
theorem conv_wf {R : Tab A B} {t : Tab B A} (h : R.conv = .ok t) (hR : R.WF) : t.WF :=
  canon_wf h ⟨hR.2, hR.1⟩

theorem outl_wf {n : USize} {X : Vals (.prod A B) n} {t : Tab (.prod A B) A} (h : Tab.outl X = .ok t)
    (hX : Vals.WF X) : t.WF := canon_wf h ⟨hX, hX.1⟩

theorem outr_wf {n : USize} {X : Vals (.prod A B) n} {t : Tab (.prod A B) B} (h : Tab.outr X = .ok t)
    (hX : Vals.WF X) : t.WF := canon_wf h ⟨hX, hX.2⟩

/-- **`tagged` keeps `Tab.WF`**: its table is the concatenation. -/
theorem tagged_wf {R S : Tab A B} {p : Tab A B × Enc} (h : R.tagged S = .ok p) (hR : R.WF) (hS : S.WF) :
    p.1.WF := by
  simp only [Tab.tagged, bind, Except.bind, pure, Except.pure] at h
  split at h; · cases h
  rename_i q hq
  have hn := catRows_ok hq
  split at h; · cases h
  rename_i x hx; split at h; · cases h
  rename_i y hy; okSplit
  cases h; exact ⟨Vals.concat_wf hn hx hR.1 hS.1, Vals.concat_wf hn hy hR.2 hS.2⟩

/-- **`select` keeps `Tab.WF`**: the kept groups' rows gathered from the tagged concatenation. -/
theorem select_wf {keep : USize → Enc → Enc → Except String Enc} {R S t : Tab A B} (h : select keep R S = .ok t)
    (hR : R.WF) (hS : S.WF) : t.WF := by
  simp only [Tab.select, bind, Except.bind, Functor.map, Except.map] at h
  split at h; · cases h
  rename_i p hp
  obtain ⟨C, tag⟩ := p
  have hC : Vals.WF (A := .prod A B) (C.key, C.val) := tagged_wf hp hR hS
  dsimp only at h
  okSplit
  cases h; exact Vals.gather_wf ‹_› hC

theorem inter_wf {R S t : Tab A B} (h : R.inter S = .ok t) (hR : R.WF) (hS : S.WF) : t.WF := select_wf h hR hS

theorem diff_wf {R S t : Tab A B} (h : R.diff S = .ok t) (hR : R.WF) (hS : S.WF) : t.WF := select_wf h hR hS

/-- **`diag q D` keeps `Tab.WF`** where `q` does (`inter_wf`). -/
theorem diag_wf {q : Tab A A → Except String (Tab A A)} (hq : ∀ D t, q D = .ok t → D.WF → t.WF) {D t : Tab A A}
    (h : diag q D = .ok t) (hD : D.WF) : t.WF := by
  simp only [Tab.diag, bind, Except.bind] at h
  split at h; · cases h
  exact inter_wf h (hq _ _ ‹_› hD) hD

end Tab

/-- **`Tab.ofBits` is `Tab.WF`** on `Vals.WF` sides: both gathered. -/
theorem Tab.ofBits_wf {n m : USize} {g w : USize} {o ra rc : Enc} {x : Vals A n} {y : Vals C m} {t : Tab A C}
    (h : Tab.ofBits g w o x ra y rc = .ok t) (hx : Vals.WF x) (hy : Vals.WF y) : t.WF := by
  simp only [Tab.ofBits, bind, Except.bind, pure, Except.pure] at h
  okSplit
  cases h; exact ⟨Vals.gather_wf ‹_› hx, Vals.gather_wf ‹_› hy⟩

/-- **`Vals.cross` keeps `Vals.WF`**: both sides gathered. -/
theorem Vals.cross_wf {n m : USize} {x : Vals A n} {y : Vals B m} {r : (T : USize) × Vals A T × Vals B T}
    (h : Vals.cross x y = .ok r) (hx : Vals.WF x) (hy : Vals.WF y) : Vals.WF r.2.1 ∧ Vals.WF r.2.2 := by
  simp only [Vals.cross, bind, Except.bind, pure, Except.pure] at h
  okSplit
  cases h; exact ⟨Vals.gather_wf ‹_› hx, Vals.gather_wf ‹_› hy⟩

namespace Tab

theorem cross_wf {n m : USize} {X : Vals A n} {Y : Vals B m} {t : Tab A B} (h : Tab.cross X Y = .ok t)
    (hX : Vals.WF X) (hY : Vals.WF Y) : t.WF := by
  simp only [Tab.cross, bind, Except.bind] at h
  split at h; · cases h
  rename_i r hr
  exact canon_wf h (Vals.cross_wf hr hX hY)

theorem top_wf {n m : USize} {X : Vals A n} {Y : Vals B m} {t : Tab A B} (h : Tab.top X Y = .ok t)
    (hX : Vals.WF X) (hY : Vals.WF Y) : t.WF := cross_wf h hX hY

/-- **`inl X` keeps `Tab.WF`**: `X` on both sides, a right summand of no row. -/
theorem inl_wf {n : USize} {X : Vals A n} {t : Tab A (.sum A B)} (h : Tab.inl (B := B) X = .ok t)
    (hX : Vals.WF X) : t.WF := by
  unfold Tab.inl at h
  split at h
  · simp only [bind, Except.bind] at h
    split at h; · cases h
    exact canon_wf h ⟨hX, by simp only [Vals.WF, Vals.view_ofOpt]⟩
  · simp only [bind, Except.bind] at h
    split at h; · cases h
    rename_i tg htg; split at h; · cases h
    rename_i z hz
    refine canon_wf h ⟨hX, ?_⟩; exact Vals.ofGen_wf (h := by assumption) hX (Vals.zeros_ok _ _ _ hz).1 (fun i _ => (Vals.zeros_ok _ _ _ hz).2 i)
      (fun i hi => by rw [tagCol_get htg i] at hi; cases hi)

theorem inr_wf {n : USize} {Y : Vals B n} {t : Tab B (.sum A B)} (h : Tab.inr (A := A) Y = .ok t)
    (hY : Vals.WF Y) : t.WF := by
  unfold Tab.inr at h
  split at h
  · exact canon_wf h ⟨hY, by simp only [Vals.WF, Vals.view_ofOpt]⟩
  · simp only [bind, Except.bind] at h
    split at h; · cases h
    rename_i tg htg; split at h; · cases h
    rename_i z hz
    refine canon_wf h ⟨hY, ?_⟩; exact Vals.ofGen_wf (h := by assumption) (Vals.zeros_ok _ _ _ hz).1 hY (fun i hi => by rw [tagCol_get htg i] at hi; cases hi)
      (fun i _ => (Vals.zeros_ok _ _ _ hz).2 i)

/-- **`compPairs` keeps `Tab.WF`**: `comp`, or `compFrom` within `crossMax`. -/
theorem compPairs_wf {R : Tab A B} {S : Tab B C} {t : Tab A C} (h : Tab.compPairs R S = .ok t) (hR : R.WF)
    (hS : S.WF) : t.WF := by
  simp only [Tab.compPairs, bind, Except.bind] at h
  okSplit
  all_goals first | exact comp_wf h hR hS | exact compFrom_wf h hR hS

/-- **`⟨R, S⟩` keeps `Tab.WF`**: `compPairs` of `⟨𝟙, R⟩°` and `S`, its key rebracketed. -/
theorem pair_wf {R : Tab A B} {S : Tab A C} {t : Tab A (.prod B C)} (h : R.pair S = .ok t) (hR : R.WF)
    (hS : S.WF) : t.WF := by
  simp only [Tab.pair, Functor.map, Except.map] at h
  split at h; · cases h
  rename_i T hT; cases h
  have := compPairs_wf hT ⟨⟨hR.1, hR.2⟩, hR.1⟩ hS
  exact ⟨this.1.1, this.1.2, this.2⟩

/-- **`Rᴵ` keeps `Tab.WF`** on a `Vals.WF` `X` (`outl_wf`, `outr_wf`, `comp_wf`, `inter_wf`). -/
theorem flat_wf {n : USize} {X : Vals (.prod I A) n} {R : Tab I (.prod A B)} {t : Tab (.prod I A) B}
    (h : Tab.flat X R = .ok t) (hX : Vals.WF X) (hR : R.WF) : t.WF := by
  simp only [Tab.flat, bind, Except.bind] at h
  split at h; · cases h
  rename_i a ha; split at h; · cases h
  rename_i L hL; split at h; · cases h
  rename_i b hb; split at h; · cases h
  rename_i c hc; split at h; · cases h
  rename_i d hd; split at h; · cases h
  rename_i M hM; split at h; · cases h
  rename_i P hP; split at h; · cases h
  rename_i e he
  have hRv : Vals.WF R.val := hR.2
  have wL := comp_wf hL (outl_wf ha hX) hR
  have wM := comp_wf hM (outr_wf hb hX) (conv_wf hd (outl_wf hc hRv))
  exact comp_wf h (inter_wf hP wL wM) (outr_wf he hRv)

end Tab

/-- **CROSS's index columns**: `T = n · m` rows, row `t` reading `t / m` and `t % m`. -/
theorem crossIx_ok {n m T : USize} {iR iS : Enc} (h : crossIx n m = .ok (T, iR, iS)) :
    T.toNat = n.toNat * m.toNat ∧ ∀ t < T.toNat,
      ((raw .i64 T iR)[t]?.getD 0).toNat = t / m.toNat ∧ ((raw .i64 T iS)[t]?.getD 0).toNat = t % m.toNat := by
  unfold crossIx at h
  by_cases hb : 2 ^ 63 ≤ n.toNat * m.toNat + m.toNat ∨ USize.size ≤ n.toNat * m.toNat
  · simp [hb, bind, Except.bind] at h
  simp only [hb, if_false, bind, Except.bind, pure, Except.pure] at h
  split at h; · cases h
  rename_i d hd
  split at h; · cases h
  rename_i e he
  simp only [Except.ok.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl, rfl⟩ := h
  have hT : (n.toNat * m.toNat).toUSize.toNat = n.toNat * m.toNat := USize.toNat_ofNat_of_lt' (by omega)
  refine ⟨hT, fun t ht => ?_⟩
  rw [hT] at ht
  have hm0 : 0 < m.toNat := Nat.pos_of_ne_zero fun h0 => by rw [h0, Nat.mul_zero] at ht; omega
  have hmU : m.toUInt64 = m.toNat.toUInt64 := UInt64.toNat_inj.mp (by simp)
  have hp : (raw .i64 (n.toNat * m.toNat).toUSize (.pos : Enc))[t]?.getD 0 = t.toUInt64 := raw_pos_word (by omega)
  have e1 := (colMap_post hd).2 t (by omega)
  have e2 := (colMap_post he).2 t (by omega)
  rw [hp, hmU, eval_rdiv_nat (by omega) (by omega) hm0, Except.ok.injEq] at e1
  rw [hp, hmU, eval_rmod_nat (by omega) (by omega) hm0, Except.ok.injEq] at e2
  rw [← e1, ← e2, toNat_toUInt64 (by have := Nat.div_le_self t m.toNat; omega),
    toNat_toUInt64 (by have := Nat.mod_lt t hm0; omega)]
  exact ⟨rfl, rfl⟩

/-- **CROSS holds every pair of rows**: a row of the answer is a row of `x` beside a row of `y`, and each such pair
is a row. -/
theorem Vals.cross_rows {A B : Obj} {n m : USize} {x : Vals A n} {y : Vals B m}
    {r : (T : USize) × Vals A T × Vals B T} (h : Vals.cross x y = .ok r) (a : A.El) (b : B.El) :
    (∃ t, Vals.row r.2.1 t = a ∧ Vals.row r.2.2 t = b) ↔ (∃ i, Vals.row x i = a) ∧ ∃ j, Vals.row y j = b := by
  unfold Vals.cross at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  split at h; · cases h
  split at h; · cases h
  rename_i c hc
  obtain ⟨T, iR, iS⟩ := c
  split at h; · cases h
  rename_i gx hx
  split at h; · cases h
  rename_i gy hy
  cases h
  obtain ⟨hT, hw⟩ := crossIx_ok hc
  constructor
  · rintro ⟨t, ha, hb⟩
    obtain ⟨i, -, hi⟩ := Vals.gather_row x hx t
    obtain ⟨j, -, hj⟩ := Vals.gather_row y hy t
    exact ⟨⟨i, hi.symm.trans ha⟩, ⟨j, hj.symm.trans hb⟩⟩
  · rintro ⟨⟨i, rfl⟩, ⟨j, rfl⟩⟩
    have hm0 : 0 < m.toNat := by have := j.2; omega
    have hle := Nat.mul_le_mul_left m.toNat (show i.1 + 1 ≤ n.toNat by have := i.2; omega)
    have ht : m.toNat * i.1 + j.1 < T.toNat := by
      rw [hT, Nat.mul_comm n.toNat m.toNat]; rw [Nat.mul_add, Nat.mul_one] at hle; have := j.2; omega
    obtain ⟨i', e1, hi⟩ := Vals.gather_row x hx ⟨_, ht⟩
    obtain ⟨j', e2, hj⟩ := Vals.gather_row y hy ⟨_, ht⟩
    rw [(hw _ ht).1, Nat.mul_add_div hm0, Nat.div_eq_of_lt j.2, Nat.add_zero] at e1
    rw [(hw _ ht).2, Nat.mul_add_mod, Nat.mod_eq_of_lt j.2] at e2
    exact ⟨⟨_, ht⟩, by rw [hi, Fin.ext e1], by rw [hj, Fin.ext e2]⟩

namespace Tab
variable {A B C D I : Obj}

/-- **`cross X Y` denotes `X × Y`**: every pair of a row of `X` and a row of `Y` (`Vals.cross_rows`). -/
theorem cross_holds {n m : USize} {X : Vals A n} {Y : Vals B m} {T : Tab A B} (h : cross X Y = .ok T) (hX : Vals.WF X)
    (hY : Vals.WF Y) (a : A.El) (b : B.El) : T.Holds a b ↔ (∃ i, X.row i = a) ∧ ∃ j, Y.row j = b := by
  unfold cross at h
  simp only [bind, Except.bind] at h
  split at h; · cases h
  rename_i r hr
  obtain ⟨T', x, y⟩ := r
  rw [canon_holds h (Vals.cross_wf hr hX hY)]
  exact Vals.cross_rows hr a b

/-- **`Tab.zero` denotes `𝟘`** (`Tm.den` at `zero`). -/
theorem zero_holds {T : Tab A B} (h : (Tab.zero : Except String (Tab A B)) = .ok T) (a : A.El) (b : B.El) :
    T.Holds a b ↔ False := by
  unfold Tab.zero at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  split at h; · cases h
  split at h; · cases h
  cases h
  exact ⟨fun ⟨i, _⟩ => absurd i.2 (by simp), False.elim⟩

/-- **`Tab.idU X` denotes `𝟙` on the values of `X`** (`Tm.den` at `id`, `uni`: `idU X ≫ 𝟙`). -/
theorem idU_holds {n : USize} {X : Vals A n} {T : Tab A A} (h : Tab.idU X = .ok T) (hX : Vals.WF X) (a b : A.El) :
    T.Holds a b ↔ a = b ∧ ∃ i, X.row i = a := by
  rw [dom_holds h hX]
  exact ⟨fun ⟨e, _, i, h1, _⟩ => ⟨e, i, h1⟩, fun ⟨e, i, h1⟩ => ⟨e, _, i, h1, rfl⟩⟩

/-- **`Tab.top K L` denotes `K ≫ ⊤ ≫ L`**: every value of `K` beside every value of `L`. -/
theorem top_holds {n m : USize} {K : Vals A n} {L : Vals B m} {T : Tab A B} (h : Tab.top K L = .ok T) (hK : Vals.WF K)
    (hL : Vals.WF L) (a : A.El) (b : B.El) : T.Holds a b ↔ (∃ i, K.row i = a) ∧ ∃ j, L.row j = b := cross_holds h hK hL a b

/-- **`Tab.top X V.val` denotes `⊤ ≫ V` on the values of `X`** (`Tm.den` at `top`: `idU X ≫ ⊤ ≫ ⟦V⟧`), `top_holds`
with `L` the values of `V`. -/
theorem top_val_holds {n : USize} {X : Vals A n} {V : Tab B B} {T : Tab A B} (h : Tab.top X V.val = .ok T) (hX : Vals.WF X) (hV : V.WF)
    (a : A.El) (b : B.El) : T.Holds a b ↔ (∃ i, X.row i = a) ∧ (Core.Rel.top ≫ V.Holds) a b := by
  rw [top_holds h hX hV.2]
  exact and_congr_right fun _ => ⟨fun ⟨j, hj⟩ => ⟨_, trivial, j, rfl, hj⟩, fun ⟨_, _, j, _, hj⟩ => ⟨j, hj⟩⟩

/-- **`Tab.outl X` denotes `π₁` on the pairs `X`** (`Tm.den` at `outl`: `idU X ≫ graph Prod.fst`). -/
theorem outl_holds {n : USize} {X : Vals (.prod A B) n} {T : Tab (.prod A B) A} (h : Tab.outl X = .ok T) (hX : Vals.WF X)
    (p : (Obj.prod A B).El) (a : A.El) : T.Holds p a ↔ (∃ i, X.row i = p) ∧ Core.Rel.graph Prod.fst p a := by
  rw [canon_holds h ⟨hX, hX.1⟩]
  exact ⟨fun ⟨i, h1, h2⟩ => ⟨⟨i, h1⟩, by subst h1 h2; rfl⟩, fun ⟨⟨i, h1⟩, h2⟩ => ⟨i, h1, by subst h1 h2; rfl⟩⟩

/-- **`Tab.outr X` denotes `π₂` on the pairs `X`** (`Tm.den` at `outr`: `idU X ≫ graph Prod.snd`). -/
theorem outr_holds {n : USize} {X : Vals (.prod A B) n} {T : Tab (.prod A B) B} (h : Tab.outr X = .ok T) (hX : Vals.WF X)
    (p : (Obj.prod A B).El) (b : B.El) : T.Holds p b ↔ (∃ i, X.row i = p) ∧ Core.Rel.graph Prod.snd p b := by
  rw [canon_holds h ⟨hX, hX.2⟩]
  exact ⟨fun ⟨i, h1, h2⟩ => ⟨⟨i, h1⟩, by subst h1 h2; rfl⟩, fun ⟨⟨i, h1⟩, h2⟩ => ⟨i, h1, by subst h1 h2; rfl⟩⟩

/-- **`compPairs` denotes `R ≫ S`**: `comp`, or `compFrom` of `compGroups` within `crossMax` (`compFrom_canon`). -/
theorem compPairs_holds {R : Tab A B} {S : Tab B C} {T : Tab A C} (h : compPairs R S = .ok T) (hR : R.WF)
    (hS : S.WF) (a : A.El) (c : C.El) : T.Holds a c ↔ ∃ b, R.Holds a b ∧ S.Holds b c := by
  unfold compPairs at h
  split at h
  · exact comp_holds h hR hS a c
  · simp only [bind] at h
    rw [Except.bind_eq_ok'] at h; obtain ⟨x, hx, h⟩ := h
    rw [Except.bind_eq_ok'] at h; obtain ⟨k, -, h⟩ := h
    split at h; · cases h
    obtain ⟨U, hU, hUw, hH⟩ := compFrom_canon hx h hR hS
    rw [canon_holds hU hUw]; exact hH a c

/-- **`R.pair S` denotes `⟨R, S⟩`** (`Tm.den` at `pair`: `rpair`). -/
theorem pair_holds {R : Tab A B} {S : Tab A C} {T : Tab A (.prod B C)} (h : R.pair S = .ok T) (hR : R.WF)
    (hS : S.WF) (a : A.El) (q : (Obj.prod B C).El) : T.Holds a q ↔ Core.Rel.rpair R.Holds S.Holds a q := by
  unfold Tab.pair at h
  cases hc : compPairs (⟨R.n, (R.key, R.val), R.key⟩ : Tab (.prod A B) A) S with
  | error s => simp [hc, Functor.map, Except.map] at h
  | ok U =>
    simp only [hc, Functor.map, Except.map, Except.ok.injEq] at h
    subst h
    obtain ⟨b, c⟩ := q
    have e := compPairs_holds hc ⟨⟨hR.1, hR.2⟩, hR.1⟩ hS (a, b) c
    simp only [Tab.Holds, Core.Rel.rpair, Vals.row, Prod.mk.injEq] at e ⊢
    rw [show (∃ i, U.key.1.row i = a ∧ U.key.2.row i = b ∧ U.val.row i = c) ↔
      ∃ i, (U.key.1.row i = a ∧ U.key.2.row i = b) ∧ U.val.row i = c from by simp only [and_assoc], e]
    exact ⟨fun ⟨_, ⟨i, ⟨h1, h2⟩, h3⟩, hS⟩ => ⟨⟨i, h1, h2⟩, by subst h3; rwa [h1] at hS⟩,
      fun ⟨⟨i, h1, h2⟩, hS⟩ => ⟨a, ⟨i, ⟨h1, h2⟩, h1⟩, hS⟩⟩

/-- **`Tab.flat X R` denotes `Rᴵ` on the pairs `X`** (`Tm.den` at `flat`: `idU X ≫ flatDen ⟦R⟧`,
`flatDen T x b = T x.1 (x.2, b)`). -/
theorem flat_holds {n : USize} {X : Vals (.prod I A) n} {R : Tab I (.prod A B)} {T : Tab (.prod I A) B}
    (h : Tab.flat X R = .ok T) (hX : Vals.WF X) (hR : R.WF) (p : (Obj.prod I A).El) (b : B.El) :
    T.Holds p b ↔ (∃ i, X.row i = p) ∧ R.Holds p.1 (p.2, b) := by
  unfold Tab.flat at h
  simp only [bind, Except.bind] at h
  split at h; · cases h
  rename_i O1 hO1
  split at h; · cases h
  rename_i L hL
  split at h; · cases h
  rename_i O2 hO2
  split at h; · cases h
  rename_i O3 hO3
  split at h; · cases h
  rename_i O3c hO3c
  split at h; · cases h
  rename_i M hM
  split at h; · cases h
  rename_i J hJ
  split at h; · cases h
  rename_i O4 hO4
  have hRv : Vals.WF R.val := hR.2
  have w1 := outl_wf hO1 hX
  have wL := comp_wf hL w1 hR
  have w2 := outr_wf hO2 hX
  have w3 := conv_wf hO3c (outl_wf hO3 hRv)
  have wM := comp_wf hM w2 w3
  rw [comp_holds h (inter_wf hJ wL wM) (outr_wf hO4 hRv)]
  simp only [inter_holds hJ wL wM, comp_holds hL w1 hR, comp_holds hM w2 w3, conv_holds hO3c (outl_wf hO3 hRv), outl_holds hO1 hX,
    outr_holds hO2 hX, outl_holds hO3 hRv, outr_holds hO4 hRv, Core.Rel.graph]
  obtain ⟨i, a⟩ := p
  constructor
  · rintro ⟨⟨a', b'⟩, ⟨⟨i', ⟨hx, rfl⟩, hR⟩, ⟨a'', ⟨-, rfl⟩, ⟨-, rfl⟩⟩⟩, ⟨-, rfl⟩⟩
    exact ⟨hx, hR⟩
  · rintro ⟨hx, hR⟩
    have hy : ∃ j, R.val.row j = (a, b) := let ⟨j, _, hj⟩ := hR; ⟨j, hj⟩
    exact ⟨(a, b), ⟨⟨i, ⟨hx, rfl⟩, hR⟩, ⟨a, ⟨hx, rfl⟩, ⟨hy, rfl⟩⟩⟩, ⟨hy, rfl⟩⟩


/-- **Every row of `Vals.optInr h Y` is `inr` of `Y`'s row**, the band column's element read as `a + b`. -/
theorem Vals.optInr_get {a b : Obj} {t : QAtomicType} {n : USize} (h : Obj.band a b = some t) (Y : Vals b n)
    (i : Fin n.toNat) : Obj.optEl h ((Vals.optInr h Y).get i) = .inr (Vals.row Y i) := by
  obtain ⟨rfl, rfl⟩ := Obj.band_some h
  unfold Vals.optInr Obj.optEl
  generalize Obj.band_some h = p; obtain ⟨p1, p2⟩ := p
  simp only [Opt.get_ofArr]; rfl

/-- The table `⟨n, X, V⟩` of rows `inl` of `X`'s rows denotes `inl` on `X`. -/
private theorem holds_inl_of_row {n : USize} {X : Vals A n} {V : Vals (.sum A B) n}
    (hrow : ∀ k, Vals.row V k = .inl (X.row k)) (a : A.El) (s : (Obj.sum A B).El) :
    Tab.Holds (⟨n, X, V⟩ : Tab A (.sum A B)) a s ↔ (∃ i, X.row i = a) ∧ Core.Rel.inl a s := by
  simp only [Tab.Holds, hrow, Core.Rel.inl, Core.Rel.graph]
  exact ⟨fun ⟨i, h1, h2⟩ => ⟨⟨i, h1⟩, by rw [← h2, h1]⟩, fun ⟨⟨i, h1⟩, h2⟩ => ⟨i, h1, by rw [h2, h1]⟩⟩

private theorem holds_inr_of_row {n : USize} {Y : Vals B n} {V : Vals (.sum A B) n}
    (hrow : ∀ k, Vals.row V k = .inr (Y.row k)) (b : B.El) (s : (Obj.sum A B).El) :
    Tab.Holds (⟨n, Y, V⟩ : Tab B (.sum A B)) b s ↔ (∃ i, Y.row i = b) ∧ Core.Rel.inr b s := by
  simp only [Tab.Holds, hrow, Core.Rel.inr, Core.Rel.graph]
  exact ⟨fun ⟨i, h1, h2⟩ => ⟨⟨i, h1⟩, by rw [← h2, h1]⟩, fun ⟨⟨i, h1⟩, h2⟩ => ⟨i, h1, by rw [h2, h1]⟩⟩

/-- **A dense sum side's tag column is a valid column**: the gather of the sum side reads it (`kgather`). -/
theorem Vals.gather_tag_valid {a b : Obj} {n m : USize} {ix : Enc} {X : Vals (.sum a b) n} {G : Vals (.sum a b) m}
    {hb : Obj.band a b = none} {tag : Arr .u1 n} {x : Vals a n} {y : Vals b n} (hv : X.view = .gen hb tag x y)
    (hG : Vals.gather m ix X = .ok G) : Kernel.Enc.Valid n tag.enc := by
  simp only [Vals.gather, hv, bind, Except.bind, pure, Except.pure] at hG
  split at hG; · cases hG
  rename_i t' ht'
  unfold Arr.gather at ht'
  split at ht'
  · rename_i o ho; exact kgather_valid ho
  · cases ht'

/-- **The rows `whereCol` selects, gathered from `X` and `g`**: where `b` holds `1` exactly at the rows with `p`, the
canonical table of `X` beside `g` has the pairs `(X.row i, g.row i)` of the rows `i` with `p i`. -/
theorem selConv_holds {S C : Obj} {n m : USize} {sel b : Enc} {X : Vals S n} {g : Vals C n} {G : Vals S m}
    {g' : Vals C m} {T : Tab S C} {p : Fin n.toNat → Bool}
    (hb : ∀ i : Fin n.toNat, (Enc.raw .i64 n b)[i.1]?.getD 0 = if p i then 1 else 0)
    (hw : whereCol n b = .ok (m, sel)) (hG : Vals.gather m sel X = .ok G) (hg' : Vals.gather m sel g = .ok g')
    (hc : Tab.canon ⟨m, G, g'⟩ = .ok T) (hX : Vals.WF X) (hg : Vals.WF g) (s : S.El) (c : C.El) :
    T.Holds s c ↔ ∃ i, p i = true ∧ X.row i = s ∧ g.row i = c := by
  rw [Tab.canon_holds hc ⟨Vals.gather_wf hG hX, Vals.gather_wf hg' hg⟩]
  have hb2 : ∀ i < n.toNat, (Enc.raw .i64 n b)[i]?.getD 0 < 2 := fun i hi => by
    rw [hb ⟨i, hi⟩]; split <;> decide
  have hsel := whereCol_spec hw hb2
  have hsz := whereCol_size hw
  have hp : ∀ i : Fin n.toNat, i.1 ∈ (Enc.raw .i64 m sel).toList.map UInt64.toNat ↔ p i = true := fun i => by
    rw [hsel, List.mem_filter, List.mem_range, hb i]
    cases p i <;> simp [i.2]
  constructor
  · rintro ⟨j, rfl, rfl⟩
    obtain ⟨i, hi, hr⟩ := Vals.gather_row X hG j
    obtain ⟨i', hi', hr'⟩ := Vals.gather_row g hg' j
    obtain rfl : i' = i := Fin.ext (hi'.symm.trans hi)
    have hj : j.1 < (Enc.raw .i64 m sel).size := by rw [hsz]; exact j.2
    refine ⟨i', (hp i').1 (List.mem_map.2 ⟨(Enc.raw .i64 m sel)[j.1], ?_, ?_⟩), hr.symm, hr'.symm⟩
    · simp
    · rw [Array.getElem?_eq_getElem hj, Option.getD_some] at hi; exact hi
  · rintro ⟨i, hpi, rfl, rfl⟩
    obtain ⟨w, hw', hwi⟩ := List.mem_map.1 ((hp i).2 hpi)
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hw'
    have hj' : j < (Enc.raw .i64 m sel).size := by simpa using hj
    have hjM : j < m.toNat := by rw [← hsz]; exact hj'
    simp only [Array.getElem_toList] at hwi
    obtain ⟨i2, hi2, hr⟩ := Vals.gather_row X hG ⟨j, hjM⟩
    obtain ⟨i3, hi3, hr3⟩ := Vals.gather_row g hg' ⟨j, hjM⟩
    have e2 : i2 = i := Fin.ext (by rw [← hi2]; simp only [Array.getElem?_eq_getElem hj', Option.getD_some, hwi])
    have e3 : i3 = i := Fin.ext (by rw [← hi3]; simp only [Array.getElem?_eq_getElem hj', Option.getD_some, hwi])
    subst e2; subst e3
    exact ⟨⟨j, hjM⟩, hr, hr3⟩

/-- **`Tab.inl X` denotes `inl` on the values `X`** (`idU X ≫ Core.Rel.inl`, the injection `junc` is defined by). -/
theorem inl_holds {n : USize} {X : Vals A n} {T : Tab A (.sum A B)} (h : Tab.inl X = .ok T) (hX : Vals.WF X)
    (a : A.El) (s : (Obj.sum A B).El) : T.Holds a s ↔ (∃ i, X.row i = a) ∧ Core.Rel.inl a s := by
  unfold Tab.inl at h
  split at h
  · rename_i t ht
    simp only [bind, Except.bind] at h
    split at h; · cases h
    rename_i z hz
    rw [canon_holds h ⟨hX, by simp only [Vals.WF, Vals.view_ofOpt]⟩]
    refine holds_inl_of_row (fun k => ?_) a s
    obtain ⟨rfl, rfl⟩ := Obj.band_some ht
    simp only [Vals.row, Vals.view_ofOpt, Opt.nuls_get hz k]
    unfold Obj.optEl; generalize Obj.band_some ht = p; obtain ⟨p1, p2⟩ := p; rfl
  · simp only [bind, Except.bind] at h
    split at h; · cases h
    rename_i tg htg
    split at h; · cases h
    rename_i y hy
    rw [canon_holds h ⟨hX, Vals.ofGen_wf (h := by assumption) hX (Vals.zeros_ok _ _ _ hy).1 (fun i _ => (Vals.zeros_ok _ _ _ hy).2 i)
      (fun i hi => by rw [tagCol_get htg i] at hi; cases hi)⟩]
    refine holds_inl_of_row (fun k => ?_) a s
    simp only [Vals.row, Vals.view_ofGen, tagCol_get htg k, Bool.false_eq_true, if_false]
    try rfl

/-- **`Tab.inr Y` denotes `inr` on the values `Y`** (`idU Y ≫ Core.Rel.inr`). -/
theorem inr_holds {n : USize} {Y : Vals B n} {T : Tab B (.sum A B)} (h : Tab.inr Y = .ok T) (hY : Vals.WF Y)
    (b : B.El) (s : (Obj.sum A B).El) : T.Holds b s ↔ (∃ i, Y.row i = b) ∧ Core.Rel.inr b s := by
  unfold Tab.inr at h
  split at h
  · rename_i t ht
    rw [canon_holds h ⟨hY, by simp only [Vals.WF, Vals.view_ofOpt]⟩]
    refine holds_inr_of_row (fun k => ?_) b s
    simp only [Vals.row, Vals.view_ofOpt]
    exact Vals.optInr_get ht Y k
  · simp only [bind, Except.bind] at h
    split at h; · cases h
    rename_i tg htg
    split at h; · cases h
    rename_i x hx
    rw [canon_holds h ⟨hY, Vals.ofGen_wf (h := by assumption) (Vals.zeros_ok _ _ _ hx).1 hY (fun i hi => by rw [tagCol_get htg i] at hi; cases hi)
      (fun i _ => (Vals.zeros_ok _ _ _ hx).2 i)⟩]
    refine holds_inr_of_row (fun k => ?_) b s
    simp only [Vals.row, Vals.view_ofGen, tagCol_get htg k, if_true]
    try rfl

/-- **`Tab.inlConv X` denotes `inl°` on the values `X`** (`idU X ≫ Core.Rel.inl°`): a sum value of `X` beside its
left summand, where it has one. -/
theorem inlConv_holds {n : USize} {X : Vals (.sum A B) n} {T : Tab (.sum A B) A} (h : Tab.inlConv X = .ok T)
    (hX : Vals.WF X) (s : (Obj.sum A B).El) (a : A.El) : T.Holds s a ↔ (∃ i, X.row i = s) ∧ Core.Rel.inl a s := by
  rcases hv : X.view with ⟨hb, x⟩ | ⟨hb, tag, x, y⟩ <;> unfold Tab.inlConv at h <;> simp only [hv] at h
  · -- a band column: `inl`'s one null row, whose left payload is the unit `1`, which every `a` is
    obtain ⟨rfl, rfl⟩ := Obj.band_some hb
    simp only [bind, Except.bind] at h
    split at h; · cases h
    rename_i D hD
    split at h; · cases h
    rename_i I hI
    split at h; · cases h
    rename_i C hC
    have wI := inl_wf hI (trivial : Vals.WF (Vals.unit rfl))
    rw [comp_holds h (idU_wf hD hX) (conv_wf hC wI)]
    constructor
    · rintro ⟨s', hd, hc⟩
      obtain ⟨rfl, hs⟩ := (idU_holds hD hX _ _).1 hd
      exact ⟨hs, ((inl_holds hI trivial _ _).1 ((conv_holds hC wI _ _).1 hc)).2⟩
    · rintro ⟨⟨i, hi⟩, hs⟩
      exact ⟨s, (idU_holds hD hX _ _).2 ⟨rfl, i, hi⟩, (conv_holds hC wI _ _).2
        ((inl_holds hI trivial _ _).2 ⟨⟨⟨0, by simp⟩, rfl⟩, hs⟩)⟩
  have hXw := hX
  simp only [Vals.WF, hv] at hX
  simp only [bind, Except.bind] at h
  split at h; · cases h
  rename_i b hbm
  split at h; · cases h
  rename_i ws hws; obtain ⟨M, sel⟩ := ws
  split at h; · cases h
  rename_i G hG
  split at h; · cases h
  rename_i g hg
  have hvt := Vals.gather_tag_valid hv hG
  have hmask : ∀ i : Fin n.toNat, (Enc.raw .i64 n b)[i.1]?.getD 0 = if (!tag.get i) = true then 1 else 0 := fun i => by
    obtain ⟨-, -, -, hr⟩ := colMap_raw hbm
    obtain ⟨a, ha, he⟩ := Arr.get_u1 tag hvt i
    have := hr i.1 i.2
    rw [ha] at this
    simp only [Option.getD_some, Op.eval, Except.ok.injEq] at this
    rw [← this, he]; cases tag.get i <;> decide
  have hrow : ∀ i, X.row i = if tag.get i then .inr (y.row i) else .inl (x.row i) := fun i => by simp only [Vals.row, hv]
  rw [selConv_holds (p := fun i => !tag.get i) hmask hws hG hg h hXw hX.1]
  simp only [Core.Rel.inl, Core.Rel.graph]
  constructor
  · rintro ⟨i, hp, rfl, rfl⟩
    have ht : tag.get i = false := by simpa using hp
    exact ⟨⟨i, rfl⟩, by rw [hrow, ht]; rfl⟩
  · rintro ⟨⟨i, hi⟩, hs⟩
    subst hs
    rcases ht : tag.get i with _ | _
    · refine ⟨i, by simp [ht], hi, ?_⟩
      simpa [hrow, ht] using hi
    · simp [hrow, ht] at hi

/-- **`Tab.inrConv X` denotes `inr°` on the values `X`** (`idU X ≫ Core.Rel.inr°`): the mirror of `inlConv_holds`. -/
theorem inrConv_holds {n : USize} {X : Vals (.sum A B) n} {T : Tab (.sum A B) B} (h : Tab.inrConv X = .ok T)
    (hX : Vals.WF X) (s : (Obj.sum A B).El) (b : B.El) : T.Holds s b ↔ (∃ i, X.row i = s) ∧ Core.Rel.inr b s := by
  rcases hv : X.view with ⟨hb, x⟩ | ⟨hb, tag, x, y⟩ <;> unfold Tab.inrConv at h <;> simp only [hv] at h
  · -- a band column: the rows `kscan .null`, `not` and `whereCol` keep are the non-null ones (`Opt.isNul_eq_false`)
    rename_i t
    have hXr : ∀ i, X.row i = Obj.optEl hb (x.get i) := fun i => by simp only [Vals.row, hv]
    obtain ⟨rfl, rfl⟩ := Obj.band_some hb
    -- `inrConvBand`'s own `obtain ⟨rfl, rfl⟩` is a cast by `rfl` proofs at `.one`, `.atom t`: its body, by `rfl`
    replace h : (do
        let Fb ← kscan .null false t .u1 n none [(n, x.enc)] [] [(.not, 0)]
        let Ms ← whereCol n Fb.1
        let G ← Vals.gather Ms.1 Ms.2 (Vals.ofOpt hb x)
        let yo ← Opt.gather Ms.1 Ms.2 x
        let Y ← Arr.of t Ms.1 yo.enc "inr°"
        pure (⟨Ms.1, G, Y⟩ : Tab (.sum .one (.atom t)) (.atom t))) = .ok T := h
    simp only [bind, Except.bind, pure, Except.pure] at h
    split at h; · cases h
    rename_i Fb hFb
    split at h; · cases h
    rename_i Ms hMs; obtain ⟨M, sel⟩ := Ms
    split at h; · cases h
    rename_i G hG
    split at h; · cases h
    rename_i yo hyo
    split at h; · cases h
    rename_i Y hY
    cases h
    obtain ⟨-, hFw⟩ := kscan_null_chain (by simp [kscanStream]) hFb
    -- the kept word is `1` exactly at a flag `0`, the flags being bits
    have hword : ∀ i < n.toNat, (Enc.raw .i64 n Fb.1)[i]?.getD 0 = if (foRNuls n x.enc)[i]?.getD 0 = 0 then 1 else 0 := by
      intro i hi
      obtain ⟨w, hw, hr⟩ := hFw i hi
      have e := foRNuls_bit n x.enc hi
      rcases hq : (foRNuls n x.enc)[i]? with _ | v
      · rw [hq] at e; cases e
      · rw [hq] at e
        simp only [Option.some.injEq, Option.getD_some] at e
        simp only [hq, chain, Op.eval, List.foldlM_cons, List.foldlM_nil, bind, Except.bind, pure, Except.pure,
          Option.getD_some, Except.ok.injEq, ↓reduceIte] at hw hr
        subst hw
        rw [hr]; simp only [Option.getD_some]
        by_cases hv0 : v = 0
        · subst hv0; decide
        · have h1 : v = 1 := by simpa [hv0] using e
          subst h1; decide
    have hsel := whereCol_spec hMs (fun i hi => by rw [hword i hi]; split <;> decide)
    have hsz := whereCol_size hMs
    have hnul : ∀ i : Fin n.toNat, x.isNul i = false ↔ (foRNuls n x.enc)[i.1]?.getD 0 = 0 := fun i => by
      rw [Opt.isNul_eq_false, Array.getElem?_eq_getElem (by rw [foRNuls_size]; exact i.2)]; simp
    have hYe : Opt.ofArr Y = yo := by
      apply Subtype.ext
      unfold Arr.of at hY
      split at hY; · split at hY; · cases hY; rfl
                     · cases hY
      cases hY
    have optInr : ∀ v, Obj.optEl hb (some v) = Sum.inr v := fun v => by
      unfold Obj.optEl; generalize Obj.band_some hb = p; obtain ⟨p1, p2⟩ := p; rfl
    have optInl : Obj.optEl hb none = Sum.inl () := by
      unfold Obj.optEl; generalize Obj.band_some hb = p; obtain ⟨p1, p2⟩ := p; rfl
    have hGr : ∀ j : Fin M.toNat, ∃ i : Fin n.toNat, ((Enc.raw .i64 M sel)[j.1]?.getD 0).toNat = i.1 ∧
        Vals.row G j = Obj.optEl hb (x.get i) ∧ Vals.row (A := .atom t) Y j = Y.get j ∧ x.get i = some (Y.get j) := fun j => by
      obtain ⟨i, hi, hr⟩ := Vals.gather_row _ hG j
      obtain ⟨i', hi', hy⟩ := Opt.gather_row x hyo j
      obtain rfl : i' = i := Fin.ext (by rw [← hi', hi])
      refine ⟨i', hi, by rw [hr]; simp only [Vals.row, Vals.view_ofOpt], rfl, ?_⟩
      rw [← hy, ← hYe, Opt.get_ofArr]
    simp only [Tab.Holds, Core.Rel.inr, Core.Rel.graph]
    constructor
    · rintro ⟨j, rfl, rfl⟩
      obtain ⟨i, -, hg, -, hx⟩ := hGr j
      rw [hg, hx, optInr]
      exact ⟨⟨i, by rw [hXr, hx, optInr]⟩, rfl⟩
    · rintro ⟨⟨i, rfl⟩, hs⟩
      rw [hXr] at hs
      cases hxi : x.get i with
      | none => rw [hxi, optInl] at hs; cases hs
      | some v =>
        rw [hxi, optInr] at hs; cases hs
        have hnn : x.isNul i = false := by
          cases hc : x.isNul i
          · rfl
          · simp [Opt.get, hc] at hxi
        have hi0 : (Enc.raw .i64 n Fb.1)[i.1]?.getD 0 ≠ 0 := by
          rw [hword i.1 i.2, if_pos ((hnul i).1 hnn)]; decide
        have hm : i.1 ∈ (Enc.raw .i64 M sel).toList.map UInt64.toNat := by
          rw [hsel, List.mem_filter, List.mem_range, decide_eq_true_eq]; exact ⟨i.2, hi0⟩
        obtain ⟨w, hw, hwi⟩ := List.mem_map.1 hm
        obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hw
        have hj' : j < (Enc.raw .i64 M sel).size := by simpa using hj
        have hjM : j < M.toNat := by rw [← hsz]; exact hj'
        simp only [Array.getElem_toList] at hwi
        obtain ⟨i2, hi2, hg, hy, hx2⟩ := hGr ⟨j, hjM⟩
        have e2 : i2 = i := Fin.ext (by
          rw [← hi2]; simp only [Array.getElem?_eq_getElem hj', Option.getD_some, hwi])
        subst e2
        refine ⟨⟨j, hjM⟩, by rw [hXr]; exact hg, ?_⟩
        rw [hy]; rw [hxi] at hx2; exact (Option.some.inj hx2).symm
  have hXw := hX
  simp only [Vals.WF, hv] at hX
  simp only [bind, Except.bind] at h
  split at h; · cases h
  rename_i ws hws; obtain ⟨M, sel⟩ := ws
  split at h; · cases h
  rename_i G hG
  split at h; · cases h
  rename_i g hg
  have hvt := Vals.gather_tag_valid hv hG
  have hmask : ∀ i : Fin n.toNat, (Enc.raw .i64 n tag.enc)[i.1]?.getD 0 = if tag.get i = true then 1 else 0 := fun i => by
    obtain ⟨a, ha, he⟩ := Arr.get_u1 tag hvt i
    rw [ha, Option.getD_some, he]
  have hrow : ∀ i, X.row i = if tag.get i then .inr (y.row i) else .inl (x.row i) := fun i => by simp only [Vals.row, hv]
  rw [selConv_holds (p := fun i => tag.get i) hmask hws hG hg h hXw hX.2.1]
  simp only [Core.Rel.inr, Core.Rel.graph]
  constructor
  · rintro ⟨i, hp, rfl, rfl⟩
    have ht : tag.get i = true := hp
    exact ⟨⟨i, rfl⟩, by rw [hrow, ht]; rfl⟩
  · rintro ⟨⟨i, hi⟩, hs⟩
    subst hs
    rcases ht : tag.get i with _ | _
    · simp [hrow, ht] at hi
    · refine ⟨i, ht, hi, ?_⟩
      simpa [hrow, ht] using hi

end Tab

/-! ## Checks on `foR` tables -/



end Rel
