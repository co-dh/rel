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

/-- **A side of no rows is `Vals.WF`**: an `arr` side of it has no cell. -/
theorem Vals.none_wf : {A : Obj} → {x : Vals A 0} → Vals.none A = .ok x → Vals.WF x
  | .atom _, _, _ => trivial
  | .one, _, _ => trivial
  | .prod _ _, _, h => by
    simp only [Vals.none, bind, Except.bind, pure, Except.pure] at h
    split at h; · cases h
    rename_i p hp; split at h; · cases h
    rename_i q hq; cases h
    exact ⟨Vals.none_wf hp, Vals.none_wf hq⟩
  | .arr _, _, h => by
    simp only [Vals.none, bind, Except.bind, pure, Except.pure] at h
    split at h; · cases h
    split at h; · cases h
    split at h; · cases h
    rename_i f hf; cases h
    exact ⟨fun i => absurd i.2 (by simp), Vals.none_wf hf⟩
  | .sum _ _, _, h => by
    simp only [Vals.none, bind, Except.bind, pure, Except.pure] at h
    split at h; · cases h
    split at h; · cases h
    split at h; · cases h
    rename_i p hp; split at h; · cases h
    rename_i q hq; cases h
    exact ⟨Vals.none_wf hp, Vals.none_wf hq⟩

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
  obtain ⟨hn, ho⟩ := catPlan_ok (show catPlan R.n S.n = .ok (q.1, q.2) from hq)
  split at h; · cases h
  rename_i x hx; split at h; · cases h
  rename_i y hy; okSplit
  cases h; exact ⟨Vals.concat_wf hn ho hx hR.1 hS.1, Vals.concat_wf hn ho hy hR.2 hS.2⟩

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
  simp only [Tab.inl, bind, Except.bind] at h
  okSplit
  exact canon_wf h ⟨hX, hX, Vals.none_wf ‹_›⟩

theorem inr_wf {n : USize} {Y : Vals B n} {t : Tab B (.sum A B)} (h : Tab.inr (A := A) Y = .ok t)
    (hY : Vals.WF Y) : t.WF := by
  simp only [Tab.inr, bind, Except.bind] at h
  okSplit
  exact canon_wf h ⟨hY, Vals.none_wf ‹_›, hY⟩

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

end Tab

/-- **`injCols`'s columns**: every tag is `s`, and row `k`'s position reads back as `k`. -/
theorem injCols_ok {n : USize} {s : Bool} {tag : Arr .u1 n} {idx : Arr .i64 n} (h : injCols n s = .ok (tag, idx))
    (k : Fin n.toNat) :
    tag.get k = s ∧ clampFin (idx.get k) n.toNat (Nat.lt_of_le_of_lt (Nat.zero_le _) k.2) = k := by
  unfold injCols at h
  by_cases hb : 2 ^ 63 < n.toNat
  · simp [hb, bind, Except.bind] at h
  simp only [hb, if_false, bind, Except.bind, pure, Except.pure] at h
  split at h; · cases h
  rename_i t ht
  split at h; · cases h
  rename_i i hi
  simp only [Except.ok.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  have hk : k.1 < n.toNat := k.2
  refine ⟨?_, ?_⟩
  · obtain ⟨a, ha, he⟩ := Arr.get_u1 t (colMap_closed (colArr_ok ht)).1 k
    obtain ⟨v, ev, hv⟩ := colMap_first_chain (colArr_ok ht) k.1 hk
    rw [ha] at hv
    simp [chain, Op.eval, bind, Except.bind, pure, Except.pure] at ev
    simp only [if_true, Option.some.injEq] at hv
    subst ev; subst hv
    cases s <;> cases hg : t.get k <;> rw [hg] at he <;> revert he <;> decide
  · rw [Arr.get_i64]
    obtain ⟨v, ev, hv⟩ := colMap_first_chain (colArr_ok hi) k.1 hk
    rw [raw_pos_word hk] at ev
    cases ev
    have hw : (raw .i64 n i.enc)[k.1]?.getD 0 = k.1.toUInt64 := by simp [hv]
    rw [hw, clampFin_word _ (by rw [toNat_toUInt64 (by omega)]; exact hk) (by omega)]
    exact Fin.ext (toNat_toUInt64 (by omega))

namespace Tab

/-- **`Tab.inl X` denotes `inl` on the values `X`** (`idU X ≫ Core.Rel.inl`, the injection `junc` is defined by). -/
theorem inl_holds {n : USize} {X : Vals A n} {T : Tab A (.sum A B)} (h : Tab.inl X = .ok T) (hX : Vals.WF X)
    (a : A.El) (s : (Obj.sum A B).El) : T.Holds a s ↔ (∃ i, X.row i = a) ∧ Core.Rel.inl a s := by
  unfold Tab.inl at h
  simp only [bind, Except.bind] at h
  split at h; · cases h
  rename_i ti hti
  obtain ⟨tag, idx⟩ := ti
  split at h; · cases h
  rename_i y hy
  rw [canon_holds h ⟨hX, hX, Vals.none_wf hy⟩]
  have hrow : ∀ k : Fin n.toNat, Vals.row (A := .sum A B) ⟨n, 0, tag, idx, X, y⟩ k = .inl (X.row k) := fun k => by
    obtain ⟨ht, hc⟩ := injCols_ok hti k
    simp only [Vals.row, ht, dif_pos (Nat.lt_of_le_of_lt (Nat.zero_le _) k.2), hc]
    rfl
  simp only [Tab.Holds, hrow, Core.Rel.inl, Core.Rel.graph]
  exact ⟨fun ⟨i, h1, h2⟩ => ⟨⟨i, h1⟩, by rw [← h2, h1]⟩, fun ⟨⟨i, h1⟩, h2⟩ => ⟨i, h1, by rw [h2, h1]⟩⟩

/-- **`Tab.inr Y` denotes `inr` on the values `Y`** (`idU Y ≫ Core.Rel.inr`). -/
theorem inr_holds {n : USize} {Y : Vals B n} {T : Tab B (.sum A B)} (h : Tab.inr Y = .ok T) (hY : Vals.WF Y)
    (b : B.El) (s : (Obj.sum A B).El) : T.Holds b s ↔ (∃ i, Y.row i = b) ∧ Core.Rel.inr b s := by
  unfold Tab.inr at h
  simp only [bind, Except.bind] at h
  split at h; · cases h
  rename_i ti hti
  obtain ⟨tag, idx⟩ := ti
  split at h; · cases h
  rename_i x hx
  rw [canon_holds h ⟨hY, Vals.none_wf hx, hY⟩]
  have hrow : ∀ k : Fin n.toNat, Vals.row (A := .sum A B) ⟨0, n, tag, idx, x, Y⟩ k = .inr (Y.row k) := fun k => by
    obtain ⟨ht, hc⟩ := injCols_ok hti k
    simp only [Vals.row, ht, dif_pos (Nat.lt_of_le_of_lt (Nat.zero_le _) k.2), hc]
    rfl
  simp only [Tab.Holds, hrow, Core.Rel.inr, Core.Rel.graph]
  exact ⟨fun ⟨i, h1, h2⟩ => ⟨⟨i, h1⟩, by rw [← h2, h1]⟩, fun ⟨⟨i, h1⟩, h2⟩ => ⟨i, h1, by rw [h2, h1]⟩⟩

/-- **`Tab.inlConv X` denotes `inl°` on the values `X`** (`idU X ≫ Core.Rel.inl°`): a sum value of `X` beside its
left summand, where it has one. -/
theorem inlConv_holds {n : USize} {X : Vals (.sum A B) n} {T : Tab (.sum A B) A} (h : Tab.inlConv X = .ok T)
    (hX : Vals.WF X) (s : (Obj.sum A B).El) (a : A.El) : T.Holds s a ↔ (∃ i, X.row i = s) ∧ Core.Rel.inl a s := by
  obtain ⟨l, r, tag, idx, x, y⟩ := X
  unfold Tab.inlConv at h
  simp only [bind, Except.bind] at h
  split at h; · cases h
  rename_i D hD
  split at h
  · split at h; · cases h
    rename_i I hI
    split at h; · cases h
    rename_i C hC
    split at h; · cases h
    rename_i E hE
    split at h; · cases h
    rename_i F hF
    split at h; · cases h
    rename_i M hM
    have wD := idU_wf hD hX
    have wF := dom_wf hF (comp_wf hE wD (conv_wf hC (inr_wf hI hX.2)))
    split at h
    · rename_i hM0
      rw [zero_holds h, false_iff]
      rintro ⟨⟨i, hi⟩, hs⟩
      simp only [Core.Rel.inl, Core.Rel.graph] at hs
      have hd : D.Holds s s := (idU_holds hD hX _ _).2 ⟨rfl, i, hi⟩
      have hn : ¬ M.Holds s s := fun ⟨j, _⟩ => by have := j.2; simp [hM0] at this
      have hf : F.Holds s s := Classical.byContradiction fun hf => hn ((diff_holds hM wD wF _ _).2 ⟨hd, hf⟩)
      obtain ⟨-, b, hb⟩ := (dom_holds hF (comp_wf hE wD (conv_wf hC (inr_wf hI hX.2))).1 _ _).1 hf
      obtain ⟨s', hs', hc⟩ := (comp_holds hE wD (conv_wf hC (inr_wf hI hX.2)) _ _).1 hb
      obtain ⟨rfl, -⟩ := (idU_holds hD hX _ _).1 hs'
      have he := ((inr_holds hI hX.2 _ _).1 ((conv_holds hC (inr_wf hI hX.2) _ _).1 hc)).2
      simp only [Core.Rel.inr, Core.Rel.graph] at he
      exact absurd (hs.symm.trans he) (by simp)
    · cases h
  · rename_i hl
    split at h; · cases h
    rename_i I hI
    split at h; · cases h
    rename_i C hC
    rw [comp_holds h (idU_wf hD hX) (conv_wf hC (inl_wf hI hX.1))]
    constructor
    · rintro ⟨s', hd, hc⟩
      obtain ⟨rfl, hs⟩ := (idU_holds hD hX _ _).1 hd
      exact ⟨hs, ((inl_holds hI hX.1 _ _).1 ((conv_holds hC (inl_wf hI hX.1) _ _).1 hc)).2⟩
    · rintro ⟨⟨i, hi⟩, hs⟩
      refine ⟨s, (idU_holds hD hX _ _).2 ⟨rfl, i, hi⟩, (conv_holds hC (inl_wf hI hX.1) _ _).2 ((inl_holds hI hX.1 _ _).2 ⟨?_, hs⟩)⟩
      simp only [Core.Rel.inl, Core.Rel.graph] at hs
      subst hs
      simp only [Vals.row] at hi
      split at hi
      · cases hi
      · rw [dif_pos (by omega)] at hi; exact ⟨_, Sum.inl.inj hi⟩

/-- **`Tab.inrConv X` denotes `inr°` on the values `X`** (`idU X ≫ Core.Rel.inr°`): the mirror of `inlConv_holds`. -/
theorem inrConv_holds {n : USize} {X : Vals (.sum A B) n} {T : Tab (.sum A B) B} (h : Tab.inrConv X = .ok T)
    (hX : Vals.WF X) (s : (Obj.sum A B).El) (b : B.El) : T.Holds s b ↔ (∃ i, X.row i = s) ∧ Core.Rel.inr b s := by
  obtain ⟨l, r, tag, idx, x, y⟩ := X
  unfold Tab.inrConv at h
  simp only [bind, Except.bind] at h
  split at h; · cases h
  rename_i D hD
  split at h
  · split at h; · cases h
    rename_i I hI
    split at h; · cases h
    rename_i C hC
    split at h; · cases h
    rename_i E hE
    split at h; · cases h
    rename_i F hF
    split at h; · cases h
    rename_i M hM
    have wD := idU_wf hD hX
    have wF := dom_wf hF (comp_wf hE wD (conv_wf hC (inl_wf hI hX.1)))
    split at h
    · rename_i hM0
      rw [zero_holds h, false_iff]
      rintro ⟨⟨i, hi⟩, hs⟩
      simp only [Core.Rel.inr, Core.Rel.graph] at hs
      have hd : D.Holds s s := (idU_holds hD hX _ _).2 ⟨rfl, i, hi⟩
      have hn : ¬ M.Holds s s := fun ⟨j, _⟩ => by have := j.2; simp [hM0] at this
      have hf : F.Holds s s := Classical.byContradiction fun hf => hn ((diff_holds hM wD wF _ _).2 ⟨hd, hf⟩)
      obtain ⟨-, a, ha⟩ := (dom_holds hF (comp_wf hE wD (conv_wf hC (inl_wf hI hX.1))).1 _ _).1 hf
      obtain ⟨s', hs', hc⟩ := (comp_holds hE wD (conv_wf hC (inl_wf hI hX.1)) _ _).1 ha
      obtain ⟨rfl, -⟩ := (idU_holds hD hX _ _).1 hs'
      have he := ((inl_holds hI hX.1 _ _).1 ((conv_holds hC (inl_wf hI hX.1) _ _).1 hc)).2
      simp only [Core.Rel.inl, Core.Rel.graph] at he
      exact absurd (hs.symm.trans he) (by simp)
    · cases h
  · rename_i hr
    split at h; · cases h
    rename_i I hI
    split at h; · cases h
    rename_i C hC
    rw [comp_holds h (idU_wf hD hX) (conv_wf hC (inr_wf hI hX.2))]
    constructor
    · rintro ⟨s', hd, hc⟩
      obtain ⟨rfl, hs⟩ := (idU_holds hD hX _ _).1 hd
      exact ⟨hs, ((inr_holds hI hX.2 _ _).1 ((conv_holds hC (inr_wf hI hX.2) _ _).1 hc)).2⟩
    · rintro ⟨⟨i, hi⟩, hs⟩
      refine ⟨s, (idU_holds hD hX _ _).2 ⟨rfl, i, hi⟩, (conv_holds hC (inr_wf hI hX.2) _ _).2 ((inr_holds hI hX.2 _ _).2 ⟨?_, hs⟩)⟩
      simp only [Core.Rel.inr, Core.Rel.graph] at hs
      subst hs
      simp only [Vals.row] at hi
      split at hi
      · rw [dif_pos (by omega)] at hi; exact ⟨_, Sum.inr.inj hi⟩
      · cases hi

end Tab

/-! ## Checks on `foR` tables -/



end Rel
