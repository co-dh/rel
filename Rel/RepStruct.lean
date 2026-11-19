import Rel.Run.Struct
import Rel.RepTabComp
import Rel.RepSetOps
import Rel.Run.CRelRelDef
import Rel.Core.Rel

/-! The laws of the structural operators (`Rel/Run/Struct.lean`), each with its `Tm` constructor's denotation
(`Tm.den`, `Rel/Lang/Den.lean`) as the right-hand side, and their checks against the old operators. -/

namespace Rel
open Rel.Ext Rel.Kernel Rel.Verify Ext.Enc
open scoped Rel.Core.Rel

/-- **CROSS's index columns**: `T = n · m` rows, row `t` reading `t / m` and `t % m`. -/
theorem crossIx_ok {n m T : USize} {iR iS : Enc} (h : crossIx n m = .ok (T, iR, iS)) :
    T.toNat = n.toNat * m.toNat ∧ ∀ t < T.toNat,
      ((raw .i64 T iR)[t]?.getD 0).toNat = t / m.toNat ∧ ((raw .i64 T iS)[t]?.getD 0).toNat = t % m.toNat := by
  unfold crossIx at h
  by_cases hb : 2 ^ 63 ≤ n.toNat * m.toNat + m.toNat ∨ USize.size ≤ n.toNat * m.toNat
  · simp [hb, bind, Except.bind] at h
  simp only [hb, if_false, bind, Except.bind, pure, Except.pure] at h
  split at h; · cases h
  rename_i c hc
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
  have hc' : (raw .i64 (n.toNat * m.toNat).toUSize c)[t]?.getD 0 = m.toNat.toUInt64 := by
    rw [colConst_raw hc, Array.getElem?_replicate, if_pos (by rw [hT]; exact ht), Option.getD_some, hmU]
  have hp : (raw .i64 (n.toNat * m.toNat).toUSize (.pos : Enc))[t]?.getD 0 = t.toUInt64 := raw_pos_word (by omega)
  have e1 := (colMap_raw hd).2.2.2 t (by omega)
  have e2 := (colMap_raw he).2.2.2 t (by omega)
  rw [hp, hc', eval_div_nat (by omega) (by omega) hm0, Except.ok.injEq] at e1
  rw [hp, hc', eval_mod_nat (by omega) (by omega) hm0, Except.ok.injEq] at e2
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
theorem idU_holds {n : USize} {X : Vals A n} {T : Tab A A} (h : Tab.idU X = .ok T) (a b : A.El) :
    T.Holds a b ↔ a = b ∧ ∃ i, X.row i = a := by
  rw [dom_holds h]
  exact ⟨fun ⟨e, _, i, h1, _⟩ => ⟨e, i, h1⟩, fun ⟨e, i, h1⟩ => ⟨e, _, i, h1, rfl⟩⟩

/-- **`Tab.top X V` denotes `⊤ ≫ V` on the values of `X`** (`Tm.den` at `top`: `idU X ≫ ⊤ ≫ ⟦V⟧`). -/
theorem top_holds {n : USize} {X : Vals A n} {V : Tab B B} {T : Tab A B} (h : Tab.top X V = .ok T) (a : A.El)
    (b : B.El) : T.Holds a b ↔ (∃ i, X.row i = a) ∧ (Core.Rel.top ≫ V.Holds) a b := by
  unfold Tab.top at h
  simp only [bind, Except.bind] at h
  split at h; · cases h
  rename_i r hr
  obtain ⟨T', x, y⟩ := r
  rw [canon_holds h]
  refine (Vals.cross_rows hr a b).trans (and_congr_right fun _ => ⟨fun ⟨j, hj⟩ => ⟨_, trivial, j, rfl, hj⟩, fun ⟨_, _, j, _, hj⟩ => ⟨j, hj⟩⟩)

/-- **`Tab.outl X` denotes `π₁` on the pairs `X`** (`Tm.den` at `outl`: `idU X ≫ graph Prod.fst`). -/
theorem outl_holds {n : USize} {X : Vals (.prod A B) n} {T : Tab (.prod A B) A} (h : Tab.outl X = .ok T)
    (p : (Obj.prod A B).El) (a : A.El) : T.Holds p a ↔ (∃ i, X.row i = p) ∧ Core.Rel.graph Prod.fst p a := by
  rw [canon_holds h]
  exact ⟨fun ⟨i, h1, h2⟩ => ⟨⟨i, h1⟩, by subst h1 h2; rfl⟩, fun ⟨⟨i, h1⟩, h2⟩ => ⟨i, h1, by subst h1 h2; rfl⟩⟩

/-- **`Tab.outr X` denotes `π₂` on the pairs `X`** (`Tm.den` at `outr`: `idU X ≫ graph Prod.snd`). -/
theorem outr_holds {n : USize} {X : Vals (.prod A B) n} {T : Tab (.prod A B) B} (h : Tab.outr X = .ok T)
    (p : (Obj.prod A B).El) (b : B.El) : T.Holds p b ↔ (∃ i, X.row i = p) ∧ Core.Rel.graph Prod.snd p b := by
  rw [canon_holds h]
  exact ⟨fun ⟨i, h1, h2⟩ => ⟨⟨i, h1⟩, by subst h1 h2; rfl⟩, fun ⟨⟨i, h1⟩, h2⟩ => ⟨i, h1, by subst h1 h2; rfl⟩⟩

/-- **`R.pair S` denotes `⟨R, S⟩`** (`Tm.den` at `pair`: `rpair`). -/
theorem pair_holds {R : Tab A B} {S : Tab A C} {T : Tab A (.prod B C)} (h : R.pair S = .ok T) (a : A.El)
    (q : (Obj.prod B C).El) : T.Holds a q ↔ Core.Rel.rpair R.Holds S.Holds a q := by
  unfold Tab.pair at h
  cases hc : comp (⟨R.n, (R.key, R.val), R.key⟩ : Tab (.prod A B) A) S with
  | error s => simp [hc, Functor.map, Except.map] at h
  | ok U =>
    simp only [hc, Functor.map, Except.map, Except.ok.injEq] at h
    subst h
    obtain ⟨b, c⟩ := q
    have e := comp_holds hc (a, b) c
    simp only [Tab.Holds, Core.Rel.rpair, Vals.row, Prod.mk.injEq] at e ⊢
    rw [show (∃ i, U.key.1.row i = a ∧ U.key.2.row i = b ∧ U.val.row i = c) ↔
      ∃ i, (U.key.1.row i = a ∧ U.key.2.row i = b) ∧ U.val.row i = c from by simp only [and_assoc], e]
    exact ⟨fun ⟨_, ⟨i, ⟨h1, h2⟩, h3⟩, hS⟩ => ⟨⟨i, h1, h2⟩, by subst h3; rwa [h1] at hS⟩,
      fun ⟨⟨i, h1, h2⟩, hS⟩ => ⟨a, ⟨i, ⟨h1, h2⟩, h1⟩, hS⟩⟩

/-- **`R.prod S` denotes `R × S`** (`Tm.den` at `prod`: `rprodMap`). -/
theorem prod_holds {R : Tab A B} {S : Tab C D} {T : Tab (.prod A C) (.prod B D)} (h : R.prod S = .ok T)
    (p : (Obj.prod A C).El) (q : (Obj.prod B D).El) : T.Holds p q ↔ Core.Rel.rprodMap R.Holds S.Holds p q := by
  unfold Tab.prod at h
  simp only [bind, Except.bind] at h
  split at h; · cases h
  rename_i r hr
  obtain ⟨T', x, y⟩ := r
  rw [canon_holds h]
  obtain ⟨a, c⟩ := p; obtain ⟨b, d⟩ := q
  have e := Vals.cross_rows hr (a, b) (c, d)
  simp only [Tab.Holds, Core.Rel.rprodMap, Vals.row, Prod.mk.injEq] at e ⊢
  rw [← e]
  exact ⟨fun ⟨t, ⟨h1, h2⟩, h3, h4⟩ => ⟨t, ⟨h1, h3⟩, h2, h4⟩, fun ⟨t, ⟨h1, h3⟩, h2, h4⟩ => ⟨t, ⟨h1, h2⟩, h3, h4⟩⟩

/-- **`Tab.flat X R` denotes `Rᴵ` on the pairs `X`** (`Tm.den` at `flat`: `idU X ≫ flatDen ⟦R⟧`,
`flatDen T x b = T x.1 (x.2, b)`). -/
theorem flat_holds {n : USize} {X : Vals (.prod I A) n} {R : Tab I (.prod A B)} {T : Tab (.prod I A) B}
    (h : Tab.flat X R = .ok T) (p : (Obj.prod I A).El) (b : B.El) :
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
  rw [comp_holds h]
  simp only [inter_holds hJ, comp_holds hL, comp_holds hM, conv_holds hO3c, outl_holds hO1, outr_holds hO2,
    outl_holds hO3, outr_holds hO4, Core.Rel.graph]
  obtain ⟨i, a⟩ := p
  constructor
  · rintro ⟨⟨a', b'⟩, ⟨⟨i', ⟨hx, rfl⟩, hR⟩, ⟨a'', ⟨-, rfl⟩, ⟨-, rfl⟩⟩⟩, ⟨-, rfl⟩⟩
    exact ⟨hx, hR⟩
  · rintro ⟨hx, hR⟩
    have hy : ∃ j, R.val.row j = (a, b) := let ⟨j, _, hj⟩ := hR; ⟨j, hj⟩
    exact ⟨(a, b), ⟨⟨i, ⟨hx, rfl⟩, hR⟩, ⟨a, ⟨hx, rfl⟩, ⟨hy, rfl⟩⟩⟩, ⟨hy, rfl⟩⟩

end Tab

/-- **`Arr.map` is `colMap`** on the array's column. -/
theorem Arr.map_ok {o : Op} {n : USize} {a b : Enc} {t : QAtomicType} {x : Arr t n} (h : Arr.map o n a b t = .ok x) :
    colMap o n a b t = .ok x.enc := by
  unfold Arr.map at h
  split at h
  next e he => cases h; exact he
  next => cases h

/-- **`injCols`'s columns**: every tag is `s`, and row `k`'s position reads back as `k`. -/
theorem injCols_ok {n : USize} {s : Bool} {tag : Arr .u1 n} {idx : Arr .i64 n} (h : injCols n s = .ok (tag, idx))
    (k : Fin n.toNat) :
    tag.get k = s ∧ clampFin (idx.get k) n.toNat (Nat.lt_of_le_of_lt (Nat.zero_le _) k.2) = k := by
  unfold injCols at h
  by_cases hb : 2 ^ 63 < n.toNat
  · simp [hb, bind, Except.bind] at h
  simp only [hb, if_false, bind, Except.bind, pure, Except.pure] at h
  split at h; · cases h
  rename_i z hz
  split at h; · cases h
  rename_i o ho
  split at h; · cases h
  rename_i t ht
  split at h; · cases h
  rename_i i hi
  simp only [Except.ok.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  have hk : k.1 < n.toNat := k.2
  refine ⟨?_, ?_⟩
  · obtain ⟨a, ha, he⟩ := Arr.get_u1 t (colMap_closed (Arr.map_ok ht)).1 k
    obtain ⟨v, ev, hv⟩ := (colMap_get (Arr.map_ok ht)).2 k.1 hk
    rw [colConst_raw hz, colConst_raw ho] at ev
    rw [ha] at hv
    simp only [Array.getElem?_replicate, hk, if_true, Option.getD_some, Op.eval, Except.ok.injEq] at ev
    simp only [if_true, Option.some.injEq] at hv
    subst ev; subst hv
    cases s <;> cases hg : t.get k <;> rw [hg] at he <;> revert he <;> decide
  · rw [Arr.get_i64]
    obtain ⟨v, ev, hv⟩ := (colMap_get (Arr.map_ok hi)).2 k.1 hk
    rw [raw_pos_word hk, colConst_raw hz] at ev
    simp only [Op.eval, Array.getElem?_replicate, hk, if_true, Option.getD_some, UInt64.add_zero,
      Except.ok.injEq] at ev
    have hw : (raw .i64 n i.enc)[k.1]?.getD 0 = k.1.toUInt64 := by simp [hv, ev]
    rw [hw, clampFin_word _ (by rw [toNat_toUInt64 (by omega)]; exact hk) (by omega)]
    exact Fin.ext (toNat_toUInt64 (by omega))

namespace Tab

/-- **`Tab.inl X` denotes `inl` on the values `X`** (`idU X ≫ Core.Rel.inl`, the injection `junc` is defined by). -/
theorem inl_holds {n : USize} {X : Vals A n} {T : Tab A (.sum A B)} (h : Tab.inl X = .ok T) (a : A.El)
    (s : (Obj.sum A B).El) : T.Holds a s ↔ (∃ i, X.row i = a) ∧ Core.Rel.inl a s := by
  unfold Tab.inl at h
  simp only [bind, Except.bind] at h
  split at h; · cases h
  rename_i ti hti
  obtain ⟨tag, idx⟩ := ti
  split at h; · cases h
  rename_i y hy
  rw [canon_holds h]
  have hrow : ∀ k : Fin n.toNat, Vals.row (A := .sum A B) ⟨n, 0, tag, idx, X, y⟩ k = .inl (X.row k) := fun k => by
    obtain ⟨ht, hc⟩ := injCols_ok hti k
    simp only [Vals.row, ht, dif_pos (Nat.lt_of_le_of_lt (Nat.zero_le _) k.2), hc]
    rfl
  simp only [Tab.Holds, hrow, Core.Rel.inl, Core.Rel.graph]
  exact ⟨fun ⟨i, h1, h2⟩ => ⟨⟨i, h1⟩, by rw [← h2, h1]⟩, fun ⟨⟨i, h1⟩, h2⟩ => ⟨i, h1, by rw [h2, h1]⟩⟩

/-- **`Tab.inr Y` denotes `inr` on the values `Y`** (`idU Y ≫ Core.Rel.inr`). -/
theorem inr_holds {n : USize} {Y : Vals B n} {T : Tab B (.sum A B)} (h : Tab.inr Y = .ok T) (b : B.El)
    (s : (Obj.sum A B).El) : T.Holds b s ↔ (∃ i, Y.row i = b) ∧ Core.Rel.inr b s := by
  unfold Tab.inr at h
  simp only [bind, Except.bind] at h
  split at h; · cases h
  rename_i ti hti
  obtain ⟨tag, idx⟩ := ti
  split at h; · cases h
  rename_i x hx
  rw [canon_holds h]
  have hrow : ∀ k : Fin n.toNat, Vals.row (A := .sum A B) ⟨0, n, tag, idx, x, Y⟩ k = .inr (Y.row k) := fun k => by
    obtain ⟨ht, hc⟩ := injCols_ok hti k
    simp only [Vals.row, ht, dif_pos (Nat.lt_of_le_of_lt (Nat.zero_le _) k.2), hc]
    rfl
  simp only [Tab.Holds, hrow, Core.Rel.inr, Core.Rel.graph]
  exact ⟨fun ⟨i, h1, h2⟩ => ⟨⟨i, h1⟩, by rw [← h2, h1]⟩, fun ⟨⟨i, h1⟩, h2⟩ => ⟨i, h1, by rw [h2, h1]⟩⟩

/-- **`R.junc S` denotes `[R, S]`** (`Tm.den` at `junc`: `Core.Rel.junc`, `inl° ≫ R ∪ inr° ≫ S`). -/
theorem junc_holds {R : Tab A C} {S : Tab B C} {T : Tab (.sum A B) C} (h : R.junc S = .ok T)
    (s : (Obj.sum A B).El) (c : C.El) : T.Holds s c ↔ Core.Rel.junc R.Holds S.Holds s c := by
  unfold Tab.junc at h
  simp only [bind, Except.bind] at h
  split at h; · cases h
  rename_i L hL
  split at h; · cases h
  rename_i Lc hLc
  split at h; · cases h
  rename_i U hU
  split at h; · cases h
  rename_i M hM
  split at h; · cases h
  rename_i Mc hMc
  split at h; · cases h
  rename_i V hV
  rw [union_holds h, comp_holds hU, comp_holds hV]
  simp only [conv_holds hLc, conv_holds hMc, inl_holds hL, inr_holds hM]
  have hk : ∀ {E : Obj} {Q : Tab E C} {e : E.El}, Q.Holds e c → ∃ i, Q.key.row i = e := fun ⟨i, hi, _⟩ => ⟨i, hi⟩
  cases s with
  | inl a =>
    simp only [Core.Rel.junc, Core.Rel.union, Core.Rel.comp, Core.Rel.recip, Core.Rel.inl, Core.Rel.inr,
      Core.Rel.graph]
    exact ⟨fun | .inl ⟨_, ⟨_, e⟩, hr⟩ => .inl ⟨_, e, hr⟩ | .inr ⟨_, ⟨_, e⟩, _⟩ => absurd e (by simp),
      fun | .inl ⟨_, e, hr⟩ => .inl ⟨_, ⟨hk hr, e⟩, hr⟩ | .inr ⟨_, e, _⟩ => absurd e (by simp)⟩
  | inr b =>
    simp only [Core.Rel.junc, Core.Rel.union, Core.Rel.comp, Core.Rel.recip, Core.Rel.inl, Core.Rel.inr,
      Core.Rel.graph]
    exact ⟨fun | .inr ⟨_, ⟨_, e⟩, hr⟩ => .inr ⟨_, e, hr⟩ | .inl ⟨_, ⟨_, e⟩, _⟩ => absurd e (by simp),
      fun | .inr ⟨_, e, hr⟩ => .inr ⟨_, ⟨hk hr, e⟩, hr⟩ | .inl ⟨_, e, _⟩ => absurd e (by simp)⟩

end Tab

/-! ## Checks on `foR` tables -/

section Checks

/-- Two lists hold the same elements: the old layer orders a float NaN first, `kasc` by `ordCode`. -/
private def setEq {α : Type} [BEq α] (a b : List α) : Bool := a.all b.contains && b.all a.contains

/-- The answer `r` runs, holds no row twice, and holds the rows `sp` (as a set). -/
private def specOk {A B : Obj} [BEq A.El] [BEq B.El] (r : Except String (Tab A B)) (sp : List (A.El × B.El)) : Bool :=
  match r with
  | .ok T => T.toList.eraseDups.length == T.toList.length && setEq T.toList sp
  | .error _ => false

/-- The answer `r` runs and holds the rows of the old table `o` (as a set), where `o` ran within capacity. -/
private def oldOk {A B : Obj} [BEq A.El] [BEq B.El] (r : Except String (Tab A B)) (o : Option (Tab A B)) : Bool :=
  match r, o with
  | .ok T, some U => setEq T.toList U.toList
  | _, _ => false

/-- The `i64` column of the integers `ws`, `foR` (`Arr.ofFn`). -/
private def col (ws : List Int64) : Arr .i64 ws.length.toUSize := Arr.ofFn .i64 _ fun i => (ws.getD i.1 0).toUInt64

/-- The table of the pairs `ps` as given, unsorted, both columns `col`. -/
private def tabW (ps : List (Int64 × Int64)) : Tab .long .long :=
  ⟨ps.length.toUSize, List.length_map _ ▸ col (ps.map (·.1)), List.length_map _ ▸ col (ps.map (·.2))⟩

/-- `-0.0`, `+0.0`, NaN with payloads `1` and `2`, `+inf`, `-inf`, `1.5`, `-0.0` again, as `f64` bits. -/
private def f64s : List UInt64 := [0x8000000000000000, 0, 0x7ff8000000000001, 0x7ff8000000000002, 0x7ff0000000000000,
  0xfff0000000000000, 0x3ff8000000000000, 0x8000000000000000]

/-- Integer tables: duplicate rows, negatives, one row, none. -/
private def ints : List (List (Int64 × Int64)) :=
  [[(3, 1), (1, 2), (3, 1), (-1, 2), (1, 2), (2, 7)], [(2, 5), (1, -3), (2, 6), (3, 3), (2, 5)], [(4, 8)], []]

/-- A float value column with a duplicate row (`-0.0` at key `3` twice). -/
private def F : Tab .long (.atom .f64) := ⟨8, col [3, 1, 2, 1, 4, 4, 0, 3], Arr.ofFn .f64 8 (f64s.getD · 0)⟩
/-- A tuple value column with duplicate rows. -/
private def P : Tab .long (.prod .long .long) := ⟨5, col [3, 1, 3, 1, 3], (col [1, 1, 1, 2, 1], col [5, 6, 5, 6, 5])⟩

/-- The canonical old table, where `canonC` ran within capacity. -/
private def oldC {A B : Obj} (T : Tab A B) : Option (Tab A B) := let c := Alg.canonC T; if c.2 then some c.1 else none

-- `𝟘` at an atom, a float, a tuple, an `arr` and a `sum` side
#guard specOk (Tab.zero : Except String (Tab .long (.atom .f64))) [] &&
  specOk (Tab.zero : Except String (Tab (.prod .long .long) (.arr .long))) [] &&
  specOk (Tab.zero : Except String (Tab (.sum .long .long) .long)) [] && (Alg.zero : Tab .long .long).toList.isEmpty

-- `𝟙` on the values `X`: duplicates, a float, a tuple, none
#guard ints.all fun ps => let R := tabW ps
  oldOk (Tab.idU R.key) (oldC (Alg.idU R.key)) && specOk (Tab.idU R.key) (R.key.toList.map fun a => (a, a))
#guard oldOk (Tab.idU F.val) (oldC (Alg.idU F.val)) && oldOk (Tab.idU P.val) (oldC (Alg.idU P.val))

/-- The rows of a side, in position order. -/
private def rows {A : Obj} {n : USize} (X : Vals A n) : List A.El := List.ofFn (Vals.row X)

/-- `top X V` against the old `topC` (on `V`'s values) and against `X × V.val` as a set. -/
private def topOk {A B : Obj} [BEq A.El] [BEq B.El] {n : USize} (X : Vals A n) (V : Tab B B) : Bool :=
  oldOk (Tab.top X V) (let c := Alg.topC X V.val; if c.2 then oldC c.1 else none) &&
    specOk (Tab.top X V) ((rows X).flatMap fun a => (rows V.val).map fun b => (a, b))

-- `⊤`: integers (an empty side on either end), a float, a tuple
#guard ints.all fun ps => ints.all fun qs => topOk (tabW ps).key (tabW qs)
#guard topOk P.val (⟨F.n, F.val, F.val⟩ : Tab (.atom .f64) (.atom .f64)) &&
  topOk F.val (⟨P.n, P.val, P.val⟩ : Tab (.prod .long .long) (.prod .long .long))

/-- `outl X`, `outr X` against the old `outl`, `outr` of `idU X` and against the projections as sets. -/
private def outOk {A B : Obj} [BEq A.El] [BEq B.El] {n : USize} (X : Vals (.prod A B) n) : Bool :=
  oldOk (Tab.outl X) (oldC (Alg.outl (Alg.idU X))) && oldOk (Tab.outr X) (oldC (Alg.outr (Alg.idU X))) &&
    specOk (Tab.outl X) ((rows X).map fun p => (p, p.1)) && specOk (Tab.outr X) ((rows X).map fun p => (p, p.2))

-- `π₁`, `π₂`: integer pairs with duplicates, none, a float component, a tuple component
#guard ints.all fun ps => let R := tabW ps; outOk (A := .long) (B := .long) (R.key, R.val)
#guard outOk (A := .long) (B := .atom .f64) (F.key, F.val) && outOk (A := .long) (B := .prod .long .long) (P.key, P.val)

/-- `pair` and `prod` against the old `CRel.pair`, `CRel.prod` and against their denotations as sets. -/
private def pairOk {A B C : Obj} [BEq A.El] [BEq B.El] [BEq C.El] (R : Tab A B) (S : Tab A C) : Bool :=
  oldOk (R.pair S) (CRel.pair (some R) (some S)) &&
    specOk (R.pair S) (R.toList.flatMap fun (a, b) => S.toList.filterMap fun (a', c) =>
      if a == a' then some (a, (b, c)) else none)
private def prodOk {A B C D : Obj} [BEq A.El] [BEq B.El] [BEq C.El] [BEq D.El] (R : Tab A B) (S : Tab C D) : Bool :=
  oldOk (R.prod S) (CRel.prod (some R) (some S)) &&
    specOk (R.prod S) (R.toList.flatMap fun (a, b) => S.toList.map fun (c, d) => ((a, c), (b, d)))

-- `⟨R, S⟩` and `R × S`: integers (duplicates, an empty side, no common key), a float and a tuple value
#guard ints.all fun ps => ints.all fun qs => pairOk (tabW ps) (tabW qs) && prodOk (tabW ps) (tabW qs)
#guard pairOk F P && pairOk P F && prodOk F P && prodOk P (tabW (ints.getD 0 []))

/-- `flat X R` against `Rᴵ` on `X` as a set: `((i, a), b)` for `(i, a)` of `X` and `(i, (a, b))` of `R`. -/
private def flatOk {I A B : Obj} [BEq I.El] [BEq A.El] [BEq B.El] {n : USize} (X : Vals (.prod I A) n)
    (R : Tab I (.prod A B)) : Bool :=
  specOk (Tab.flat X R) ((rows X).flatMap fun p => R.toList.filterMap fun (i, a, b) =>
    if p.1 == i && p.2 == a then some (p, b) else none)

-- `Rᴵ`: a tuple family on integer pairs (duplicates, a pair `R` misses), on none, and a float source
#guard flatOk (I := .long) (A := .long) (col [3, 1, 3, 3, 9], col [1, 2, 1, 5, 1]) P &&
  flatOk (I := .long) (A := .long) (col [], col []) P &&
  flatOk (I := .long) (A := .atom .f64) (F.key, F.val) (⟨F.n, F.key, (F.val, F.key)⟩ : Tab .long (.prod (.atom .f64) .long))

/-- `inl X` and `inr X` against the old `inlC`, `inrC` and against the injections as sets. -/
private def injOk {A B : Obj} [BEq A.El] [BEq B.El] {n : USize} (X : Vals A n) (Y : Vals B n) : Bool :=
  oldOk (Tab.inl (B := B) X) (let c := Alg.inlC (B := B) X; if c.2 then oldC c.1 else none) &&
    oldOk (Tab.inr (A := A) Y) (let c := Alg.inrC (A := A) Y; if c.2 then oldC c.1 else none) &&
    specOk (Tab.inl (B := B) X) ((rows X).map fun a => (a, .inl a)) &&
    specOk (Tab.inr (A := A) Y) ((rows Y).map fun b => (b, .inr b))

/-- `[R, S]` against the old `juncC` and against `inl° ≫ R ∪ inr° ≫ S` as a set. -/
private def juncOk {A B C : Obj} [BEq A.El] [BEq B.El] [BEq C.El] (R : Tab A C) (S : Tab B C) : Bool :=
  oldOk (R.junc S) (let c := Alg.juncC R S; if c.2 then oldC c.1 else none) &&
    specOk (R.junc S) ((R.toList.map fun (a, c) => (.inl a, c)) ++ S.toList.map fun (b, c) => (.inr b, c))

-- `inl`, `inr`: duplicates, none, a float and a tuple summand
#guard ints.all fun ps => let R := tabW ps; injOk R.key R.val
#guard injOk F.val F.key && injOk P.val P.key
/-- `[R, S]` stops at `union`'s `Vals.concat`, which has no `sum` case yet (branch w3arrcat): until then the
guards assert that error; once it lands they become `juncOk`. -/
private def juncBlocked {A B C : Obj} (R : Tab A C) (S : Tab B C) : Bool :=
  match R.junc S with
  | .error s => s == "concat: a sum side is not atom columns"
  | .ok _ => false

-- `[R, S]`: integers (duplicates, a summand of no rows, both empty), a float and a tuple value
#guard ints.all fun ps => ints.all fun qs => juncBlocked (tabW ps) (tabW qs)
#guard juncBlocked F F && juncBlocked (A := .long) (B := .long) P P &&
  juncBlocked (tabW []) (⟨F.n, F.val, F.key⟩ : Tab (.atom .f64) .long)

end Checks

#print axioms Tab.zero_holds
#print axioms Tab.idU_holds
#print axioms Tab.top_holds
#print axioms Tab.outl_holds
#print axioms Tab.outr_holds
#print axioms Tab.pair_holds
#print axioms Tab.prod_holds
#print axioms Tab.inl_holds
#print axioms Tab.inr_holds
#print axioms Tab.junc_holds
#print axioms Tab.flat_holds

end Rel
