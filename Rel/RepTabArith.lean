import Rel.Run.Arith
import Rel.RepTabComp
import Rel.RepSetOps
import Rel.Lang.Den

/-! Laws of `Tab.arith` and `Tab.succ` (`Rel/Run/Arith.lean`): `stepCols_spec`, `Tab.succ_holds`; and checks
against the meanings `arithDen`, `succDen` of
`Rel/Lang/Den.lean`, read on lists. -/

namespace Rel
open Rel.Ext Rel.Kernel Rel.Verify Ext.Enc
/-- Word `i` of the `n`-word `i64` column `e`. -/
abbrev wd (n : USize) (e : Enc) (i : Nat) : UInt64 := (raw .i64 n e)[i]?.getD 0

/-! ### `Op.eval` of the steps `stepCols` runs, on raw words -/

private theorem ev_ne (A B : UInt64) : Op.eval .ne A B = .ok (if A ≠ B then 1 else 0) := by
  show Except.ok (if (A != B) = true then 1 else 0) = _; by_cases h : A = B <;> simp [h]
private theorem ev_eq (A B : UInt64) : Op.eval .eq A B = .ok (if A = B then 1 else 0) := by
  show Except.ok (if (A == B) = true then 1 else 0) = _; by_cases h : A = B <;> simp [h]
private theorem ev_le (A B : UInt64) : Op.eval .le A B = .ok (if A.toInt64 ≤ B.toInt64 then 1 else 0) := by
  show Except.ok (if decide (A.toInt64 ≤ B.toInt64) = true then 1 else 0) = _; simp
private theorem ev_ge (A B : UInt64) : Op.eval .ge A B = .ok (if B.toInt64 ≤ A.toInt64 then 1 else 0) := by
  show Except.ok (if decide (B.toInt64 ≤ A.toInt64) = true then 1 else 0) = _; simp
private theorem ev_div (A B : UInt64) (h : B ≠ 0) :
    Op.eval .div A B = .ok (Int64.ofInt (Int.fdiv A.toInt64.toInt B.toInt64.toInt)).toUInt64 := by
  show (if (B == 0) = true then _ else _) = _; simp [h]; rfl
private theorem ev_mod (A B : UInt64) (h : B ≠ 0) :
    Op.eval .mod A B = .ok (Int64.ofInt (Int.fmod A.toInt64.toInt B.toInt64.toInt)).toUInt64 := by
  show (if (B == 0) = true then _ else _) = _; simp [h]; rfl

private theorem ev_max (A B : UInt64) : Op.eval .max A B = .ok (if A.toInt64 < B.toInt64 then B else A) := rfl
private theorem ev_min (A B : UInt64) : Op.eval .min A B = .ok (if B.toInt64 < A.toInt64 then B else A) := rfl
private theorem ev_not (A B : UInt64) : Op.eval .not A B = .ok (B ^^^ 1) := rfl

private theorem bit_and (p q : Prop) [Decidable p] [Decidable q] :
    ((if p then 1 else 0 : UInt64) &&& if q then 1 else 0) = if p ∧ q then 1 else 0 := by
  by_cases hp : p <;> by_cases hq : q <;> simp [hp, hq]
private theorem bit_or (p q : Prop) [Decidable p] [Decidable q] :
    ((if p then 1 else 0 : UInt64) ||| if q then 1 else 0) = if p ∨ q then 1 else 0 := by
  by_cases hp : p <;> by_cases hq : q <;> simp [hp, hq]
private theorem bit_eq (p q : Prop) [Decidable p] [Decidable q] :
    ((if p then 1 else 0 : UInt64) = if q then 1 else 0) ↔ (p ↔ q) := by
  by_cases hp : p <;> by_cases hq : q <;> simp [hp, hq]
private theorem bit_not (p : Prop) [Decidable p] : ((if p then 1 else 0 : UInt64) ^^^ 1) = if ¬p then 1 else 0 := by
  by_cases hp : p <;> simp [hp]
private theorem bit_ne (p : Prop) [Decidable p] : ((if p then 1 else 0 : UInt64) ≠ 0) ↔ p := by
  by_cases hp : p <;> simp [hp]
private theorem bit_lt (p : Prop) [Decidable p] : (if p then 1 else 0 : UInt64) < 2 := by
  by_cases hp : p <;> simp [hp] <;> decide
private theorem or_zero (A : UInt64) : (A ||| if A = 0 then 1 else 0) = if A = 0 then 1 else A := by
  by_cases hp : A = 0 <;> simp [hp]
private theorem one_ne (A : UInt64) : (if A = 0 then 1 else A) ≠ 0 := by by_cases hp : A = 0 <;> simp [hp]

/-! ### Words as `Int64`s -/

private theorem toU_inj (x y : Int64) : x.toUInt64 = y.toUInt64 ↔ x = y :=
  ⟨fun h => by simpa using congrArg UInt64.toInt64 h, fun h => h ▸ rfl⟩
private theorem toU_eq_zero (x : Int64) : x.toUInt64 = 0 ↔ x = 0 := toU_inj x 0
private theorem toU_ite (p : Prop) [Decidable p] (x y : Int64) :
    (if p then x.toUInt64 else y.toUInt64) = (if p then x else y).toUInt64 := by split <;> rfl
private theorem toU_ite1 (p : Prop) [Decidable p] (y : Int64) :
    (if p then (1 : UInt64) else y.toUInt64) = (if p then 1 else y).toUInt64 := by split <;> rfl

/-! ### `stepDen k` on `Int64`s, each verb in the shape `stepCols` computes -/

private theorem add_iff (a b v : Int64) :
    (((a ≠ Alg.nul ∧ b ≠ Alg.nul) ∧ a + b ≠ Alg.nul) ∧ (0 ≤ b ↔ a ≤ a + b)) ∧ v = a + b ↔
      Lang.stepDen Ew.add (a, b) v := by
  simp only [Lang.stepDen, Ew.intStep_add]
  simp (config := {decide := true}) only [if_true]
  by_cases ha : a = Alg.nul <;> by_cases hb : b = Alg.nul <;> simp [ha, hb] <;> grind
private theorem sub_iff (a b v : Int64) :
    (((a ≠ Alg.nul ∧ b ≠ Alg.nul) ∧ a - b ≠ Alg.nul) ∧ (0 ≤ b ↔ a - b ≤ a)) ∧ v = a - b ↔
      Lang.stepDen Ew.sub (a, b) v := by
  simp only [Lang.stepDen, Ew.intStep_sub]
  simp (config := {decide := true}) only [if_true, if_false]
  by_cases ha : a = Alg.nul <;> by_cases hb : b = Alg.nul <;> simp [ha, hb] <;> grind
private theorem mul_iff (a b v : Int64) : (((a ≠ Alg.nul ∧ b ≠ Alg.nul) ∧ a * b ≠ Alg.nul) ∧
    (Int64.ofInt (Int.fdiv (a * b).toInt (if a = 0 then 1 else a).toInt) = b ∨ a = 0)) ∧ v = a * b ↔
      Lang.stepDen Ew.mul (a, b) v := by
  simp only [Lang.stepDen, Ew.intStep_mul, Ew.intStep_idiv]
  simp (config := {decide := true}) only [if_true, if_false]
  have hn0 : (0 : Int64) ≠ Alg.nul := by decide
  by_cases ha : a = Alg.nul <;> by_cases hb : b = Alg.nul <;> by_cases h0 : a = 0 <;>
    simp only [ha, hb, h0, hn0, if_true, if_false, or_false, or_true, true_or, not_false_eq_true,
      not_true_eq_false, and_true, true_and, and_false, false_and, ne_eq]
  all_goals constructor <;> intro h <;> grind
private theorem div_iff (a b v : Int64) : (((a ≠ Alg.nul ∧ b ≠ Alg.nul) ∧ ¬ b = 0) ∧
    Int64.ofInt (Int.fdiv a.toInt (if b = 0 then 1 else b).toInt) ≠ Alg.nul) ∧
      v = Int64.ofInt (Int.fdiv a.toInt (if b = 0 then 1 else b).toInt) ↔ Lang.stepDen Ew.idiv (a, b) v := by
  simp only [Lang.stepDen, Ew.intStep_idiv]
  simp (config := {decide := true}) only []
  by_cases ha : a = Alg.nul <;> by_cases hb : b = Alg.nul <;> by_cases h0 : b = 0 <;> simp [ha, hb, h0] <;> grind
private theorem mod_iff (a b v : Int64) : (((a ≠ Alg.nul ∧ b ≠ Alg.nul) ∧ ¬ b = 0) ∧
    Int64.ofInt (Int.fmod a.toInt (if b = 0 then 1 else b).toInt) ≠ Alg.nul) ∧
      v = Int64.ofInt (Int.fmod a.toInt (if b = 0 then 1 else b).toInt) ↔ Lang.stepDen Ew.imod (a, b) v := by
  simp only [Lang.stepDen, Ew.intStep_imod]
  simp (config := {decide := true}) only [Ew.idiv, if_false]
  by_cases ha : a = Alg.nul <;> by_cases hb : b = Alg.nul <;> by_cases h0 : b = 0 <;> simp [ha, hb, h0] <;> grind
private theorem max_iff (a b v : Int64) : (if a < b then b else a) ≠ Alg.nul ∧ v = (if a < b then b else a) ↔
    Lang.stepDen Ew.greater (a, b) v := by
  simp only [Lang.stepDen, Ew.intStep_greater]
  simp (config := {decide := true}) only []
  grind
private theorem min_iff (a b v : Int64) : (if b < a then b else a) ≠ Alg.nul ∧ v = (if b < a then b else a) ↔
    Lang.stepDen Ew.lesser (a, b) v := by
  simp only [Lang.stepDen, Ew.intStep_lesser]
  simp (config := {decide := true}) only [if_false]
  grind

private theorem nulWord_eq : nulWord = Alg.nul.toUInt64 := rfl

/-- **`stepCols k` computes `stepDen k` row by row**: at each row `i` the keep flag is a bit, set exactly where some
`v` is `stepDen k` of the row's operands, and then `v` is the answer word. -/
theorem stepCols_spec {k : UInt8} {n : USize} {a b : Enc} {w : Arr .i64 n} {keep : Enc}
    (h : stepCols k n a b = .ok (w, keep)) (i : Nat) (hi : i < n.toNat) :
    wd n keep i < 2 ∧ ∀ v, (wd n keep i ≠ 0 ∧ v = (wd n w.enc i).toInt64) ↔
      Lang.stepDen k ((wd n a i).toInt64, (wd n b i).toInt64) v := by
  have cm : ∀ {op x y e}, colMap op n x y = .ok e → ∀ {r}, op.eval (wd n x i) (wd n y i) = .ok r → wd n e i = r :=
    fun hc _ he => (Except.ok.inj (he.symm.trans ((colMap_raw hc).2.2.2 i hi))).symm
  have cc : ∀ {c e}, colConst n c = .ok e → wd n e i = c := fun hc => by simp [wd, colConst_raw hc, hi]
  have ofA : ∀ A : UInt64, ∃ x : Int64, x.toUInt64 = A := fun A => ⟨A.toInt64, UInt64.toUInt64_toInt64 A⟩
  simp only [stepCols, bind, Except.bind_eq_ok'] at h
  obtain ⟨N, hN, Z, hZ, na, hna, nb, hnb, bo, hbo, h⟩ := h
  by_cases e1 : k = Ew.add
  · subst e1
    simp (config := {decide := true}) only [Ew.add, Ew.sub, Ew.mul, Ew.idiv, Ew.imod, Ew.greater, Ew.lesser, if_true,
      if_false, Bool.true_or, Bool.false_or, Bool.or_false, bind, Except.bind_eq_ok', pure, Except.pure,
      Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨w', hw', ord, hord, g, hg, ex, hex, nw, hnw, t1, ht1, kp, hkp, rfl, rfl⟩ := h
    rw [cm hkp rfl, cm ht1 rfl, cm hbo rfl, cm hna (ev_ne _ _), cm hnb (ev_ne _ _), cm hnw (ev_ne _ _),
      cm hex (ev_eq _ _), cm hg (ev_ge _ _), cm hord (ev_le _ _), cm (colArr_ok hw') rfl, cc hN, cc hZ]
    simp only [bit_and, bit_eq]
    refine ⟨bit_lt _, fun v => ?_⟩
    rw [bit_ne]
    obtain ⟨x, hx⟩ := ofA (wd n a i); obtain ⟨y, hy⟩ := ofA (wd n b i); rw [← hx, ← hy]
    simp only [nulWord_eq, ← Int64.toUInt64_add, ne_eq, toU_inj, Int64.toInt64_toUInt64,
      show UInt64.toInt64 0 = 0 from rfl]
    exact add_iff x y v
  by_cases e2 : k = Ew.sub
  · subst e2
    simp (config := {decide := true}) only [Ew.add, Ew.sub, Ew.mul, Ew.idiv, Ew.imod, Ew.greater, Ew.lesser, if_true,
      if_false, Bool.true_or, Bool.false_or, Bool.or_false, Bool.or_true, bind, Except.bind_eq_ok', pure, Except.pure,
      Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨w', hw', ord, hord, g, hg, ex, hex, nw, hnw, t1, ht1, kp, hkp, rfl, rfl⟩ := h
    rw [cm hkp rfl, cm ht1 rfl, cm hbo rfl, cm hna (ev_ne _ _), cm hnb (ev_ne _ _), cm hnw (ev_ne _ _),
      cm hex (ev_eq _ _), cm hg (ev_ge _ _), cm hord (ev_le _ _), cm (colArr_ok hw') rfl, cc hN, cc hZ]
    simp only [bit_and, bit_eq]
    refine ⟨bit_lt _, fun v => ?_⟩
    rw [bit_ne]
    obtain ⟨x, hx⟩ := ofA (wd n a i); obtain ⟨y, hy⟩ := ofA (wd n b i); rw [← hx, ← hy]
    simp only [nulWord_eq, ← Int64.toUInt64_sub, ne_eq, toU_inj, Int64.toInt64_toUInt64,
      show UInt64.toInt64 0 = 0 from rfl]
    exact sub_iff x y v
  by_cases e3 : k = Ew.mul
  · subst e3
    simp (config := {decide := true}) only [Ew.add, Ew.sub, Ew.mul, Ew.idiv, Ew.imod, Ew.greater, Ew.lesser, if_true,
      if_false, Bool.true_or, Bool.false_or, Bool.or_false, Bool.or_true, bind, Except.bind_eq_ok', pure, Except.pure,
      Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨w', hw', a0, ha0, o1, ho1, dv, hdv, e0, he0, ex, hex, nw, hnw, t1, ht1, kp, hkp, rfl, rfl⟩ := h
    have h0 : wd n o1 i ≠ 0 := by rw [cm ho1 rfl, cm ha0 (ev_eq _ _), cc hZ, or_zero]; exact one_ne _
    rw [cm hkp rfl, cm ht1 rfl, cm hbo rfl, cm hna (ev_ne _ _), cm hnb (ev_ne _ _), cm hnw (ev_ne _ _),
      cm hex rfl, cm he0 (ev_eq _ _), cm hdv (ev_div _ _ h0), cm ho1 rfl, cm ha0 (ev_eq _ _),
      cm (colArr_ok hw') rfl, cc hN, cc hZ]
    simp only [bit_and, bit_or, bit_eq, or_zero]
    refine ⟨bit_lt _, fun v => ?_⟩
    rw [bit_ne]
    obtain ⟨x, hx⟩ := ofA (wd n a i); obtain ⟨y, hy⟩ := ofA (wd n b i); rw [← hx, ← hy]
    simp only [nulWord_eq, ← Int64.toUInt64_mul, toU_eq_zero, toU_ite1, ne_eq, toU_inj, Int64.toInt64_toUInt64]
    exact mul_iff x y v
  by_cases e4 : k = Ew.idiv ∨ k = Ew.imod
  · rcases e4 with rfl | rfl
    all_goals
      simp (config := {decide := true}) only [Ew.add, Ew.sub, Ew.mul, Ew.idiv, Ew.imod, Ew.greater, Ew.lesser, if_true,
        if_false, Bool.true_or, Bool.false_or, Bool.or_false, Bool.or_true, bind, Except.bind_eq_ok', pure,
        Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨b0, hb0, o, ho, w', hw', nb0, hnb0, t, ht, nw, hnw, kp, hkp, rfl, rfl⟩ := h
      have h0 : wd n o i ≠ 0 := by rw [cm ho rfl, cm hb0 (ev_eq _ _), cc hZ, or_zero]; exact one_ne _
      rw [cm hkp rfl, cm ht rfl, cm hbo rfl, cm hna (ev_ne _ _), cm hnb (ev_ne _ _), cm hnw (ev_ne _ _),
        cm hnb0 (ev_not _ _), cm (colArr_ok hw') (by first | exact ev_div _ _ h0 | exact ev_mod _ _ h0), cm ho rfl,
        cm hb0 (ev_eq _ _), cc hN, cc hZ]
      simp only [bit_and, bit_not, or_zero]
      refine ⟨bit_lt _, fun v => ?_⟩
      rw [bit_ne]
      obtain ⟨x, hx⟩ := ofA (wd n a i); obtain ⟨y, hy⟩ := ofA (wd n b i); rw [← hx, ← hy]
      simp only [nulWord_eq, toU_eq_zero, toU_ite1, ne_eq, toU_inj, Int64.toInt64_toUInt64]
      first | exact div_iff x y v | exact mod_iff x y v
  by_cases e5 : k = Ew.greater ∨ k = Ew.lesser
  · rcases e5 with rfl | rfl
    all_goals
      simp (config := {decide := true}) only [Ew.add, Ew.sub, Ew.mul, Ew.idiv, Ew.imod, Ew.greater, Ew.lesser, if_true,
        if_false, Bool.true_or, Bool.false_or, Bool.or_false, Bool.or_true, bind, Except.bind_eq_ok', pure,
        Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨w', hw', nw, hnw, rfl, rfl⟩ := h
      rw [cm hnw (ev_ne _ _), cm (colArr_ok hw') (by first | exact ev_max _ _ | exact ev_min _ _), cc hN]
      refine ⟨bit_lt _, fun v => ?_⟩
      rw [bit_ne]
      obtain ⟨x, hx⟩ := ofA (wd n a i); obtain ⟨y, hy⟩ := ofA (wd n b i); rw [← hx, ← hy]
      simp only [nulWord_eq, Int64.toInt64_toUInt64, toU_ite, ne_eq, toU_inj]
      first | exact max_iff x y v | exact min_iff x y v
  simp only [Bool.or_eq_true, beq_iff_eq, e1, e2, e3, false_or, if_false, decide_false] at h
  rw [if_neg (by simpa using e4), if_neg (by simpa using e5)] at h
  cases h

/-- **`Tab.succ` answers `D ≫ succDen U`** (`Rel/Lang/Den.lean`): a row `(x, w)` of the answer is a row `(x, u)` of `D`
with `u` in `dom U`, `w = u + 1` (`Ew.intStep`, the null to itself), and `w` in `dom U`; `U X` agrees with `TU`
at the values `X`. -/
theorem Tab.succ_holds {K : Obj} {D : Tab K .long} {U : {n : USize} → Vals .long n → Except String (Tab .long .long)}
    {TU : Core.Rel Int64 Int64}
    (hU : ∀ n (X : Vals .long n) t, U X = .ok t → ∀ a v, (∃ i, X.row i = a) → (t.Holds a v ↔ TU a v))
    {T : Tab K .long} (h : D.succ U = .ok T) (x : K.El)
    (w : Int64) : T.Holds x w ↔ ∃ u, D.Holds x u ∧ Lang.succDen TU u w := by
  simp only [Tab.succ, bind, Except.bind_eq_ok'] at h
  obtain ⟨u₁, hu₁, du₁, hdu₁, E, hE, N, hN, ne, hne, s, hs, u₂, hu₂, du₂, hdu₂, hT⟩ := h
  have hrow : ∀ i : Fin E.n.toNat, Vals.row (A := .long) s i = Ew.intStep Ew.add Alg.nul (E.val.row i) 1 := by
    intro i
    show s.get i = Ew.intStep Ew.add Alg.nul (Arr.get E.val i) 1
    rw [Arr.get_i64, Arr.get_i64]
    have r1 := (colMap_raw (colArr_ok hs)).2.2.2 i i.2
    have r2 := (colMap_raw hne).2.2.2 i i.2
    rw [colConst_raw hN] at r2
    simp only [Array.getElem?_replicate, i.2, if_true, Option.getD_some] at r2
    rw [ev_ne] at r2
    rw [← Except.ok.inj r2] at r1
    rw [← Except.ok.inj r1]
    generalize (raw .i64 E.n E.val.enc)[i.1]?.getD 0 = A
    obtain ⟨a, rfl⟩ : ∃ a : Int64, a.toUInt64 = A := ⟨A.toInt64, UInt64.toUInt64_toInt64 A⟩
    by_cases ha : a = Alg.nul
    · subst ha; decide
    · have : a.toUInt64 ≠ nulWord := fun e => ha ((toU_inj _ _).1 e)
      simp (config := {decide := true}) only [ne_eq, this, not_false_eq_true, if_true, Ew.intStep_add]
      show (a + 1).toUInt64.toInt64 = _
      simp [ha]
  rw [Tab.comp_holds hT]
  have inD : ∀ {u}, D.Holds x u → ∃ j, D.val.row j = u := fun ⟨j, _, hj⟩ => ⟨j, hj⟩
  constructor
  · rintro ⟨b, ⟨i, hx, hb⟩, hd⟩
    obtain ⟨rfl, y, hy⟩ := (Tab.dom_holds hdu₂ _ _).1 hd
    obtain ⟨u, hDu, hd'⟩ := (Tab.comp_holds hE x (E.val.row i)).1 ⟨i, hx, rfl⟩
    obtain ⟨rfl, y', hy'⟩ := (Tab.dom_holds hdu₁ _ _).1 hd'
    exact ⟨_, hDu, ⟨y', (hU _ _ _ hu₁ _ _ (inD hDu)).1 hy'⟩, (hrow i ▸ hb).symm, y,
      (hU _ _ _ hu₂ _ _ ⟨i, hb⟩).1 hy⟩
  · rintro ⟨u, hDu, ⟨y', hy'⟩, rfl, y, hy⟩
    obtain ⟨i, hx, hu⟩ := (Tab.comp_holds hE x u).2
      ⟨u, hDu, (Tab.dom_holds hdu₁ u u).2 ⟨rfl, y', (hU _ _ _ hu₁ _ _ (inD hDu)).2 hy'⟩⟩
    have hsi : Vals.row (A := .long) s i = Ew.intStep Ew.add Alg.nul u 1 := by rw [hrow, hu]
    exact ⟨_, ⟨i, hx, hsi⟩, (Tab.dom_holds hdu₂ _ _).2 ⟨rfl, y, (hU _ _ _ hu₂ _ _ ⟨i, hsi⟩).2 hy⟩⟩

/-! ### The value verbs at a float atom: `fstepCols` computes `stepAt` -/

/-- **`fverbBy` commutes with a reading of its operands**: a map `f` taking each step `ap` to the step `ap'` takes the
whole verb (`ap = colMap`, `ap' = Op.eval`, `f` reading row `i` is the column form agreeing with the word form). -/
theorem fverbBy_map {α β : Type} {ap : Op → α → α → Except String α} {ap' : Op → β → β → Except String β}
    (f : α → β) (hap : ∀ {o x y z}, ap o x y = .ok z → ap' o (f x) (f y) = .ok (f z)) {k : UInt8} {x y z : α}
    (h : fverbBy ap k x y = .ok z) : fverbBy ap' k (f x) (f y) = .ok (f z) := by
  unfold fverbBy at h ⊢
  cases hk : fverbOne k with
  | some oc =>
    obtain ⟨o, c⟩ := oc
    simp only [hk, bind, Except.bind_eq_ok'] at h ⊢
    obtain ⟨q, hq, hz⟩ := h
    refine ⟨_, hap hq, ?_⟩
    clear hq hk
    induction c generalizing q with
    | nil => simp only [List.foldlM_nil, pure, Except.pure, Except.ok.injEq] at hz ⊢; rw [hz]
    | cons p c ih =>
      simp only [List.foldlM_cons, bind, Except.bind_eq_ok'] at hz ⊢
      obtain ⟨q', hq', hz⟩ := hz
      exact ⟨_, hap hq', ih _ hz⟩
  | none =>
  simp only [hk] at h ⊢
  by_cases c7 : (k == Ew.imod) = true <;> simp only [c7, ↓reduceIte, Bool.false_eq_true] at h ⊢
  · simp only [bind, Except.bind_eq_ok'] at h ⊢
    obtain ⟨q, hq, g, hg, m, hm, hz⟩ := h
    exact ⟨_, hap hq, _, hap hg, _, hap hm, hap hz⟩
  · cases h

/-- **`widen` reads a float word as `fval`**: the word `W` of the float atom `t` through `chain (widen t)` is the `f64`
word of the element `W` holds. -/
theorem widen_fval {t : QAtomicType} (hf : t = .f32 ∨ t = .f64) (W : UInt64) :
    ∃ X, chain (widen t) W = .ok X ∧ fval t (QAtomicType.ofBits t W) = some X := by
  rcases hf with rfl | rfl
  · refine ⟨Op.widen32 W, rfl, ?_⟩
    simp only [fval, QAtomicType.ofBits, Op.widen32, show W.toUInt32.toUInt64.toUInt32 = W.toUInt32 from
      UInt32.toNat_inj.mp (by simp)]
  · exact ⟨W, rfl, rfl⟩

/-- **`wideCol` reads a float column as `fval`**: row `i` of `wideCol t` of the column `x` is the `f64` word of element
`i` (an `f32` one read at `f32` and widened). -/
theorem wideCol_word {t : QAtomicType} {n : USize} (x : Arr t n) {a' : Enc} (h : wideCol t n x.enc = .ok a')
    (hf : t = .f32 ∨ t = .f64) (i : Fin n.toNat) : fval t (x.get i) = some ((raw .i64 n a')[i.1]?.getD 0) := by
  obtain ⟨X, hX, hfv⟩ := widen_fval hf ((raw t n x.enc)[i.1]?.getD 0)
  rw [Arr.get_word x (by rcases hf with rfl | rfl <;> decide) i, hfv]
  unfold wideCol at h
  split at h
  · rename_i he
    rcases hf with rfl | rfl
    · exact absurd he (by decide)
    simp only [pure, Except.pure, Except.ok.injEq] at h; subst h
    cases hX
    have hw := x.wf
    simp only [Option.some.injEq]
    cases hc : x.enc <;> rw [hc] at hw <;> simp_all [raw, Enc.WF, QAtomicType.width]
  · obtain ⟨x', y', v, w, hx', -, hv, hw, ho⟩ := (colMap_chain h).2.2.2 i.1 i.2
    rw [hX] at hx'; cases hx'; cases hv; cases hw
    simp only [ho, Option.getD_some, if_neg (show QAtomicType.i64 ≠ .u1 by decide)]

/-- **`colMap` of two float columns through `widen`**: row `i` of the answer is `chain post` of `op` on the operands'
`f64` words (`fval`). -/
theorem colMap_widen {t u : QAtomicType} {op : Op} {n : USize} {x y : Arr t n} {o : Enc}
    {post : List (Op × UInt64)} (hf : t = .f32 ∨ t = .f64) (hu : u ≠ .u1)
    (h : colMap op n x.enc y.enc u t (widen t) post = .ok o) (i : Fin n.toNat) :
    ∃ X Y v, fval t (x.get i) = some X ∧ fval t (y.get i) = some Y ∧ op.eval X Y = .ok v ∧
      chain post v = .ok (wd n o i) := by
  obtain ⟨X, Y, v, W, hX, hY, hv, hW, ho⟩ := (colMap_chain h).2.2.2 i.1 i.2
  have ht : t.ordNum.isSome := by rcases hf with rfl | rfl <;> decide
  obtain ⟨X', hX', hfx⟩ := widen_fval hf ((raw t n x.enc)[i.1]?.getD 0)
  obtain ⟨Y', hY', hfy⟩ := widen_fval hf ((raw t n y.enc)[i.1]?.getD 0)
  rw [hX] at hX'; rw [hY] at hY'; cases hX'; cases hY'
  rw [if_neg hu] at ho
  refine ⟨X, Y, v, by rw [Arr.get_word x ht i]; exact hfx, by rw [Arr.get_word y ht i]; exact hfy, hv, ?_⟩
  simp only [wd, ho, Option.getD_some]; exact hW

/-- **`fverbOne` is `fverb`**: a verb with one `Op` and a chain computes that `Op`, then the chain. -/
theorem fverb_one {k : UInt8} {o : Op} {c : List (Op × UInt64)} (h : fverbOne k = some (o, c)) (x y : UInt64) :
    fverb k x y = (o.eval x y >>= chain c) := by
  have hc : c = [] ∨ c = [(.ffloor, 0)] := by
    unfold fverbOne at h
    repeat' split at h
    all_goals first | (cases h; simp) | cases h
  simp only [fverb, fverbBy, h]
  rcases hc with rfl | rfl <;> cases o.eval x y <;> rfl

namespace Tab

/-- An atom holding a number (`storeFmt?`) is none of `general`, `sym`, `u1`. -/
theorem storeFmt_ne {u : QAtomicType} (h : u.storeFmt?.isSome) : u ≠ .general ∧ u ≠ .sym ∧ u ≠ .u1 := by
  cases u <;> revert h <;> decide

/-- A word read as an atom holding a number (`atomOfBits`) is `ofBits t` of it. -/
theorem of_atomOfBits {t : QAtomicType} (a : UInt64) (hg : t ≠ .general) (h : t.storeFmt?.isSome) :
    (Dep.Carrier.of? t (.atom (Column.atomOfBits t a hg))).getD default = QAtomicType.ofBits t a := by
  cases t <;> first | rfl | exact absurd h (by decide)

end Tab

/-- **`nanFlag` of an answer `w`** at a number atom `t`: the flag is a bit, set exactly where `w`'s word is not
`2^63`, and then `w`'s element is that word read at `t`. -/
theorem nanFlag_spec {t : QAtomicType} {n : USize} {w : Arr t n} {keep : Enc} (hf : t.storeFmt?.isSome)
    (hv : Kernel.Enc.Valid n w.enc) (h : nanFlag n w.enc = .ok keep) (i : Fin n.toNat) :
    wd n keep i < 2 ∧ ∀ v, (wd n keep i ≠ 0 ∧ w.get i = v) ↔
      (wd n w.enc i ≠ 0x8000000000000000 ∧ v = QAtomicType.ofBits t (wd n w.enc i)) := by
  obtain ⟨x, y, u, W, hx, -, hu, hW, hk⟩ := (colMap_chain h).2.2.2 i.1 i.2
  simp only [chain, List.foldlM_nil, pure, Except.pure, Except.ok.injEq] at hx
  subst hx
  have hu' : u = (raw .i64 n w.enc)[i.1]?.getD 0 :=
    (Except.ok.inj (show (Except.ok ((raw .i64 n w.enc)[i.1]?.getD 0) : Except String UInt64) = .ok u from hu)).symm
  subst hu'
  simp only [chain, List.foldlM_cons, List.foldlM_nil, ev_ne, bind, Except.bind, pure, Except.pure,
    Except.ok.injEq] at hW
  subst hW
  rw [if_pos rfl] at hk
  obtain ⟨hg, hs, -⟩ := Tab.storeFmt_ne hf
  obtain ⟨a, ha, -, ew⟩ := Arr.get_raw_atom w hv hg hs i
  have ew' : w.get i = QAtomicType.ofBits t a := by rw [ew, Tab.of_atomOfBits a hg hf]
  rw [ha, Option.getD_some] at hk
  have hka : wd n keep i = if nulWord ≠ a then 1 else 0 := by
    simp only [wd, hk, Option.getD_some]; split <;> rfl
  have hwa : wd n w.enc i = a := by simp only [wd, ha, Option.getD_some]
  rw [hka, hwa, ew', show nulWord = 0x8000000000000000 from rfl]
  refine ⟨bit_lt _, fun v => ?_⟩
  rw [bit_ne]
  constructor
  · rintro ⟨h1, rfl⟩; exact ⟨Ne.symm h1, rfl⟩
  · rintro ⟨h1, rfl⟩; exact ⟨Ne.symm h1, rfl⟩

/-- **`fstepCols t k` computes `stepAt t k` row by row** at a float atom `t`: `ftoCols_spec` of the `fverb` answer on
the operands' `f64` words (`wideCol_word`). -/
theorem fstepCols_spec {t : QAtomicType} {k : UInt8} {n : USize} {x y w : Arr t n} {keep : Enc}
    (hf : t = .f32 ∨ t = .f64) (h : fstepCols t k n x.enc y.enc = .ok (w, keep)) (i : Fin n.toNat) :
    wd n keep i < 2 ∧ ∀ v, (wd n keep i ≠ 0 ∧ w.get i = v) ↔ ∃ X Y R, fval t (x.get i) = some X ∧
      fval t (y.get i) = some Y ∧ fstep t k X Y = .ok R ∧ R ≠ 0x8000000000000000 ∧ v = QAtomicType.ofBits t R := by
  simp only [fstepCols, bind, Except.bind_eq_ok', pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
  obtain ⟨w', hw', kp, hkp, rfl, rfl⟩ := h
  -- row `i` of `w'` is `fstep t k` of the operands' `f64` words, in either branch
  have key : ∃ X Y, fval t (x.get i) = some X ∧ fval t (y.get i) = some Y ∧
      fstep t k X Y = .ok (wd n w'.enc i) ∧ Kernel.Enc.Valid n w'.enc := by
    unfold fstepArr at hw'
    split at hw'
    · rename_i o c hk
      have hc := colArr_ok hw'
      obtain ⟨X, Y, v, hX, hY, hv, hW⟩ := colMap_widen hf (by rcases hf with rfl | rfl <;> decide) hc i
      refine ⟨X, Y, hX, hY, ?_, (colMap_closed hc).1⟩
      have e : chain (c ++ [(.fto t, 0)]) v = (chain c v >>= fun q => (Op.fto t).eval 0 q) := by
        simp [chain, List.foldlM_append]
      rw [e] at hW
      show (fverb k X Y >>= fun q => (Op.fto t).eval 0 q) = _
      rw [fverb_one hk, hv]; exact hW
    · simp only [bind, Except.bind_eq_ok'] at hw'
      obtain ⟨a', ha, b', hb, r, hr, hw''⟩ := hw'
      have hr' := fverbBy_map (ap := fun o x y => colMap o n x y) (ap' := Op.eval) (fun e => wd n e i)
        (fun hc => (colMap_raw hc).2.2.2 i i.2) hr
      have hc := colArr_ok hw''
      obtain ⟨v0, hv0, hwi⟩ := (colMap_get hc).2 i i.2
      refine ⟨_, _, wideCol_word x ha hf i, wideCol_word y hb hf i, ?_, (colMap_closed hc).1⟩
      show (fverb k _ _ >>= fun q => (Op.fto t).eval 0 q) = _
      rw [show fverb k (wd n a' i) (wd n b' i) = .ok (wd n r i) from hr']
      rw [if_neg (by rcases hf with rfl | rfl <;> decide)] at hwi
      simp only [wd, hwi, Option.getD_some]; exact hv0
  obtain ⟨X, Y, hX, hY, hst, hv⟩ := key
  obtain ⟨h2, hn⟩ := nanFlag_spec (by rcases hf with rfl | rfl <;> decide) hv hkp i
  refine ⟨h2, fun v => (hn v).trans ?_⟩
  constructor
  · rintro ⟨h1, rfl⟩; exact ⟨X, Y, _, hX, hY, hst, h1, rfl⟩
  · rintro ⟨X', Y', R, hX', hY', hR, h1, rfl⟩
    rw [hX] at hX'; cases hX'; rw [hY] at hY'; cases hY'; rw [hst] at hR; cases hR; exact ⟨h1, rfl⟩

/-- **`fmapCols t u o` computes `o` row by row** from a float atom `t` to a number atom `u`, for an `o` that reads one
operand: `o` on the `f64` word (`colMap_widen`), then `Op.ofF64 u`, kept where that is not `2^63` (`nanFlag_spec`). -/
theorem fmapCols_spec {t u : QAtomicType} {o : Op} {n : USize} {x : Arr t n} {w : Arr u n} {keep : Enc}
    (hf : t = .f32 ∨ t = .f64) (hu : u.storeFmt?.isSome) (ho : o.readsAcc = false)
    (h : fmapCols t u o n x.enc = .ok (w, keep)) (i : Fin n.toNat) :
    wd n keep i < 2 ∧ ∀ v, (wd n keep i ≠ 0 ∧ w.get i = v) ↔ ∃ X Y R, fval t (x.get i) = some X ∧
      o.eval 0 X = .ok Y ∧ (Op.ofF64 u).eval 0 Y = .ok R ∧ R ≠ 0x8000000000000000 ∧ v = QAtomicType.ofBits u R := by
  simp only [fmapCols, bind, Except.bind_eq_ok', pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
  obtain ⟨w', hw', kp, hkp, rfl, rfl⟩ := h
  have hc := colArr_ok hw'
  obtain ⟨X, Y, v, hX, hY, hv, hW⟩ := colMap_widen hf (Tab.storeFmt_ne hu).2.2 hc i
  rw [hX] at hY; cases hY
  have hv' : o.eval 0 X = .ok v := by rw [← hv]; cases o <;> first | rfl | exact absurd ho (by decide)
  have hW' : (Op.ofF64 u).eval 0 v = .ok (wd n w'.enc i) := by
    simpa only [chain, List.foldlM_cons, List.foldlM_nil, bind_pure] using hW
  obtain ⟨h2, hn⟩ := nanFlag_spec hu (colMap_closed hc).1 hkp i
  refine ⟨h2, fun v' => (hn v').trans ?_⟩
  constructor
  · rintro ⟨h1, rfl⟩; exact ⟨X, v, _, hX, hv', hW', h1, rfl⟩
  · rintro ⟨X', Y', R, hX', hY', hR, h1, rfl⟩
    rw [hX] at hX'; cases hX'; rw [hv'] at hY'; cases hY'; rw [hW'] at hR; cases hR; exact ⟨h1, rfl⟩

/-- **`stepColsAt t k` computes `stepAt t k` row by row**, at every atom: `stepCols_spec` at `i64`, `fstepCols_spec` at
a float atom, and no answer at any other (`stepColsAt` refuses it). -/
theorem stepColsAt_spec {t : QAtomicType} {k : UInt8} {n : USize} {x y w : Arr t n} {keep : Enc}
    (h : stepColsAt t k n x.enc y.enc = .ok (w, keep)) (i : Fin n.toNat) :
    wd n keep i < 2 ∧ ∀ v, (wd n keep i ≠ 0 ∧ w.get i = v) ↔ Lang.stepAt t k (x.get i, y.get i) v := by
  cases t <;> simp only [stepColsAt, throw, throwThe, MonadExceptOf.throw, reduceCtorEq] at h
  · obtain ⟨h2, hv⟩ := stepCols_spec h i.1 i.2
    refine ⟨h2, fun v => ?_⟩
    rw [Arr.get_i64, Arr.get_i64, Arr.get_i64]
    exact (and_congr Iff.rfl eq_comm).trans (hv v)
  all_goals first | cases h | exact fstepCols_spec (by decide) h i

/-- `arithDen t k TU` pointwise: both operands in `dom TU`, then `stepAt t k ≫ TU`. -/
theorem Lang.arithDen_iff (t : QAtomicType) (k : UInt8) (TU : Core.Rel (Obj.atom t).El (Obj.atom t).El)
    (p : (Obj.atom t).El × (Obj.atom t).El) (w : (Obj.atom t).El) :
    Lang.arithDen t k TU p w ↔ (∃ c, TU p.1 c) ∧ (∃ c, TU p.2 c) ∧ ∃ v, Lang.stepAt t k p v ∧ TU v w := by
  simp only [Lang.arithDen, Core.Rel.comp, Core.Rel.inter, Core.Rel.recip, Core.Rel.id, Core.Rel.graph]
  constructor
  · rintro ⟨_, ⟨rfl, c, ⟨_, rfl, h1⟩, -⟩, _, ⟨rfl, c', ⟨_, rfl, h2⟩, -⟩, v, hs, hv⟩
    exact ⟨⟨c, h1⟩, ⟨c', h2⟩, v, hs, hv⟩
  · rintro ⟨⟨c, h1⟩, ⟨c', h2⟩, v, hs, hv⟩
    exact ⟨p, ⟨rfl, c, ⟨_, rfl, h1⟩, _, rfl, h1⟩, p, ⟨rfl, c', ⟨_, rfl, h2⟩, _, rfl, h2⟩, v, hs, hv⟩

/-- **`Tab.arith` answers `D ≫ arithDen k U`** (`Rel/Lang/Den.lean`): a row `(x, w)` of the answer is a row `(x, p)`
of `D` with `p`'s operands in `dom U`, `v = stepDen k p` (no null, no wrap), and `v U w`; `U X` agrees with `TU` at
the values `X`. -/
theorem Tab.arith_holds {K : Obj} {t : QAtomicType} {k : UInt8} {D : Tab K (.prod (.atom t) (.atom t))}
    {U : {n : USize} → Vals (.atom t) n → Except String (Tab (.atom t) (.atom t))}
    {TU : Core.Rel (Obj.atom t).El (Obj.atom t).El}
    (hU : ∀ n (X : Vals (.atom t) n) u, U X = .ok u → ∀ a v, (∃ i, X.row i = a) → (u.Holds a v ↔ TU a v))
    {T : Tab K (.atom t)} (h : D.arith t k U = .ok T) (x : K.El) (w : (Obj.atom t).El) :
    T.Holds x w ↔ ∃ p, D.Holds x p ∧ Lang.arithDen t k TU p w := by
  simp only [Tab.arith, bind, Except.bind_eq_ok'] at h
  obtain ⟨u₁, hu₁, du₁, hdu₁, E₁, hE₁, u₂, hu₂, du₂, hdu₂, E, hE, wb, hwb, h⟩ := h
  obtain ⟨w', b⟩ := wb
  simp only [bind, Except.bind_eq_ok'] at h
  obtain ⟨Kp, hKp, u₃, hu₃, hT⟩ := h
  have key : ∀ {A B : Obj} (T : Tab A B) a, (∃ i, T.key.row i = a) ↔ ∃ c, T.Holds a c :=
    fun _ _ => ⟨fun ⟨i, h⟩ => ⟨_, i, h, rfl⟩, fun ⟨_, i, h, _⟩ => ⟨i, h⟩⟩
  have k1 : ∀ x p, (∃ i, E₁.key.row i = (x, p)) ↔ D.Holds x p ∧ ∃ y, TU p.1 y := by
    intro x p
    rw [key]
    simp only [Tab.comp_holds hE₁]
    constructor
    · rintro ⟨c, b, ⟨i, hi, hb⟩, hdb⟩
      obtain ⟨rfl, y, hy⟩ := (Tab.dom_holds hdu₁ b c).1 hdb
      have hi' : D.key.row i = x ∧ D.val.row i = p := Prod.ext_iff.1 hi
      have e : b = p.1 := hb.symm.trans (congrArg Prod.fst hi'.2)
      exact ⟨⟨i, hi'.1, hi'.2⟩, y, e ▸ (hU _ _ _ hu₁ _ _ ⟨i, hb⟩).1 hy⟩
    · rintro ⟨⟨i, rfl, rfl⟩, y, hy⟩
      exact ⟨_, _, ⟨i, rfl, rfl⟩, (Tab.dom_holds hdu₁ _ _).2 ⟨rfl, y, (hU _ _ _ hu₁ _ _ ⟨i, rfl⟩).2 hy⟩⟩
  have k2 : ∀ x p, (∃ i, E.key.row i = (x, p)) ↔ D.Holds x p ∧ (∃ y, TU p.1 y) ∧ ∃ y, TU p.2 y := by
    intro x p
    rw [key]
    simp only [Tab.comp_holds hE]
    constructor
    · rintro ⟨c, b, ⟨i, hi, hb⟩, hdb⟩
      obtain ⟨rfl, y, hy⟩ := (Tab.dom_holds hdu₂ b c).1 hdb
      have h1 := (k1 x p).1 ⟨i, hi⟩
      have e : b = p.2 := hb.symm.trans (congrArg (fun q : K.El × ((Obj.atom t).El × (Obj.atom t).El) => q.2.2) hi)
      exact ⟨h1.1, h1.2, y, e ▸ (hU _ _ _ hu₂ _ _ ⟨i, hb⟩).1 hy⟩
    · rintro ⟨hD, h1, y, hy⟩
      obtain ⟨i, hi⟩ := (k1 x p).2 ⟨hD, h1⟩
      exact ⟨_, _, ⟨i, hi, rfl⟩, (Tab.dom_holds hdu₂ _ _).2 ⟨rfl, y, (hU _ _ _ hu₂ _ _ ⟨i, rfl⟩).2
        (by show TU (E₁.key.row i).2.2 y; rw [hi]; exact hy)⟩⟩
  have inP : ∀ {v}, Kp.Holds x v → ∃ j, Kp.val.row j = v := fun ⟨j, _, hj⟩ => ⟨j, hj⟩
  have st : ∀ (i : Fin E.n.toNat) v, ((Enc.raw .i64 E.n b)[i.1]?.getD 0 ≠ 0 ∧ Vals.row (A := .atom t) w' i = v) ↔
      Lang.stepAt t k (E.key.row i).2 v := (stepColsAt_spec hwb · |>.2)
  rw [Tab.comp_holds hT]
  have kp := Tab.keep_holds hKp (fun i hi => (stepColsAt_spec hwb ⟨i, hi⟩).1)
  constructor
  · rintro ⟨v, hk, hvw⟩
    obtain ⟨i, h0, hx, hv⟩ := (kp x v).1 hk
    obtain ⟨hD, h1, h2⟩ := (k2 x (E.key.row i).2).1 ⟨i, Prod.ext hx rfl⟩
    exact ⟨_, hD, (Lang.arithDen_iff t k _ _ w).2
      ⟨h1, h2, v, (st i v).1 ⟨h0, hv⟩, (hU _ _ _ hu₃ _ _ (inP hk)).1 hvw⟩⟩
  · rintro ⟨p, hD, ha⟩
    obtain ⟨h1, h2, v, hs, hvw⟩ := (Lang.arithDen_iff t k _ _ w).1 ha
    obtain ⟨i, hi⟩ := (k2 x p).2 ⟨hD, h1, h2⟩
    have e := (st i v).2 (by rw [hi]; exact hs)
    have hk := (kp x v).2 ⟨i, e.1, congrArg Prod.fst hi, e.2⟩
    exact ⟨v, hk, (hU _ _ _ hu₃ _ _ (inP hk)).2 hvw⟩

section Checks

/-- The `Int64`s `l.map f` as an `i64` column of stored words (`Arr.ofFn`). -/
private def colOf {α : Type} (f : α → Int64) (l : List α) : Arr .i64 l.length.toUSize :=
  Arr.ofFn .i64 _ (fun i => ((l.map f).getD i.1 0).toUInt64)

/-- The rows `l` as a table keyed by the first and valued by the pair. -/
private def dTab (l : List (Int64 × Int64 × Int64)) : Tab .long (.prod .long .long) :=
  ⟨_, colOf (·.1) l, (colOf (·.2.1) l, colOf (·.2.2) l)⟩

/-- The coreflexive on the elements `u`. -/
private def uTab (u : List Int64) : Tab .long .long := ⟨_, colOf id u, colOf id u⟩

private def sameSet {α : Type} [BEq α] (a b : List α) : Bool := a.all b.contains && b.all a.contains

/-- `stepDen k`'s exactness test (`Rel/Lang/Den.lean`), as a `Bool`. -/
private def exactB (k : UInt8) (a b w : Int64) : Bool :=
  if k == Ew.add then (decide (0 ≤ b) == decide (a ≤ w)) else if k == Ew.sub then (decide (0 ≤ b) == decide (w ≤ a))
  else if k == Ew.mul then (Ew.intStep Ew.idiv Alg.nul w a == b || a == 0) else true

/-- Whether `Tab.arith k` answers `D ≫ arithDen k U` on lists. -/
private def arithOk (k : UInt8) (d : List (Int64 × Int64 × Int64)) (u : List Int64) : Bool :=
  let inU (x : Int64) := u.contains x
  let spec := d.filterMap fun (x, a, b) => let w := Ew.intStep k Alg.nul a b
    if inU a && inU b && w != Alg.nul && exactB k a b w && inU w then some (x, w) else none
  match (dTab d).arith .i64 k (fun _ => pure (uTab u)) with
  | .ok T => sameSet T.toList spec
  | .error _ => false

/-- Whether `Tab.succ` answers `D ≫ succDen U` on lists. -/
private def succOk (d : List (Int64 × Int64)) (u : List Int64) : Bool :=
  let inU (x : Int64) := u.contains x
  let spec := d.filterMap fun (x, v) => let w := Ew.intStep Ew.add Alg.nul v 1
    if inU v && inU w then some (x, w) else none
  match (⟨_, colOf (·.1) d, colOf (·.2) d⟩ : Tab .long .long).succ (fun _ => pure (uTab u)) with
  | .ok T => sameSet T.toList spec
  | .error _ => false

/-- Operands and answers: the null `Int64.minValue`, its neighbour, `Int64.maxValue`, zero, signs, a value outside
`U`, so wraps, zero divisors, null operands and answers outside `U` all occur. -/
private def us : List Int64 := [Int64.minValue, Int64.minValue + 1, Int64.maxValue, 0, 1, 2, 3, 4, 6, -1, -2, -3,
  -4, 7, -7, 12, -12, 5, -5, 21, -21, 9]
/-- Pairs of `us` (and `100`, outside `U`), keyed `0, 1, …`, with a duplicate row and two rows of one key. -/
private def ds : List (Int64 × Int64 × Int64) :=
  let ps := [(Int64.minValue, 1), (1, Int64.minValue), (Int64.maxValue, 1), (Int64.maxValue, -1), (Int64.minValue + 1, -1),
    (Int64.minValue + 1, -2), (-7, 2), (7, -2), (-7, 3), (7, 0), (0, 0), (6, 3), (-12, -3), (3, 4), (100, 1), (1, 100),
    (Int64.maxValue, 2), (Int64.minValue, -1), (Int64.minValue, 0), (-1, -1), (2, 2)]
  (List.range ps.length).zip ps |>.map (fun (i, p) => (Int64.ofNat i, p)) |> (· ++ [(0, Int64.minValue, 1), (0, 4, 5)])

-- every verb of `Op.table` (`+ * − div mod max min`) on all of `ds`, an empty `D`, an empty `U`, and `U` without
-- the null (so a wrapped `max + 1` is not in `U`)
#guard [Ew.add, Ew.sub, Ew.mul, Ew.idiv, Ew.imod, Ew.greater, Ew.lesser].all fun k =>
  arithOk k ds us && arithOk k [] us && arithOk k ds [] && arithOk k ds (us.filter (· != Int64.minValue))
-- `%` (`Ew.divide`) has no step at `i64`, which the elaborator refuses before: here it is the error naming the code
#guard (dTab ds).arith .i64 Ew.divide (fun _ => pure (uTab us)) matches .error _
-- `succ`: the top of `U` goes nowhere, `maxValue` to the null only where `U` holds it, the null to itself
#guard succOk ((List.range us.length).zip us |>.map fun (i, u) => (Int64.ofNat i, u)) us
#guard succOk [(1, 3), (1, 3), (2, Int64.maxValue), (3, Int64.minValue), (4, 9), (5, 100)] [3, 4, 9, Int64.maxValue]
#guard succOk [(1, 3), (2, 4)] [] && succOk [] us

end Checks

end Rel
