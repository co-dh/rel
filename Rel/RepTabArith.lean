module

public import Rel.Run.Arith
public import Rel.RepTabComp
public import Rel.RepSetOps
public import Rel.Lang.Den

-- exposed: every def body is a spec a downstream `rfl`/`decide`/`simp` may unfold (PLAN W.8)
@[expose] public section

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
theorem stepCols_spec {k : UInt8} {n : USize} {p q : Arr .i64 n} {w : Arr .i64 n} {keep : Enc}
    (h : stepCols k n p q = .ok (w, keep)) (i : Nat) (hi : i < n.toNat) :
    wd n keep i < 2 ∧ ∀ v, (wd n keep i ≠ 0 ∧ v = (wd n w.enc i).toInt64) ↔
      Lang.stepDen k ((wd n p.enc i).toInt64, (wd n q.enc i).toInt64) v := by
  have cm : ∀ {op x y e}, colMap op n x y = .ok e → ∀ {r}, op.eval (wd n x i) (wd n y i) = .ok r →
      (hk : kscanStream op [(n, x), (n, y)] [] [] = false := by lockstep) → (hn : op ≠ .null := by decide) →
      (hF : op.nulFold = none ∨ ∀ p ∈ [(n, x), (n, y)], hasNul p.2 = false := by nulfree) → wd n e i = r :=
    fun hc _ he hk hn hF => (Except.ok.inj (he.symm.trans ((colMap_raw hc hk hn hF).2.2.2 i hi))).symm
  have cp : ∀ {op op' : Op} {c x e}, (∀ y, op.eval c y = op'.eval y c) →
      colMap .first n x x .i64 .i64 [] [(op, c)] = .ok e → ∀ {r}, op'.eval (wd n x i) c = .ok r → wd n e i = r :=
    fun hop hc _ he => (Except.ok.inj (he.symm.trans ((hop _).symm.trans ((colMap_post hc).2 i hi)))).symm
  have sne : ∀ y : UInt64, Op.ne.eval nulWord y = Op.ne.eval y nulWord := fun y => by simp only [Op.eval, bne_comm]
  have seq : ∀ y : UInt64, Op.eq.eval 0 y = Op.eq.eval y 0 := fun y => by simp only [Op.eval, BEq.comm]
  have sge : ∀ y : UInt64, Op.le.eval 0 y = Op.ge.eval y 0 := fun _ => rfl
  have ofA : ∀ A : UInt64, ∃ x : Int64, x.toUInt64 = A := fun A => ⟨A.toInt64, UInt64.toUInt64_toInt64 A⟩
  simp only [stepCols, bind, Except.bind_eq_ok'] at h
  obtain ⟨na, hna, nb, hnb, bo, hbo, h⟩ := h
  by_cases e1 : k = Ew.add
  · subst e1
    simp (config := { decide := true }) only [Ew.add, Ew.sub, Ew.mul, Ew.idiv, if_true, if_false,
      Bool.or_false, bind, Except.bind_eq_ok', pure, Except.pure, Except.ok.injEq,
      Prod.mk.injEq] at h
    obtain ⟨w', hw', ord, hord, g, hg, ex, hex, nw, hnw, t1, ht1, kp, hkp, rfl, rfl⟩ := h
    rw [cm hkp rfl, cm ht1 rfl, cm hbo rfl, cp sne hna (ev_ne _ _), cp sne hnb (ev_ne _ _), cp sne hnw (ev_ne _ _),
      cm hex (ev_eq _ _), cp sge hg (ev_ge _ _), cm hord (ev_le _ _), cm (colArr_ok hw') rfl]
    simp only [bit_and, bit_eq]
    refine ⟨bit_lt _, fun v => ?_⟩
    rw [bit_ne]
    obtain ⟨x, hx⟩ := ofA (wd n p.enc i); obtain ⟨y, hy⟩ := ofA (wd n q.enc i); rw [← hx, ← hy]
    simp only [nulWord_eq, ← Int64.toUInt64_add, ne_eq, toU_inj, Int64.toInt64_toUInt64,
      show UInt64.toInt64 0 = 0 from rfl]
    exact add_iff x y v
  by_cases e2 : k = Ew.sub
  · subst e2
    simp (config := { decide := true }) only [Ew.sub, Ew.lesser, if_true, if_false, Bool.true_or,
      Bool.false_or, Bool.or_false, Bool.or_true, bind, Except.bind_eq_ok', pure, Except.pure,
      Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨w', hw', ord, hord, g, hg, ex, hex, nw, hnw, t1, ht1, kp, hkp, rfl, rfl⟩ := h
    rw [cm hkp rfl, cm ht1 rfl, cm hbo rfl, cp sne hna (ev_ne _ _), cp sne hnb (ev_ne _ _), cp sne hnw (ev_ne _ _),
      cm hex (ev_eq _ _), cp sge hg (ev_ge _ _), cm hord (ev_le _ _), cm (colArr_ok hw') rfl]
    simp only [bit_and, bit_eq]
    refine ⟨bit_lt _, fun v => ?_⟩
    rw [bit_ne]
    obtain ⟨x, hx⟩ := ofA (wd n p.enc i); obtain ⟨y, hy⟩ := ofA (wd n q.enc i); rw [← hx, ← hy]
    simp only [nulWord_eq, ← Int64.toUInt64_sub, ne_eq, toU_inj, Int64.toInt64_toUInt64,
      show UInt64.toInt64 0 = 0 from rfl]
    exact sub_iff x y v
  by_cases e3 : k = Ew.mul
  · subst e3
    simp (config := { decide := true }) only [Ew.add, Ew.sub, Ew.mul, if_true, if_false,
      Bool.false_or, Bool.or_false, Bool.or_true, bind, Except.bind_eq_ok', pure, Except.pure,
      Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨w', hw', a0, ha0, o1, ho1, dv, hdv, e0, he0, ex, hex, nw, hnw, t1, ht1, kp, hkp, rfl, rfl⟩ := h
    have h0 : wd n o1 i ≠ 0 := by rw [cm ho1 rfl, cp seq ha0 (ev_eq _ _), or_zero]; exact one_ne _
    rw [cm hkp rfl, cm ht1 rfl, cm hbo rfl, cp sne hna (ev_ne _ _), cp sne hnb (ev_ne _ _), cp sne hnw (ev_ne _ _),
      cm hex rfl, cm he0 (ev_eq _ _), cm hdv (ev_div _ _ h0), cm ho1 rfl, cp seq ha0 (ev_eq _ _),
      cm (colArr_ok hw') rfl]
    simp only [bit_and, bit_or, or_zero]
    refine ⟨bit_lt _, fun v => ?_⟩
    rw [bit_ne]
    obtain ⟨x, hx⟩ := ofA (wd n p.enc i); obtain ⟨y, hy⟩ := ofA (wd n q.enc i); rw [← hx, ← hy]
    simp only [nulWord_eq, ← Int64.toUInt64_mul, toU_eq_zero, toU_ite1, ne_eq, toU_inj, Int64.toInt64_toUInt64]
    exact mul_iff x y v
  by_cases e4 : k = Ew.idiv ∨ k = Ew.imod
  · rcases e4 with rfl | rfl
    all_goals
      simp (config := { decide := true }) only [Ew.add, Ew.sub, Ew.mul, Ew.idiv, Ew.imod, if_true,
        if_false, Bool.or_false, bind, Except.bind_eq_ok', pure, Except.pure, Except.ok.injEq,
        Prod.mk.injEq] at h
      obtain ⟨b0, hb0, o, ho, w', hw', nb0, hnb0, t, ht, nw, hnw, kp, hkp, rfl, rfl⟩ := h
      have h0 : wd n o i ≠ 0 := by rw [cm ho rfl, cp seq hb0 (ev_eq _ _), or_zero]; exact one_ne _
      rw [cm hkp rfl, cm ht rfl, cm hbo rfl, cp sne hna (ev_ne _ _), cp sne hnb (ev_ne _ _), cp sne hnw (ev_ne _ _),
        cm hnb0 (ev_not _ _), cm (colArr_ok hw') (by first | exact ev_div _ _ h0 | exact ev_mod _ _ h0), cm ho rfl,
        cp seq hb0 (ev_eq _ _)]
      simp only [bit_and, bit_not, or_zero]
      refine ⟨bit_lt _, fun v => ?_⟩
      rw [bit_ne]
      obtain ⟨x, hx⟩ := ofA (wd n p.enc i); obtain ⟨y, hy⟩ := ofA (wd n q.enc i); rw [← hx, ← hy]
      simp only [nulWord_eq, toU_eq_zero, toU_ite1, ne_eq, toU_inj, Int64.toInt64_toUInt64]
      first | exact div_iff x y v | exact mod_iff x y v
  by_cases e5 : k = Ew.greater ∨ k = Ew.lesser
  · rcases e5 with rfl | rfl
    all_goals
      simp (config := { decide := true }) only [Ew.add, Ew.sub, Ew.mul, Ew.imod, Ew.greater,
        Ew.lesser, if_true, if_false, Bool.false_or, Except.bind_eq_ok', pure, Except.pure,
        Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨w', hw', nw, hnw, rfl, rfl⟩ := h
      rw [cp sne hnw (ev_ne _ _), cm (colArr_ok hw') (by first | exact ev_max _ _ | exact ev_min _ _) (hF := Or.inr (nulFree₂ p.plain q.plain))]
      refine ⟨bit_lt _, fun v => ?_⟩
      rw [bit_ne]
      obtain ⟨x, hx⟩ := ofA (wd n p.enc i); obtain ⟨y, hy⟩ := ofA (wd n q.enc i); rw [← hx, ← hy]
      simp only [nulWord_eq, Int64.toInt64_toUInt64, toU_ite, ne_eq, toU_inj]
      first | exact max_iff x y v | exact min_iff x y v
  simp only [Bool.or_eq_true, beq_iff_eq, e1, e2, e3, false_or, if_false] at h
  rw [if_neg (by simpa using e4), if_neg (by simpa using e5)] at h
  cases h

/-- **`succCol` is `Ew.intStep`'s `u + 1`** at each row (the null to itself). -/
theorem Tab.succCol_row {n : USize} {X : Vals .long n} {s : Arr .i64 n} (hs : Tab.succCol n X.enc = .ok s)
    (i : Fin n.toNat) : ValsB.row (A := .long) s i = Ew.intStep Ew.add Alg.nul (X.row i) 1 := by
  simp only [Tab.succCol, bind, Except.bind_eq_ok'] at hs
  obtain ⟨ne, hne, hs⟩ := hs
  show s.get i = Ew.intStep Ew.add Alg.nul (Arr.get X i) 1
  rw [Arr.get_i64, Arr.get_i64]
  have r1 := (colMap_raw (colArr_ok hs)).2.2.2 i i.2
  have r2 := (colMap_post hne).2 i i.2
  rw [ev_ne] at r2
  simp only [ne_comm (a := nulWord)] at r2
  rw [← Except.ok.inj r2] at r1
  rw [← Except.ok.inj r1]
  generalize (raw .i64 n X.enc)[i.1]?.getD 0 = A
  obtain ⟨a, rfl⟩ : ∃ a : Int64, a.toUInt64 = A := ⟨A.toInt64, UInt64.toUInt64_toInt64 A⟩
  by_cases ha : a = Alg.nul
  · subst ha; decide
  · have : a.toUInt64 ≠ nulWord := fun e => ha ((toU_inj _ _).1 e)
    simp (config := {decide := true}) only [ne_eq, this, not_false_eq_true, if_true, Ew.intStep_add]
    show (a + 1).toUInt64.toInt64 = _
    simp [ha]

/-- **`colArr .mix` is `Op.mixWord`** at each row. -/
theorem Tab.mixCol_row {n : USize} {X : Vals .long n} {s : Arr .i64 n} (hs : colArr .mix n X.enc X.enc = .ok s)
    (i : Fin n.toNat) : ValsB.row (A := .long) s i = (Op.mixWord (X.row i).toUInt64).toInt64 := by
  show s.get i = (Op.mixWord (Arr.get X i).toUInt64).toInt64
  rw [Arr.get_i64, Arr.get_i64, UInt64.toUInt64_toInt64]
  have r1 := (colMap_raw (colArr_ok hs)).2.2.2 i i.2
  simp only [Op.eval] at r1
  rw [← Except.ok.inj r1]

/-! ### The value verbs at a float atom: `fstepCols` computes `stepAt` -/

/-- Every `Op` of a verb `fverbOne` names is a unary or float `Op`, none the stream `.first`. -/
theorem fverbOne_ne {k : UInt8} {o : Op} {c : List (Op × UInt64)} (h : fverbOne k = some (o, c)) :
    o ≠ .first ∧ o ≠ .null ∧ o.nulFold = none ∧ ∀ p ∈ c, p.1 ≠ .first ∧ p.1 ≠ .null ∧ p.1.nulFold = none := by
  unfold fverbOne at h
  repeat' split at h
  all_goals first | (cases h; decide) | cases h

/-- **`fverbBy` commutes with a reading of its operands**: a map `f` taking each step `ap` to the step `ap'` takes the
whole verb (`ap = colMap`, `ap' = Op.eval`, `f` reading row `i` is the column form agreeing with the word form). The
steps `fverbBy` applies are none `.first` or `.null` (`fverbOne_ne`), and `hap` need hold only there (`colMap .first` is a stream). -/
theorem fverbBy_map {α β : Type} {ap : Op → α → α → Except String α} {ap' : Op → β → β → Except String β}
    (f : α → β) (hap : ∀ {o x y z}, o ≠ .first → o ≠ .null → o.nulFold = none → ap o x y = .ok z → ap' o (f x) (f y) = .ok (f z)) {k : UInt8}
    {x y z : α} (h : fverbBy ap k x y = .ok z) : fverbBy ap' k (f x) (f y) = .ok (f z) := by
  unfold fverbBy at h ⊢
  cases hk : fverbOne k with
  | some oc =>
    obtain ⟨o, c⟩ := oc
    obtain ⟨hon, hnn, hof, hcn⟩ := fverbOne_ne hk
    simp only [hk, bind, Except.bind_eq_ok'] at h ⊢
    obtain ⟨q, hq, hz⟩ := h
    refine ⟨_, hap hon hnn hof hq, ?_⟩
    clear hq hk hon
    induction c generalizing q with
    | nil => simp only [List.foldlM_nil, pure, Except.pure, Except.ok.injEq] at hz ⊢; rw [hz]
    | cons p c ih =>
      simp only [List.foldlM_cons, bind, Except.bind_eq_ok'] at hz ⊢
      obtain ⟨q', hq', hz⟩ := hz
      exact ⟨_, hap (hcn p (by simp)).1 (hcn p (by simp)).2.1 (hcn p (by simp)).2.2 hq', ih (fun p' hp' => hcn p' (by simp [hp'])) _ hz⟩
  | none =>
  simp only [hk] at h ⊢
  by_cases c7 : (k == Ew.imod) = true <;> simp only [c7, ↓reduceIte, Bool.false_eq_true] at h ⊢
  · simp only [bind, Except.bind_eq_ok'] at h ⊢
    obtain ⟨q, hq, g, hg, m, hm, hz⟩ := h
    exact ⟨_, hap (by decide) (by decide) (by decide) hq, _, hap (by decide) (by decide) (by decide) hg, _, hap (by decide) (by decide) (by decide) hm, hap (by decide) (by decide) (by decide) hz⟩
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
  · rename_i he
    have hs : kscanStream .first [(n, x.enc), (n, x.enc)] (widen t) [] = false := by
      rcases hf with rfl | rfl
      · simp [kscanStream, widen]
      · exact absurd (by decide) he
    obtain ⟨x', y', v, w, hx', -, hv, hw, ho⟩ := (colMap_chain h hs).2.2.2 i.1 i.2
    rw [hX] at hx'; cases hx'; cases hv; cases hw
    simp only [ho, Option.getD_some, if_neg (show QAtomicType.i64 ≠ .u1 by decide)]

/-- **`colMap` of two float columns through `widen`**: row `i` of the answer is `chain post` of `op` on the operands'
`f64` words (`fval`). -/
theorem colMap_widen {t u : QAtomicType} {op : Op} {n : USize} {x y : Arr t n} {o : Enc}
    {post : List (Op × UInt64)} (hf : t = .f32 ∨ t = .f64) (hu : u ≠ .u1)
    (h : colMap op n x.enc y.enc u t (widen t) post = .ok o) (i : Fin n.toNat)
    (hs : kscanStream op [(n, x.enc), (n, y.enc)] (widen t) post = false := by lockstep)
    (hn : op ≠ .null := by decide)
    (hF : op.nulFold = none ∨ ∀ p ∈ [(n, x.enc), (n, y.enc)], hasNul p.2 = false := Or.inr (nulFree₂ x.plain y.plain)) :
    ∃ X Y v, fval t (x.get i) = some X ∧ fval t (y.get i) = some Y ∧ op.eval X Y = .ok v ∧
      chain post v = .ok (wd n o i) := by
  obtain ⟨X, Y, v, W, hX, hY, hv, hW, ho⟩ := (colMap_chain h hs hn hF).2.2.2 i.1 i.2
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
    (h : nanFlag n w.enc = .ok keep) (i : Fin n.toNat) :
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
  obtain ⟨hg, -, -⟩ := Tab.storeFmt_ne hf
  obtain ⟨a, ha, -, ew⟩ := Arr.get_raw_atom w hg i
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
    (hf : t = .f32 ∨ t = .f64) (h : fstepCols t k n x y = .ok (w, keep)) (i : Fin n.toNat) :
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
      have hs := kscanStream_ne (fverbOne_ne hk).1 [(n, x.enc), (n, y.enc)] (widen t) (c ++ [(.fto t, 0)])
      obtain ⟨X, Y, v, hX, hY, hv, hW⟩ := colMap_widen hf (by rcases hf with rfl | rfl <;> decide) hc i hs (fverbOne_ne hk).2.1
      refine ⟨X, Y, hX, hY, ?_, (colMap_closed hs hc (Or.inr (nulFree₂ x.plain y.plain))).1⟩
      have e : chain (c ++ [(.fto t, 0)]) v = (chain c v >>= fun q => (Op.fto t).eval 0 q) := by
        simp [chain, List.foldlM_append]
      rw [e] at hW
      show (fverb k X Y >>= fun q => (Op.fto t).eval 0 q) = _
      rw [fverb_one hk, hv]; exact hW
    · simp only [bind, Except.bind_eq_ok'] at hw'
      obtain ⟨a', ha, b', hb, r, hr, hw''⟩ := hw'
      have hr' := fverbBy_map (ap := fun o x y => colMap o n x y) (ap' := Op.eval) (fun e => wd n e i)
        (fun hne hnn hnf hc => (colMap_raw hc (kscanStream_ne hne _ _ _) hnn (Or.inl hnf)).2.2.2 i i.2) hr
      have hc := colArr_ok hw''
      obtain ⟨v0, hv0, hwi⟩ := (colMap_get hc (by lockstep) nofun).2 i i.2
      refine ⟨_, _, wideCol_word x ha hf i, wideCol_word y hb hf i, ?_, (colMap_closed (by lockstep) hc).1⟩
      show (fverb k _ _ >>= fun q => (Op.fto t).eval 0 q) = _
      rw [show fverb k (wd n a' i) (wd n b' i) = .ok (wd n r i) from hr']
      rw [if_neg (by rcases hf with rfl | rfl <;> decide)] at hwi
      simp only [wd, hwi, Option.getD_some]; exact hv0
  obtain ⟨X, Y, hX, hY, hst, hv⟩ := key
  obtain ⟨h2, hn⟩ := nanFlag_spec (by rcases hf with rfl | rfl <;> decide) hkp i
  refine ⟨h2, fun v => (hn v).trans ?_⟩
  constructor
  · rintro ⟨h1, rfl⟩; exact ⟨X, Y, _, hX, hY, hst, h1, rfl⟩
  · rintro ⟨X', Y', R, hX', hY', hR, h1, rfl⟩
    rw [hX] at hX'; cases hX'; rw [hY] at hY'; cases hY'; rw [hst] at hR; cases hR; exact ⟨h1, rfl⟩

/-- An `Op` that reads no running value answers the same from any: `eval a x = eval 0 x`. -/
theorem Op.eval_acc {o : Op} (ho : o.readsAcc = false) (a x : UInt64) : o.eval a x = o.eval 0 x := by
  cases o <;> first | rfl | exact absurd ho (by decide)

/-- **`fmapCols t u o` computes `o` row by row** from a float atom `t` to a number atom `u` on the operand rows `x`,
`y`: `o` on their `f64` words (`colMap_widen`), then `Op.ofF64 u`, kept where that is not `2^63` (`nanFlag_spec`). -/
theorem fmapCols_spec {t u : QAtomicType} {o : Op} {n : USize} {x y : Arr t n} {w : Arr u n} {keep : Enc}
    (hf : t = .f32 ∨ t = .f64) (hu : u.storeFmt?.isSome)
    (h : fmapCols t u o n x y = .ok (w, keep)) (i : Fin n.toNat) (ho : o ≠ .first := by decide)
    (hn : o ≠ .null := by decide) :
    wd n keep i < 2 ∧ ∀ v, (wd n keep i ≠ 0 ∧ w.get i = v) ↔ ∃ X X' Y R, fval t (x.get i) = some X ∧
      fval t (y.get i) = some X' ∧ o.eval X X' = .ok Y ∧ (Op.ofF64 u).eval 0 Y = .ok R ∧ R ≠ 0x8000000000000000 ∧
      v = QAtomicType.ofBits u R := by
  simp only [fmapCols, bind, Except.bind_eq_ok', pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
  obtain ⟨w', hw', kp, hkp, rfl, rfl⟩ := h
  have hc := colArr_ok hw'
  have hs := kscanStream_ne ho [(n, x.enc), (n, y.enc)] (widen t) [(.ofF64 u, 0)]
  obtain ⟨X, X', v, hX, hX', hv, hW⟩ := colMap_widen hf (Tab.storeFmt_ne hu).2.2 hc i hs hn
  have hW' : (Op.ofF64 u).eval 0 v = .ok (wd n w'.enc i) := by
    simpa only [chain, List.foldlM_cons, List.foldlM_nil, bind_pure] using hW
  obtain ⟨h2, hn⟩ := nanFlag_spec hu hkp i
  refine ⟨h2, fun v' => (hn v').trans ?_⟩
  constructor
  · rintro ⟨h1, rfl⟩; exact ⟨X, X', v, _, hX, hX', hv, hW', h1, rfl⟩
  · rintro ⟨X₁, X₂, Y', R, hX₁, hX₂, hY', hR, h1, rfl⟩
    rw [hX] at hX₁; cases hX₁; rw [hX'] at hX₂; cases hX₂; rw [hv] at hY'; cases hY'; rw [hW'] at hR; cases hR
    exact ⟨h1, rfl⟩

/-- **`stepColsAt t k` computes `stepAt t k` row by row**, at every atom: `stepCols_spec` at `i64`, `fstepCols_spec` at
a float atom, and no answer at any other (`stepColsAt` refuses it). -/
theorem stepColsAt_spec {t : QAtomicType} {k : UInt8} {n : USize} {x y w : Arr t n} {keep : Enc}
    (h : stepColsAt t k n x y = .ok (w, keep)) (i : Fin n.toNat) :
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

end Rel
