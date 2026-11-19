import Rel.Run.Arith
import Rel.Run.Alg
import Rel.RepTabComp
import Rel.RepSetOps
import Rel.Lang.Den

/-! Checks of `Tab.arith` and `Tab.succ` (`Rel/Run/Arith.lean`) against the meanings `arithDen`, `succDen` of
`Rel/Lang/Den.lean`, read on lists, and against the old `Alg.arith`, `Alg.succ` on the same data. -/

namespace Rel
open Rel.Ext Rel.Kernel Rel.Verify Ext.Enc
/-- Word `i` of the `n`-word `i64` column `e`. -/
private abbrev wd (n : USize) (e : Enc) (i : Nat) : UInt64 := (raw .i64 n e)[i]?.getD 0

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
  simp (config := {decide := true}) only [Lang.stepDen, Ew.intStep, Ew.add, if_true, beq_iff_eq, Bool.or_eq_true]
  by_cases ha : a = Alg.nul <;> by_cases hb : b = Alg.nul <;> simp [ha, hb] <;> grind
private theorem sub_iff (a b v : Int64) :
    (((a ≠ Alg.nul ∧ b ≠ Alg.nul) ∧ a - b ≠ Alg.nul) ∧ (0 ≤ b ↔ a - b ≤ a)) ∧ v = a - b ↔
      Lang.stepDen Ew.sub (a, b) v := by
  simp (config := {decide := true}) only [Lang.stepDen, Ew.intStep, Ew.sub, if_true, if_false, beq_iff_eq,
    Bool.or_eq_true]
  by_cases ha : a = Alg.nul <;> by_cases hb : b = Alg.nul <;> simp [ha, hb] <;> grind
private theorem mul_iff (a b v : Int64) : (((a ≠ Alg.nul ∧ b ≠ Alg.nul) ∧ a * b ≠ Alg.nul) ∧
    (Int64.ofInt (Int.fdiv (a * b).toInt (if a = 0 then 1 else a).toInt) = b ∨ a = 0)) ∧ v = a * b ↔
      Lang.stepDen Ew.mul (a, b) v := by
  simp (config := {decide := true}) only [Lang.stepDen, Ew.intStep, Ew.mul, Ew.idiv, Ew.add, Ew.sub, if_true,
    if_false, beq_iff_eq, Bool.or_eq_true]
  have hn0 : (0 : Int64) ≠ Alg.nul := by decide
  by_cases ha : a = Alg.nul <;> by_cases hb : b = Alg.nul <;> by_cases h0 : a = 0 <;>
    simp only [ha, hb, h0, hn0, if_true, if_false, or_false, or_true, true_or, not_false_eq_true,
      not_true_eq_false, and_true, true_and, and_false, false_and, ne_eq]
  all_goals constructor <;> intro h <;> grind
private theorem div_iff (a b v : Int64) : (((a ≠ Alg.nul ∧ b ≠ Alg.nul) ∧ ¬ b = 0) ∧
    Int64.ofInt (Int.fdiv a.toInt (if b = 0 then 1 else b).toInt) ≠ Alg.nul) ∧
      v = Int64.ofInt (Int.fdiv a.toInt (if b = 0 then 1 else b).toInt) ↔ Lang.stepDen Ew.idiv (a, b) v := by
  simp (config := {decide := true}) only [Lang.stepDen, Ew.intStep, Ew.idiv, if_true, beq_iff_eq, Bool.or_eq_true]
  by_cases ha : a = Alg.nul <;> by_cases hb : b = Alg.nul <;> by_cases h0 : b = 0 <;> simp [ha, hb, h0] <;> grind
private theorem mod_iff (a b v : Int64) : (((a ≠ Alg.nul ∧ b ≠ Alg.nul) ∧ ¬ b = 0) ∧
    Int64.ofInt (Int.fmod a.toInt (if b = 0 then 1 else b).toInt) ≠ Alg.nul) ∧
      v = Int64.ofInt (Int.fmod a.toInt (if b = 0 then 1 else b).toInt) ↔ Lang.stepDen Ew.imod (a, b) v := by
  simp (config := {decide := true}) only [Lang.stepDen, Ew.intStep, Ew.imod, Ew.idiv, Ew.add, Ew.sub, Ew.mul,
    if_true, if_false, beq_iff_eq, Bool.or_eq_true]
  by_cases ha : a = Alg.nul <;> by_cases hb : b = Alg.nul <;> by_cases h0 : b = 0 <;> simp [ha, hb, h0] <;> grind
private theorem max_iff (a b v : Int64) : (if a < b then b else a) ≠ Alg.nul ∧ v = (if a < b then b else a) ↔
    Lang.stepDen Ew.greater (a, b) v := by
  simp (config := {decide := true}) only [Lang.stepDen, Ew.intStep, Ew.greater, if_true, beq_iff_eq, Bool.or_eq_true]
  grind
private theorem min_iff (a b v : Int64) : (if b < a then b else a) ≠ Alg.nul ∧ v = (if b < a then b else a) ↔
    Lang.stepDen Ew.lesser (a, b) v := by
  simp (config := {decide := true}) only [Lang.stepDen, Ew.intStep, Ew.lesser, Ew.greater, if_true, if_false,
    beq_iff_eq, Bool.or_eq_true]
  grind

private theorem nulWord_eq : nulWord = Alg.nul.toUInt64 := rfl

theorem colArr_ok {op : Op} {n : USize} {a b : Enc} {w : Arr .i64 n} (h : colArr op n a b = .ok w) :
    colMap op n a b = .ok w.enc := by
  unfold colArr at h; split at h
  · cases h; rename_i o hc; exact hc
  · cases h

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

/-- Whether `Tab.arith k` answers `D ≫ arithDen k U` on lists, and agrees with the old `Alg.arith` on the pairs of
`D` whose operands are in `U`, then `≫ U`. -/
private def arithOk (k : UInt8) (d : List (Int64 × Int64 × Int64)) (u : List Int64) : Bool :=
  let inU (x : Int64) := u.contains x
  let spec := d.filterMap fun (x, a, b) => let w := Ew.intStep k Alg.nul a b
    if inU a && inU b && w != Alg.nul && exactB k a b w && inU w then some (x, w) else none
  let d' := d.filter fun (_, a, b) => inU a && inU b
  let old := ((Alg.arith k (dTab d').val).toList).filter (inU ·.2)
  let viaOld := d.flatMap fun (x, p) => (old.filter (·.1 == p)).map fun q => (x, q.2)
  match (dTab d).arith k (uTab u) with
  | .ok T => sameSet T.toList spec && sameSet T.toList viaOld
  | .error _ => false

/-- Whether `Tab.succ` answers `D ≫ succDen U` on lists, and agrees with the old `Alg.succ` composed after `D`. -/
private def succOk (d : List (Int64 × Int64)) (u : List Int64) : Bool :=
  let inU (x : Int64) := u.contains x
  let spec := d.filterMap fun (x, v) => let w := Ew.intStep Ew.add Alg.nul v 1
    if inU v && inU w then some (x, w) else none
  let old := (Alg.succ (colOf id u)).toList
  let viaOld := d.flatMap fun (x, v) => (old.filter (·.1 == v)).map fun q => (x, q.2)
  match (⟨_, colOf (·.1) d, colOf (·.2) d⟩ : Tab .long .long).succ (uTab u) with
  | .ok T => sameSet T.toList spec && sameSet T.toList viaOld
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
-- a code outside `Op.table` is the error naming it
#guard (dTab ds).arith 3 (uTab us) matches .error _
-- `succ`: the top of `U` goes nowhere, `maxValue` to the null only where `U` holds it, the null to itself
#guard succOk ((List.range us.length).zip us |>.map fun (i, u) => (Int64.ofNat i, u)) us
#guard succOk [(1, 3), (1, 3), (2, Int64.maxValue), (3, Int64.minValue), (4, 9), (5, 100)] [3, 4, 9, Int64.maxValue]
#guard succOk [(1, 3), (2, 4)] [] && succOk [] us

end Checks

end Rel
