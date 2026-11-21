import Rel.RepAsc
import Rel.RepTabDiv
import Rel.Lang.DfnLaw
import Rel.Run.SetOps

/-! The law of `Tab.sums` (`Rel/Run/SetOps.lean`): `canon` puts each key's rows in one run ascending in the position
(`kseen_runs`, the `i64` order codes), the segmented `kscan .add` holds at each row its key's prefix sum
(`segScan_ok`), a row's bad word is `0` exactly when its step is `plus` (`badWord_spec`, `stepDen_add_iff`), and the
segmented `kscan .or` keeps a row exactly when no step of its key up to it failed: the left fold `⦇[0, plus]⦈` of
`sumsDen` over the key's values up to the row. -/

namespace Rel
open Rel.Ext Rel.Kernel Rel.Verify Rel.Rep
open scoped Rel.Core.Rel

/-- Flipping the top bit `b` of a word of `b + 1` bits adds `2^b` below it and takes `2^b` off above it. -/
theorem Nat.xor_top {b x : Nat} (hx : x < 2 ^ (b + 1)) :
    x ^^^ 2 ^ b = if x < 2 ^ b then x + 2 ^ b else x - 2 ^ b := by
  have hb : 2 ^ (b + 1) = 2 * 2 ^ b := by rw [Nat.pow_succ, Nat.mul_comm]
  have key : ∀ y < 2 ^ b, y ^^^ 2 ^ b = y + 2 ^ b := fun y hy => by
    rw [Nat.add_comm]
    apply Nat.eq_of_testBit_eq; intro i
    rw [Nat.testBit_xor, Nat.testBit_two_pow]
    rcases Nat.lt_trichotomy i b with hi | rfl | hi
    · rw [Nat.testBit_two_pow_add_gt hi, decide_eq_false (by omega : ¬ b = i)]; simp
    · rw [Nat.testBit_two_pow_add_eq, Nat.testBit_lt_two_pow hy]; simp
    · have h1 : 2 ^ b + y < 2 ^ i := Nat.lt_of_lt_of_le (by omega) (Nat.pow_le_pow_right (by omega) hi)
      rw [Nat.testBit_lt_two_pow h1, Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hy (Nat.pow_le_pow_right
        (by omega) (Nat.le_of_lt hi))), decide_eq_false (by omega : ¬ b = i)]; simp
  split
  · exact key x ‹_›
  · have e := key (x - 2 ^ b) (by omega)
    rw [show x - 2 ^ b + 2 ^ b = x by omega] at e
    have e' : x ^^^ 2 ^ b = (x - 2 ^ b ^^^ 2 ^ b) ^^^ 2 ^ b := by rw [e]
    rw [e', Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]

/-- An `Int64` from its word: the word below `2^63`, the word less `2^64` above. -/
theorem Int64.toInt_word (a : Int64) : a.toInt =
    if a.toUInt64.toNat < 2 ^ 63 then (a.toUInt64.toNat : Int) else (a.toUInt64.toNat : Int) - 2 ^ 64 := by
  have h1 : a.toInt = a.toBitVec.toInt := rfl
  have h2 : a.toUInt64.toNat = a.toBitVec.toNat := rfl
  rw [h1, h2, BitVec.toInt_eq_toNat_cond]
  split <;> split <;> omega

/-- **The `i64` order code** (`Order.rank .i64`, `ordCode 8 false true`): the sign bit flipped, `toInt + 2^63`. -/
theorem Int64.code_toNat (a : Int64) : (a.toUInt64 ^^^ 0x8000000000000000).toNat = (a.toInt + 2 ^ 63).toNat := by
  have hx := a.toUInt64.toNat_lt
  rw [UInt64.toNat_xor, show (0x8000000000000000 : UInt64).toNat = 2 ^ 63 from rfl, Nat.xor_top (b := 63) hx,
    Int64.toInt_word]
  split <;> omega

theorem ordCode_i64 (u : UInt64) : ordCode 8 false true u = u ^^^ 0x8000000000000000 := by
  apply UInt64.toNat_inj.1
  have m64 : (18446744073709551615 : UInt64).toNat = 2 ^ 64 - 1 := rfl
  simp only [ordCode, Nat.reduceMul, Nat.reduceSub, Nat.reducePow, beq_self_eq_true, if_true, Bool.false_eq_true,
    if_false, UInt64.toNat_xor, UInt64.toNat_and, m64]
  rw [show (18446744073709551615 : Nat) = 2 ^ 64 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod,
    Nat.mod_eq_of_lt u.toNat_lt]
  rfl

/-- `ordCode` orders `i64` words as `Int64`. -/
theorem ordCode_i64_le (a b : Int64) :
    (ordCode 8 false true a.toUInt64).toNat ≤ (ordCode 8 false true b.toUInt64).toNat ↔ a ≤ b := by
  have := Int64.le_toInt a; have := Int64.toInt_lt a; have := Int64.le_toInt b; have := Int64.toInt_lt b
  rw [ordCode_i64, ordCode_i64, Int64.code_toNat, Int64.code_toNat, Int64.le_iff_toInt_le]; omega

/-- **q's order on longs is `Int64`'s**. -/
theorem Obj.lt_long (a b : Int64) : Obj.lt .long a b ↔ a < b := by
  have h := ordCode_i64_le b a
  show [(ordCode 8 false true a.toUInt64).toNat] < [(ordCode 8 false true b.toUInt64).toNat] ↔ a < b
  simp only [List.cons_lt_cons_iff, List.lt_irrefl, and_false, or_false, Int64.lt_iff_toInt_lt,
    Int64.le_iff_toInt_le] at h ⊢
  omega

/-- `kseen` read every column it was given: `ascCol` answers on each. -/
theorem kseen_codes {n : USize} {es : List (AscKey × Enc)} {r : Nat × Enc × Enc} (h : kseen n es = .ok r) :
    ∃ cs, es.mapM (ascCol n) = .ok cs := by
  unfold kseen at h
  simp only [bind, Except.bind] at h
  split at h; · cases h
  rename_i kss heq
  obtain ⟨hlen, hf⟩ := mapM_ok heq
  have hok : ∀ e ∈ es, ∃ c, ascCol n e = .ok c := fun e he => by
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem he
    obtain ⟨b, hb⟩ : ∃ b, kss[i]? = some b :=
      ⟨kss[i]'(by rw [hlen, List.length_zipIdx]; exact hi), List.getElem?_eq_getElem _⟩
    have he' := hf i (es[i], i) b (by simp [hi]) hb
    cases hce : ascCol n es[i] with
    | error s => simp [hce, Functor.map, Except.map, Except.mapError] at he'
    | ok c => exact ⟨c, rfl⟩
  clear h heq hf hlen
  induction es with
  | nil => exact ⟨[], rfl⟩
  | cons e es ih =>
    obtain ⟨c, hc⟩ := hok e List.mem_cons_self
    obtain ⟨cs, hcs⟩ := ih fun e' he' => hok e' (List.mem_cons_of_mem _ he')
    exact ⟨c :: cs, by simp [List.mapM_cons, hc, hcs, bind, Except.bind, pure, Except.pure]⟩

/-- Key columns on which two rows agree leave `lexLe` to the columns after them. -/
theorem lexLe_append_of_eq : ∀ (ks ks2 : List (Array UInt64)) {i j : Nat},
    ks.map (·[i]?.getD 0) = ks.map (·[j]?.getD 0) → lexLe (ks ++ ks2) i j = lexLe ks2 i j
  | [], _, _, _, _ => rfl
  | c :: cs, ks2, i, j, h => by
    simp only [List.map_cons, List.cons.injEq] at h
    simp [lexLe, h.1, lexLe_append_of_eq cs ks2 h.2]

namespace Lang

/-- The left fold of `xs ++ [x]` is one step from the left fold of `xs`. -/
theorem foldDen_snoc {E V : Obj} (Te : Den V V) (TS : Den (.prod V E) V) (xs : List E.El) (x : E.El) (w : V.El) :
    foldDen Te TS (xs ++ [x]) w ↔ ∃ u, foldDen Te TS xs u ∧ TS (u, x) w := by
  constructor
  · rintro ⟨ys, hy, ⟨a, ha⟩, hs, rfl⟩
    simp only [List.length_append, List.length_singleton] at hy
    refine ⟨ys[xs.length]'(by omega), ⟨ys.take (xs.length + 1), by simp; omega, ⟨a, by simpa using ha⟩,
      fun t ht => ?_, by simp⟩, ?_⟩
    · have := hs t (by simp; omega)
      simpa [List.getElem_append_left ht, List.getElem_take] using this
    · have := hs xs.length (by simp)
      simpa using this
  · rintro ⟨u, ⟨ys, hy, ⟨a, ha⟩, hs, rfl⟩, hS⟩
    refine ⟨ys ++ [w], by simp [hy], ⟨a, by rw [List.getElem_append_left (by omega)]; exact ha⟩, fun t ht => ?_,
      by simp [hy]⟩
    simp only [List.length_append, List.length_singleton] at ht
    by_cases ht' : t < xs.length
    · have := hs t ht'
      simpa [List.getElem_append_left ht', List.getElem_append_left (show t < ys.length by omega),
        List.getElem_append_left (show t + 1 < ys.length by omega)] using this
    · obtain rfl : t = xs.length := by omega
      simpa [List.getElem_append_left (show xs.length < ys.length by omega), hy] using hS

/-- `dom(T) (𝟙 × ≥) dom(T)` pointwise. -/
theorem upToDen_iff {K V : Obj} {t : QAtomicType} (T : Den (.prod K (.atom t)) V) (a b : (Obj.prod K (.atom t)).El) :
    upToDen T a b ↔ (∃ c, T a c) ∧ (∃ c, T b c) ∧ a.1 = b.1 ∧ leAt t b.2 a.2 := by
  simp only [upToDen, Core.Rel.comp, Core.Rel.inter, Core.Rel.recip, Core.Rel.id, Core.Rel.graph]
  constructor
  · rintro ⟨a', ⟨rfl, c, hc, -⟩, b', ⟨⟨k, hk1, hk2⟩, s, rfl, s', hs, rfl⟩, rfl, c', -, hc'⟩
    exact ⟨⟨c, hc⟩, ⟨c', hc'⟩, hk1.symm.trans hk2, hs⟩
  · rintro ⟨⟨c, hc⟩, ⟨c', hc'⟩, h1, h2⟩
    exact ⟨a, ⟨rfl, c, hc, hc⟩, b, ⟨⟨a.1, rfl, h1⟩, a.2, rfl, b.2, h2, rfl⟩, rfl, c', hc', hc'⟩

/-- **A `plus` step from a non-null sum, read from its wrapped result**: `v` and `acc + v` not the null and no wrap
(`Tab.sum`'s bad word at `0`, `badWord_spec`) exactly when `stepDen Ew.add` takes `(acc, v)` to `acc + v`. -/
theorem stepDen_add_word {acc v : Int64} (ha : acc ≠ Alg.nul) :
    (v ≠ Alg.nul ∧ acc + v ≠ Alg.nul ∧ ¬((v < 0 ↔ acc < 0) ∧ ¬(v < 0 ↔ acc + v < 0))) ↔
      stepDen Ew.add (acc, v) (acc + v) := by
  rw [stepDen_add_iff, Int64.add_comm acc v]
  have e := Int64.add_exact_iff v acc
  constructor
  · rintro ⟨hv, hn, ho⟩; have := e.1 ⟨hn, ho⟩; exact ⟨ha, hv, by omega, by omega, rfl⟩
  · rintro ⟨-, hv, h1, h2, -⟩; obtain ⟨hn, ho⟩ := e.2 ⟨by omega, by omega⟩; exact ⟨hv, hn, ho⟩

/-- **One `plus` step read from the words**: from a non-null sum `acc = W - v`, the step takes `(acc, v)` to `w`
exactly when the row's bad word is `0` and `w` is the row's sum `W`. -/
theorem sums_step {acc : Int64} (ha : acc ≠ Alg.nul) {v W bad : UInt64} (hWv : (W - v).toInt64 = acc)
    (hbad : bad = 0 ↔ v.toInt64 ≠ Alg.nul ∧ W.toInt64 ≠ Alg.nul ∧
      ¬((v.toInt64 < 0 ↔ (W - v).toInt64 < 0) ∧ ¬(v.toInt64 < 0 ↔ W.toInt64 < 0))) (w : Int64) :
    stepDen Ew.add (acc, v.toInt64) w ↔ bad = 0 ∧ w = W.toInt64 := by
  have hW : W.toInt64 = acc + v.toInt64 := by
    rw [← hWv]; show W.toInt64 = (W - v + v).toInt64; rw [UInt64.sub_add_cancel]
  rw [hbad, hWv, hW, stepDen_add_word ha]
  constructor
  · intro h; obtain ⟨-, -, -, -, rfl⟩ := (stepDen_add_iff _ _ _).1 h; exact ⟨h, rfl⟩
  · rintro ⟨h, rfl⟩; exact h

/-- **The left fold of a run one row longer**: if the fold of the rows `P` is their sum `A` exactly when no row of `P`
is bad, so is the fold of `P ++ [q]` with `q`'s sum `W q`, `W q - v q = A`. -/
theorem sums_snoc {v W bad : Nat → UInt64} {P : List Nat} {A : Int64} {q : Nat}
    (hfold : ∀ w, foldDen (E := .long) (V := .long) (fun _ b => b = 0) (stepDen Ew.add)
      (P.map fun p => (v p).toInt64) w ↔ (∀ p ∈ P, bad p = 0) ∧ w = A)
    (hA : (∀ p ∈ P, bad p = 0) → A ≠ Alg.nul) (hsub : (W q - v q).toInt64 = A)
    (hbq : bad q = 0 ↔ (v q).toInt64 ≠ Alg.nul ∧ (W q).toInt64 ≠ Alg.nul ∧
      ¬(((v q).toInt64 < 0 ↔ (W q - v q).toInt64 < 0) ∧ ¬((v q).toInt64 < 0 ↔ (W q).toInt64 < 0))) (w : Int64) :
    foldDen (E := .long) (V := .long) (fun _ b => b = 0) (stepDen Ew.add)
      ((P ++ [q]).map fun p => (v p).toInt64) w ↔ (∀ p ∈ P ++ [q], bad p = 0) ∧ w = (W q).toInt64 := by
  rw [List.map_append, List.map_singleton, foldDen_snoc]
  simp only [List.mem_append, List.mem_singleton, or_imp, forall_and, forall_eq]
  constructor
  · rintro ⟨u, hu, hs⟩
    obtain ⟨hb, rfl⟩ := (hfold u).1 hu
    have := (sums_step (hA hb) hsub hbq w).1 hs
    exact ⟨⟨hb, this.1⟩, this.2⟩
  · rintro ⟨⟨hb, hq⟩, rfl⟩
    exact ⟨A, (hfold A).2 ⟨hb, rfl⟩, (sums_step (hA hb) hsub hbq _).2 ⟨hq, rfl⟩⟩

/-- The rows `≤ t + 1` of `t + 1`'s group: those of `t`'s group when `t` is in it (groups are runs), then `t + 1`. -/
theorem groupRows_succ {α : Type} [DecidableEq α] {g : Nat → α} {m : Nat}
    (hrun : ∀ a b c, a ≤ b → b ≤ c → c < m → g a = g c → g b = g a) {t : Nat} (ht : t + 1 < m) :
    (List.range (t + 2)).filter (fun q => Verify.groupOf g m q = Verify.groupOf g m (t + 1)) =
      (if g t = g (t + 1) then (List.range (t + 1)).filter (fun q => Verify.groupOf g m q = Verify.groupOf g m t) else []) ++
        [t + 1] := by
  have hG := (firsts_spec g m).2.2.1
  rw [List.range_succ, List.filter_append]
  congr 1
  · split
    · rename_i h
      apply List.filter_congr; intro q hq; rw [List.mem_range] at hq
      rw [decide_eq_decide, hG q (by omega) (t + 1) ht, hG q (by omega) t (by omega), h]
    · rename_i h
      apply List.filter_eq_nil_iff.2; intro q hq; rw [List.mem_range] at hq
      simp only [decide_eq_true_eq]; rw [hG q (by omega) (t + 1) ht]; intro hq'
      exact h ((hrun q t (t + 1) (by omega) (by omega) ht hq').trans hq')
  · simp

/-- **The prefix sums of a key, as a left fold**: over the rows `≤ t` of `t`'s group, `⦇[0, plus]⦈` of their values
is `t`'s scanned sum `W t` exactly when none of their bad words is set (`segScan_ok`, `badWord_spec`). -/
theorem sums_fold {α : Type} [DecidableEq α] {g : Nat → α} {m : Nat}
    (hrun : ∀ a b c, a ≤ b → b ≤ c → c < m → g a = g c → g b = g a) (v W bad : Nat → UInt64)
    (hW : ∀ t < m, W t =
      (((List.range (t + 1)).filter fun q => Verify.groupOf g m q = Verify.groupOf g m t).map v).foldl (· + ·) 0)
    (hbad : ∀ t < m, (bad t = 0 ↔ (v t).toInt64 ≠ Alg.nul ∧ (W t).toInt64 ≠ Alg.nul ∧
        ¬(((v t).toInt64 < 0 ↔ (W t - v t).toInt64 < 0) ∧ ¬((v t).toInt64 < 0 ↔ (W t).toInt64 < 0)))) :
    ∀ t < m, ∀ w, foldDen (E := .long) (V := .long) (fun _ b => b = 0) (stepDen Ew.add)
      (((List.range (t + 1)).filter fun q => Verify.groupOf g m q = Verify.groupOf g m t).map fun q => (v q).toInt64) w ↔
      (∀ q ∈ (List.range (t + 1)).filter (fun q => Verify.groupOf g m q = Verify.groupOf g m t), bad q = 0) ∧
        w = (W t).toInt64 := by
  have h0 : ∀ q < m, ((List.range (q + 1)).filter fun p => Verify.groupOf g m p = Verify.groupOf g m q) = [] ++ [q] →
      ∀ w, foldDen (E := .long) (V := .long) (fun _ b => b = 0) (stepDen Ew.add)
        (([] ++ [q]).map fun p => (v p).toInt64) w ↔ (∀ p ∈ [] ++ [q], bad p = 0) ∧ w = (W q).toInt64 :=
    fun q hq e => sums_snoc (A := 0) (fun w => by rw [List.map_nil, foldDen_nil]; simp) (fun _ => by decide)
      (by rw [hW q hq, e]; simp) (hbad q hq)
  intro t
  induction t with
  | zero => intro ht; have e : ((List.range 1).filter fun p => Verify.groupOf g m p = Verify.groupOf g m 0) = [] ++ [0] := by simp
            rw [e]; exact h0 0 ht e
  | succ t ih =>
    intro ht
    have e := groupRows_succ hrun ht
    rw [e]
    split
    · rename_i hg
      have hmem : t ∈ (List.range (t + 1)).filter (fun q => Verify.groupOf g m q = Verify.groupOf g m t) := by simp
      refine sums_snoc (ih (by omega)) (fun hb => ((hbad t (by omega)).1 (hb t hmem)).2.1) ?_ (hbad (t + 1) ht)
      rw [hW (t + 1) ht, hW t (by omega), e, if_pos hg, List.map_append, List.foldl_append]; simp
    · rename_i hg; rw [if_neg hg] at e; exact h0 (t + 1) ht e

/-- `kscan .fadd`'s step as a total function, the `fn` `segScan_ok` folds (`Op.eval .fadd` never fails). -/
abbrev faddW (a x : UInt64) : UInt64 := match Op.eval .fadd a x with | .ok r => r | .error _ => 0

/-- **A float `plus` step read from the scan**: `stepAt .f64 add` takes `(acc, v)` to `fto` of the IEEE sum, so where
the scan's row is that sum `W` and its `fto` is `W` or `2^63`, the step holds exactly when the row's `fto` is `W`, not
`2^63`, and `w` is `W`. No property of `Float` is used. -/
theorem stepF_word {acc v W W' : UInt64} (hW : W = faddW acc v) (hW' : W' = Op.ftoWord .f64 W)
    (hodd : W' = W ∨ W' = 0x8000000000000000) (w : (Obj.atom .f64).El) :
    stepAt .f64 Ew.add (acc, v) w ↔ (W' = W ∧ W' ≠ 0x8000000000000000) ∧ w = W := by
  have hs : fstep .f64 Ew.add acc v = .ok (Op.ftoWord .f64 (faddW acc v)) := rfl
  have e : stepAt .f64 Ew.add (acc, v) w ↔ W' ≠ 0x8000000000000000 ∧ w = W' := by
    rw [hW', hW]
    constructor
    · rintro ⟨X, Y, r, hX, hY, hr, hn, rfl⟩
      cases hX; cases hY; rw [hs] at hr; cases hr; exact ⟨hn, rfl⟩
    · rintro ⟨hn, rfl⟩; exact ⟨_, _, _, rfl, rfl, hs, hn, rfl⟩
  rw [e]; rcases hodd with h | h <;> rw [h] <;> simp

/-- **The left fold of a float run one row longer** (`sums_snoc` at `f64`). -/
theorem sumsF_snoc {v W bad : Nat → UInt64} {P : List Nat} {A : UInt64} {q : Nat}
    (hfold : ∀ w, foldDen (E := .atom .f64) (V := .atom .f64) (fun _ b => b = QAtomicType.ofBits .f64 0)
      (stepAt .f64 Ew.add) (P.map v) w ↔ (∀ p ∈ P, bad p = 0) ∧ w = A)
    (hq : ∀ w, stepAt .f64 Ew.add (A, v q) w ↔ bad q = 0 ∧ w = W q) (w : (Obj.atom .f64).El) :
    foldDen (E := .atom .f64) (V := .atom .f64) (fun _ b => b = QAtomicType.ofBits .f64 0) (stepAt .f64 Ew.add)
      ((P ++ [q]).map v) w ↔ (∀ p ∈ P ++ [q], bad p = 0) ∧ w = W q := by
  rw [List.map_append, List.map_singleton, foldDen_snoc]
  simp only [List.mem_append, List.mem_singleton, or_imp, forall_and, forall_eq]
  constructor
  · rintro ⟨u, hu, hs⟩
    obtain ⟨hb, rfl⟩ := (hfold u).1 hu
    obtain ⟨h1, h2⟩ := (hq w).1 hs
    exact ⟨⟨hb, h1⟩, h2⟩
  · rintro ⟨⟨hb, h1⟩, rfl⟩
    exact ⟨A, (hfold A).2 ⟨hb, rfl⟩, (hq _).2 ⟨h1, rfl⟩⟩

/-- **The prefix sums of a key at `f64`, as a left fold** (`sums_fold` at `f64`): `W` the segmented `kscan .fadd`,
`W'` its `fto`, every row's `W'` either `W` or `2^63`; the fold is `W t` exactly when no row up to `t` is bad. -/
theorem sumsF_fold {α : Type} [DecidableEq α] {g : Nat → α} {m : Nat}
    (hrun : ∀ a b c, a ≤ b → b ≤ c → c < m → g a = g c → g b = g a) (v W W' bad : Nat → UInt64)
    (hW : ∀ t < m, W t =
      (((List.range (t + 1)).filter fun q => Verify.groupOf g m q = Verify.groupOf g m t).map v).foldl faddW 0)
    (hW' : ∀ t < m, W' t = Op.ftoWord .f64 (W t)) (hodd : ∀ t < m, W' t = W t ∨ W' t = 0x8000000000000000)
    (hbad : ∀ t < m, (bad t = 0 ↔ W' t = W t ∧ W' t ≠ 0x8000000000000000)) :
    ∀ t < m, ∀ w, foldDen (E := .atom .f64) (V := .atom .f64) (fun _ b => b = QAtomicType.ofBits .f64 0)
      (stepAt .f64 Ew.add)
      (((List.range (t + 1)).filter fun q => Verify.groupOf g m q = Verify.groupOf g m t).map v) w ↔
      (∀ q ∈ (List.range (t + 1)).filter (fun q => Verify.groupOf g m q = Verify.groupOf g m t), bad q = 0) ∧
        w = W t := by
  have hq : ∀ q < m, ∀ A, W q = faddW A (v q) → ∀ w, stepAt .f64 Ew.add (A, v q) w ↔ bad q = 0 ∧ w = W q :=
    fun q hq A hA w => by rw [hbad q hq]; exact stepF_word hA (hW' q hq) (hodd q hq) w
  have h0 : ∀ q < m, ((List.range (q + 1)).filter fun p => Verify.groupOf g m p = Verify.groupOf g m q) = [] ++ [q] →
      ∀ w, foldDen (E := .atom .f64) (V := .atom .f64) (fun _ b => b = QAtomicType.ofBits .f64 0)
        (stepAt .f64 Ew.add) (([] ++ [q]).map v) w ↔ (∀ p ∈ [] ++ [q], bad p = 0) ∧ w = W q :=
    fun q hq' e => sumsF_snoc (A := 0) (fun w => by rw [List.map_nil, foldDen_nil]; simp; rfl)
      (hq q hq' 0 (by rw [hW q hq', e]; rfl))
  intro t
  induction t with
  | zero => intro ht; have e : ((List.range 1).filter fun p => Verify.groupOf g m p = Verify.groupOf g m 0) = [] ++ [0] := by simp
            rw [e]; exact h0 0 ht e
  | succ t ih =>
    intro ht
    have e := groupRows_succ hrun ht
    rw [e]
    split
    · rename_i hg
      refine sumsF_snoc (ih (by omega)) (hq (t + 1) ht _ ?_)
      rw [hW (t + 1) ht, hW t (by omega), e, if_pos hg, List.map_append, List.foldl_append]; rfl
    · rename_i hg; rw [if_neg hg] at e; exact h0 (t + 1) ht e

/-- **canon's order on the atom `t` is the language's** (`ltAt`, `leAt`): what `sums` needs of its positions, which
canon sorts by their order codes (`Obj.lt`) while `sumsDen` reads them in `leAt t`. -/
def OrdAt (t : QAtomicType) : Prop :=
  (∀ a b, Obj.lt (.atom t) a b ↔ ltAt t a b) ∧ ∀ a b, leAt t a b ↔ ltAt t a b ∨ a = b

/-- An `i64` word holding `n` reads back as `n`. -/
theorem i64_word (n : Int) (h1 : -2 ^ 63 ≤ n) (h2 : n < 2 ^ 63) :
    (QAtomicType.word .i64 (QAtomicType.ofNum .i64 n)).toInt64.toInt = n := by
  have e := QAtomicType.ofBits_word (t := .i64) (Int64.ofInt n) rfl
  simp only [QAtomicType.ofBits, QAtomicType.ofNum] at e ⊢
  rw [e, Int64.toInt_ofInt_of_le (by omega) (by omega)]

/-- **An integer word widened to `i64`** (`castWord r .i64`): its value, q's null `-2^63` where it is the null. -/
theorem castWord_int {r : QAtomicType} {s : Bool} {b : Nat} (hr : r.storeFmt? = some (.int s b))
    (hlo : -2 ^ 63 ≤ (QAtomicType.NumFmt.int s b).lo - 1) (x : UInt64)
    (hn : (QAtomicType.NumFmt.int s b).lo - 1 ≤ r.num (QAtomicType.ofBits r x) ∧ r.num (QAtomicType.ofBits r x) < 2 ^ 63) :
    (QAtomicType.castWord r .i64 x).toInt64.toInt =
      if (QAtomicType.NumFmt.int s b).lo ≤ r.num (QAtomicType.ofBits r x) then r.num (QAtomicType.ofBits r x)
      else -2 ^ 63 := by
  simp only [QAtomicType.castWord, QAtomicType.embed, QAtomicType.value, hr]
  split
  · simp only [Option.bind_some, QAtomicType.ofValue, (show QAtomicType.i64.storeFmt? = some (.int true 64) from rfl), QAtomicType.intOf, QAtomicType.NumFmt.lo,
      QAtomicType.NumFmt.hi]
    simp only [Int.le_refl, ↓reduceIte, Int.toNat_zero, Int.pow_zero, Int.mul_one, Option.bind_some]
    rw [if_pos (by constructor <;> omega)]
    exact i64_word _ (by omega) (by omega)
  · rfl

/-- The code of a signed `w`-byte word: its low `8w` bits with the top one flipped. -/
theorem ordCode_signed {w : Nat} (h1 : 1 ≤ w) (h8 : w ≤ 8) (u : UInt64) :
    (ordCode w false true u).toNat = (u.toNat % 2 ^ (8 * w) + 2 ^ (8 * w - 1)) % 2 ^ (8 * w) := by
  have hm := Verify.toNat_and_mask h1 h8 u
  have ht : ((2 ^ (8 * w - 1)).toUInt64 : UInt64).toNat = 2 ^ (8 * w - 1) := by
    rw [Nat.toUInt64_eq, UInt64.toNat_ofNat', Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by omega) (by omega))]
  have hx := Nat.mod_lt u.toNat (Nat.two_pow_pos (8 * w))
  have e : 8 * w = 8 * w - 1 + 1 := by omega
  simp only [ordCode, Bool.false_eq_true, ↓reduceIte, UInt64.toNat_xor, hm, ht]
  rw [e] at hx ⊢
  rw [Nat.add_sub_cancel, Nat.xor_top hx]
  have hb : 2 ^ (8 * w - 1 + 1) = 2 * 2 ^ (8 * w - 1) := by rw [Nat.pow_succ, Nat.mul_comm]
  rw [hb] at hx ⊢
  generalize u.toNat % (2 * 2 ^ (8 * w - 1)) = m at hx ⊢
  generalize 2 ^ (8 * w - 1) = d at hx ⊢
  split
  · rw [Nat.mod_eq_of_lt (by omega)]
  · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]; omega

/-- The code of an unsigned `w`-byte word: its low `8w` bits. -/
theorem ordCode_unsigned {w : Nat} (h1 : 1 ≤ w) (h8 : w ≤ 8) (u : UInt64) :
    (ordCode w false false u).toNat = u.toNat % 2 ^ (8 * w) := by
  simp only [ordCode, Bool.false_eq_true, ↓reduceIte]; exact Verify.toNat_and_mask h1 h8 u

/-- What the order proofs read off an integer-stored atom `t`: its storage atom `r`, width `w` bytes and signedness
`s`, its layout, and the range of `num`. -/
theorem intOrd_shape {t : QAtomicType} (h : t.intOrd = true) : ∃ r w s, t.ordNum = some r ∧
    r.storeFmt? = some (.int s (8 * w)) ∧ t.storeFmt? = some (.int s (8 * w)) ∧ ascLayout t = some (w, false, s) ∧
    (w = 1 ∨ w = 2 ∨ w = 4 ∨ w = 8) ∧ (s = false → w = 1) ∧ (∀ x, r.num (QAtomicType.ofBits r x) = t.num (QAtomicType.ofBits t x)) ∧
    ∀ v : (Obj.atom t).El, if s then -2 ^ (8 * w - 1) ≤ t.num v ∧ t.num v < 2 ^ (8 * w - 1)
      else 0 ≤ t.num v ∧ t.num v < 2 ^ (8 * w) := by
  cases t <;> first | exact absurd h (by decide) | skip
  case u8 => exact ⟨.u8, 1, false, rfl, rfl, rfl, rfl, by omega, by decide, fun _ => rfl, fun v => by
    have := v.toNat_lt; simp [QAtomicType.num]; omega⟩
  case char => exact ⟨.u8, 1, false, rfl, rfl, rfl, rfl, by omega, by decide, fun _ => rfl, fun v => by
    have := v.toNat_lt; simp [QAtomicType.num]; omega⟩
  case i8 => exact ⟨.i8, 1, true, rfl, rfl, rfl, rfl, by omega, by decide, fun _ => rfl, fun v => by
    have := Int8.le_toInt v; have := Int8.toInt_lt v; simp [QAtomicType.num]; omega⟩
  case i16 => exact ⟨.i16, 2, true, rfl, rfl, rfl, rfl, by omega, by decide, fun _ => rfl, fun v => by
    have := Int16.le_toInt v; have := Int16.toInt_lt v; simp [QAtomicType.num]; omega⟩
  case i32 => exact ⟨.i32, 4, true, rfl, rfl, rfl, rfl, by omega, by decide, fun _ => rfl, fun v => by
    have := Int32.le_toInt v; have := Int32.toInt_lt v; simp [QAtomicType.num]; omega⟩
  case date => exact ⟨.i32, 4, true, rfl, rfl, rfl, rfl, by omega, by decide, fun _ => rfl, fun v => by
    have := Int32.le_toInt v; have := Int32.toInt_lt v; simp [QAtomicType.num]; omega⟩
  case i64 => exact ⟨.i64, 8, true, rfl, rfl, rfl, rfl, by omega, by decide, fun _ => rfl, fun v => by
    have := Int64.le_toInt v; have := Int64.toInt_lt v; simp [QAtomicType.num]; omega⟩
  case datetime => exact ⟨.i64, 8, true, rfl, rfl, rfl, rfl, by omega, by decide, fun _ => rfl, fun v => by
    have := Int64.le_toInt v; have := Int64.toInt_lt v; simp [QAtomicType.num]; omega⟩

/-- An integer-stored atom's key is its `num` moved up by half its range when signed. -/
theorem key_num {t : QAtomicType} (h : t.intOrd = true) : ∃ off : Int, ∀ v : (Obj.atom t).El,
    Obj.key (.atom t) v = [(t.num v + off).toNat] ∧ 0 ≤ t.num v + off := by
  obtain ⟨r, w, s, -, -, hst, hl, hw, -, -, hb⟩ := intOrd_shape h
  refine ⟨if s then 2 ^ (8 * w - 1) else 0, fun v => ?_⟩
  have hs : t.storeFmt?.isSome := by rw [hst]; rfl
  have hg : t ≠ .general := by rintro rfl; cases hst
  have k := Obj.key_ordCode hl hg (QAtomicType.word t v) (fun e => by subst e; cases hst)
  have ho : (Dep.Carrier.of? t (.atom (Column.atomOfBits t (QAtomicType.word t v) hg))).getD default =
      QAtomicType.ofBits t (QAtomicType.word t v) := by
    cases t <;> first | rfl | exact absurd hs (by decide)
  rw [ho, QAtomicType.ofBits_word v hs] at k
  have hv := hb v
  have hu : (QAtomicType.word t v).toNat = (t.num v % 2 ^ 64).toNat := by
    simp [QAtomicType.word, UInt64.ofInt]; omega
  refine ⟨?_, ?_⟩
  · rw [k, List.cons.injEq]; refine ⟨?_, rfl⟩
    cases s
    · rw [ordCode_unsigned (by omega) (by omega), hu]
      rcases hw with rfl | rfl | rfl | rfl <;> simp at hv ⊢ <;> omega
    · rw [ordCode_signed (by omega) (by omega), hu]
      rcases hw with rfl | rfl | rfl | rfl <;> simp at hv ⊢ <;> omega
  · cases s <;> simp at hv ⊢ <;> omega


/-- `iordAt`'s orders at an integer-stored atom are those of `num`. -/
theorem iord_num {t : QAtomicType} (h : t.intOrd = true) (a b : (Obj.atom t).El) :
    (iordAt .lt t a b ↔ t.num a < t.num b) ∧ (iordAt .le t a b ↔ t.num a ≤ t.num b) := by
  obtain ⟨r, w, s, hr, hrs, hst, -, hw, hsw, hx, hb⟩ := intOrd_shape h
  have hs : t.storeFmt?.isSome := by rw [hst]; rfl
  have cw : ∀ x, (QAtomicType.castWord r .i64 x).toInt64.toInt =
      if (QAtomicType.NumFmt.int s (8 * w)).lo ≤ t.num (QAtomicType.ofBits t x) then t.num (QAtomicType.ofBits t x)
      else -2 ^ 63 := fun x => by
    have hv := hb (QAtomicType.ofBits t x)
    rw [← hx x]; refine castWord_int hrs ?_ x ?_
    · rcases hw with rfl | rfl | rfl | rfl <;> cases s <;> simp [QAtomicType.NumFmt.lo]
    · rw [hx x]; rcases hw with rfl | rfl | rfl | rfl <;> cases s <;> simp [QAtomicType.NumFmt.lo] at hv hsw ⊢ <;> omega
  have hv := hb a; have hv' := hb b
  have key : ∀ x y, QAtomicType.ofBits t x = a → QAtomicType.ofBits t y = b →
      ((QAtomicType.castWord r .i64 x).toInt64 < (QAtomicType.castWord r .i64 y).toInt64 ↔ t.num a < t.num b) ∧
      ((QAtomicType.castWord r .i64 x).toInt64 ≤ (QAtomicType.castWord r .i64 y).toInt64 ↔ t.num a ≤ t.num b) := by
    intro x y hxa hyb
    rw [Int64.lt_iff_toInt_lt, Int64.le_iff_toInt_le, cw, cw, hxa, hyb]
    generalize t.num a = A at *; generalize t.num b = B at *
    rcases hw with rfl | rfl | rfl | rfl <;> cases s <;> simp only [QAtomicType.NumFmt.lo] at hv hv' ⊢ <;>
      simp at hv hv' ⊢ <;> split <;> split <;> (constructor <;> constructor <;> intro <;> omega)
  have elt : ∀ p q : UInt64, Op.eval .lt p q = .ok 1 ↔ p.toInt64 < q.toInt64 := fun p q => by
    rw [show Op.eval .lt p q = .ok (if decide (p.toInt64 < q.toInt64) = true then 1 else 0) from rfl]
    by_cases hp : p.toInt64 < q.toInt64 <;> simp [hp]
  have ele : ∀ p q : UInt64, Op.eval .le p q = .ok 1 ↔ p.toInt64 ≤ q.toInt64 := fun p q => by
    rw [show Op.eval .le p q = .ok (if decide (p.toInt64 ≤ q.toInt64) = true then 1 else 0) from rfl]
    by_cases hp : p.toInt64 ≤ q.toInt64 <;> simp [hp]
  constructor <;> constructor
  · rintro ⟨r', x, y, hr', hxa, hyb, he⟩
    rw [hr] at hr'; cases hr'; exact (key x y hxa hyb).1.1 ((elt _ _).1 he)
  · intro hl; exact ⟨r, _, _, hr, QAtomicType.ofBits_word a hs, QAtomicType.ofBits_word b hs,
      (elt _ _).2 ((key _ _ (QAtomicType.ofBits_word a hs) (QAtomicType.ofBits_word b hs)).1.2 hl)⟩
  · rintro ⟨r', x, y, hr', hxa, hyb, he⟩
    rw [hr] at hr'; cases hr'; exact (key x y hxa hyb).2.1 ((ele _ _).1 he)
  · intro hl; exact ⟨r, _, _, hr, QAtomicType.ofBits_word a hs, QAtomicType.ofBits_word b hs,
      (ele _ _).2 ((key _ _ (QAtomicType.ofBits_word a hs) (QAtomicType.ofBits_word b hs)).2.2 hl)⟩

/-- The order of an integer-stored atom's values, three ways, each the order of `num`: canon's (`Obj.lt`), `ltAt`'s,
`leAt`'s; and `num` is one to one. -/
theorem num_order {t : QAtomicType} (h : t.intOrd = true) (a b : (Obj.atom t).El) :
    (Obj.lt (.atom t) a b ↔ t.num a < t.num b) ∧ (ltAt t a b ↔ t.num a < t.num b) ∧
      (leAt t a b ↔ t.num a ≤ t.num b) ∧ (t.num a = t.num b → a = b) := by
  have hs : t.storeFmt?.isSome := by
    obtain ⟨_, _, _, _, _, hst, _⟩ := intOrd_shape h; rw [hst]; rfl
  obtain ⟨off, hk⟩ := key_num h
  refine ⟨?_, ?_, ?_, fun e => ?_⟩
  · obtain ⟨ka, ha⟩ := hk a; obtain ⟨kb, hb⟩ := hk b
    simp only [Obj.lt, ka, kb, List.cons_lt_cons_iff, List.lt_irrefl, and_false, or_false]
    omega
  · cases t <;> first | exact absurd h (by decide) | exact (iord_num h a b).1 | exact Int64.lt_iff_toInt_lt
  · cases t <;> first | exact absurd h (by decide) | exact (iord_num h a b).2 | exact Int64.le_iff_toInt_le
  · rw [← QAtomicType.ofBits_word a hs, ← QAtomicType.ofBits_word b hs]
    simp only [QAtomicType.word, e]

/-- **canon's order is the value order at every integer-stored atom** (`u8 i8 i16 i32 i64 char date datetime`). -/
theorem ordAt_int {t : QAtomicType} (h : t.intOrd = true) : OrdAt t :=
  ⟨fun a b => (num_order h a b).1.trans (num_order h a b).2.1.symm, fun a b => by
    obtain ⟨-, h2, h3, h4⟩ := num_order h a b
    rw [h2, h3]; constructor
    · intro hl; rcases Int.lt_or_eq_of_le hl with e | e
      · exact .inl e
      · exact .inr (h4 e)
    · rintro (e | rfl)
      · exact Int.le_of_lt e
      · exact Int.le_refl _⟩

/-- Only an atom with an order code (`ascOrd`) can have canon's order be `ltAt`: `u1`'s `false < true`, `sym`'s
`"" < "a"` have no `ltAt`, and a `general` value is not `leAt` itself. -/
theorem OrdAt.ascOrd {t : QAtomicType} (h : OrdAt t) : ∃ f, ascOrd t = some f := by
  cases t
  case u1 => exact absurd ((h.1 false true).1 (by decide)) (by simp [ltAt, iordAt, QAtomicType.ordNum,
    QAtomicType.numFmt?, QAtomicType.width])
  case sym => exact absurd ((h.1 "" "a").1 (by decide)) (by simp [ltAt, iordAt, QAtomicType.ordNum,
    QAtomicType.numFmt?, QAtomicType.width])
  case general => exact absurd ((h.2 default default).2 (.inr rfl)) (by simp [leAt, iordAt, QAtomicType.ordNum,
    QAtomicType.numFmt?, QAtomicType.width])
  all_goals exact ⟨_, rfl⟩

end Lang

/-- **`sumsDen` on a table of distinct keys whose groups `grp` (equal `κ`) ascend in `ν` with the row**: `(κ, ν)` to
the left fold over the values of the rows `≤ t` of `t`'s group, `t` the row of `(κ, ν)`. -/
theorem sumsDen_rows {K : Obj} {t u : QAtomicType} (hord : Lang.OrdAt t) (C : Tab (.prod K (.atom t)) (.atom u))
    (grp : Nat → Nat) (hD : ∀ i j : Fin C.n.toNat, C.key.row i = C.key.row j → i = j)
    (hG : ∀ i j : Fin C.n.toNat, grp i = grp j ↔ (C.key.row i).1 = (C.key.row j).1)
    (hO : ∀ i j : Fin C.n.toNat, i.1 < j.1 → (C.key.row i).1 = (C.key.row j).1 →
      Obj.lt (.atom t) (C.key.row i).2 (C.key.row j).2) (a : (Obj.prod K (.atom t)).El) (w : (Obj.atom u).El) :
    Lang.sumsDen (rep C) a w ↔ ∃ t : Fin C.n.toNat, C.key.row t = a ∧
      Lang.foldDen (E := .atom u) (V := .atom u) (fun _ b => b = QAtomicType.ofBits u 0) (Lang.stepAt u Ew.add)
        (((List.range (t.1 + 1)).filter fun q => grp q = grp t).map fun q =>
          if hq : q < C.n.toNat then C.val.row ⟨q, hq⟩ else default) w := by
  have hR : ∀ b v, rep C b v ↔ ∃ i, C.key.row i = b ∧ C.val.row i = v := fun _ _ => Iff.rfl
  have hU : ∀ b c, Lang.upToDen (rep C) b c ↔ (∃ v, rep C b v) ∧ (∃ v, rep C c v) ∧ b.1 = c.1 ∧
      Lang.leAt t c.2 b.2 := fun b c => Lang.upToDen_iff _ b c
  have hle : ∀ y, Lang.leAt t y y := fun y => (hord.2 y y).2 (.inr rfl)
  have hP : ∀ t : Fin C.n.toNat, ∀ q ∈ (List.range (t.1 + 1)).filter (fun q => grp q = grp t),
      q < C.n.toNat ∧ q ≤ t.1 ∧ grp q = grp t := fun t q hq => by
    simp only [List.mem_filter, List.mem_range, decide_eq_true_eq] at hq; exact ⟨by omega, by omega, hq.2⟩
  let kAt (t : Fin C.n.toNat) (q : Nat) : (Obj.prod K (.atom _)).El :=
    if hq : q < C.n.toNat then C.key.row ⟨q, hq⟩ else C.key.row t
  have hM : ∀ t : Fin C.n.toNat, ∀ b, b ∈ ((List.range (t.1 + 1)).filter fun q => grp q = grp t).map (kAt t) ↔
      (∃ v, rep C b v) ∧ (C.key.row t).1 = b.1 ∧ Lang.leAt _ b.2 (C.key.row t).2 := by
    intro t b
    rw [List.mem_map]
    constructor
    · rintro ⟨q, hq, rfl⟩
      obtain ⟨hqn, hqt, hg⟩ := hP t q hq
      simp only [kAt, dif_pos hqn]
      refine ⟨⟨_, (hR _ _).2 ⟨⟨q, hqn⟩, rfl, rfl⟩⟩, ((hG ⟨q, hqn⟩ t).1 hg).symm, ?_⟩
      rcases Nat.lt_or_ge q t.1 with h | h
      · exact (hord.2 _ _).2 (.inl ((hord.1 _ _).1 (hO ⟨q, hqn⟩ t h ((hG ⟨q, hqn⟩ t).1 hg))))
      · obtain rfl : t = ⟨q, hqn⟩ := Fin.ext (show t.1 = q by omega); exact hle _
    · rintro ⟨⟨v, hv⟩, h1, h2⟩
      obtain ⟨q, rfl, -⟩ := (hR _ _).1 hv
      refine ⟨q.1, ?_, by simp only [kAt, dif_pos q.2]⟩
      simp only [List.mem_filter, List.mem_range, decide_eq_true_eq]
      refine ⟨?_, (hG q t).2 h1.symm⟩
      apply Nat.lt_of_not_le; intro hc
      have := hO t q (by omega) h1
      rcases (hord.2 _ _).1 h2 with e | e
      · exact Obj.lt_asymm _ this ((hord.1 _ _).2 e)
      · rw [e] at this; exact Obj.lt_irrefl _ _ this
  have hS : ∀ t : Fin C.n.toNat,
      (((List.range (t.1 + 1)).filter fun q => grp q = grp t).map (kAt t)).Pairwise (Obj.prod K (.atom _)).lt := by
    intro t
    rw [List.pairwise_map]
    refine ((List.pairwise_lt_range).filter _).imp_of_mem fun {q q'} hq hq' hlt => ?_
    obtain ⟨hqn, -, hg⟩ := hP t q hq; obtain ⟨hqn', -, hg'⟩ := hP t q' hq'
    simp only [kAt, dif_pos hqn, dif_pos hqn']
    have e := (hG ⟨q, hqn⟩ ⟨q', hqn'⟩).1 (hg.trans hg'.symm)
    exact (Obj.lt_prod _ _ _ _ _ _).2 (Or.inr ⟨congrArg _ e, hO ⟨q, hqn⟩ ⟨q', hqn'⟩ hlt e⟩)
  have hrow : ∀ i : Fin C.n.toNat, ∀ v, rep C (C.key.row i) v ↔ v = C.val.row i := fun i v => by
    rw [hR]; constructor
    · rintro ⟨j, hj, rfl⟩; rw [hD j i hj]
    · rintro rfl; exact ⟨i, rfl, rfl⟩
  -- the values at the rows of `t`'s run are what `mapDen` pairs with its keys
  have hV : ∀ t : Fin C.n.toNat, ∀ vs : List (Obj.atom u).El,
      Lang.mapDen (rep C) (((List.range (t.1 + 1)).filter fun q => grp q = grp t).map (kAt t)) vs ↔
      vs = ((List.range (t.1 + 1)).filter fun q => grp q = grp t).map fun q =>
        if hq : q < C.n.toNat then C.val.row ⟨q, hq⟩ else default := by
    intro t vs
    have hval : ∀ q ∈ (List.range (t.1 + 1)).filter (fun q => grp q = grp t), ∀ v,
        rep C (kAt t q) v ↔ v = if hq : q < C.n.toNat then C.val.row ⟨q, hq⟩ else default := fun q hq v => by
      have hqn := (hP t q hq).1
      simp only [kAt, dif_pos hqn]; exact hrow _ v
    constructor
    · rintro ⟨hlen, hvs⟩
      apply List.ext_getElem (by simpa using hlen)
      intro i hi hi'
      have := hvs i (by simpa [← hlen] using hi) hi
      simp only [List.getElem_map] at this ⊢
      exact (hval _ (List.getElem_mem _) _).1 this
    · rintro rfl
      refine ⟨by simp, fun i hi hi' => ?_⟩
      simp only [List.getElem_map]
      exact (hval _ (List.getElem_mem _) _).2 rfl
  simp only [Lang.sumsDen, Core.Rel.comp, Core.Rel.inter, Core.Rel.id, Core.Rel.recip]
  constructor
  · rintro ⟨a', ⟨rfl, b, hb, -⟩, ys, ⟨hys, hmem⟩, vs, hmap, hf⟩
    obtain ⟨⟨c, hc⟩, -⟩ := (hU _ _).1 hb
    obtain ⟨t, rfl, -⟩ := (hR _ _).1 hc
    have hy : ys = ((List.range (t.1 + 1)).filter fun q => grp q = grp t).map (kAt t) :=
      lt_sorted_unique hys (hS t) fun b => (hmem b).trans ((hU _ _).trans
        ⟨fun ⟨_, h⟩ => (hM t b).2 h, fun h => ⟨⟨_, (hR _ _).2 ⟨t, rfl, rfl⟩⟩, (hM t b).1 h⟩⟩)
    subst hy
    exact ⟨t, rfl, (hV t vs).1 hmap ▸ hf⟩
  · rintro ⟨t, rfl, hf⟩
    have hd : ∃ v, rep C (C.key.row t) v := ⟨_, (hR _ _).2 ⟨t, rfl, rfl⟩⟩
    exact ⟨_, ⟨rfl, _, (hU _ _).2 ⟨hd, hd, rfl, hle _⟩, (hU _ _).2 ⟨hd, hd, rfl, hle _⟩⟩, _,
      ⟨hS t, fun b => ((hM t b).trans ⟨fun h => ⟨hd, h⟩, fun ⟨_, h⟩ => h⟩).trans (hU _ _).symm⟩, _,
      (hV t _).2 rfl, hf⟩

namespace Tab

/-- **`canon` ascends in `ν` within a `κ`**: its rows are sorted by the codes of `κ`'s columns, then `ν`'s, then the
value's (`canon_sorted`), so two distinct rows of one `κ` ascend strictly in `ν`. -/
theorem canon_pos_lt {K : Obj} {t : QAtomicType} {f : UInt64 → UInt64} (hf : ascOrd t = some f)
    {x C : Tab (.prod K (.atom t)) .long} (hC : x.canon = .ok C)
    (hD : ∀ i j : Fin C.n.toNat, C.key.row i = C.key.row j → i = j) (i j : Fin C.n.toNat) (hij : i.1 < j.1)
    (hk : (C.key.row i).1 = (C.key.row j).1) : Obj.lt (.atom t) (C.key.row i).2 (C.key.row j).2 := by
  obtain ⟨es, cs, hes, hcs⟩ := canon_codes hC
  obtain ⟨sel, hsel, hord⟩ := canon_sorted hC hes
  have hki : ∀ j, C.key.row j = x.key.row (sel j) := fun j => congrArg Prod.fst (hsel j)
  cases heK : Vals.cols x.key.1 with
  | error s => simp [Vals.cols, heK, bind, Except.bind] at hes
  | ok eK =>
  have hes' : es = eK ++ [(.atom t, Arr.enc x.key.2), (.atom .i64, Arr.enc (t := .i64) x.val)] := by
    simp only [Vals.cols, heK, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at hes; rw [← hes]; simp
  rw [hes'] at hcs
  obtain ⟨csK, csP, hcsK, hcsP, -⟩ := mapM_append_ok hcs
  obtain ⟨cs1, -, hcs1, -, -⟩ := mapM_append_ok (l1 := [(AscKey.atom t, Arr.enc x.key.2)])
    (l2 := [(AscKey.atom .i64, Arr.enc (t := .i64) x.val)]) hcsP
  have hκ : x.key.1.row (sel i) = x.key.1.row (sel j) := by rw [hki, hki] at hk; exact hk
  have hcode := Vals.codes_of_row x.key.1 heK hcsK (sel i) (sel j) hκ
  have hlex := (hord i j hij).1
  rw [hes', ascKeys_append, lexLe_append_of_eq _ _ hcode] at hlex
  have hg : t ≠ .general := by rintro rfl; simp [ascOrd, ascLayout, orderKind] at hf
  have hs : t ≠ .sym := by rintro rfl; simp [ascOrd, ascLayout, orderKind] at hf
  have hv := (Arr.eq_of_codes x.key.2 hcs1).1
  obtain ⟨a, ha, hua, hga⟩ := Arr.get_raw_atom x.key.2 hv hg hs (sel i)
  obtain ⟨b, hb, hub, hgb⟩ := Arr.get_raw_atom x.key.2 hv hg hs (sel j)
  simp only [ascKeys, ascKey, List.cons_append, List.singleton_append, lexLe, Array.getElem?_map, ha, hb,
    Option.map_some, Option.getD_some, hf, Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true,
    beq_iff_eq] at hlex
  obtain ⟨⟨w, fl, sg⟩, hL⟩ : ∃ L, ascLayout t = some L := by
    cases hL : ascLayout t <;> simp [ascOrd, hL] at hf ⊢
  have hfL : f = ordCode w fl sg := by simp [ascOrd, hL] at hf; exact hf.symm
  rw [hki, hki]
  show Obj.lt (.atom t) (Vals.row (A := .atom t) x.key.2 (sel i)) (Vals.row (A := .atom t) x.key.2 (sel j))
  rw [Vals.row_atom, Vals.row_atom, hga, hgb]
  unfold Obj.lt
  rw [Obj.key_ordCode hL hg a hua, Obj.key_ordCode hL hg b hub, ← hfL]
  rcases hlex with h | ⟨h, -⟩
  · simp only [List.cons_lt_cons_iff, List.lt_irrefl, and_false, or_false]
    exact UInt64.lt_iff_toNat_lt.1 h
  · -- equal codes are one position, and two rows of one `κ` at one position are one row
    have e := (Verify.ascOrd_atom hf hg fun h => ⟨hua h, hub h⟩).1 h
    have hne : C.key.row i ≠ C.key.row j := fun e => absurd (hD i j e) (fun h => by rw [h] at hij; exact Nat.lt_irrefl _ hij)
    refine absurd (Prod.ext hk ?_) hne
    rw [hki, hki]
    show Vals.row (A := .atom t) x.key.2 (sel i) = Vals.row (A := .atom t) x.key.2 (sel j)
    rw [Vals.row_atom, Vals.row_atom, hga, hgb, e]

/-- **`sums x` denotes `sumsDen`** (`Rel/Lang/Den.lean`): `x` simple (one value per `(κ, ν)`, else the error), the
segmented `kscan .add` holds each row's prefix sum over its `κ`'s rows ascending in `ν`, and the segmented `kscan .or`
of the bad words keeps a row exactly when no `plus` step of its key up to it wrapped or met the null. -/
theorem sums_holds {K : Obj} {t : QAtomicType} (hord : Lang.OrdAt t) {x T : Tab (.prod K (.atom t)) .long}
    (h : Tab.sumsOn x = .ok T) : rep T = Lang.sumsDen (rep x) := by
  obtain ⟨f, hf⟩ := hord.ascOrd
  dsimp only [Tab.sumsOn] at h
  simp only [bind] at h
  rw [Except.bind_eq_ok'] at h; obtain ⟨C, hC, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨e1, he1, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨⟨m, g1, f1⟩, hk1, h⟩ := h
  split at h
  · iterate 6 (rw [Except.bind_eq_ok'] at h; obtain ⟨_, -, h⟩ := h)
    rw [Except.bind_eq_ok'] at h; obtain ⟨_, h, -⟩ := h; cases h
  rename_i hmn; simp only [ne_eq, Decidable.not_not] at hmn
  rw [Except.bind_eq_ok'] at h; obtain ⟨-, -, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨e2, he2, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨⟨gk, g2, fk⟩, hk2, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨one, hone, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨seg, hseg, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨z, hz, h⟩ := h
  dsimp only at h
  rw [Except.bind_eq_ok'] at h; obtain ⟨⟨W, W2⟩, hr, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨sv, hsv, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨d, hd, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨sd, hsd, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨q1, hq1, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨sw, hsw, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨q2, hq2, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨ovf, hovf, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨nl, hnl, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨eW, heW, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨ev, hev, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨o1, ho1, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨bad, hbad, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨⟨R, R2⟩, hr2, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨Wa, hWa, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨nb, hnb, h⟩ := h
  -- distinct keys: `kseen` over the whole key found `n` runs, so every row is the first of its run
  obtain ⟨cs1, hcs1⟩ := kseen_codes hk1
  obtain ⟨cs2, hcs2⟩ := kseen_codes hk2
  have hfs1 := firsts_spec (seenKey C.n e1) C.n.toNat
  have hall : firstsOf (seenKey C.n e1) C.n.toNat = List.range C.n.toNat :=
    List.filter_sublist.eq_of_length (by rw [List.length_range]; exact (kseen_ok hk1).1.symm.trans hmn)
  have hfirst : ∀ i j : Fin C.n.toNat, i.1 < j.1 → C.key.row i ≠ C.key.row j := fun i j h e =>
    ((hfs1.2.1 j).1 (by rw [hall]; exact List.mem_range.2 j.2)).2 i h (Vals.codes_of_row C.key he1 hcs1 i j e)
  have hD : ∀ i j : Fin C.n.toNat, C.key.row i = C.key.row j → i = j := fun i j e => by
    rcases Nat.lt_trichotomy i.1 j.1 with h' | h' | h'
    · exact absurd e (hfirst i j h')
    · exact Fin.ext h'
    · exact absurd e.symm (hfirst j i h')
  have hG : ∀ i j : Fin C.n.toNat, Verify.groupOf (seenKey C.n e2) C.n.toNat i =
      Verify.groupOf (seenKey C.n e2) C.n.toNat j ↔ (C.key.row i).1 = (C.key.row j).1 := fun i j =>
    ((firsts_spec (seenKey C.n e2) C.n.toNat).2.2.1 i i.2 j j.2).trans
      ⟨Vals.row_of_codes C.key.1 he2 hcs2 i j, Vals.codes_of_row C.key.1 he2 hcs2 i j⟩
  -- the scans: prefix sums and prefix `|` of the bad words over each row's group
  have hbw := badWord_spec hz hsv hd hsd hq1 hsw hq2 hovf hnl heW hev ho1 hbad
  have hW := (segScan_ok (op := .add) (fn := (· + ·)) (fun _ _ => rfl) hk2 hone hseg hz hr).2
  have hB := (segScan_ok (op := .or) (fn := (· ||| ·)) (fun _ _ => rfl) hk2 hone hseg hz hr2).2
  have hF := Lang.sums_fold (kseen_runs hk2) (fun q => (Enc.raw .i64 C.n (Arr.enc (t := .i64) C.val))[q]?.getD 0)
    (fun q => (Enc.raw .i64 C.n W)[q]?.getD 0) (fun q => (Enc.raw .i64 C.n bad)[q]?.getD 0) hW
    (fun t ht => (hbw t ht).2)
  have hBR : ∀ t < C.n.toNat, ((Enc.raw .i64 C.n R)[t]?.getD 0 = 0 ∨ (Enc.raw .i64 C.n R)[t]?.getD 0 = 1) ∧
      ((Enc.raw .i64 C.n R)[t]?.getD 0 = 0 ↔ ∀ q ∈ (List.range (t + 1)).filter (fun q =>
        Verify.groupOf (seenKey C.n e2) C.n.toNat q = Verify.groupOf (seenKey C.n e2) C.n.toNat t),
        (Enc.raw .i64 C.n bad)[q]?.getD 0 = 0) := fun t ht => by
    rw [hB t ht]
    have := foldl_or01 (((List.range (t + 1)).filter (fun q =>
        Verify.groupOf (seenKey C.n e2) C.n.toNat q = Verify.groupOf (seenKey C.n e2) C.n.toNat t)).map
        ((Enc.raw .i64 C.n bad)[·]?.getD 0)) 0 (Or.inl rfl) (fun y hy => by
      obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hy
      simp only [List.mem_filter, List.mem_range] at hq
      exact (hbw q (by omega)).1)
    exact ⟨this.1, this.2.trans ((and_iff_right rfl).trans List.forall_mem_map)⟩
  have hNB : ∀ t < C.n.toNat, (Enc.raw .i64 C.n nb)[t]?.getD 0 = (Enc.raw .i64 C.n R)[t]?.getD 0 ^^^ 1 :=
    fun t ht => by
      have := (colMap_raw hnb).2.2.2 t ht
      simp only [Op.eval, Except.ok.injEq] at this; exact this.symm
  have hWa : ∀ i : Fin C.n.toNat, Vals.row (A := .long) Wa i = ((Enc.raw .i64 C.n W)[i.1]?.getD 0).toInt64 :=
    fun i => by
      have := (colMap_raw (colArr_ok hWa)).2.2.2 i i.2
      rw [colConst_raw hz, Array.getElem?_replicate, if_pos i.2, Option.getD_some] at this
      simp only [Op.eval, Except.ok.injEq, UInt64.add_zero] at this
      rw [Vals.row_atom, Arr.get_i64, ← this]
  have hx : rep x = rep C := funext fun a => funext fun c => propext (canon_holds hC a c).symm
  rw [hx]
  funext a c
  apply propext
  rw [sumsDen_rows hord C (Verify.groupOf (seenKey C.n e2) C.n.toNat) hD hG (canon_pos_lt hf hC hD) a c]
  simp only [show QAtomicType.ofBits .i64 0 = (0 : Int64) from rfl, show Lang.stepAt .i64 Ew.add = Lang.stepDen Ew.add from rfl]
  show T.Holds a c ↔ _
  rw [keep_holds h (fun i hi => by
    rw [hNB i hi]; rcases (hBR i hi).1 with e | e <;> rw [e] <;> decide) a c]
  apply exists_congr; intro t
  have hmap : (((List.range (t.1 + 1)).filter fun q => Verify.groupOf (seenKey C.n e2) C.n.toNat q =
      Verify.groupOf (seenKey C.n e2) C.n.toNat t).map fun q =>
        if hq : q < C.n.toNat then C.val.row ⟨q, hq⟩ else default) =
      ((List.range (t.1 + 1)).filter fun q => Verify.groupOf (seenKey C.n e2) C.n.toNat q =
        Verify.groupOf (seenKey C.n e2) C.n.toNat t).map
        fun q => ((Enc.raw .i64 C.n (Arr.enc (t := .i64) C.val))[q]?.getD 0).toInt64 := by
    apply List.map_congr_left; intro q hq
    simp only [List.mem_filter, List.mem_range] at hq
    rw [dif_pos (by omega), Vals.row_atom, Arr.get_i64]
  rw [hmap, hF t t.2 c, hNB t t.2, hWa t]
  have hb := hBR t t.2
  have hx1 : (Enc.raw .i64 C.n R)[t.1]?.getD 0 ^^^ 1 ≠ 0 ↔ (Enc.raw .i64 C.n R)[t.1]?.getD 0 = 0 := by
    rcases hb.1 with e | e <;> rw [e] <;> decide
  rw [hx1, hb.2]
  constructor <;> rintro ⟨h1, h2, h3⟩ <;> exact ⟨h2, h1, h3.symm⟩

/-- **`sums x` at `f64` values denotes `sumsDen`**, the left fold of `stepAt .f64 add`: `sums_holds`' runs and
segments, the segmented `kscan .fadd` holds each row's IEEE prefix sum `W` (`segScan_ok`), `fto` of it is `W'`; with no
row whose `W'` is neither `W` nor `2^63` (else the error), `sumsF_fold` reads the fold off the bad words. -/
theorem sumsF_holds {K : Obj} {t : QAtomicType} (hord : Lang.OrdAt t)
    {x T : Tab (.prod K (.atom t)) (.atom .f64)} (h : Tab.sumsOn x = .ok T) : rep T = Lang.sumsDen (rep x) := by
  obtain ⟨f, hf⟩ := hord.ascOrd
  dsimp only [Tab.sumsOn] at h
  simp only [bind] at h
  rw [Except.bind_eq_ok'] at h; obtain ⟨C, hC, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨e1, he1, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨⟨m, g1, f1⟩, hk1, h⟩ := h
  split at h
  · iterate 6 (rw [Except.bind_eq_ok'] at h; obtain ⟨_, -, h⟩ := h)
    rw [Except.bind_eq_ok'] at h; obtain ⟨_, h, -⟩ := h; cases h
  rename_i hmn; simp only [ne_eq, Decidable.not_not] at hmn
  rw [Except.bind_eq_ok'] at h; obtain ⟨-, -, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨e2, he2, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨⟨gk, g2, fk⟩, hk2, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨one, hone, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨seg, hseg, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨z, hz, h⟩ := h
  dsimp only at h
  rw [Except.bind_eq_ok'] at h; obtain ⟨⟨W, W2⟩, hr, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨W', hW', h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨nl, hnl, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨nE, hnE, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨nan, hnan, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨nn, hnn, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨odd, hodd, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨⟨k, sel⟩, hk, h⟩ := h
  dsimp only at h
  split at h
  · first | cases h | (simp only [throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at h; cases h)
  rename_i hk0; simp only [ne_eq, Decidable.not_not] at hk0
  rw [Except.bind_eq_ok'] at h; obtain ⟨bad, hbad, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨⟨R, R2⟩, hr2, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨nb, hnb, h⟩ := h
  obtain ⟨cs1, hcs1⟩ := kseen_codes hk1
  obtain ⟨cs2, hcs2⟩ := kseen_codes hk2
  have hfs1 := firsts_spec (seenKey C.n e1) C.n.toNat
  have hall : firstsOf (seenKey C.n e1) C.n.toNat = List.range C.n.toNat :=
    List.filter_sublist.eq_of_length (by rw [List.length_range]; exact (kseen_ok hk1).1.symm.trans hmn)
  have hfirst : ∀ i j : Fin C.n.toNat, i.1 < j.1 → C.key.row i ≠ C.key.row j := fun i j h e =>
    ((hfs1.2.1 j).1 (by rw [hall]; exact List.mem_range.2 j.2)).2 i h (Vals.codes_of_row C.key he1 hcs1 i j e)
  have hD : ∀ i j : Fin C.n.toNat, C.key.row i = C.key.row j → i = j := fun i j e => by
    rcases Nat.lt_trichotomy i.1 j.1 with h' | h' | h'
    · exact absurd e (hfirst i j h')
    · exact Fin.ext h'
    · exact absurd e.symm (hfirst j i h')
  have hG : ∀ i j : Fin C.n.toNat, Verify.groupOf (seenKey C.n e2) C.n.toNat i =
      Verify.groupOf (seenKey C.n e2) C.n.toNat j ↔ (C.key.row i).1 = (C.key.row j).1 := fun i j =>
    ((firsts_spec (seenKey C.n e2) C.n.toNat).2.2.1 i i.2 j j.2).trans
      ⟨Vals.row_of_codes C.key.1 he2 hcs2 i j, Vals.codes_of_row C.key.1 he2 hcs2 i j⟩
  -- the words of each row: the IEEE sum `W`, its `fto` `W'`, the flags
  have hget : ∀ {N : USize} (y : Arr .f64 N) (i : Fin N.toNat), y.get i = (Enc.raw .i64 N y.enc)[i.1]?.getD 0 :=
    fun y i => by have := wideCol_word y rfl (Or.inr rfl) i; simpa [fval] using this
  have hWs := (segScan_ok (op := .fadd) (fn := Lang.faddW) (fun _ _ => rfl) hk2 hone hseg hz hr).2
  have hB := (segScan_ok (op := .or) (fn := (· ||| ·)) (fun _ _ => rfl) hk2 hone hseg hz hr2).2
  have hFW : ∀ q < C.n.toNat, (Enc.raw .i64 C.n W'.enc)[q]?.getD 0 =
      Op.ftoWord .f64 ((Enc.raw .i64 C.n W)[q]?.getD 0) := fun q hq => by
    obtain ⟨v0, hv0, hwi⟩ := (colMap_get (colArr_ok hW')).2 q hq
    rw [hwi, if_neg (by decide), Option.getD_some]; exact (Except.ok.inj hv0).symm
  have hNE := fun q hq => eval_ne_word ((colMap_raw hnE).2.2.2 q hq)
  have hNAN : ∀ q < C.n.toNat, (Enc.raw .i64 C.n nan)[q]?.getD 0 =
      if (Enc.raw .i64 C.n W'.enc)[q]?.getD 0 = 0x8000000000000000 then 1 else 0 := fun q hq => by
    have := eval_eq_word ((colMap_raw hnan).2.2.2 q hq)
    rwa [colConst_raw hnl, Array.getElem?_replicate, if_pos hq, Option.getD_some] at this
  have hOp : ∀ {o : Op} {a b e : Enc}, colMap o C.n a b = .ok e → ∀ q < C.n.toNat,
      o.eval ((Enc.raw .i64 C.n a)[q]?.getD 0) ((Enc.raw .i64 C.n b)[q]?.getD 0) = .ok ((Enc.raw .i64 C.n e)[q]?.getD 0) :=
    fun h q hq => (colMap_raw h).2.2.2 q hq
  have hODD : ∀ q < C.n.toNat, (Enc.raw .i64 C.n odd)[q]?.getD 0 = (Enc.raw .i64 C.n nE)[q]?.getD 0 &&&
      ((Enc.raw .i64 C.n nan)[q]?.getD 0 ^^^ 1) := fun q hq => by
    have a := hOp hodd q hq; have b := hOp hnn q hq
    simp only [Op.eval, Except.ok.injEq] at a b; rw [← a, ← b]
  have hBAD : ∀ q < C.n.toNat, (Enc.raw .i64 C.n bad)[q]?.getD 0 = (Enc.raw .i64 C.n nE)[q]?.getD 0 |||
      (Enc.raw .i64 C.n nan)[q]?.getD 0 := fun q hq => by
    have a := hOp hbad q hq; simp only [Op.eval, Except.ok.injEq] at a; rw [← a]
  have hodd2 : ∀ q < C.n.toNat, (Enc.raw .i64 C.n odd)[q]?.getD 0 < 2 := fun q hq => by
    rw [hODD q hq, hNE q hq, hNAN q hq]; split <;> split <;> decide
  -- no row's `fto` is other than its sum or `2^63`: `whereCol` found none
  have hH : ∀ q < C.n.toNat, (Enc.raw .i64 C.n W'.enc)[q]?.getD 0 = (Enc.raw .i64 C.n W)[q]?.getD 0 ∨
      (Enc.raw .i64 C.n W'.enc)[q]?.getD 0 = 0x8000000000000000 := fun q hq => by
    have h0 : (Enc.raw .i64 C.n odd)[q]?.getD 0 = 0 := by
      by_contra hc
      obtain ⟨j, hj, -⟩ := (whereCol_mem hk hodd2 q).2 ⟨hq, hc⟩
      rw [hk0] at hj; exact absurd hj (by decide)
    rw [hODD q hq, hNE q hq, hNAN q hq] at h0
    by_cases a : (Enc.raw .i64 C.n W'.enc)[q]?.getD 0 = (Enc.raw .i64 C.n W)[q]?.getD 0
    · exact .inl a
    · by_cases b : (Enc.raw .i64 C.n W'.enc)[q]?.getD 0 = 0x8000000000000000
      · exact .inr b
      · rw [if_pos a, if_neg b] at h0; exact absurd h0 (by decide)
  have hbw : ∀ q < C.n.toNat, ((Enc.raw .i64 C.n bad)[q]?.getD 0 = 0 ∨ (Enc.raw .i64 C.n bad)[q]?.getD 0 = 1) ∧
      ((Enc.raw .i64 C.n bad)[q]?.getD 0 = 0 ↔ (Enc.raw .i64 C.n W'.enc)[q]?.getD 0 =
        (Enc.raw .i64 C.n W)[q]?.getD 0 ∧ (Enc.raw .i64 C.n W'.enc)[q]?.getD 0 ≠ 0x8000000000000000) :=
    fun q hq => by
      rw [hBAD q hq, hNE q hq, hNAN q hq]
      by_cases a : (Enc.raw .i64 C.n W'.enc)[q]?.getD 0 = (Enc.raw .i64 C.n W)[q]?.getD 0 <;>
        by_cases b : (Enc.raw .i64 C.n W'.enc)[q]?.getD 0 = 0x8000000000000000 <;> simp [a, b]
  have hF := Lang.sumsF_fold (kseen_runs hk2)
    (fun q => (Enc.raw .i64 C.n (Arr.enc (t := .f64) C.val))[q]?.getD 0)
    (fun q => (Enc.raw .i64 C.n W)[q]?.getD 0) (fun q => (Enc.raw .i64 C.n W'.enc)[q]?.getD 0)
    (fun q => (Enc.raw .i64 C.n bad)[q]?.getD 0) hWs hFW hH (fun t ht => (hbw t ht).2)
  have hBR : ∀ t < C.n.toNat, ((Enc.raw .i64 C.n R)[t]?.getD 0 = 0 ∨ (Enc.raw .i64 C.n R)[t]?.getD 0 = 1) ∧
      ((Enc.raw .i64 C.n R)[t]?.getD 0 = 0 ↔ ∀ q ∈ (List.range (t + 1)).filter (fun q =>
        Verify.groupOf (seenKey C.n e2) C.n.toNat q = Verify.groupOf (seenKey C.n e2) C.n.toNat t),
        (Enc.raw .i64 C.n bad)[q]?.getD 0 = 0) := fun t ht => by
    rw [hB t ht]
    have := foldl_or01 (((List.range (t + 1)).filter (fun q =>
        Verify.groupOf (seenKey C.n e2) C.n.toNat q = Verify.groupOf (seenKey C.n e2) C.n.toNat t)).map
        ((Enc.raw .i64 C.n bad)[·]?.getD 0)) 0 (Or.inl rfl) (fun y hy => by
      obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hy
      simp only [List.mem_filter, List.mem_range] at hq
      exact (hbw q (by omega)).1)
    exact ⟨this.1, this.2.trans ((and_iff_right rfl).trans List.forall_mem_map)⟩
  have hNB : ∀ t < C.n.toNat, (Enc.raw .i64 C.n nb)[t]?.getD 0 = (Enc.raw .i64 C.n R)[t]?.getD 0 ^^^ 1 :=
    fun t ht => by
      have := (colMap_raw hnb).2.2.2 t ht
      simp only [Op.eval, Except.ok.injEq] at this; exact this.symm
  have hWa : ∀ i : Fin C.n.toNat, Vals.row (A := .atom .f64) W' i = (Enc.raw .i64 C.n W'.enc)[i.1]?.getD 0 :=
    fun i => by rw [Vals.row_atom, hget]
  have hx : rep x = rep C := funext fun a => funext fun c => propext (canon_holds hC a c).symm
  rw [hx]
  funext a c
  apply propext
  rw [sumsDen_rows hord C (Verify.groupOf (seenKey C.n e2) C.n.toNat) hD hG (canon_pos_lt hf hC hD) a c]
  show T.Holds a c ↔ _
  rw [keep_holds h (fun i hi => by
    rw [hNB i hi]; rcases (hBR i hi).1 with e | e <;> rw [e] <;> decide) a c]
  apply exists_congr; intro t
  have hmap : (((List.range (t.1 + 1)).filter fun q => Verify.groupOf (seenKey C.n e2) C.n.toNat q =
      Verify.groupOf (seenKey C.n e2) C.n.toNat t).map fun q =>
        if hq : q < C.n.toNat then C.val.row ⟨q, hq⟩ else default) =
      ((List.range (t.1 + 1)).filter fun q => Verify.groupOf (seenKey C.n e2) C.n.toNat q =
        Verify.groupOf (seenKey C.n e2) C.n.toNat t).map
        fun q => (Enc.raw .i64 C.n (Arr.enc (t := .f64) C.val))[q]?.getD 0 := by
    apply List.map_congr_left; intro q hq
    simp only [List.mem_filter, List.mem_range] at hq
    rw [dif_pos (by omega), Vals.row_atom, hget]
  rw [hmap, hF t t.2 c, hNB t t.2, hWa t]
  have hb := hBR t t.2
  have hx1 : (Enc.raw .i64 C.n R)[t.1]?.getD 0 ^^^ 1 ≠ 0 ↔ (Enc.raw .i64 C.n R)[t.1]?.getD 0 = 0 := by
    rcases hb.1 with e | e <;> rw [e] <;> decide
  rw [hx1, hb.2]
  have hmem : t.1 ∈ (List.range (t.1 + 1)).filter (fun q => Verify.groupOf (seenKey C.n e2) C.n.toNat q =
      Verify.groupOf (seenKey C.n e2) C.n.toNat t) := by simp
  constructor
  · rintro ⟨hall, h1, h2⟩
    exact ⟨h1, hall, by rw [← h2]; exact ((hbw t t.2).2.1 (hall t hmem)).1⟩
  · rintro ⟨h1, hall, h2⟩
    exact ⟨hall, h1, by rw [h2]; exact ((hbw t t.2).2.1 (hall t hmem)).1.symm⟩

/-- **`sums x` at any position object denotes `sumsAt`**: it runs only at an integer-stored atom (`intOrd`), where
`ordAt_int` gives `sums_holds` its order. -/
theorem sums_den {K P V : Obj} {x T : Tab (.prod K P) V} (h : Tab.sums x = .ok T) :
    rep T = Lang.sumsAt K P V (rep x) := by
  cases P with
  | atom t =>
    cases V with
    | atom u =>
      cases u <;> simp only [Tab.sums] at h <;> try cases h
      all_goals
        split at h
        · first | exact sums_holds (Lang.ordAt_int ‹_›) h | exact sumsF_holds (Lang.ordAt_int ‹_›) h
        · cases h
    | _ => cases h
  | _ => cases h

end Tab

end Rel
