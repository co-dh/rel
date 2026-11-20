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

/-- Flipping bit 63 of a word adds `2^63` below it and takes `2^63` off above it. -/
theorem Nat.xor_top {x : Nat} (hx : x < 2 ^ 64) : x ^^^ 2 ^ 63 = if x < 2 ^ 63 then x + 2 ^ 63 else x - 2 ^ 63 := by
  have key : ∀ y < 2 ^ 63, y ^^^ 2 ^ 63 = y + 2 ^ 63 := fun y hy => by
    rw [Nat.add_comm]
    apply Nat.eq_of_testBit_eq; intro i
    rw [Nat.testBit_xor, Nat.testBit_two_pow]
    rcases Nat.lt_trichotomy i 63 with hi | rfl | hi
    · rw [Nat.testBit_two_pow_add_gt hi, decide_eq_false (by omega : ¬ 63 = i)]; simp
    · rw [Nat.testBit_two_pow_add_eq, Nat.testBit_lt_two_pow hy]; simp
    · have h1 : 2 ^ 63 + y < 2 ^ i := Nat.lt_of_lt_of_le (by omega) (Nat.pow_le_pow_right (by omega) hi)
      rw [Nat.testBit_lt_two_pow h1, Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hy (Nat.pow_le_pow_right
        (by omega) (by omega))), decide_eq_false (by omega : ¬ 63 = i)]; simp
  split
  · exact key x ‹_›
  · have e := key (x - 2 ^ 63) (by omega)
    rw [show x - 2 ^ 63 + 2 ^ 63 = x by omega] at e
    have e' : x ^^^ 2 ^ 63 = (x - 2 ^ 63 ^^^ 2 ^ 63) ^^^ 2 ^ 63 := by rw [e]
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
  rw [UInt64.toNat_xor, show (0x8000000000000000 : UInt64).toNat = 2 ^ 63 from rfl, Nat.xor_top hx,
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
  have := Int64.le_toInt a; have := Int64.toInt_lt a; have := Int64.le_toInt b; have := Int64.toInt_lt b
  show [(Order.rank .i64 a.toUInt64).toNat] < [(Order.rank .i64 b.toUInt64).toNat] ↔ a < b
  simp only [List.cons_lt_cons_iff, List.lt_irrefl, and_false, or_false, Order.rank, Int64.code_toNat,
    Int64.lt_iff_toInt_lt]
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
theorem upToDen_iff {K : Obj} (T : Den (.prod K .long) .long) (a b : (Obj.prod K .long).El) :
    upToDen T a b ↔ (∃ c, T a c) ∧ (∃ c, T b c) ∧ a.1 = b.1 ∧ b.2 ≤ a.2 := by
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

end Lang

/-- **`sumsDen` on a table of distinct keys whose groups `grp` (equal `κ`) ascend in `ν` with the row**: `(κ, ν)` to
the left fold over the values of the rows `≤ t` of `t`'s group, `t` the row of `(κ, ν)`. -/
theorem sumsDen_rows {K : Obj} (C : Tab (.prod K .long) .long) (grp : Nat → Nat)
    (hD : ∀ i j : Fin C.n.toNat, C.key.row i = C.key.row j → i = j)
    (hG : ∀ i j : Fin C.n.toNat, grp i = grp j ↔ (C.key.row i).1 = (C.key.row j).1)
    (hO : ∀ i j : Fin C.n.toNat, i.1 < j.1 → (C.key.row i).1 = (C.key.row j).1 →
      (C.key.row i).2 < (C.key.row j).2) (a : (Obj.prod K .long).El) (w : Int64) :
    Lang.sumsDen (rep C) a w ↔ ∃ t : Fin C.n.toNat, C.key.row t = a ∧
      Lang.foldDen (E := .long) (V := .long) (fun _ b => b = 0) (Lang.stepDen Ew.add)
        (((List.range (t.1 + 1)).filter fun q => grp q = grp t).map fun q =>
          if hq : q < C.n.toNat then C.val.row ⟨q, hq⟩ else 0) w := by
  have hR : ∀ b v, rep C b v ↔ ∃ i, C.key.row i = b ∧ C.val.row i = v := fun _ _ => Iff.rfl
  have hU : ∀ b c, Lang.upToDen (rep C) b c ↔ (∃ v, rep C b v) ∧ (∃ v, rep C c v) ∧ b.1 = c.1 ∧ c.2 ≤ b.2 :=
    fun b c => Lang.upToDen_iff _ b c
  have hle : ∀ y : Int64, y ≤ y := fun y => by rw [Int64.le_iff_toInt_le]; exact Int.le_refl _
  have hP : ∀ t : Fin C.n.toNat, ∀ q ∈ (List.range (t.1 + 1)).filter (fun q => grp q = grp t),
      q < C.n.toNat ∧ q ≤ t.1 ∧ grp q = grp t := fun t q hq => by
    simp only [List.mem_filter, List.mem_range, decide_eq_true_eq] at hq; exact ⟨by omega, by omega, hq.2⟩
  let kAt (t : Fin C.n.toNat) (q : Nat) : (Obj.prod K .long).El :=
    if hq : q < C.n.toNat then C.key.row ⟨q, hq⟩ else C.key.row t
  have hM : ∀ t : Fin C.n.toNat, ∀ b, b ∈ ((List.range (t.1 + 1)).filter fun q => grp q = grp t).map (kAt t) ↔
      (∃ v, rep C b v) ∧ (C.key.row t).1 = b.1 ∧ b.2 ≤ (C.key.row t).2 := by
    intro t b
    rw [List.mem_map]
    constructor
    · rintro ⟨q, hq, rfl⟩
      obtain ⟨hqn, hqt, hg⟩ := hP t q hq
      simp only [kAt, dif_pos hqn]
      refine ⟨⟨_, (hR _ _).2 ⟨⟨q, hqn⟩, rfl, rfl⟩⟩, ((hG ⟨q, hqn⟩ t).1 hg).symm, ?_⟩
      rcases Nat.lt_or_ge q t.1 with h | h
      · have := hO ⟨q, hqn⟩ t h ((hG ⟨q, hqn⟩ t).1 hg)
        rw [Int64.lt_iff_toInt_lt] at this; rw [Int64.le_iff_toInt_le]; omega
      · obtain rfl : t = ⟨q, hqn⟩ := Fin.ext (show t.1 = q by omega); exact hle _
    · rintro ⟨⟨v, hv⟩, h1, h2⟩
      obtain ⟨q, rfl, -⟩ := (hR _ _).1 hv
      refine ⟨q.1, ?_, by simp only [kAt, dif_pos q.2]⟩
      simp only [List.mem_filter, List.mem_range, decide_eq_true_eq]
      refine ⟨?_, (hG q t).2 h1.symm⟩
      apply Nat.lt_of_not_le; intro hc
      have := hO t q (by omega) h1
      rw [Int64.lt_iff_toInt_lt] at this; rw [Int64.le_iff_toInt_le] at h2; omega
  have hS : ∀ t : Fin C.n.toNat,
      (((List.range (t.1 + 1)).filter fun q => grp q = grp t).map (kAt t)).Pairwise (Obj.prod K .long).lt := by
    intro t
    rw [List.pairwise_map]
    refine ((List.pairwise_lt_range).filter _).imp_of_mem fun {q q'} hq hq' hlt => ?_
    obtain ⟨hqn, -, hg⟩ := hP t q hq; obtain ⟨hqn', -, hg'⟩ := hP t q' hq'
    simp only [kAt, dif_pos hqn, dif_pos hqn']
    have e := (hG ⟨q, hqn⟩ ⟨q', hqn'⟩).1 (hg.trans hg'.symm)
    exact (Obj.lt_prod _ _ _ _ _ _).2 (Or.inr ⟨congrArg _ e, (Obj.lt_long _ _).2 (hO ⟨q, hqn⟩ ⟨q', hqn'⟩ hlt e)⟩)
  have hrow : ∀ i : Fin C.n.toNat, ∀ v, rep C (C.key.row i) v ↔ v = C.val.row i := fun i v => by
    rw [hR]; constructor
    · rintro ⟨j, hj, rfl⟩; rw [hD j i hj]
    · rintro rfl; exact ⟨i, rfl, rfl⟩
  -- the values at the rows of `t`'s run are what `mapDen` pairs with its keys
  have hV : ∀ t : Fin C.n.toNat, ∀ vs : List Int64,
      Lang.mapDen (rep C) (((List.range (t.1 + 1)).filter fun q => grp q = grp t).map (kAt t)) vs ↔
      vs = ((List.range (t.1 + 1)).filter fun q => grp q = grp t).map fun q =>
        if hq : q < C.n.toNat then C.val.row ⟨q, hq⟩ else 0 := by
    intro t vs
    have hval : ∀ q ∈ (List.range (t.1 + 1)).filter (fun q => grp q = grp t), ∀ v,
        rep C (kAt t q) v ↔ v = if hq : q < C.n.toNat then C.val.row ⟨q, hq⟩ else 0 := fun q hq v => by
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

end Rel
