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

end Lang

end Rel
