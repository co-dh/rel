module

public import Rel.KernelSpec.Closure

-- exposed: every def body is a spec a downstream `rfl`/`decide`/`simp` may unfold (PLAN W.8)
@[expose] public section

/-! The count of `kseen`'s groups read off its group column: a `kscan max` from a seed of zeros, with no row starting
a segment, folds every row's group, and the largest group is the count less one (the last first row's group). So a
plan that keeps only `kseen`'s group column (`seenB`) reads the count `kseen` answers. -/

namespace Rel.Verify
open Rel.Kernel Enc

/-- `max` of two words below `2^63`, which `Op.max` compares signed: the larger, as `Nat`. -/
theorem eval_max_nat {a b : Nat} (ha : a < 2 ^ 63) (hb : b < 2 ^ 63) :
    Op.eval .max a.toUInt64 b.toUInt64 = .ok (max a b).toUInt64 := by
  have e : ∀ x : Nat, x < 2 ^ 63 → x.toUInt64.toInt64.toInt = x := fun x hx => by
    rw [toInt_toInt64, if_pos (by simp; omega)]; simp; omega
  simp only [Op.eval, Op.i, Except.ok.injEq]
  have hl : a.toUInt64.toInt64 < b.toUInt64.toInt64 ↔ a < b := by rw [Int64.lt_iff_toInt_lt, e a ha, e b hb]; omega
  by_cases h : a < b
  · rw [if_pos (hl.2 h), Nat.max_eq_right (by omega)]
  · rw [if_neg (fun h' => h (hl.1 h')), Nat.max_eq_left (by omega)]

/-- **`kscan max` over `kseen`'s groups answers its count**: from the seed `z` of `n` zeros (`kscatter` of no row),
with `z` also as the segment marks (no row starts a segment), the fold over the group column `g` is the largest
group, `k − 1`; at `n = 0` there is no row, no fold and no group. The groups are compared signed, so `n ≤ 2^63`. -/
theorem kseen_count_max {n : USize} {es : List (AscKey × Enc)} {k : Nat} {g f z : Enc} {r : Enc × Option UInt64}
    (hn : n.toNat ≤ 2 ^ 63) (hk : kseen n es = .ok (k, g, f))
    (hz : kscatter .last 0 (wordsFoR #[]) (wordsFoR #[]) n 0 = .ok z)
    (hs : kscan .max false .i64 .i64 n (some z) [(n, z), (n, g)] = .ok r) :
    (n.toNat = 0 → k = 0 ∧ r.2 = none) ∧ (n.toNat ≠ 0 → 0 < k ∧ r.2 = some (k - 1).toUInt64) := by
  obtain ⟨hkk, rfl, -⟩ := kseen_ok hk
  have fs := firsts_spec (seenKey n es) n.toNat
  generalize hG : groupOf (seenKey n es) n.toNat = G at hs
  have hGk : ∀ i < n.toNat, G i < k := fun i hi => by rw [← hG, hkk]; exact groupOf_lt hi
  have hzN : hasNul z = false := kscatter_plain hz (hasNul_wordsFoR _)
  obtain ⟨hzf, -, -, hzs, -, hz0, -⟩ := raw_scatter 0 _ _ n 0 z (hasNul_wordsFoR _) hz
  have hz0 : ∀ i < n.toNat, (raw .i64 n z)[i]?.getD 0 = 0 := fun i hi => by
    rw [hz0 i hi (fun _ h => absurd h (by simp))]; rfl
  obtain ⟨M, P, rfl⟩ : ∃ M P, z = .foR M P := ⟨_, _, hzf⟩
  -- the marks read at `u1` are the low bits of the zeros read at `i64`
  have hseg : ∀ i < n.toNat, (raw .u1 n (.foR M P))[i]?.getD 0 = 0 := fun i hi => by
    have h := hz0 i hi
    simp only [raw, QAtomicType.width, Array.getElem?_map, Array.getElem?_range, hi, if_true, Option.map_some,
      Option.getD_some] at h ⊢
    have hb := (Column.foRBits M P (Column.blockStarts M) i).toNat_lt
    have h0 : (Column.foRBits M P (Column.blockStarts M) i).toNat = 0 := by
      have := congrArg UInt64.toNat h; simp at this; omega
    rw [h0]; rfl
  have hgN : hasNul (wordsFoR (Array.ofFn (n := n.toNat) fun i => (G i.1).toUInt64)) = false := hasNul_wordsFoR _
  have hgw : ∀ i < n.toNat, (raw .i64 n (wordsFoR (Array.ofFn (n := n.toNat) fun i => (G i.1).toUInt64)))[i]?.getD 0 =
      (G i).toUInt64 := fun i hi => by
    rw [(wordsFoR_closed _ (by simp)).2.1]; simp [hi]
  obtain ⟨-, -, c, cs, hc, out, hos, -, hv, hrow⟩ := raw_kscan .max (by decide) false .i64 .i64 8 rfl n (.foR M P)
    [(n, .foR M P), (n, wordsFoR (Array.ofFn (n := n.toNat) fun i => (G i.1).toUInt64))] r rfl
    (Or.inr (by simp [hzN, hgN])) hs
  simp only [List.map_cons, List.map_nil, List.cons.injEq] at hc
  obtain ⟨rfl, rfl⟩ := hc
  have hkn : k ≤ n.toNat := by rw [hkk]; exact Nat.le_trans (List.length_filter_le _ _) (by simp)
  have hlt : ∀ i < n.toNat, G i < 2 ^ 63 := fun i hi => by have := hGk i hi; omega
  -- row `i` holds the largest group of the rows up to it
  have inv : ∀ i < n.toNat, ∃ m, out[i]?.getD 0 = m.toUInt64 ∧ m < k ∧ (∃ j ≤ i, G j = m) ∧ ∀ j ≤ i, G j ≤ m := by
    intro i
    induction i with
    | zero =>
      intro hi
      have e := hrow 0 (by omega)
      simp only [Bool.false_eq_true, ↓reduceIte, Nat.lt_irrefl, false_and, List.map_cons, List.map_nil,
        List.foldlM_cons, List.foldlM_nil, hz0 0 hi, hgw 0 hi] at e
      rw [show (0 : UInt64) = (0 : Nat).toUInt64 from rfl, eval_max_nat (by omega) (hlt 0 hi)] at e
      refine ⟨G 0, ?_, hGk 0 hi, ⟨0, Nat.le_refl _, rfl⟩, fun j hj => by rw [Nat.le_zero.1 hj]; exact Nat.le_refl _⟩
      rw [Array.getElem?_eq_getElem (by omega), Option.getD_some]
      simpa using (Except.ok.inj e).symm
    | succ i ih =>
      intro hi
      obtain ⟨m, hm, hmk, ⟨j0, hj0, hjm⟩, hle⟩ := ih (by omega)
      have e := hrow (i + 1) (by omega)
      simp only [Bool.false_eq_true, ↓reduceIte, List.map_cons, List.map_nil, List.foldlM_cons, List.foldlM_nil,
        hseg (i + 1) hi, Nat.add_sub_cancel, hm, hgw (i + 1) hi, show 0 < i + 1 by omega, and_self] at e
      rw [eval_max_nat (by omega) (hlt (i + 1) hi)] at e
      refine ⟨max m (G (i + 1)), ?_, by have := hGk (i + 1) hi; omega, ?_, fun j hj => ?_⟩
      · rw [Array.getElem?_eq_getElem (by omega), Option.getD_some]; simpa using (Except.ok.inj e).symm
      · by_cases h : m ≤ G (i + 1)
        · exact ⟨i + 1, Nat.le_refl _, by omega⟩
        · exact ⟨j0, by omega, by omega⟩
      · rcases Nat.lt_or_ge j (i + 1) with h | h
        · have := hle j (by omega); omega
        · rw [show j = i + 1 by omega]; omega
  refine ⟨fun h0 => ⟨?_, ?_⟩, fun h0 => ?_⟩
  · rw [hkk]; exact List.length_eq_zero_iff.2 (List.filter_eq_nil_iff.2 fun i hi => by simp [h0] at hi)
  · rw [hv, Array.back?_eq_getElem?]; simp [hos, h0]
  -- the last first row's group is `k − 1`, so the largest group is
  have hk0 : 0 < k := by have := hGk 0 (by omega); omega
  obtain ⟨m, hm, hmk, -, hle⟩ := inv (n.toNat - 1) (by omega)
  have hl : k - 1 < (firstsOf (seenKey n es) n.toNat).length := by rw [← hkk]; omega
  have hf := fs.2.2.2.1 (k - 1) hl
  rw [hG] at hf
  have hfn : (firstsOf (seenKey n es) n.toNat)[k - 1] < n.toNat := firsts_lt _ _ (List.getElem_mem _)
  have := hle _ (by omega : (firstsOf (seenKey n es) n.toNat)[k - 1] ≤ n.toNat - 1)
  rw [hf] at this
  refine ⟨hk0, ?_⟩
  rw [hv, Array.back?_eq_getElem?, hos, Array.getElem?_eq_getElem (by omega), Option.map_some]
  have hm' : out[n.toNat - 1]'(by omega) = m.toUInt64 := by
    rw [← hm, Array.getElem?_eq_getElem (by omega), Option.getD_some]
  rw [hm', show m = k - 1 by omega]
  simp only [if_neg (show QAtomicType.i64 ≠ .u1 by decide), Option.some.injEq]
  rw [UInt64.toNat_ofNat', Nat.mod_mod]; simp only [Nat.reducePow]
  rw [Nat.mod_eq_of_lt (by omega)]

end Rel.Verify
