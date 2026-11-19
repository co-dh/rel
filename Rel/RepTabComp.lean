import Rel.Run.Comp
import Rel.RepCols
import Rel.RepCanon
import Rel.Run.CRelDef

/-! The laws of `Tab.conv` and `Tab.comp` (`Rel/Run/Comp.lean`), from the five kernels' laws and `Tab.canon_holds`. -/

namespace Rel
open Rel.Ext Rel.Kernel Rel.Verify Ext.Enc


/-- A predicate closed under betweenness, least at `a` wherever it holds, and only below `N`, holds exactly on
`[a, a + c)`, `c` the count of its rows below `N`: a group of sorted rows is one run from its first row. -/
theorem interval_count {P : Nat → Bool} {a N : Nat} (hcl : ∀ x y z, x ≤ y → y ≤ z → P x → P z → P y)
    (hlo : ∀ q, P q → a ≤ q) (hN : ∀ q, P q → q < N) (ha : ∀ q, P q → P a) :
    ∀ q, P q ↔ a ≤ q ∧ q < a + (List.range N).countP P := by
  have key : ∀ M, (∀ q < M, (P q ↔ a ≤ q ∧ q < a + (List.range M).countP P)) ∧
      ((List.range M).countP P = 0 ∨ a + (List.range M).countP P ≤ M) := by
    intro M
    induction M with
    | zero => simp
    | succ M ih =>
      obtain ⟨h1, h2⟩ := ih
      rw [List.range_succ, List.countP_append]
      generalize (List.range M).countP P = c at h1 h2
      by_cases hM : P M
      · have hc' : a + c = M := by
          rcases Nat.eq_zero_or_pos c with h0 | hpos
          · subst h0
            have := hlo M hM
            have hpa := ha M hM
            rcases Nat.lt_or_ge a M with hlt | hge
            · have := (h1 a hlt).1 hpa; omega
            · omega
          · rcases h2 with h2 | h2; · omega
            have hlast : P (a + c - 1) := (h1 (a + c - 1) (by omega)).2 ⟨by omega, by omega⟩
            rcases Nat.lt_or_ge (a + c) M with hlt | hge
            · have := (h1 (a + c) hlt).1 (hcl _ (a + c) M (by omega) (by omega) hlast hM); omega
            · omega
        simp only [List.countP_singleton, hM, if_true]
        refine ⟨fun q hq => ?_, Or.inr (by omega)⟩
        by_cases hqM : q = M
        · subst hqM; exact ⟨fun _ => ⟨by omega, by omega⟩, fun _ => hM⟩
        · rw [h1 q (by omega)]; omega
      · simp only [List.countP_singleton, hM, Bool.false_eq_true, if_false, Nat.add_zero]
        refine ⟨fun q hq => ?_, by omega⟩
        by_cases hqM : q = M
        · subst hqM; simp only [hM, Bool.false_eq_true, false_iff]; omega
        · exact h1 q (by omega)
  intro q
  by_cases hq : q < N
  · exact (key N).1 q hq
  · have h := (key N).2
    exact ⟨fun h1 => absurd (hN q h1) hq, fun h3 => by omega⟩

/-- `lexLe` reads its second row only through its codes. -/
theorem lexLe_congr_right : ∀ (ks : List (Array UInt64)) {i j j' : Nat},
    ks.map (·[j]?.getD 0) = ks.map (·[j']?.getD 0) → lexLe ks i j = lexLe ks i j'
  | [], _, _, _, _ => rfl
  | c :: cs, i, j, j', h => by
    simp only [List.map_cons, List.cons.injEq] at h
    simp only [lexLe, h.1, lexLe_congr_right cs h.2]

/-- Rows with equal codes are `lexLe` both ways. -/
theorem lexLe_of_keys : ∀ (ks : List (Array UInt64)) {i j : Nat},
    ks.map (·[i]?.getD 0) = ks.map (·[j]?.getD 0) → lexLe ks i j = true
  | [], _, _, _ => rfl
  | c :: cs, i, j, h => by
    simp only [List.map_cons, List.cons.injEq] at h
    simp [lexLe, h.1, lexLe_of_keys cs h.2]

/-- Rows `lexLe` both ways have equal codes. -/
theorem keys_of_lexLe : ∀ (ks : List (Array UInt64)) {i j : Nat}, lexLe ks i j = true → lexLe ks j i = true →
    ks.map (·[i]?.getD 0) = ks.map (·[j]?.getD 0)
  | [], _, _, _, _ => rfl
  | c :: cs, i, j, h1, h2 => by
    simp only [lexLe, Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true, beq_iff_eq] at h1 h2
    simp only [List.map_cons, List.cons.injEq]
    rcases h1 with h1 | ⟨e1, h1⟩ <;> rcases h2 with h2 | ⟨e2, h2⟩
    · have := UInt64.lt_iff_toNat_lt.1 h1; have := UInt64.lt_iff_toNat_lt.1 h2; omega
    · rw [e2] at h1; exact absurd (UInt64.lt_iff_toNat_lt.1 h1) (Nat.lt_irrefl _)
    · rw [e1] at h2; exact absurd (UInt64.lt_iff_toNat_lt.1 h2) (Nat.lt_irrefl _)
    · exact ⟨e1, keys_of_lexLe cs h1 h2⟩

/-- Splitting a count by a second predicate. -/
theorem countP_split (p q : Nat → Bool) : ∀ l : List Nat,
    l.countP p = l.countP (fun x => p x && q x) + l.countP (fun x => p x && !q x)
  | [] => rfl
  | x :: l => by
    simp only [List.countP_cons, countP_split p q l]
    cases p x <;> cases q x <;> simp <;> omega

private theorem sum_append_nat : ∀ l1 l2 : List Nat, (l1 ++ l2).sum = l1.sum + l2.sum
  | [], _ => by simp
  | x :: l, l2 => by simp [sum_append_nat l l2, Nat.add_assoc]

/-- **Counting by groups**: where every row's group `gr` is below `K`, the `K` groups' counts of rows with `P` sum
to the count of all rows with `P`. -/
theorem sum_countP_groups (gr : Nat → Nat) (P : Nat → Bool) (l : List Nat) :
    ∀ K, ((List.range K).map fun G => l.countP fun q => gr q == G && P q).sum =
      l.countP fun q => decide (gr q < K) && P q
  | 0 => by simp
  | K + 1 => by
    rw [List.range_succ, List.map_append, sum_append_nat, sum_countP_groups gr P l K,
      countP_split (fun q => decide (gr q < K + 1) && P q) (fun q => gr q == K) l]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero]
    rw [Nat.add_comm]
    congr 1 <;> apply List.countP_congr <;> intro x _ <;> by_cases h : gr x = K <;>
      simp [h] <;> omega

/-- A word below `2^63` read signed is its `Nat`. -/
theorem toInt64_toInt {x : UInt64} (h : x.toNat < 2 ^ 63) : x.toInt64.toInt = x.toNat := by
  rw [show x.toInt64.toInt = x.toBitVec.toInt from rfl, BitVec.toInt]; simp only [UInt64.toNat_toBitVec]
  omega

/-- Folding `.add` over `0`/`1` words counts the ones. -/
theorem foldl_add_count (P : Nat → Bool) : ∀ (l : List Nat) (a : UInt64),
    (l.map fun q => if P q then (1 : UInt64) else 0).foldl (· + ·) a = a + (l.countP P).toUInt64
  | [], a => by simp
  | q :: l, a => by
    simp only [List.map_cons, List.foldl_cons, foldl_add_count P l, List.countP_cons]
    cases P q <;> simp [UInt64.ofNat_add, UInt64.add_assoc, UInt64.add_comm]

/-- Folding signed `max` over words below `2^63`: the answer is the start or an element, at least each. -/
theorem foldl_max_spec : ∀ (l : List UInt64) (a : UInt64), (∀ x ∈ l, x.toNat < 2 ^ 63) → a.toNat < 2 ^ 63 →
    let r := l.foldl (fun a x => if a.toInt64 < x.toInt64 then x else a) a
    a.toNat ≤ r.toNat ∧ (∀ x ∈ l, x.toNat ≤ r.toNat) ∧ (r = a ∨ r ∈ l)
  | [], a, _, _ => by simp
  | x :: l, a, hl, ha => by
    have hx := hl x (List.mem_cons_self ..)
    simp only [List.foldl_cons]
    have hlt : a.toInt64 < x.toInt64 ↔ a.toNat < x.toNat := by
      rw [Int64.lt_iff_toInt_lt, toInt64_toInt ha, toInt64_toInt hx]; omega
    have ha' : (if a.toInt64 < x.toInt64 then x else a).toNat < 2 ^ 63 := by split <;> assumption
    obtain ⟨h1, h2, h3⟩ := foldl_max_spec l _ (fun y hy => hl y (List.mem_cons_of_mem _ hy)) ha'
    have hge : a.toNat ≤ (if a.toInt64 < x.toInt64 then x else a).toNat ∧
        x.toNat ≤ (if a.toInt64 < x.toInt64 then x else a).toNat := by
      split <;> rename_i h <;> rw [hlt] at h <;> omega
    refine ⟨Nat.le_trans hge.1 h1, fun y hy => ?_, ?_⟩
    · rcases List.mem_cons.1 hy with rfl | hy
      · exact Nat.le_trans hge.2 h1
      · exact h2 y hy
    · rcases h3 with e | e
      · rw [e]; split
        · exact Or.inr (List.mem_cons_self ..)
        · exact Or.inl rfl
      · exact Or.inr (List.mem_cons_of_mem _ e)

namespace Tab
variable {A B C : Obj}

/-- **`R.conv` denotes `R°`** (`Rep.rep_conv`'s statement, pointwise). -/
theorem conv_holds {R : Tab A B} {S : Tab B A} (h : R.conv = .ok S) (b : B.El) (a : A.El) :
    S.Holds b a ↔ R.Holds a b := by
  rw [canon_holds h]; exact ⟨fun ⟨i, h1, h2⟩ => ⟨i, h2, h1⟩, fun ⟨i, h1, h2⟩ => ⟨i, h2, h1⟩⟩

end Tab

/-! ## Checks on `foR` tables -/

section Checks


#guard ((tab [(3, 1), (1, 2), (3, 1), (-1, 2)]).conv.toOption.map Tab.toList) == some [(1, 3), (2, -1), (2, 1)]
#guard ((tab [(3, 1), (1, 2), (-1, 2), (1, 2)]).comp (tab [(2, 5), (1, -3), (2, 6), (7, 7)])).toOption.map Tab.toList ==
  some [(-1, 5), (-1, 6), (1, 5), (1, 6), (3, -3)]
-- the five-kernel `comp` and `conv` against the old `CRel.comp` and `ofC (R°)` on the same tables: duplicates,
-- negatives, an empty side, no common middle value, a group whose run product is past 1
#guard
  let ts : List (List (Int64 × Int64)) := [[(3, 1), (1, 2), (3, 1), (-1, 2), (1, 2), (2, 7), (-5, -5), (0, 0)],
    [(2, 5), (1, -3), (2, 6), (7, 7), (9, 0), (2, 5), (-5, 4), (0, 0)], [(-2, 9), (-2, 9), (7, -3)], [(4, 8)], []]
  ts.all fun ps => (ts.all fun qs => ((tab ps).comp (tab qs)).toOption.isSome &&
    ((tab ps).comp (tab qs)).toOption.map Tab.toList == (CRel.comp (some (tab ps)) (some (tab qs))).map Tab.toList) &&
    (tab ps).conv.toOption.isSome && ((tab ps).conv.toOption.map Tab.toList) ==
      (let c := Alg.canonC (⟨(tab ps).n, (tab ps).val, (tab ps).key⟩ : Tab .long .long)
       if c.2 then some c.1.toList else none)

end Checks

#print axioms Tab.conv_holds

end Rel
