module

public import Rel.Run.Merge
public import Rel.RepSetOps
public import Rel.RepOrder
public import Rel.RepCanon
public import Rel.RepTabComp
public import Rel.RepTabDiv
public import Rel.RepWF

-- exposed: every def body is a spec a downstream `rfl`/`decide`/`simp` may unfold (PLAN W.8)
@[expose] public section

/-! The laws of `Vals.cmpRows` and `Vals.rank` (`Rel/Run/Merge.lean`, architecture §4.7): the row compare reads `<` and `=`
of two rows off the group numbers of `kasc ≫ kseen`, so it is `Obj.lt` and `=`; `rank` is the bisection on that compare. -/

namespace Rel
open Rel.Ext Rel.Kernel Rel.Verify

/-- **Groups are numbered in the order of their keys**: where a key's rows are runs (`kseen_runs`), rows `a < b` of two
different keys are in groups `groupOf a < groupOf b`. The first row `f` of `b`'s group, if it were before `a`'s,
would put `a` between two rows of one key. -/
theorem groupOf_lt_of_runs {K : Nat → List UInt64} {m : Nat}
    (runs : ∀ a b c, a ≤ b → b ≤ c → c < m → K a = K c → K b = K a) {a b : Nat} (hb : b < m) (hab : a < b)
    (hne : K a ≠ K b) : groupOf K m a < groupOf K m b := by
  have ha : a < m := by omega
  obtain ⟨fp, -, hg, -, -, hf⟩ := firsts_spec K m
  have hne' : groupOf K m a ≠ groupOf K m b := fun e => hne ((hg a ha b hb).1 e)
  obtain ⟨hja, hfa, hKa, -⟩ := hf a ha
  obtain ⟨hjb, hfb, hKb, -⟩ := hf b hb
  rcases Nat.lt_or_gt_of_ne hne' with h | h
  · exact h
  · exfalso
    have hl := List.pairwise_iff_getElem.1 fp _ _ hjb hja h
    have := runs (firstsOf K m)[groupOf K m b] a b (by omega) (by omega) hb hKb
    exact hne (this.trans hKb)

/-- **`kasc ≫ kseen ≫ kscatter .last` numbers every row by its key's rank**: row `r` gets `cd r < N`; two rows have one
number iff they have one `seenKey`, and a smaller number means `lexLe` and a different `seenKey`. -/
theorem codes_spec {A : Obj} {N : USize} {x : Vals A N} {es : List (AscKey × Enc)} (hes : ValsB.cols x = .ok es)
    {vs : List Enc} {p : Enc} (ha : kasc N es = .ok (vs, p)) {k : Nat} {g f : Enc}
    (hs : kseen N ((es.map (·.1)).zip vs) = .ok (k, g, f)) {code : Enc} (hsc : kscatter .last N p g N 0 = .ok code) :
    hasNul code = false ∧ ∃ cd : Nat → Nat, (∀ r < N.toNat, (Enc.raw .i64 N code)[r]?.getD 0 = (cd r).toUInt64 ∧ cd r < N.toNat) ∧
      (∀ a < N.toNat, ∀ b < N.toNat, cd a = cd b ↔ seenKey N es a = seenKey N es b) ∧
      ∀ a < N.toNat, ∀ b < N.toNat, cd a < cd b → lexLe (ascKeys N es) a b = true ∧ seenKey N es a ≠ seenKey N es b := by
  obtain ⟨ps, hp, hperm, -⟩ := asc_perm N es vs p ha
  have hps := asc_perm_grade ha hp hperm
  have hkey := Vals.sorted_key hes ha hp hperm
  have hlen : ps.length = N.toNat := by simpa using hperm.length_eq
  obtain ⟨-, hg, -⟩ := kseen_ok hs
  have hruns := kseen_runs hs
  generalize seenKey N ((es.map (·.1)).zip vs) = K at hg hkey hruns
  have hn := N.toNat_lt_size
  have hU : USize.size ≤ 2 ^ 64 := by rcases USize.size_eq with h | h <;> omega
  have hc64 : ∀ a, a < N.toNat → a.toUInt64.toNat = a := fun a ha => by simp; omega
  have hrp : Enc.raw .i64 N p = (ps.map Nat.toUInt64).toArray := by
    rw [hp]; exact (wordsFoR_closed _ (by simp [hlen])).2.1
  have hrg : Enc.raw .i64 N g = Array.ofFn (n := N.toNat) fun i => (groupOf K N.toNat i.1).toUInt64 := by
    rw [hg]; exact (wordsFoR_closed _ (by simp)).2.1
  obtain ⟨-, -, -, hws, -, -, hlast⟩ := raw_scatter N p g N 0 code (by rw [hg]; exact hasNul_wordsFoR _) hsc
  have hnd : ps.Nodup := hperm.nodup_iff.2 (List.nodup_range)
  have hinj : ∀ i j (hi : i < ps.length) (hj : j < ps.length), ps[i] = ps[j] → i = j := fun i j hi hj e => by
    have hp := List.pairwise_iff_getElem.1 hnd
    rcases Nat.lt_trichotomy i j with h | h | h
    · exact absurd e (hp i j hi hj h)
    · exact h
    · exact absurd e.symm (hp j i hj hi h)
  have hlt : ∀ q (hq : q < ps.length), ps[q] < N.toNat := fun q hq =>
    List.mem_range.1 (hperm.mem_iff.1 (List.getElem_mem hq))
  have hrpk : ∀ k (hk : k < ps.length), (Enc.raw .i64 N p)[k]?.getD 0 = ps[k].toUInt64 := fun k hk => by
    rw [hrp]; simp [hk]
  have hrgk : ∀ q, q < N.toNat → (Enc.raw .i64 N g)[q]?.getD 0 = (groupOf K N.toNat q).toUInt64 := fun q hq => by
    rw [hrg]; simp [hq]
  have cq : ∀ q (hq : q < ps.length), (Enc.raw .i64 N code)[ps[q]]?.getD 0 = (groupOf K N.toNat q).toUInt64 := by
    intro q hq
    have := hlast q (by omega) fun k' h1 h2 e => by
      rw [hrpk k' (by omega), hrpk q hq] at e
      have e' := congrArg UInt64.toNat e
      rw [hc64 _ (hlt k' (by omega)), hc64 _ (hlt q hq)] at e'
      have := hinj _ _ (by omega) hq e'
      omega
    rw [hrpk q hq, hc64 _ (hlt q hq), hrgk q (by omega)] at this
    rw [this]; rfl
  have pos : ∀ r, ∃ q, r < N.toNat → ∃ hq : q < ps.length, ps[q] = r := fun r => by
    by_cases hr : r < N.toNat
    · obtain ⟨q, hq, e⟩ := List.getElem_of_mem (hperm.mem_iff.2 (List.mem_range.2 hr))
      exact ⟨q, fun _ => ⟨hq, e⟩⟩
    · exact ⟨0, fun h => absurd h hr⟩
  obtain ⟨pos, hpos⟩ := Classical.axiomOfChoice pos
  have hfl : (firstsOf K N.toNat).length ≤ N.toNat := by
    unfold firstsOf; exact Nat.le_trans (List.length_filter_le _ _) (by simp)
  have hKq : ∀ q (hq : q < ps.length), K q = seenKey N es ps[q] := hkey
  have hsort : ps.Pairwise fun i j => lexLe (ascKeys N es) i j = true ∧ (lexLe (ascKeys N es) j i = true → i < j) := by
    rw [hps]; exact (ascGrade_spec N.toNat (ascKeys N es)).2
  refine ⟨kscatter_plain hsc (by rw [hg]; exact hasNul_wordsFoR _), fun r => groupOf K N.toNat (pos r), fun r hr => ?_, fun a ha b hb => ?_, fun a ha b hb hab => ?_⟩
  · obtain ⟨hq, e⟩ := hpos r hr
    refine ⟨?_, Nat.lt_of_lt_of_le (groupOf_lt (by omega)) hfl⟩
    rw [← cq _ hq, e]
  · obtain ⟨hqa, ea⟩ := hpos a ha
    obtain ⟨hqb, eb⟩ := hpos b hb
    show groupOf K N.toNat (pos a) = groupOf K N.toNat (pos b) ↔ _
    rw [(firsts_spec K N.toNat).2.2.1 _ (by omega) _ (by omega), hKq _ hqa, hKq _ hqb, ea, eb]
  · obtain ⟨hqa, ea⟩ := hpos a ha
    obtain ⟨hqb, eb⟩ := hpos b hb
    have hne : K (pos a) ≠ K (pos b) := fun e => by
      have := ((firsts_spec K N.toNat).2.2.1 _ (by omega) _ (by omega)).2 e
      simp only at hab; omega
    have hpab : pos a < pos b := by
      refine Classical.byContradiction fun hn => ?_
      rcases Nat.lt_or_ge (pos b) (pos a) with h | h
      · have := groupOf_lt_of_runs hruns (by omega) h (Ne.symm hne)
        simp only at hab; omega
      · have : pos a = pos b := by omega
        exact hne (by rw [this])
    refine ⟨?_, fun e => hne (by rw [hKq _ hqa, hKq _ hqb, ea, eb]; exact e)⟩
    have := (List.pairwise_iff_getElem.1 hsort _ _ hqa hqb hpab).1
    rwa [ea, eb] at this




/-- **`cmpRows` is `<` and `=` of the rows**, row by row, as `0`/`1` words: `P.row i` against `T.row i` in `Obj.lt`
and in `=`. The group numbers are below `2 * m ≤ 2^63`, so the signed `lt` word reads them as naturals. -/
theorem Vals.cmpRows_spec {A : Obj} {m : USize} {P T : Vals A m} (hP : Vals.WF P) (hT : Vals.WF T)
    (hm : 2 * m.toNat ≤ 2 ^ 63) {c e : Enc} (h : Vals.cmpRows P T = .ok (c, e)) (i : Fin m.toNat) :
    ((Enc.raw .i64 m c)[i.1]?.getD 0 = 1 ↔ A.lt (P.row i) (T.row i)) ∧ (Enc.raw .i64 m c)[i.1]?.getD 0 ≤ 1 ∧
    ((Enc.raw .i64 m e)[i.1]?.getD 0 = 1 ↔ P.row i = T.row i) ∧ (Enc.raw .i64 m e)[i.1]?.getD 0 ≤ 1 := by
  unfold Vals.cmpRows at h
  simp only [Bind.bind] at h
  rw [Except.bind_eq_ok'] at h; obtain ⟨n2, hn2, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨C, hC, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨es, hes, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨⟨vs, p⟩, ha, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨⟨k, g, f⟩, hs, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨code, hsc, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨a, ha', h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨sh, hsh, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨b, hb, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨c', hc', h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨e', he', h⟩ := h
  simp only [Pure.pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  have hn := catRows_ok hn2
  have hrow := Vals.concat_row hn P T hC hP hT
  obtain ⟨hnc, cd, hcd, heq, hlt⟩ := codes_spec hes ha hs hsc
  have hwC := Vals.concat_wf hn hC hP hT
  obtain ⟨cs, hcs, -⟩ := kasc_ok ha
  have hU := m.toNat_lt_size
  have hUs : USize.size ≤ 2 ^ 64 := by rcases USize.size_eq with h | h <;> omega
  have hc64 : ∀ x, x < 2 ^ 63 → x.toUInt64.toNat = x := fun x hx => by
    simpa using Nat.mod_eq_of_lt (show x < 2 ^ 64 by omega)
  have hoff : ∀ k < m.toNat, ((Enc.raw .i64 m sh)[k]?.getD 0).toNat = k + m.toNat := fun k hk => by
    rw [shiftCol_raw hsh k hk]; simp [UInt64.toNat_add]; omega
  have j := i.1
  have hj := i.2
  have hja : i.1 < n2.toNat := by omega
  have hjb : m.toNat + i.1 < n2.toNat := by omega
  have rA : (Enc.raw .i64 m a)[i.1]?.getD 0 = (cd i.1).toUInt64 := by
    obtain ⟨-, e1⟩ := kgather_word ha' hnc i.1 hj
    rw [e1, raw_pos_word hj, hc64 _ (by omega), (hcd i.1 hja).1]
  have rB : (Enc.raw .i64 m b)[i.1]?.getD 0 = (cd (m.toNat + i.1)).toUInt64 := by
    obtain ⟨-, e1⟩ := kgather_word hb hnc i.1 hj
    rw [e1, hoff _ hj, Nat.add_comm, (hcd _ hjb).1]
  have wA := (hcd i.1 hja).2
  have wB := (hcd _ hjb).2
  have rowA : ValsB.row C ⟨i.1, hja⟩ = P.row i := by rw [hrow]; simp [hj]
  have rowB : ValsB.row C ⟨m.toNat + i.1, hjb⟩ = T.row i := by
    rw [hrow, dif_neg (by simp)]; exact congrArg _ (Fin.ext (by simp))
  have lt1 : ∀ x y : Fin n2.toNat, cd x.1 < cd y.1 → A.lt (ValsB.row C x) (ValsB.row C y) := fun x y h => by
    obtain ⟨hl, hne⟩ := hlt x.1 x.2 y.1 y.2 h
    exact ValsB.lt_of_codes C _ hwC hes hcs x y trivial trivial (lexLe_lt _ hl hne)
  have eq1 : ∀ x y : Fin n2.toNat, cd x.1 = cd y.1 ↔ ValsB.row C x = ValsB.row C y := fun x y =>
    (heq x.1 x.2 y.1 y.2).trans ⟨fun k => Vals.row_of_codes C hwC hes hcs x y k, fun r => Vals.codes_of_row C hwC hes hcs x y r⟩
  have key : cd i.1 < cd (m.toNat + i.1) ↔ A.lt (P.row i) (T.row i) := by
    rw [← rowA, ← rowB]
    refine ⟨lt1 ⟨i.1, hja⟩ ⟨m.toNat + i.1, hjb⟩, fun hl => Classical.byContradiction fun hn => ?_⟩
    rcases Nat.lt_trichotomy (cd i.1) (cd (m.toNat + i.1)) with h | h | h
    · exact hn h
    · exact Obj.lt_irrefl A _ (by have := (eq1 ⟨i.1, hja⟩ ⟨m.toNat + i.1, hjb⟩).1 h; rw [this] at hl; exact hl)
    · exact Obj.lt_asymm A hl (lt1 ⟨m.toNat + i.1, hjb⟩ ⟨i.1, hja⟩ h)
  have key2 : cd i.1 = cd (m.toNat + i.1) ↔ P.row i = T.row i := by
    rw [← rowA, ← rowB]; exact eq1 ⟨i.1, hja⟩ ⟨m.toNat + i.1, hjb⟩
  obtain ⟨-, hv1⟩ := colMap_get hc'
  obtain ⟨v, hv, rv⟩ := hv1 i.1 hj
  obtain ⟨-, hw1⟩ := colMap_get he'
  obtain ⟨w, hw, rw'⟩ := hw1 i.1 hj
  rw [rA, rB, eval_lt_nat (by omega) (by omega)] at hv
  rw [rA, rB] at hw
  have hv' := Except.ok.inj hv
  have hw' := eval_eq_word hw
  simp only [if_neg (show ¬ QAtomicType.i64 = .u1 by decide)] at rv rw'
  rw [rv, Option.getD_some, ← hv']
  rw [rw', Option.getD_some, hw']
  have hi : (cd i.1).toUInt64 = (cd (m.toNat + i.1)).toUInt64 ↔ cd i.1 = cd (m.toNat + i.1) :=
    ⟨fun h => by have := congrArg UInt64.toNat h; rwa [hc64 _ (by omega), hc64 _ (by omega)] at this, fun h => by rw [h]⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← key]; by_cases h : cd i.1 < cd (m.toNat + i.1) <;> simp [h]
  · by_cases h : cd i.1 < cd (m.toNat + i.1) <;> simp [h]
  · rw [← key2, ← hi]; by_cases h : (cd i.1).toUInt64 = (cd (m.toNat + i.1)).toUInt64 <;> simp [h]
  · by_cases h : (cd i.1).toUInt64 = (cd (m.toNat + i.1)).toUInt64 <;> simp [h]

private theorem w64 {x : Nat} (hx : x < 2 ^ 63) : x.toUInt64.toNat = x := by
  simpa using Nat.mod_eq_of_lt (show x < 2 ^ 64 by omega)

/-- **The bisection keeps the cut `t` of each row of `T` in `[base, base + len]`**, `t i` the number of rows of `X` below
`T.row i` (`ht`): a probe at `base + half - 1` is below `T.row i` iff `base + half ≤ t i`, so the cut stays in the new
window, and `len` halves (rounding up) until it is `1`, which `len ≤ 2 ^ fuel` reaches by the last round. -/
theorem Vals.bisect_spec {A : Obj} {n m : USize} {X : Vals A n} {T : Vals A m} (hX : Vals.WF X) (hT : Vals.WF T)
    (hm : 2 * m.toNat ≤ 2 ^ 63) (hn : n.toNat < 2 ^ 63) (t : Fin m.toNat → Nat)
    (ht : ∀ i, ∀ j : Fin n.toNat, A.lt (X.row j) (T.row i) ↔ j.1 < t i) :
    ∀ (fuel len : Nat) (base r : Enc), Vals.bisect X T fuel len base = .ok r → 1 ≤ len → len ≤ 2 ^ fuel →
      (∀ i : Fin m.toNat, ((Enc.raw .i64 m base)[i.1]?.getD 0).toNat ≤ t i ∧
        t i ≤ ((Enc.raw .i64 m base)[i.1]?.getD 0).toNat + len ∧
        ((Enc.raw .i64 m base)[i.1]?.getD 0).toNat + len ≤ n.toNat) →
      ∀ i : Fin m.toNat, ((Enc.raw .i64 m r)[i.1]?.getD 0).toNat ≤ t i ∧
        t i ≤ ((Enc.raw .i64 m r)[i.1]?.getD 0).toNat + 1 ∧ ((Enc.raw .i64 m r)[i.1]?.getD 0).toNat + 1 ≤ n.toNat := by
  intro fuel
  induction fuel with
  | zero =>
    intro len base r h h1 h2 hb i
    simp only [Vals.bisect, pure, Except.pure, Except.ok.injEq] at h
    subst h
    have : len = 1 := by simp at h2; omega
    subst this; exact hb i
  | succ fuel ih =>
    intro len base r h h1 h2 hb
    unfold Vals.bisect at h
    by_cases hl : len ≤ 1
    · simp only [hl, if_true, Bind.bind] at h
      simp only [Pure.pure, Except.pure, Except.ok.injEq] at h; subst h
      have : len = 1 := by omega
      subst this; exact hb
    simp only [hl, if_false, Bind.bind] at h
    rw [Except.bind_eq_ok'] at h; obtain ⟨-, -, h⟩ := h
    rw [Except.bind_eq_ok'] at h; obtain ⟨q, hq, h⟩ := h
    rw [Except.bind_eq_ok'] at h; obtain ⟨g, hg, h⟩ := h
    rw [Except.bind_eq_ok'] at h; obtain ⟨pk, hpk, h⟩ := h
    rw [Except.bind_eq_ok'] at h; obtain ⟨⟨c, e⟩, hc, h⟩ := h
    rw [Except.bind_eq_ok'] at h; obtain ⟨mu, hmu, h⟩ := h
    rw [Except.bind_eq_ok'] at h; obtain ⟨b', hb', h⟩ := h
    rw [Nat.pow_succ] at h2
    refine ih (len - len / 2) b' r h (by omega) (by omega) ?_
    have hgW := Vals.gather_wf hg hX
    have hpkW : Vals.WF pk := ValsB.pack_wf hpk (P := fun _ => True) hgW (fun _ _ => trivial)
    intro i
    obtain ⟨hb1, hb2, hb3⟩ := hb i
    have hq1 := (colMap_post hq).2 i.1 i.2
    simp only [Op.eval, Except.ok.injEq] at hq1
    have hbn : ((Enc.raw .i64 m base)[i.1]?.getD 0).toNat < 2 ^ 63 := by omega
    have hqn : ((Enc.raw .i64 m q)[i.1]?.getD 0).toNat = (len / 2 - 1) + ((Enc.raw .i64 m base)[i.1]?.getD 0).toNat := by
      rw [← hq1, UInt64.toNat_add, w64 (by omega)]; exact Nat.mod_eq_of_lt (by omega)
    obtain ⟨i', hi', hrow⟩ := ValsB.gather_row X hg i
    rw [hqn] at hi'
    have hrp := ValsB.pack_row g hpk (P := fun _ => True) hgW (fun _ _ => trivial) i trivial
    obtain ⟨c1, c2, -, -⟩ := Vals.cmpRows_spec hpkW hT hm hc i
    rw [hrp, hrow] at c1
    have hlt := ht i i'
    have hmu1 := (colMap_post hmu).2 i.1 i.2
    simp only [Op.eval, Except.ok.injEq] at hmu1
    obtain ⟨-, hb1'⟩ := colMap_get hb'
    obtain ⟨v, hv, rv⟩ := hb1' i.1 i.2
    simp only [Op.eval, Except.ok.injEq] at hv
    simp only [if_neg (show ¬ QAtomicType.i64 = .u1 by decide)] at rv
    rw [rv, Option.getD_some, ← hv, ← hmu1]
    by_cases hcj : ((Enc.raw .i64 m c)[i.1]?.getD 0) = 1
    · have hl1 := hlt.1 (c1.1 hcj)
      rw [hcj, UInt64.mul_one, UInt64.toNat_add, w64 (by omega), Nat.mod_eq_of_lt (by omega)]
      omega
    · have h0 : ((Enc.raw .i64 m c)[i.1]?.getD 0) = 0 := by
        have h1 := UInt64.le_iff_toNat_le.1 c2
        have h2 : ((Enc.raw .i64 m c)[i.1]?.getD 0).toNat ≠ 1 := fun e => hcj (UInt64.toNat_inj.1 (by simpa using e))
        exact UInt64.toNat_inj.1 (by simp at h1 ⊢; omega)
      have hnl : ¬ (i'.1 < t i) := fun h => hcj (c1.2 (hlt.2 h))
      rw [h0, UInt64.mul_zero, UInt64.add_zero]
      omega

/-- `min` of two words below `2^63`, signed as `Op.eval` reads them. -/
theorem eval_min_nat {a x : UInt64} (ha : a.toNat < 2 ^ 63) (hx : x.toNat < 2 ^ 63) :
    Op.eval .min a x = .ok (if x.toNat < a.toNat then x else a) := by
  show Except.ok (if x.toInt64 < a.toInt64 then x else a) = _
  simp only [Int64.lt_iff_toInt_lt, toInt64_toInt ha, toInt64_toInt hx]
  simp

/-- **Where `T`'s value cuts a strictly ascending `X`**: the rows of `X` below `v` are exactly the first `t`. -/
theorem Vals.cut {A : Obj} {n : USize} {X : Vals A n}
    (hs : ∀ i j : Fin n.toNat, i.1 < j.1 → A.lt (X.row i) (X.row j)) (v : A.El) :
    ∃ t ≤ n.toNat, ∀ j : Fin n.toNat, A.lt (X.row j) v ↔ j.1 < t := by
  have key : ∀ k ≤ n.toNat, ∃ t ≤ k, ∀ j : Fin n.toNat, j.1 < k → (A.lt (X.row j) v ↔ j.1 < t) := by
    intro k
    induction k with
    | zero => intro _; exact ⟨0, Nat.le_refl _, fun j hj => absurd hj (by omega)⟩
    | succ k ih =>
      intro hk
      obtain ⟨t, htk, hj⟩ := ih (by omega)
      by_cases hl : A.lt (X.row ⟨k, by omega⟩) v
      · refine ⟨k + 1, Nat.le_refl _, fun j hjk => ?_⟩
        refine ⟨fun _ => hjk, fun _ => ?_⟩
        rcases Nat.lt_or_ge j.1 k with h | h
        · exact List.lt_trans (hs j ⟨k, by omega⟩ h) hl
        · have : j = ⟨k, by omega⟩ := Fin.ext (by show j.1 = k; omega)
          rw [this]; exact hl
      · refine ⟨t, by omega, fun j hjk => ?_⟩
        rcases Nat.lt_or_ge j.1 k with h | h
        · exact hj j h
        · have : j = ⟨k, by omega⟩ := Fin.ext (by show j.1 = k; omega)
          rw [this]; exact ⟨fun h => absurd h hl, fun h => absurd h (by omega)⟩
  obtain ⟨t, ht, h⟩ := key n.toNat (Nat.le_refl _)
  exact ⟨t, ht, fun j => h j j.2⟩

private theorem count_lt : ∀ (n t : Nat), t ≤ n → ((List.range n).filter fun j => decide (j < t)).length = t
  | 0, t, h => by simp; omega
  | n + 1, t, h => by
    rw [List.range_succ, List.filter_append]
    by_cases ht : t ≤ n
    · simp [count_lt n t ht, ht]
    · have : t = n + 1 := by omega
      subst this
      rw [List.filter_eq_self.2 (fun j hj => by simp at hj ⊢; omega)]
      simp

end Rel
