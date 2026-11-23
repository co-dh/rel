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
    ((Enc.raw .i64 m e)[i.1]?.getD 0 = 1 ↔ P.row i = T.row i) ∧ (Enc.raw .i64 m e)[i.1]?.getD 0 ≤ 1 ∧
    ((Enc.raw .i64 m c)[i.1]?.getD 0 = 0 → (Enc.raw .i64 m e)[i.1]?.getD 0 = 0 → A.lt (T.row i) (P.row i)) := by
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
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [← key]; by_cases h : cd i.1 < cd (m.toNat + i.1) <;> simp [h]
  · by_cases h : cd i.1 < cd (m.toNat + i.1) <;> simp [h]
  · rw [← key2, ← hi]; by_cases h : (cd i.1).toUInt64 = (cd (m.toNat + i.1)).toUInt64 <;> simp [h]
  · by_cases h : (cd i.1).toUInt64 = (cd (m.toNat + i.1)).toUInt64 <;> simp [h]
  · intro hc he
    have h1 : ¬ cd i.1 < cd (m.toNat + i.1) := fun hh => by simp [hh] at hc
    have h2 : cd i.1 ≠ cd (m.toNat + i.1) := fun hh => by simp [hh] at he
    have := lt1 ⟨m.toNat + i.1, hjb⟩ ⟨i.1, hja⟩ (by simp only; omega)
    rwa [rowA, rowB] at this

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

/-- **`rank(X)` on `T`** (architecture §4.7, `Tab.rank_spec`): for a strictly ascending `X` and both sides `WF`, `r[i]` is
the number of rows of `X` below `T.row i`, and `h[i] = 1` iff `T.row i` is a row of `X` (else `0`). -/
theorem Vals.rank_spec {A : Obj} {n m : USize} {X : Vals A n} {T : Vals A m} (hX : Vals.WF X) (hT : Vals.WF T)
    (hs : ∀ i j : Fin n.toNat, i.1 < j.1 → A.lt (X.row i) (X.row j)) {r h : Enc}
    (hk : Vals.rank X T = .ok (r, h)) (i : Fin m.toNat) :
    ((Enc.raw .i64 m r)[i.1]?.getD 0).toNat =
      ((List.range n.toNat).filter fun j => if hj : j < n.toNat then decide (A.lt (X.row ⟨j, hj⟩) (T.row i)) else false).length ∧
    ((Enc.raw .i64 m h)[i.1]?.getD 0 = 1 ↔ ∃ j, X.row j = T.row i) ∧ (Enc.raw .i64 m h)[i.1]?.getD 0 ≤ 1 ∧
    (∀ j : Fin n.toNat, ((Enc.raw .i64 m r)[i.1]?.getD 0).toNat ≤ j.1 → (Enc.raw .i64 m h)[i.1]?.getD 0 = 0 →
      A.lt (T.row i) (X.row j)) := by
  unfold Vals.rank at hk
  simp only [Bind.bind] at hk
  split at hk
  · rw [Except.bind_eq_ok'] at hk; obtain ⟨_, hth, _⟩ := hk; cases hth
  rename_i hn63
  rw [Except.bind_eq_ok'] at hk; obtain ⟨-, -, hk⟩ := hk
  split at hk
  · rw [Except.bind_eq_ok'] at hk; obtain ⟨_, hth, _⟩ := hk; cases hth
  rename_i hm62
  rw [Except.bind_eq_ok'] at hk; obtain ⟨-, -, hk⟩ := hk
  split at hk
  · rename_i hn0
    rw [Except.bind_eq_ok'] at hk; obtain ⟨z, hz, hk⟩ := hk
    simp only [Pure.pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hk
    obtain ⟨rfl, rfl⟩ := hk
    have hn0' : n.toNat = 0 := by rw [hn0]; rfl
    have hz0 : (Enc.raw .i64 m z)[i.1]?.getD 0 = 0 := by
      rw [colConst_raw hz, Array.getElem?_replicate]; simp [i.2]
    rw [hz0]
    exact ⟨by simp [hn0'], ⟨fun e => absurd e (by decide), fun ⟨j, _⟩ => absurd j.2 (by omega)⟩, by decide,
      fun j => absurd j.2 (by omega)⟩
  rename_i hn0
  have hn1 : 1 ≤ n.toNat := by
    refine Nat.pos_of_ne_zero fun e => hn0 ?_
    apply USize.toNat_inj.1; simpa using e
  rw [Except.bind_eq_ok'] at hk; obtain ⟨-, -, hk⟩ := hk
  rw [Except.bind_eq_ok'] at hk; obtain ⟨z0, hz0, hk⟩ := hk
  rw [Except.bind_eq_ok'] at hk; obtain ⟨base, hbis, hk⟩ := hk
  rw [Except.bind_eq_ok'] at hk; obtain ⟨g1, hg1, hk⟩ := hk
  rw [Except.bind_eq_ok'] at hk; obtain ⟨p1, hp1, hk⟩ := hk
  rw [Except.bind_eq_ok'] at hk; obtain ⟨⟨c1, e1⟩, hc1, hk⟩ := hk
  rw [Except.bind_eq_ok'] at hk; obtain ⟨r', hr', hk⟩ := hk
  rw [Except.bind_eq_ok'] at hk; obtain ⟨q, hq, hk⟩ := hk
  rw [Except.bind_eq_ok'] at hk; obtain ⟨g2, hg2, hk⟩ := hk
  rw [Except.bind_eq_ok'] at hk; obtain ⟨p2, hp2, hk⟩ := hk
  rw [Except.bind_eq_ok'] at hk; obtain ⟨⟨c2, e2⟩, hc2, hk⟩ := hk
  simp only [Pure.pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hk
  obtain ⟨rfl, rfl⟩ := hk
  have hn63' : n.toNat < 2 ^ 63 := by omega
  have hm' : 2 * m.toNat ≤ 2 ^ 63 := by omega
  obtain ⟨t, ht⟩ := Classical.axiomOfChoice (fun i : Fin m.toNat => Vals.cut hs (T.row i))
  have hbs := Vals.bisect_spec hX hT hm' hn63' t (fun i => (ht i).2) _ _ z0 base hbis hn1
    (Nat.le_of_lt (Nat.lt_log2_self (n := n.toNat))) (fun i => by
      rw [colConst_raw hz0, Array.getElem?_replicate]; simp [i.2]; exact (ht i).1) i
  obtain ⟨hb1, hb2, hb3⟩ := hbs
  have hgW1 := Vals.gather_wf hg1 hX
  have hpW1 : Vals.WF p1 := ValsB.pack_wf hp1 (P := fun _ => True) hgW1 (fun _ _ => trivial)
  obtain ⟨i1, hi1, hrow1⟩ := ValsB.gather_row X hg1 i
  have hrp1 := ValsB.pack_row g1 hp1 (P := fun _ => True) hgW1 (fun _ _ => trivial) i trivial
  obtain ⟨d1, d2, -, -⟩ := Vals.cmpRows_spec hpW1 hT hm' hc1 i
  rw [hrp1, hrow1] at d1
  have hlt1 := (ht i).2 i1
  obtain ⟨-, hr1⟩ := colMap_get hr'
  obtain ⟨v, hv, rv⟩ := hr1 i.1 i.2
  simp only [Op.eval, Except.ok.injEq] at hv
  simp only [if_neg (show ¬ QAtomicType.i64 = .u1 by decide)] at rv
  have htn := (ht i).1
  have hrt : ((Enc.raw .i64 m r')[i.1]?.getD 0).toNat = t i := by
    rw [rv, Option.getD_some, ← hv]
    by_cases hc : ((Enc.raw .i64 m c1)[i.1]?.getD 0) = 1
    · have hl := hlt1.1 (d1.1 hc)
      rw [hc, UInt64.toNat_add]; simp only [UInt64.toNat_one]; rw [Nat.mod_eq_of_lt (by omega)]; omega
    · have h0 : ((Enc.raw .i64 m c1)[i.1]?.getD 0) = 0 := by
        have h1 := UInt64.le_iff_toNat_le.1 d2
        have h2 : ((Enc.raw .i64 m c1)[i.1]?.getD 0).toNat ≠ 1 := fun e => hc (UInt64.toNat_inj.1 (by simpa using e))
        exact UInt64.toNat_inj.1 (by simp at h1 ⊢; omega)
      have hnl : ¬ (i1.1 < t i) := fun h => hc (d1.2 (hlt1.2 h))
      rw [h0, UInt64.add_zero]; omega
  have hq1 := (colMap_post hq).2 i.1 i.2
  rw [eval_min_nat (by rw [w64 (by omega)]; omega) (by omega)] at hq1
  have e := Except.ok.inj hq1
  have hqn : ((Enc.raw .i64 m q)[i.1]?.getD 0).toNat = min (t i) (n.toNat - 1) := by
    rw [← e]
    by_cases hc : ((Enc.raw .i64 m r')[i.1]?.getD 0).toNat < ((n.toNat - 1).toUInt64).toNat
    · rw [if_pos hc, hrt]; rw [w64 (by omega)] at hc; omega
    · rw [if_neg hc, w64 (by omega)]; rw [w64 (by omega), hrt] at hc; omega
  have hgW2 := Vals.gather_wf hg2 hX
  have hpW2 : Vals.WF p2 := ValsB.pack_wf hp2 (P := fun _ => True) hgW2 (fun _ _ => trivial)
  obtain ⟨i2, hi2, hrow2⟩ := ValsB.gather_row X hg2 i
  have hrp2 := ValsB.pack_row g2 hp2 (P := fun _ => True) hgW2 (fun _ _ => trivial) i trivial
  obtain ⟨f0, f0', f1, f2, f3⟩ := Vals.cmpRows_spec hpW2 hT hm' hc2 i
  rw [hrp2, hrow2] at f1 f0 f3
  refine ⟨?_, ?_, f2, ?_⟩
  · rw [hrt, List.filter_congr (l := List.range n.toNat) (q := fun j => decide (j < t i)) (fun j hj => by
      have hj' := List.mem_range.1 hj
      rw [dif_pos hj']; exact decide_eq_decide.2 ((ht i).2 ⟨j, hj'⟩))]
    exact (count_lt _ _ (ht i).1).symm
  · refine ⟨fun hc => ⟨i2, f1.1 hc⟩, fun ⟨j, hj⟩ => f1.2 ?_⟩
    have hnl : ¬ (j.1 < t i) := fun hjt => Obj.lt_irrefl A _ (by have := ((ht i).2 j).2 hjt; rwa [hj] at this)
    rcases Nat.lt_or_ge (t i) n.toNat with htn' | htn'
    · have hi2' : i2.1 = t i := by rw [← hi2, hqn]; omega
      by_cases hjt : j.1 = t i
      · have : i2 = j := Fin.ext (by omega)
        rw [this]; exact hj
      · have := hs ⟨t i, htn'⟩ j (by simp only; omega)
        rw [hj] at this
        exact absurd (((ht i).2 ⟨t i, htn'⟩).1 this) (by simp)
    · exact absurd (by omega) hnl
  · intro j hj h0
    have hj' : t i ≤ j.1 := by rw [← hrt]; exact hj
    have htn' : t i < n.toNat := by have := j.2; omega
    have hi2' : i2.1 = t i := by rw [← hi2, hqn]; omega
    have hnl : ¬ A.lt (X.row i2) (T.row i) := fun hl => by have := ((ht i).2 i2).1 hl; omega
    have hc0 : (Enc.raw .i64 m c2)[i.1]?.getD 0 = 0 := by
      have h1 := UInt64.le_iff_toNat_le.1 f0'
      have h2 : ((Enc.raw .i64 m c2)[i.1]?.getD 0).toNat ≠ 1 := fun e => hnl (f0.1 (UInt64.toNat_inj.1 (by simpa using e)))
      exact UInt64.toNat_inj.1 (by simp at h1 ⊢; omega)
    have g0 := f3 hc0 h0
    by_cases hij : i2 = j
    · rw [hij] at g0; exact g0
    · have := hs i2 j (by have : i2.1 ≠ j.1 := fun e => hij (Fin.ext e); omega)
      exact List.lt_trans g0 this

/-- `cmpRows` answers two columns that hold no null (`colMap_closed` of its last two `colMap`s). -/
theorem Vals.cmpRows_plain {A : Obj} {m : USize} {P T : Vals A m} {c e : Enc} (h : Vals.cmpRows P T = .ok (c, e)) :
    hasNul c = false ∧ hasNul e = false := by
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
  exact ⟨(colMap_closed (kscanStream_ne (by decide) _ _ _) hc').2.2, (colMap_closed (kscanStream_ne (by decide) _ _ _) he').2.2⟩

/-- `rank` answers two columns that hold no null. -/
theorem Vals.rank_plain {A : Obj} {n m : USize} {X : Vals A n} {T : Vals A m} {r h : Enc}
    (hk : Vals.rank X T = .ok (r, h)) : hasNul r = false ∧ hasNul h = false := by
  unfold Vals.rank at hk
  simp only [Bind.bind] at hk
  split at hk
  · rw [Except.bind_eq_ok'] at hk; obtain ⟨_, hth, _⟩ := hk; cases hth
  rw [Except.bind_eq_ok'] at hk; obtain ⟨-, -, hk⟩ := hk
  split at hk
  · rw [Except.bind_eq_ok'] at hk; obtain ⟨_, hth, _⟩ := hk; cases hth
  rw [Except.bind_eq_ok'] at hk; obtain ⟨-, -, hk⟩ := hk
  split at hk
  · rw [Except.bind_eq_ok'] at hk; obtain ⟨z, hz, hk⟩ := hk
    simp only [Pure.pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hk
    obtain ⟨rfl, rfl⟩ := hk
    exact ⟨kscatter_plain hz rfl, kscatter_plain hz rfl⟩
  rw [Except.bind_eq_ok'] at hk; obtain ⟨-, -, hk⟩ := hk
  rw [Except.bind_eq_ok'] at hk; obtain ⟨z0, hz0, hk⟩ := hk
  rw [Except.bind_eq_ok'] at hk; obtain ⟨base, hbis, hk⟩ := hk
  rw [Except.bind_eq_ok'] at hk; obtain ⟨g1, hg1, hk⟩ := hk
  rw [Except.bind_eq_ok'] at hk; obtain ⟨p1, hp1, hk⟩ := hk
  rw [Except.bind_eq_ok'] at hk; obtain ⟨⟨c1, e1⟩, hc1, hk⟩ := hk
  rw [Except.bind_eq_ok'] at hk; obtain ⟨r', hr', hk⟩ := hk
  rw [Except.bind_eq_ok'] at hk; obtain ⟨q, hq, hk⟩ := hk
  rw [Except.bind_eq_ok'] at hk; obtain ⟨g2, hg2, hk⟩ := hk
  rw [Except.bind_eq_ok'] at hk; obtain ⟨p2, hp2, hk⟩ := hk
  rw [Except.bind_eq_ok'] at hk; obtain ⟨⟨c2, e2⟩, hc2, hk⟩ := hk
  simp only [Pure.pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hk
  obtain ⟨rfl, rfl⟩ := hk
  exact ⟨(colMap_closed (kscanStream_ne (by decide) _ _ _) hr').2.2, (Vals.cmpRows_plain hc2).2⟩

/-- **`rank` as a cut**: `r[i] ≤ n`, and the rows of the strictly ascending `X` below `T.row i` are exactly the first
`r[i]` (`Vals.cut` and the count `rank_spec` states). -/
theorem Vals.rank_cut {A : Obj} {n m : USize} {X : Vals A n} {T : Vals A m} (hX : Vals.WF X) (hT : Vals.WF T)
    (hs : ∀ i j : Fin n.toNat, i.1 < j.1 → A.lt (X.row i) (X.row j)) {r h : Enc}
    (hk : Vals.rank X T = .ok (r, h)) (i : Fin m.toNat) :
    ((Enc.raw .i64 m r)[i.1]?.getD 0).toNat ≤ n.toNat ∧
      ∀ j : Fin n.toNat, A.lt (X.row j) (T.row i) ↔ j.1 < ((Enc.raw .i64 m r)[i.1]?.getD 0).toNat := by
  obtain ⟨h1, -⟩ := Vals.rank_spec hX hT hs hk i
  obtain ⟨t, ht, hj⟩ := Vals.cut hs (T.row i)
  rw [h1, List.filter_congr (l := List.range n.toNat) (q := fun j => decide (j < t)) (fun j hj' => by
    have hj'' := List.mem_range.1 hj'
    rw [dif_pos hj'']; exact decide_eq_decide.2 (hj ⟨j, hj''⟩)), count_lt _ _ ht]
  exact ⟨ht, hj⟩

/-- **`canon` is strictly ascending in `Obj.lt`**: `canon_sorted`'s `lexLe` of two rows with different codes is `Obj.lt`
(`ValsB.lt_of_codes`). -/
theorem Tab.canon_lt {k v : Obj} {R U : Tab k v} (h : R.canon = .ok U) (hR : R.WF) (j j' : Fin U.n.toNat)
    (hjj : j.1 < j'.1) :
    (Obj.prod k v).lt (U.key.row j, U.val.row j) (U.key.row j', U.val.row j') := by
  unfold Tab.canon at h
  cases hn : Vals.nub (A := .prod k v) (R.key, R.val) with
  | error s => simp [hn, Functor.map, Except.map] at h
  | ok r =>
    simp only [hn, Functor.map, Except.map, Except.ok.injEq] at h
    subst h
    obtain ⟨es, vs, p, -, -, -, -, -, hes, ha, -⟩ := Vals.nub_ok hn
    obtain ⟨sel, hrow, hsel⟩ := Vals.nub_sorted hn hes
    obtain ⟨cs, hcs, -⟩ := kasc_ok ha
    obtain ⟨hl, hne⟩ := hsel j j' hjj
    have := ValsB.lt_of_codes (A := .prod k v) (R.key, R.val) (fun _ => True) (show Vals.WF (A := .prod k v) (R.key, R.val) from ⟨hR.1, hR.2⟩) hes hcs
      (sel j) (sel j') trivial trivial (lexLe_lt _ hl hne)
    rw [← hrow j, ← hrow j'] at this
    exact this

/-- The number of rows of `U` ranked at or before row `i`: `U[j]` sits below `X[i]` iff `t j ≤ i`. -/
def cntLe (d : Nat) (t : Nat → Nat) (i : Nat) : Nat := (List.range d).countP fun j => decide (t j ≤ i)

theorem cntLe_mono {d : Nat} {t : Nat → Nat} {i i' : Nat} (h : i ≤ i') : cntLe d t i ≤ cntLe d t i' :=
  List.countP_mono_left fun j _ hj => by simp at hj ⊢; omega

theorem cntLe_le (d : Nat) (t : Nat → Nat) (i : Nat) : cntLe d t i ≤ d :=
  by have := List.countP_le_length (p := fun j => decide (t j ≤ i)) (l := List.range d); simpa [cntLe] using this

theorem countP_range_le {p : Nat → Bool} {j : Nat} (h : ∀ x, j ≤ x → p x = false) : ∀ d, (List.range d).countP p ≤ j
  | 0 => by simp
  | d + 1 => by
    rw [List.range_succ, List.countP_append]
    have ih := countP_range_le h d
    by_cases hd : j ≤ d
    · have : List.countP p [d] = 0 := by simp [List.countP_cons, h d hd]
      omega
    · have h1 : List.countP p [d] ≤ 1 := List.countP_le_length
      have h2 : List.countP p (List.range d) ≤ d := by
        have := List.countP_le_length (p := p) (l := List.range d); simpa using this
      omega

theorem le_countP_range {p : Nat → Bool} {j : Nat} (h : ∀ x, x ≤ j → p x = true) :
    ∀ k, j + 1 ≤ (List.range (j + 1 + k)).countP p
  | 0 => by rw [List.countP_eq_length.2 (fun x hx => h x (by simp at hx; omega))]; simp
  | k + 1 => by
    have ih := le_countP_range h k
    rw [show j + 1 + (k + 1) = (j + 1 + k) + 1 by omega, List.range_succ, List.countP_append]
    omega

theorem cntLe_lt {d : Nat} {t : Nat → Nat} (hm : ∀ j j', j ≤ j' → t j ≤ t j') {i j : Nat} (hij : i < t j) :
    cntLe d t i ≤ j :=
  countP_range_le (fun x hx => by simp only [decide_eq_false_iff_not]; have := hm j x hx; omega) d

theorem le_cntLe {d : Nat} {t : Nat → Nat} (hm : ∀ j j', j ≤ j' → t j ≤ t j') {i j : Nat} (hj : j < d)
    (hle : t j ≤ i) : j + 1 ≤ cntLe d t i := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le (show j + 1 ≤ d by omega)
  exact le_countP_range (fun x hx => by simp only [decide_eq_true_eq]; have := hm x j hx; omega) k

/-- **The merge position map**: row `i` of `X` goes to `i + cntLe`, row `j` of `U` to `j + t j`. -/
def mpos (n d : Nat) (t : Nat → Nat) (q : Nat) : Nat := if q < n then q + cntLe d t q else (q - n) + t (q - n)

/-- `mpos` maps `[0, n + d)` into itself and is injective there, given `t` monotone and below `n`. -/
theorem mpos_inj {n d : Nat} {t : Nat → Nat} (hm : ∀ j j', j ≤ j' → t j ≤ t j') (ht : ∀ j, j < d → t j ≤ n) :
    (∀ q, q < n + d → mpos n d t q < n + d) ∧ ∀ q q', q < n + d → q' < n + d → mpos n d t q = mpos n d t q' → q = q' := by
  have hb := cntLe_le d t
  refine ⟨fun q hq => ?_, fun q q' hq hq' he => ?_⟩
  · unfold mpos; split
    · have := hb q; omega
    · have := ht (q - n) (by omega); omega
  · unfold mpos at he
    split at he <;> split at he
    · refine Classical.byContradiction fun hne => ?_
      rcases Nat.lt_or_gt_of_ne hne with h | h
      · have := cntLe_mono (d := d) (t := t) (Nat.le_of_lt h); omega
      · have := cntLe_mono (d := d) (t := t) (Nat.le_of_lt h); omega
    · rename_i h1 h2
      rcases Nat.lt_or_ge q (t (q' - n)) with h | h
      · have := cntLe_lt (d := d) hm h; omega
      · have := le_cntLe hm (show q' - n < d by omega) h; omega
    · rename_i h1 h2
      rcases Nat.lt_or_ge q' (t (q - n)) with h | h
      · have := cntLe_lt (d := d) hm h; omega
      · have := le_cntLe hm (show q - n < d by omega) h; omega
    · refine Classical.byContradiction fun hne => ?_
      rcases Nat.lt_or_gt_of_ne (show q - n ≠ q' - n by omega) with h | h
      · have := hm _ _ (Nat.le_of_lt h); omega
      · have := hm _ _ (Nat.le_of_lt h); omega

/-- **An injective self-map of `[0, N)` is onto** (pigeonhole). -/
theorem surj_of_inj (N : Nat) (f : Nat → Nat) (hb : ∀ q < N, f q < N)
    (hi : ∀ q q', q < N → q' < N → f q = f q' → q = q') : ∀ p < N, ∃ q < N, f q = p := by
  intro p hp
  refine Classical.byContradiction fun hne => ?_
  have hnd : ((List.range N).map f).Nodup := by
    unfold List.Nodup
    rw [List.pairwise_map]
    exact List.Pairwise.imp_of_mem (fun {a b} ha hb hab e =>
      Nat.ne_of_lt hab (hi a b (List.mem_range.1 ha) (List.mem_range.1 hb) e)) List.pairwise_lt_range
  have := nodup_length_le hnd fun x hx => by
    obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hx
    have hq := List.mem_range.1 hq
    exact (List.mem_erase_of_ne (fun e => hne ⟨q, hq, e⟩)).2 (List.mem_range.2 (hb q hq))
  rw [List.length_erase_of_mem (List.mem_range.2 hp)] at this
  simp at this; omega

/-- **The merge is sorted**: rows `vr` placed by `mpos` from the ascending `xr` (`n` rows) and `ur` (`d` rows), where
`xr i < ur j` iff `i < t j`, form an ascending row list. -/
theorem merge_sorted {E : Type} (lt : E → E → Prop) {n d : Nat} {t : Nat → Nat} (hm : ∀ j j', j ≤ j' → t j ≤ t j')
    (ht : ∀ j, j < d → t j ≤ n) (xr ur vr : Nat → E) (hxs : ∀ i i', i < i' → i' < n → lt (xr i) (xr i'))
    (hus : ∀ j j', j < j' → j' < d → lt (ur j) (ur j'))
    (hxu : ∀ i j, i < n → j < d → i < t j → lt (xr i) (ur j))
    (hux : ∀ i j, i < n → j < d → t j ≤ i → lt (ur j) (xr i))
    (hv : ∀ q, q < n + d → vr (mpos n d t q) = if q < n then xr q else ur (q - n)) :
    ∀ p p', p < p' → p' < n + d → lt (vr p) (vr p') := by
  intro p p' hpp hp'
  obtain ⟨hb, hi⟩ := mpos_inj hm ht
  have hsurj := surj_of_inj (n + d) (mpos n d t) hb hi
  obtain ⟨q, hq, rfl⟩ := hsurj p (by omega)
  obtain ⟨q', hq', rfl⟩ := hsurj p' hp'
  rw [hv q hq, hv q' hq']
  by_cases h1 : q < n <;> by_cases h2 : q' < n
  · simp only [mpos, if_pos h1, if_pos h2] at hpp
    rw [if_pos h1, if_pos h2]
    have : q < q' := Classical.byContradiction fun hn => by
      have := cntLe_mono (d := d) (t := t) (show q' ≤ q by omega); omega
    exact hxs q q' this h2
  · simp only [mpos, if_pos h1, if_neg h2] at hpp
    rw [if_pos h1, if_neg h2]
    refine hxu q (q' - n) h1 (by omega) (Classical.byContradiction fun hn => ?_)
    have := le_cntLe hm (show q' - n < d by omega) (show t (q' - n) ≤ q by omega); omega
  · simp only [mpos, if_neg h1, if_pos h2] at hpp
    rw [if_neg h1, if_pos h2]
    refine hux q' (q - n) h2 (by omega) (Classical.byContradiction fun hn => ?_)
    have := cntLe_lt (d := d) hm (show q' < t (q - n) by omega); omega
  · simp only [mpos, if_neg h1, if_neg h2] at hpp
    rw [if_neg h1, if_neg h2]
    have : q - n < q' - n := Classical.byContradiction fun hn => by
      have := hm _ _ (show q' - n ≤ q - n by omega); omega
    exact hus _ _ this (by omega)

/-- `rank` answers only below its row bounds (`n < 2^63`, `m < 2^62`). -/
theorem Vals.rank_bounds {A : Obj} {n m : USize} {X : Vals A n} {T : Vals A m} {r h : Enc}
    (hk : Vals.rank X T = .ok (r, h)) : n.toNat < 2 ^ 63 ∧ m.toNat < 2 ^ 62 := by
  unfold Vals.rank at hk
  simp only [Bind.bind] at hk
  split at hk
  · rw [Except.bind_eq_ok'] at hk; obtain ⟨_, hth, _⟩ := hk; cases hth
  rename_i hn63
  rw [Except.bind_eq_ok'] at hk; obtain ⟨-, -, hk⟩ := hk
  split at hk
  · rw [Except.bind_eq_ok'] at hk; obtain ⟨_, hth, _⟩ := hk; cases hth
  rename_i hm62
  exact ⟨by omega, by omega⟩

/-- Counting by value, then summing the counts of the values up to `i`, counts the values `≤ i`. -/
theorem sum_countP_eq (l : List Nat) (t : Nat → Nat) (i : Nat) :
    ((List.range (i + 1)).map fun g => l.countP fun j => decide (t j = g)).sum = l.countP fun j => decide (t j ≤ i) := by
  induction i with
  | zero =>
    rw [show List.range (0 + 1) = [0] from rfl]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero]
    exact List.countP_congr fun j _ => by simp only [decide_eq_true_eq]; omega
  | succ i ih =>
    have hsa : ∀ a b : List Nat, (a ++ b).sum = a.sum + b.sum := fun a b => by induction a <;> simp_all [Nat.add_assoc]
    rw [List.range_succ, List.map_append, hsa, ih]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero]
    clear ih
    induction l with
    | nil => rfl
    | cons a l ih =>
      simp only [List.countP_cons, decide_eq_true_eq]
      split <;> split <;> split <;> omega

/-- A left fold of `+` over ones adds the length. -/
theorem foldl_add_one (l : List Nat) (acc : UInt64) :
    (l.map fun _ => (1 : UInt64)).foldl (· + ·) acc = acc + l.length.toUInt64 := by
  induction l generalizing acc with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.foldl_cons, ih, List.length_cons]
    apply UInt64.toNat_inj.1; simp [UInt64.toNat_add]; omega

/-- **`(X ∪ T, T − X)` by rank** (architecture §4.7): for a strictly ascending `X` and both tables `WF`, `mergeDiff`
answers `V` holding `X ∪ T` and `U` holding `T − X`, both `WF` and strictly ascending — what `unionDiff` gives. `U` is
the canonical `T` at the misses of `rank`; row `i` of `X` lands at `i + cntLe`, row `j` of `U` at `j + t j` (`mpos`),
and `kscatter .last` of the positions inverts that map, so `merge_sorted` orders `V`. -/
theorem Tab.mergeDiff_holds {k v : Obj} {X T V U : Tab k v} (hX : X.WF) (hT : T.WF)
    (hs : ∀ i j : Fin X.n.toNat, i.1 < j.1 →
      (Obj.prod k v).lt (X.key.row i, X.val.row i) (X.key.row j, X.val.row j))
    (h : X.mergeDiff T = .ok (V, U)) :
    (∀ a b, V.Holds a b ↔ X.Holds a b ∨ T.Holds a b) ∧ (∀ a b, U.Holds a b ↔ T.Holds a b ∧ ¬ X.Holds a b) ∧
      V.WF ∧ U.WF ∧
      (∀ i j : Fin V.n.toNat, i.1 < j.1 → (Obj.prod k v).lt (V.key.row i, V.val.row i) (V.key.row j, V.val.row j)) ∧
      ∀ i j : Fin U.n.toNat, i.1 < j.1 → (Obj.prod k v).lt (U.key.row i, U.val.row i) (U.key.row j, U.val.row j) := by
  unfold Tab.mergeDiff at h
  simp only [Bind.bind] at h
  rw [Except.bind_eq_ok'] at h; obtain ⟨Tc, hTc, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨⟨r, hh⟩, hrk, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨nm, hnm, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨⟨d, sel⟩, hwh, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨gk, hgk, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨gv, hgv, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨rD, hrD, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨posD, hposD, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨ones, hones, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨cnt, hcnt, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨kg, hkg, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨c, hc, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨posX, hposX, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨N, hN, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨ix1, hix1, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨ix2, hix2, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨cc, hcc, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨Vv, hVv, h⟩ := h
  simp only [Pure.pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  dsimp only at *
  -- 1. the canonical `T` and the rank of `X` on it
  have hTcW := Tab.canon_wf hTc hT
  have hXW : Vals.WF (A := .prod k v) (X.key, X.val) := ⟨hX.1, hX.2⟩
  have hTW : Vals.WF (A := .prod k v) (Tc.key, Tc.val) := ⟨hTcW.1, hTcW.2⟩
  obtain ⟨hn63, hm62⟩ := Vals.rank_bounds hrk
  obtain ⟨hNr, hNh⟩ := Vals.rank_plain hrk
  have rs := Vals.rank_spec hXW hTW hs hrk
  have rc := Vals.rank_cut hXW hTW hs hrk
  -- 2. `nm[s] ≠ 0` iff `T[s]` is no row of `X`
  obtain ⟨-, -, -, hnmw⟩ := colMap_raw hnm (hF := Or.inr (nulFree₂ hNh hNh))
  have hnmb : ∀ s < Tc.n.toNat, (Enc.raw .i64 Tc.n nm)[s]?.getD 0 < 2 ∧
      ((Enc.raw .i64 Tc.n nm)[s]?.getD 0 ≠ 0 ↔ (Enc.raw .i64 Tc.n hh)[s]?.getD 0 = 0) := by
    intro s hs'
    have e := hnmw s hs'
    simp only [Op.eval, Except.ok.injEq] at e
    have hb := UInt64.le_iff_toNat_le.1 (rs ⟨s, hs'⟩).2.2.1
    rw [← e]
    rcases (show ((Enc.raw .i64 Tc.n hh)[s]?.getD 0).toNat = 0 ∨ ((Enc.raw .i64 Tc.n hh)[s]?.getD 0).toNat = 1 by
      simp at hb; omega) with h0 | h1
    · rw [UInt64.toNat_inj.1 (show _ = (0 : UInt64).toNat from h0)]; decide
    · rw [UInt64.toNat_inj.1 (show _ = (1 : UInt64).toNat from h1)]; decide
  -- 3. `sel`: the positions of the misses, ascending; `U` row `j` is `T` row `sel j`
  have hb2 : ∀ s < Tc.n.toNat, (Enc.raw .i64 Tc.n nm)[s]?.getD 0 < 2 := fun s hs' => (hnmb s hs').1
  have hsz := whereCol_size hwh
  have hdm : d.toNat ≤ Tc.n.toNat := by
    rw [← hsz, ← Array.length_toList, ← List.length_map (f := UInt64.toNat), whereCol_spec hwh hb2]
    exact Nat.le_trans (List.length_filter_le _ _) (by simp)
  obtain ⟨sl, hsl⟩ : ∃ f : Nat → Nat, ∀ j, f j = ((Enc.raw .i64 d sel)[j]?.getD 0).toNat := ⟨_, fun _ => rfl⟩
  have hslm : ∀ j < d.toNat, sl j < Tc.n.toNat ∧ (Enc.raw .i64 Tc.n hh)[sl j]?.getD 0 = 0 := fun j hj => by
    obtain ⟨h1, h2⟩ := (whereCol_mem hwh hb2 (sl j)).1 ⟨j, hj, (hsl j).symm⟩
    exact ⟨h1, (hnmb _ h1).2.1 h2⟩
  have hslon : ∀ s < Tc.n.toNat, (Enc.raw .i64 Tc.n hh)[s]?.getD 0 = 0 → ∃ j < d.toNat, sl j = s := fun s hs' h0 => by
    obtain ⟨j, hj, e⟩ := (whereCol_mem hwh hb2 s).2 ⟨hs', (hnmb s hs').2.2 h0⟩
    exact ⟨j, hj, (hsl j).trans e⟩
  have hslmono : ∀ j j', j < j' → j' < d.toNat → sl j < sl j' := by
    have hp : ((Enc.raw .i64 d sel).toList.map UInt64.toNat).Pairwise (· < ·) := by
      rw [whereCol_spec hwh hb2]; exact List.pairwise_lt_range.filter _
    intro j j' hjj hj'
    have := List.pairwise_iff_getElem.1 hp j j' (by simp [hsz]; omega) (by simp [hsz]; omega) hjj
    simpa [hsl, hsz, show j < d.toNat by omega, hj'] using this
  have hU : ∀ j : Fin d.toNat, ∃ s : Fin Tc.n.toNat, sl j = s.1 ∧
      ValsB.row (A := .prod k v) (gk, gv) j = ValsB.row (A := .prod k v) (Tc.key, Tc.val) s := fun j => by
    obtain ⟨i, hi, e⟩ := ValsB.gather_row Tc.key hgk j
    obtain ⟨i', hi', e'⟩ := ValsB.gather_row Tc.val hgv j
    have : i = i' := Fin.ext (by rw [← hi, ← hi'])
    subst this
    exact ⟨i, (hsl j).trans hi, by simp only [ValsB.row, e, e']⟩
  have hUW : Vals.WF (A := .prod k v) (gk, gv) := ⟨Vals.gather_wf hgk hTcW.1, Vals.gather_wf hgv hTcW.2⟩
  have hUs : ∀ i j : Fin d.toNat, i.1 < j.1 →
      (Obj.prod k v).lt (ValsB.row (A := .prod k v) (gk, gv) i) (ValsB.row (A := .prod k v) (gk, gv) j) := by
    intro j j' hjj
    obtain ⟨s, hs1, hs2⟩ := hU j
    obtain ⟨s', hs1', hs2'⟩ := hU j'
    rw [hs2, hs2']
    exact Tab.canon_lt hTc hT s s' (by rw [← hs1, ← hs1']; exact hslmono _ _ hjj j'.2)
  -- 4. `t j`: the rank of `U` row `j`, `rD[j]`; monotone and `≤ n` (`n` past `d`)
  obtain ⟨rv, hrv⟩ : ∃ f : Nat → Nat, ∀ s, f s = ((Enc.raw .i64 Tc.n r)[s]?.getD 0).toNat := ⟨_, fun _ => rfl⟩
  have hrD' := kgather_word hrD hNr
  obtain ⟨t, ht⟩ : ∃ f : Nat → Nat, ∀ j, f j = if j < d.toNat then rv (sl j) else X.n.toNat := ⟨_, fun _ => rfl⟩
  have htD : ∀ j < d.toNat, ((Enc.raw .i64 d rD)[j]?.getD 0).toNat = t j := fun j hj => by
    rw [ht, if_pos hj, hrv, hsl, (hrD' j hj).2]
  have hrvn : ∀ s < Tc.n.toNat, rv s ≤ X.n.toNat := fun s hs' => by rw [hrv]; exact (rc ⟨s, hs'⟩).1
  have htn : ∀ j, j < d.toNat → t j ≤ X.n.toNat := fun j hj => by
    rw [ht, if_pos hj]; exact hrvn _ (hslm j hj).1
  have hm : ∀ j j', j ≤ j' → t j ≤ t j' := by
    intro j j' hjj
    by_cases hj' : j' < d.toNat
    · have hj : j < d.toNat := by omega
      rw [ht, ht, if_pos hj, if_pos hj']
      rcases Nat.lt_or_eq_of_le hjj with hlt | rfl
      · refine Nat.le_of_not_lt fun hlt' => ?_
        have h1 := hslm j hj
        have h2 := hslm j' hj'
        have hin : rv (sl j') < X.n.toNat := by have := hrvn _ h1.1; omega
        have a1 := ((rc ⟨sl j, h1.1⟩).2 ⟨rv (sl j'), hin⟩).2 (by rw [← hrv]; exact hlt')
        have a2 := Tab.canon_lt hTc hT ⟨sl j, h1.1⟩ ⟨sl j', h2.1⟩ (hslmono j j' hlt hj')
        have a3 := ((rc ⟨sl j', h2.1⟩).2 ⟨rv (sl j'), hin⟩).1 (List.lt_trans a1 a2)
        rw [← hrv] at a3; exact Nat.lt_irrefl _ a3
      · exact Nat.le_refl _
    · rw [ht j', if_neg hj']
      by_cases hj : j < d.toNat
      · exact htn j hj
      · rw [ht, if_neg hj]; exact Nat.le_refl _
  -- 5. `cnt[g]` counts the `j` with `t j = g`; `c[i] = cntLe`; `posX[i] = i + cntLe`, `posD[j] = j + t j`
  have hNones := kscatter_plain hones rfl
  have hones' := colConst_raw hones
  obtain ⟨hrDs, -, hsw⟩ := kscatter_words hcnt hNones
  obtain ⟨-, hcntw⟩ := scatterWords_fold (op := .add) (f := (· + ·)) (fun _ _ => rfl) hsw
  have hkg' := kgather_word hkg (kscatter_plain hcnt hNones)
  have hkgw : ∀ g < X.n.toNat, (Enc.raw .i64 X.n kg)[g]?.getD 0 =
      ((List.range d.toNat).countP fun j => decide (t j = g)).toUInt64 := by
    intro g hg
    obtain ⟨hgK, e⟩ := hkg' g hg
    rw [raw_pos_word hg] at hgK e
    have hg' : g.toUInt64.toNat = g := by simp; omega
    rw [hg'] at hgK e
    rw [e, hcntw g hgK, hrDs]
    rw [List.map_congr_left (g := fun _ => (1 : UInt64)) (fun k hk => by
      simp only [List.mem_filter, List.mem_range] at hk; rw [hones']; simp [hk.1])]
    rw [foldl_add_one, UInt64.zero_add, ← List.countP_eq_length_filter]
    congr 1
    exact List.countP_congr fun j hj => by
      simp only [List.mem_range] at hj; simp only [decide_eq_true_eq]; rw [htD j hj]
  have hcw := colPrefix_add_sum hc (fun g => (List.range d.toNat).countP fun j => decide (t j = g)) hkgw
  have hpX : ∀ i < X.n.toNat, (Enc.raw .i64 X.n posX.enc)[i]?.getD 0 = (i + cntLe d.toNat t i).toUInt64 := fun i hi => by
    obtain ⟨-, -, -, hw⟩ := colMap_raw (colArr_ok hposX)
    have e := hw i hi
    simp only [Op.eval, Except.ok.injEq] at e
    rw [← e, hcw i hi, sum_countP_eq, raw_pos_word hi]
    have := cntLe_le d.toNat t i
    apply UInt64.toNat_inj.1; simp [UInt64.toNat_add, cntLe] at this ⊢; omega
  have hpD : ∀ j < d.toNat, (Enc.raw .i64 d posD.enc)[j]?.getD 0 = (j + t j).toUInt64 := fun j hj => by
    obtain ⟨-, -, -, hw⟩ := colMap_raw (colArr_ok hposD)
    have e := hw j hj
    simp only [Op.eval, Except.ok.injEq] at e
    rw [← e, raw_pos_word hj, ← htD j hj]
    apply UInt64.toNat_inj.1; simp [UInt64.toNat_add]; omega
  -- 6. `ix1[q] = mpos q`; `ix2` inverts it
  have hNn := catRows_ok hN
  have hix1w : ∀ p < N.toNat, (Enc.raw .i64 N (ColB.enc ix1))[p]?.getD 0 = (mpos X.n.toNat d.toNat t p).toUInt64 := by
    intro p hp
    have e := congrArg Int64.toUInt64 (ColB.concat_get (o := false) hNn hix1 ⟨p, hp⟩)
    unfold mpos
    by_cases hpn : p < X.n.toNat
    · rw [dif_pos hpn] at e; rw [if_pos hpn, ← hpX p hpn]
      simpa [ColB.get, Arr.get_i64] using e
    · rw [dif_neg hpn] at e; rw [if_neg hpn, ← hpD (p - X.n.toNat) (by omega)]
      simpa [ColB.get, Arr.get_i64] using e
  obtain ⟨hb, hi⟩ := mpos_inj hm htn
  have hmb : ∀ q < N.toNat, mpos X.n.toNat d.toNat t q < N.toNat := fun q hq => by have := hb q (by omega); omega
  have hsc := raw_scatter N (ColB.enc ix1) .pos N 0 ix2 rfl hix2
  dsimp only at hsc
  obtain ⟨-, -, -, -, -, -, hlast⟩ := hsc
  have hix2w : ∀ q < N.toNat, (Enc.raw .i64 N ix2)[mpos X.n.toNat d.toNat t q]?.getD 0 = q.toUInt64 := by
    intro q hq
    have e := hlast q hq (fun q' hqq hq' he => by
      rw [hix1w q' hq', hix1w q hq] at he
      have h1 := hmb q' hq'
      have h2 := hmb q hq
      have := hi q' q (by omega) (by omega) (by have := congrArg UInt64.toNat he; simp at this; omega)
      omega)
    rw [hix1w q hq, raw_pos_word hq] at e
    have hq' : (mpos X.n.toNat d.toNat t q).toUInt64.toNat = mpos X.n.toNat d.toNat t q := by
      have := hmb q hq; simp; omega
    rw [hq'] at e
    simp [e]
  -- 7. `V` row `mpos q` is row `q` of `X ++ U`
  have hccW := Vals.concat_wf hNn hcc hXW hUW
  have hcc' := Vals.concat_row hNn _ _ hcc hXW hUW
  have hVq : ∀ q (hq : q < N.toNat), ValsB.row Vv ⟨mpos X.n.toNat d.toNat t q, hmb q hq⟩ = ValsB.row cc ⟨q, hq⟩ := by
    intro q hq
    obtain ⟨i, hi', e⟩ := ValsB.gather_row cc hVv ⟨_, hmb q hq⟩
    rw [e]; congr 1; apply Fin.ext; rw [← hi', hix2w q hq]; simp; omega
  have hVW := Vals.gather_wf hVv hccW
  -- 8. the conclusions
  have hUH : ∀ a b, Tab.Holds ⟨d, gk, gv⟩ a b ↔ Tc.Holds a b ∧ ¬ X.Holds a b := by
    intro a b
    simp only [Tab.Holds]
    constructor
    · rintro ⟨j, h1, h2⟩
      obtain ⟨s, hs1, hs2⟩ := hU j
      simp only [ValsB.row, Prod.mk.injEq] at hs2
      refine ⟨⟨s, hs2.1 ▸ h1, hs2.2 ▸ h2⟩, ?_⟩
      rintro ⟨i, e1, e2⟩
      have h0 := (hslm j j.2).2
      rw [hs1] at h0
      have h1' := ((rs s).2.1).2 ⟨i, by simp only [ValsB.row]; rw [e1, e2, ← h1, ← h2, hs2.1, hs2.2]⟩
      rw [h0] at h1'; exact absurd h1' (by decide)
    · rintro ⟨⟨s, h1, h2⟩, hn⟩
      have h0 : (Enc.raw .i64 Tc.n hh)[s.1]?.getD 0 = 0 := by
        have hle := UInt64.le_iff_toNat_le.1 (rs s).2.2.1
        rcases (show ((Enc.raw .i64 Tc.n hh)[s.1]?.getD 0).toNat = 0 ∨ ((Enc.raw .i64 Tc.n hh)[s.1]?.getD 0).toNat = 1 by
          simp at hle; omega) with e | e
        · exact UInt64.toNat_inj.1 (by simpa using e)
        · obtain ⟨i, hi⟩ := (rs s).2.1.1 (UInt64.toNat_inj.1 (by simpa using e))
          simp only [ValsB.row, Prod.mk.injEq] at hi
          exact absurd ⟨i, by rw [hi.1, h1], by rw [hi.2, h2]⟩ hn
      obtain ⟨j, hj, e⟩ := hslon s s.2 h0
      obtain ⟨s', hs1, hs2⟩ := hU ⟨j, hj⟩
      have : s' = s := Fin.ext (by rw [← hs1, e])
      subst this
      simp only [ValsB.row, Prod.mk.injEq] at hs2
      exact ⟨⟨j, hj⟩, by rw [hs2.1, h1], by rw [hs2.2, h2]⟩
  have hVH : ∀ a b, Tab.Holds ⟨N, Vv.1, Vv.2⟩ a b ↔ X.Holds a b ∨ Tab.Holds ⟨d, gk, gv⟩ a b := by
    intro a b
    simp only [Tab.Holds]
    constructor
    · rintro ⟨p, h1, h2⟩
      obtain ⟨q, -, e⟩ := ValsB.gather_row cc hVv p
      have e' := e.trans (hcc' q)
      split at e'
      · simp only [ValsB.row, Prod.mk.injEq] at e'
        exact .inl ⟨_, e'.1.symm.trans h1, e'.2.symm.trans h2⟩
      · simp only [ValsB.row, Prod.mk.injEq] at e'
        exact .inr ⟨_, e'.1.symm.trans h1, e'.2.symm.trans h2⟩
    · rintro (⟨i, h1, h2⟩ | ⟨j, h1, h2⟩)
      · have e := (hVq i.1 (by omega)).trans (hcc' ⟨i.1, by omega⟩)
        rw [dif_pos i.2] at e
        simp only [ValsB.row, Prod.mk.injEq] at e
        exact ⟨_, e.1.trans h1, e.2.trans h2⟩
      · have e := (hVq (X.n.toNat + j.1) (by omega)).trans (hcc' ⟨X.n.toNat + j.1, by omega⟩)
        rw [dif_neg (by simp)] at e
        simp only [ValsB.row, Prod.mk.injEq, Nat.add_sub_cancel_left] at e
        exact ⟨_, e.1.trans h1, e.2.trans h2⟩
  have hsV := merge_sorted (E := Option (Obj.prod k v).El)
    (fun a b => ∃ x y, a = some x ∧ b = some y ∧ (Obj.prod k v).lt x y) hm htn
    (fun i => if h : i < X.n.toNat then some (ValsB.row (A := .prod k v) (X.key, X.val) ⟨i, h⟩) else none)
    (fun j => if h : j < d.toNat then some (ValsB.row (A := .prod k v) (gk, gv) ⟨j, h⟩) else none)
    (fun p => if h : p < N.toNat then some (ValsB.row Vv ⟨p, h⟩) else none)
    (fun i i' hii hi' => ⟨_, _, dif_pos (by omega), dif_pos hi', hs ⟨i, by omega⟩ ⟨i', hi'⟩ hii⟩)
    (fun j j' hjj hj' => ⟨_, _, dif_pos (by omega), dif_pos hj', hUs ⟨j, by omega⟩ ⟨j', hj'⟩ hjj⟩)
    (fun i j hi hj hij => ⟨_, _, dif_pos hi, dif_pos hj, by
      obtain ⟨s, hs1, hs2⟩ := hU ⟨j, hj⟩
      rw [hs2]
      have := ht j
      rw [if_pos hj, hs1, hrv] at this
      exact ((rc s).2 ⟨i, hi⟩).2 (by rw [← this]; exact hij)⟩)
    (fun i j hi hj hij => ⟨_, _, dif_pos hj, dif_pos hi, by
      obtain ⟨s, hs1, hs2⟩ := hU ⟨j, hj⟩
      rw [hs2]
      have := ht j
      rw [if_pos hj, hs1, hrv] at this
      have h0 := (hslm j hj).2
      rw [hs1] at h0
      exact (rs s).2.2.2 ⟨i, hi⟩ (by rw [← this]; exact hij) h0⟩)
    (fun q hq => by
      dsimp only
      rw [dif_pos (hmb q (by omega)), hVq q (by omega), hcc' ⟨q, by omega⟩]
      by_cases hqn : q < X.n.toNat
      · rw [dif_pos hqn, if_pos hqn, dif_pos hqn]
      · rw [dif_neg hqn, if_neg hqn, dif_pos (show q - X.n.toNat < d.toNat by omega)])
  refine ⟨fun a b => by rw [hVH, hUH, Tab.canon_holds hTc hT]; by_cases hx : X.Holds a b <;> simp [hx],
    fun a b => by rw [hUH, Tab.canon_holds hTc hT], ⟨hVW.1, hVW.2⟩, ⟨hUW.1, hUW.2⟩, fun i j hij => ?_, hUs⟩
  obtain ⟨x, y, hx, hy, hl⟩ := hsV i j hij (by omega)
  dsimp only at hx hy
  rw [dif_pos i.2] at hx
  rw [dif_pos j.2] at hy
  obtain rfl := Option.some.inj hx
  obtain rfl := Option.some.inj hy
  exact hl

/-- **`X` strictly ascending in `Obj.lt`** (a `canon`ical table; the hypothesis `mergeDiff_holds` reads). -/
def Tab.Asc {k v : Obj} (X : Tab k v) : Prop :=
  ∀ i j : Fin X.n.toNat, i.1 < j.1 → (Obj.prod k v).lt (X.key.row i, X.val.row i) (X.key.row j, X.val.row j)

/-- **`𝟘` is strictly ascending**: it has no rows. -/
theorem Tab.zero_asc {k v : Obj} {t : Tab k v} (h : (Tab.zero : Except String (Tab k v)) = .ok t) : t.Asc := by
  simp only [Tab.zero, bind, Except.bind, pure, Except.pure] at h
  split at h; · cases h
  split at h; · cases h
  cases h
  exact fun i => absurd i.2 (by simp)

/-- **A strictly ascending table has distinct rows**: `Obj.lt` is irreflexive. -/
theorem Tab.Asc.nodup {k v : Obj} {R : Tab k v} (hs : R.Asc) : R.toList.Nodup :=
  toList_nodup fun j j' hne e => by
    rcases Nat.lt_or_gt_of_ne (Fin.val_ne_of_ne hne) with h | h
    · have := hs j j' h; rw [e] at this; exact Obj.lt_irrefl _ _ this
    · have := hs j' j h; rw [← e] at this; exact Obj.lt_irrefl _ _ this

/-- **`pack` keeps the order of the rows** (`pack_toList`: the same rows in the same positions). -/
theorem Tab.pack_asc {k v : Obj} {R R' : Tab k v} (h : R.pack = .ok R') (wR : R.WF) (hs : R.Asc) : R'.Asc := by
  obtain ⟨hn, hl⟩ := pack_toList h wR
  have hk : R'.n.toNat = R.n.toNat := congrArg USize.toNat hn
  have e : ∀ i : Fin R'.n.toNat, (R'.key.row i, R'.val.row i) =
      (R.key.row ⟨i, by have := i.2; omega⟩, R.val.row ⟨i, by have := i.2; omega⟩) := fun i => by
    have := congrArg (fun l => l[i.1]?) hl
    simp only [Tab.toList, List.getElem?_ofFn] at this
    obtain ⟨h1, h2⟩ := by simpa [i.2, show i.1 < R.n.toNat by have := i.2; omega] using this
    exact Prod.ext h1 h2
  intro i j hij
  rw [e i, e j]; exact hs _ _ hij

/-- **`(X ∪ T, T − X)` by either path** (`Tab.unionDiffSel`): for a strictly ascending `X`, both tables `WF`, the
answer holds `X ∪ T` and `T − X`, both `WF`, `X ∪ T` strictly ascending — `mergeDiff_holds` on the small-`T` branch,
`unionDiff_ok` with `union_holds`, `rdiff_holds` and `canon_lt` on the other. -/
theorem Tab.unionDiffSel_holds {k v : Obj} {X T V U : Tab k v} (hX : X.WF) (hT : T.WF) (hs : X.Asc)
    (h : X.unionDiffSel T = .ok (V, U)) :
    (∀ a b, V.Holds a b ↔ X.Holds a b ∨ T.Holds a b) ∧ (∀ a b, U.Holds a b ↔ T.Holds a b ∧ ¬ X.Holds a b) ∧
      V.WF ∧ U.WF ∧ V.Asc := by
  unfold Tab.unionDiffSel at h
  split at h
  · obtain ⟨hV, hU, wV, wU, aV, -⟩ := Tab.mergeDiff_holds hX hT hs h
    exact ⟨hV, hU, wV, wU, aV⟩
  · obtain ⟨hu, hd⟩ := Tab.unionDiff_ok h
    obtain ⟨C, hC, hc⟩ := Tab.union_sorted hu
    exact ⟨fun a b => Tab.union_holds hu hX hT a b, fun a b => Tab.rdiff_holds hd hX hT a b, Tab.union_wf hu hX hT,
      Tab.select_wf hd hX hT, fun i j hij => Tab.canon_lt hc (Tab.concat_wf hC hX hT) i j hij⟩

end Rel
