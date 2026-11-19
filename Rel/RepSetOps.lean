import Rel.Run.SetOps
import Rel.RepCols

/-! The laws of `Tab.union`, `Tab.inter`, `Tab.diff` and `Tab.le` (`Rel/Run/SetOps.lean`), from the five kernels' laws
and `Tab.canon`'s (`Rel/RepCanon.lean`). -/

namespace Rel
open Rel.Ext Rel.Kernel Rel.Verify

/-! ## WHERE -/

/-- Among the positions `< n` where `f` holds, ascending, the one at index `#{j < i | f j}` is `i` (`f i`, `i < n`):
`range (i + 1)` is a prefix of `range n`, and its filter ends in `i`. -/
private theorem filter_range_at (f : Nat → Bool) {n i : Nat} (hi : i < n) (hf : f i) :
    ∃ h : ((List.range i).filter f).length < ((List.range n).filter f).length,
      ((List.range n).filter f)[((List.range i).filter f).length] = i := by
  have hp : ((List.range (i + 1)).filter f) <+: ((List.range n).filter f) := List.IsPrefix.filter f
    (List.prefix_iff_eq_take.2 (by rw [List.length_range, List.take_range, Nat.min_eq_left (by omega)]))
  have hl : (List.range (i + 1)).filter f = (List.range i).filter f ++ [i] := by
    rw [List.range_succ, List.filter_append]; simp [hf]
  have hlt : ((List.range i).filter f).length < ((List.range (i + 1)).filter f).length := by rw [hl]; simp
  exact ⟨Nat.lt_of_lt_of_le hlt hp.length_le, by rw [← hp.getElem hlt]; simp [hl]⟩

/-- **`whereCol m b` answers the positions of `b`'s `1` words, ascending**, `b` holding `0`/`1` words. With `C i` the
number of kept rows before row `i`: the prefix sum is `C (i + 1)` (`colPrefix_add_sum`), its fold result `C m = K`
(`kscan_last`), the destination `d = s − b` is `C i`; a kept row `i` is the last row sent to cell `C i` (every later
row's `C` is larger), so the cell holds `i`; and the kept row at index `c` of the filter is the one with `C i = c`
(`filter_range_at`). -/
theorem whereCol_spec {m K : USize} {b o : Enc} (h : whereCol m b = .ok (K, o))
    (hb : ∀ i < m.toNat, (Enc.raw .i64 m b)[i]?.getD 0 < 2) :
    (Enc.raw .i64 K o).toList.map UInt64.toNat =
      (List.range m.toNat).filter fun i => (Enc.raw .i64 m b)[i]?.getD 0 ≠ 0 := by
  unfold whereCol at h
  have hB : m.toNat < min (USize.size - 1) (2 ^ 63) := by
    refine Classical.byContradiction fun hn => ?_; simp only [hn, if_false] at h; cases h
  simp only [hB, if_true, bind, Except.bind, Functor.map, Except.map] at h
  repeat (split at h; · cases h)
  rename_i _ z hz _ sk hsk _ d hd _ e he _ o' ho'
  obtain ⟨hK, rfl⟩ := Prod.mk.inj (Except.ok.inj h)
  rw [hK] at he ho'
  have hU : USize.size ≤ 2 ^ 64 := by rcases USize.size_eq with h | h <;> omega
  have hc64 : ∀ a, a < 2 ^ 63 → a.toUInt64.toNat = a := fun a ha => by simp; omega
  obtain ⟨f, hf⟩ : ∃ f : Nat → Bool, f = fun i => decide ((Enc.raw .i64 m b)[i]?.getD 0 ≠ 0) := ⟨_, rfl⟩
  suffices hs : (Enc.raw .i64 K o').toList.map UInt64.toNat = (List.range m.toNat).filter f by rw [hf] at hs; exact hs
  obtain ⟨C, hC⟩ : ∃ C : Nat → Nat, C = fun a => ((List.range a).filter f).length := ⟨_, rfl⟩
  -- `b[i]` is `f i` as a word
  have hbit : ∀ i < m.toNat, (Enc.raw .i64 m b)[i]?.getD 0 = if f i then 1 else 0 := by
    intro i hi
    have h2 := UInt64.lt_iff_toNat_lt.1 (hb i hi)
    rw [hf]
    by_cases h0 : (Enc.raw .i64 m b)[i]?.getD 0 = 0
    · simp [h0]
    · simp only [h0, ne_eq, not_false_eq_true, decide_true, if_true]
      have : ((Enc.raw .i64 m b)[i]?.getD 0).toNat ≠ 0 := fun e0 => h0 (UInt64.toNat_inj.1 (by simpa using e0))
      apply UInt64.toNat_inj.1; simp at h2 ⊢; omega
  have hstep : ∀ a, C (a + 1) = C a + if f a then 1 else 0 := fun a => by
    rw [hC]; dsimp only; rw [List.range_succ, List.filter_append, List.length_append]; by_cases hfa : f a <;> simp [hfa]
  have hCle : ∀ a, C a ≤ a := fun a => by
    rw [hC]; exact Nat.le_trans (List.length_filter_le _ _) (by simp)
  have hmono : ∀ a a', a ≤ a' → C a ≤ C a' := fun a a' h => by
    rw [hC]; exact (List.IsPrefix.filter f (List.prefix_iff_eq_take.2
      (by rw [List.length_range, List.take_range, Nat.min_eq_left h]))).length_le
  -- the prefix sum: `s[i] = C (i + 1)`
  have hP : colPrefix .add m b = .ok sk.1 := by
    unfold colPrefix; simp only [hz, hsk, bind, Except.bind, pure, Except.pure]
  have hsum : ∀ a, ((List.range a).map fun G => if f G then 1 else 0).sum = C a := by
    intro a; induction a with
    | zero => rw [hC]; rfl
    | succ a ih => rw [hstep, ← ih, List.range_succ, List.map_append, sum_append_nat]; simp
  have hs : ∀ i < m.toNat, (Enc.raw .i64 m sk.1)[i]?.getD 0 = (C (i + 1)).toUInt64 := fun i hi => by
    rw [colPrefix_add_sum hP (fun G => if f G then 1 else 0) (fun G hG => by rw [hbit G hG]; by_cases hfg : f G <;> simp [hfg]) i hi,
      hsum]
  -- the count: the fold result is `C m`, `0` with no rows
  have hk : sk.2.getD 0 = (C m.toNat).toUInt64 := by
    rw [kscan_last (w := 8) rfl hsk]
    simp only [Bool.false_eq_true, if_false]
    rcases Nat.eq_zero_or_pos m.toNat with h0 | h0
    · rw [h0, hC]; simp [(colPrefix_raw hP).2.1, h0]
    · have := hs (m.toNat - 1) (by omega)
      rw [Nat.sub_add_cancel h0] at this
      rw [← this, Array.getElem?_eq_getElem (by rw [(colPrefix_raw hP).2.1]; omega)]
  have hKn : K.toNat = C m.toNat := by
    rw [← hK, hk, hc64 _ (by have := hCle m.toNat; omega)]
    exact USize.toNat_ofNat_of_lt' (by have := hCle m.toNat; omega)
  -- the destination: `d[i] = s[i] − b[i] = C i`
  have hdv : ∀ i < m.toNat, (Enc.raw .i64 m d)[i]?.getD 0 = (C i).toUInt64 := by
    intro i hi
    have := (colMap_raw hd).2.2.2 i hi
    rw [hs i hi, hbit i hi, hstep] at this
    simp only [Op.eval, Except.ok.injEq] at this
    rw [← this]
    cases f i
    · simp
    · show UInt64.ofNat (C i + 1) - 1 = UInt64.ofNat (C i); rw [UInt64.ofNat_add]; simp
  -- a kept row `i` is the last row sent to cell `C i`
  obtain ⟨-, -, -, hws, -, -, hlast⟩ := raw_scatter m d .pos _ 0 e he
  have hpos : ∀ n : USize, ∀ k < n.toNat, (Enc.raw .i64 n (.pos : Enc))[k]?.getD 0 = k.toUInt64 := fun n k hk => by
    simp only [Enc.raw, Array.getElem?_map, Array.getElem?_range, hk, if_true, Option.map_some, Option.getD_some]
  have hcell : ∀ i < m.toNat, f i → (Enc.raw .i64 (K.toNat + 1).toUSize e)[C i]? = some i.toUInt64 := by
    intro i hi hfi
    have := hlast i hi fun k' h1 h2 e' => by
      rw [hdv k' h2, hdv i hi] at e'
      have := congrArg UInt64.toNat e'
      rw [hc64 _ (by have := hCle k'; omega), hc64 _ (by have := hCle i; omega)] at this
      have := hmono (i + 1) k' h1; rw [hstep, if_pos hfi] at this; omega
    rwa [hdv i hi, hc64 _ (by have := hCle i; omega), hpos m i hi] at this
  -- the answer: cell `c` of `e` at each `c < K`
  obtain ⟨his, -, -, hoe⟩ := raw_kgather _ _ _ _ _ ho'
  have hro : Enc.raw .i64 K o' = (Enc.raw .i64 K (.pos : Enc)).map fun c =>
      (Enc.raw .i64 (K.toNat + 1).toUSize e)[c.toNat]?.getD 0 := by
    rw [hoe, (wordsFoR_closed _ (by rw [Array.size_map, his])).2.1]
  -- the filter ascends strictly, so a position names one index
  have hpw := List.pairwise_iff_getElem.1 ((List.pairwise_lt_range (n := m.toNat)).filter f)
  apply List.ext_getElem
  · rw [List.length_map, Array.length_toList, hro, Array.size_map, his, hKn, hC]
  · intro c h1 h2
    have hj := List.getElem_mem h2
    rw [List.mem_filter, List.mem_range] at hj
    obtain ⟨hlt, hat⟩ := filter_range_at f hj.1 hj.2
    have hcj : C ((List.range m.toNat).filter f)[c] = c := by
      rw [hC]; dsimp only
      rcases Nat.lt_trichotomy ((List.range ((List.range m.toNat).filter f)[c]).filter f).length c with h | h | h
      · have := hpw _ _ hlt h2 h; rw [hat] at this; omega
      · exact h
      · have := hpw _ _ h2 hlt h; rw [hat] at this; omega
    have hcK : c < K.toNat := by rw [hKn, hC]; exact h2
    have hcm : c < 2 ^ 63 := by have := hCle m.toNat; omega
    have hpc : ∀ hc, (Enc.raw .i64 K (.pos : Enc))[c]'hc = c.toUInt64 := fun hc => by
      have := hpos K c hcK; rwa [Array.getElem?_eq_getElem hc, Option.getD_some] at this
    have hec : (Enc.raw .i64 (K.toNat + 1).toUSize e)[c]? = some (((List.range m.toNat).filter f)[c]).toUInt64 := by
      have := hcell _ hj.1 hj.2; rwa [hcj] at this
    simp only [List.getElem_map, Array.getElem_toList, hro, Array.getElem_map, hpc, hc64 _ hcm, hec, Option.getD_some]
    exact hc64 _ (by omega)

/-- **`whereCol` answers `K` words**: its last step is a `kgather` of `K` rows. -/
theorem whereCol_size {m K : USize} {b o : Enc} (h : whereCol m b = .ok (K, o)) : (Enc.raw .i64 K o).size = K.toNat := by
  unfold whereCol at h
  have hB : m.toNat < min (USize.size - 1) (2 ^ 63) := by
    refine Classical.byContradiction fun hn => ?_; simp only [hn, if_false] at h; cases h
  simp only [hB, if_true, bind, Except.bind, Functor.map, Except.map] at h
  repeat (split at h; · cases h)
  rename_i o' ho'
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj h).symm
  obtain ⟨his, -, -, hoe⟩ := raw_kgather _ _ _ _ _ ho'
  rw [hoe, (wordsFoR_closed _ (by rw [Array.size_map, his])).2.1, Array.size_map, his]

/-! ## CONCAT and `∪` -/
namespace Tab
variable {k v : Obj}

/-- **`keep T b` holds the rows of `T` whose word of `b` is `1`**, `b` holding `0`/`1` words: answer row `j` is input
row `sel[j]`, and `sel` lists every position of a `1` (`whereCol_spec`, `whereCol_size`). -/
theorem keep_holds {A B : Obj} {T U : Tab A B} {b : Enc} (h : T.keep b = .ok U)
    (hb : ∀ i < T.n.toNat, (Enc.raw .i64 T.n b)[i]?.getD 0 < 2) (a : A.El) (c : B.El) :
    U.Holds a c ↔ ∃ i : Fin T.n.toNat, (Enc.raw .i64 T.n b)[i.1]?.getD 0 ≠ 0 ∧ T.key.row i = a ∧ T.val.row i = c := by
  unfold keep at h; simp only [bind, Except.bind] at h
  split at h; · cases h
  rename_i Ms hMs; obtain ⟨M, sel⟩ := Ms
  split at h; · cases h
  rename_i x hx
  split at h; · cases h
  rename_i y hy
  cases h
  have hsel := whereCol_spec hMs hb
  have hsz := whereCol_size hMs
  simp only [Tab.Holds]
  constructor
  · rintro ⟨j, rfl, rfl⟩
    obtain ⟨i, hi, hxi⟩ := Vals.gather_row _ hx j
    obtain ⟨i', hi', hyi⟩ := Vals.gather_row _ hy j
    have e : i' = i := Fin.ext (by rw [← hi', hi])
    subst e
    have hj : j.1 < (Enc.raw .i64 M sel).size := by rw [hsz]; exact j.2
    have hGm := List.mem_map_of_mem (f := UInt64.toNat) (Array.getElem_mem_toList hj)
    rw [hsel, List.mem_filter, decide_eq_true_eq] at hGm
    rw [Array.getElem?_eq_getElem hj, Option.getD_some] at hi
    rw [hi] at hGm
    exact ⟨i', hGm.2, hxi.symm, hyi.symm⟩
  · rintro ⟨i, hbi, rfl, rfl⟩
    have hm : i.1 ∈ (Enc.raw .i64 M sel).toList.map UInt64.toNat := by
      rw [hsel, List.mem_filter, List.mem_range, decide_eq_true_eq]; exact ⟨i.2, hbi⟩
    obtain ⟨w, hw, hwi⟩ := List.mem_map.1 hm
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hw
    have hj' : j < (Enc.raw .i64 M sel).size := by simpa using hj
    have hjM : j < M.toNat := by rw [← hsz]; exact hj'
    simp only [Array.getElem_toList] at hwi
    have hsj : ((Enc.raw .i64 M sel)[j]?.getD 0).toNat = i.1 := by
      rw [Array.getElem?_eq_getElem hj', Option.getD_some, hwi]
    obtain ⟨i1, hi1, hx1⟩ := Vals.gather_row _ hx ⟨j, hjM⟩
    obtain ⟨i2, hi2, hy2⟩ := Vals.gather_row _ hy ⟨j, hjM⟩
    have e1 : i1 = i := Fin.ext (by rw [← hi1, hsj])
    have e2 : i2 = i := Fin.ext (by rw [← hi2, hsj])
    subst e1 e2
    exact ⟨⟨j, hjM⟩, hx1, hy2⟩

/-- **`R.concat S` denotes `R ∪ S`**, rows counted with repeats. -/
theorem concat_holds {R S C : Tab k v} (h : R.concat S = .ok C) (a : k.El) (b : v.El) :
    C.Holds a b ↔ R.Holds a b ∨ S.Holds a b := by
  unfold Tab.concat at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  split at h; · cases h
  rename_i p hp
  obtain ⟨n, off⟩ := p
  split at h; · cases h
  rename_i K hK
  split at h; · cases h
  rename_i V hV
  cases h
  obtain ⟨hn, hoff⟩ := catPlan_ok hp
  have rk := Vals.concat_row hn hoff R.key S.key hK
  have rv := Vals.concat_row hn hoff R.val S.val hV
  simp only [Tab.Holds]
  constructor
  · rintro ⟨c, ha, hb⟩
    rw [rk] at ha; rw [rv] at hb
    split at ha
    · rename_i hl; rw [dif_pos hl] at hb; exact .inl ⟨_, ha, hb⟩
    · rename_i hl; rw [dif_neg hl] at hb; exact .inr ⟨_, ha, hb⟩
  · rintro (⟨i, ha, hb⟩ | ⟨j, ha, hb⟩)
    · refine ⟨⟨i.1, by omega⟩, ?_, ?_⟩
      · rw [rk, dif_pos i.2]; exact ha
      · rw [rv, dif_pos i.2]; exact hb
    · refine ⟨⟨R.n.toNat + j.1, by omega⟩, ?_, ?_⟩
      · rw [rk, dif_neg (by simp)]; simpa using ha
      · rw [rv, dif_neg (by simp)]; simpa using hb

/-- **`R.union S` denotes `R ∪ S`** (`Rep.rep_unionC`'s statement, pointwise). -/
theorem union_holds {R S U : Tab k v} (h : R.union S = .ok U) (a : k.El) (b : v.El) :
    U.Holds a b ↔ R.Holds a b ∨ S.Holds a b := by
  unfold Tab.union at h
  cases hc : R.concat S with
  | error s => simp [hc, bind, Except.bind] at h
  | ok C => simp only [hc, bind, Except.bind] at h; rw [canon_holds h, concat_holds hc]

/-- **`R.canon` is sorted and duplicate-free**: `Vals.nub_sorted` of its pair side, the rows of `U` being rows `sel j`
of `R`, ascending in `kasc`'s order of their codes, no two with equal codes. -/
theorem canon_sorted {R U : Tab k v} (h : R.canon = .ok U) {es : List (AscKey × Enc)}
    (hes : Vals.cols (A := .prod k v) (R.key, R.val) = .ok es) :
    ∃ sel : Fin U.n.toNat → Fin R.n.toNat,
      (∀ j, (U.key.row j, U.val.row j) = (R.key.row (sel j), R.val.row (sel j))) ∧
      ∀ j j' : Fin U.n.toNat, j.1 < j'.1 → lexLe (ascKeys R.n es) (sel j) (sel j') = true ∧
        seenKey R.n es (sel j) ≠ seenKey R.n es (sel j') := by
  unfold Tab.canon at h
  cases hn : Vals.nub (A := .prod k v) (R.key, R.val) with
  | error s => simp [hn, Functor.map, Except.map] at h
  | ok r =>
    simp only [hn, Functor.map, Except.map, Except.ok.injEq] at h
    subst h
    exact Vals.nub_sorted hn hes

/-- **`R.canon`'s rows are distinct** (`Vals.nub_distinct` of its pair side). -/
theorem canon_distinct {k v : Obj} {R U : Tab k v} (h : R.canon = .ok U) {j j' : Fin U.n.toNat} (hjj : j ≠ j') :
    (U.key.row j, U.val.row j) ≠ (U.key.row j', U.val.row j') := by
  unfold Tab.canon at h
  cases hn : Vals.nub (A := .prod k v) (R.key, R.val) with
  | error s => simp [hn, Functor.map, Except.map] at h
  | ok r =>
    simp only [hn, Functor.map, Except.map, Except.ok.injEq] at h
    subst h
    exact Vals.nub_distinct hn hjj

/-- **A canonical table's columns have codes**: `canon`
ran `Vals.cols` and `kasc` on `(R.key, R.val)`. -/
theorem canon_codes {k v : Obj} {R r : Tab k v} (h : R.canon = .ok r) :
    ∃ es cs, Vals.cols (A := .prod k v) (R.key, R.val) = .ok es ∧ es.mapM (ascCol R.n) = .ok cs := by
  simp only [Tab.canon, Functor.map, Except.map] at h
  split at h; · cases h
  rename_i y hy
  obtain ⟨es, vs, p, -, -, -, -, -, hes, hasc, -⟩ := Vals.nub_ok hy
  obtain ⟨cs, hcs, -⟩ := kasc_grade hasc
  exact ⟨es, cs, hes, hcs⟩


/-- **`R.union S` is sorted and duplicate-free**: `canon_sorted` of the concatenation. -/
theorem union_sorted {R S U : Tab k v} (h : R.union S = .ok U) :
    ∃ C, R.concat S = .ok C ∧ C.canon = .ok U := by
  unfold Tab.union at h
  cases hc : R.concat S with
  | error s => simp [hc, bind, Except.bind] at h
  | ok C => simp only [hc, bind, Except.bind] at h; exact ⟨C, rfl, h⟩

/-- **The source tag of `R.tagged S`**: its table is `R.concat S`, and row `c`'s tag is `1` iff `c ≥ R.n` (a row of
`S`), `0` below (a row of `R`). -/
theorem tagged_ok {R S C : Tab k v} {tag : Enc} (h : R.tagged S = .ok (C, tag)) :
    R.concat S = .ok C ∧ C.n.toNat = R.n.toNat + S.n.toNat ∧ (Enc.raw .i64 C.n tag).size = C.n.toNat ∧
      ∀ c < C.n.toNat, (Enc.raw .i64 C.n tag)[c]?.getD 0 = if R.n.toNat ≤ c then 1 else 0 := by
  unfold Tab.tagged at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  split at h; · cases h
  rename_i p hp
  obtain ⟨n, off⟩ := p
  split at h; · cases h
  rename_i K hK
  split at h; · cases h
  rename_i V hV
  split at h; · cases h
  rename_i one h1
  split at h; · cases h
  rename_i t ht
  cases h
  obtain ⟨hn, hoff⟩ := catPlan_ok hp
  refine ⟨by unfold Tab.concat; simp only [hp, hK, hV, bind, Except.bind, pure, Except.pure], hn, ?_⟩
  obtain ⟨-, -, -, hws, -, hfix, hlast⟩ := raw_scatter S.n off one n 0 _ ht
  refine ⟨hws, fun c hc => ?_⟩
  have hc' : c < n.toNat := hc
  split
  · rename_i hl
    have e := hlast (c - R.n.toNat) (by omega) fun k' h1 h2 e => by
      have := congrArg UInt64.toNat e; rw [hoff k' h2, hoff _ (by omega)] at this; omega
    rw [hoff _ (by omega), show R.n.toNat + (c - R.n.toNat) = c by omega] at e
    rw [e, colConst_raw h1]
    simp [show c - R.n.toNat < S.n.toNat by omega]
  · rename_i hl
    have e := hfix c hc' fun k hk e => by rw [hoff k hk] at e; omega
    simp [e]

/-- **`R.concat S` row by row**: its rows below `R.n` are `R`'s, from there `S`'s. -/
theorem concat_split {R S C : Tab k v} (h : R.concat S = .ok C) {a : k.El} {b : v.El} :
    ((∃ c : Fin C.n.toNat, c.1 < R.n.toNat ∧ C.key.row c = a ∧ C.val.row c = b) ↔ R.Holds a b) ∧
      ((∃ c : Fin C.n.toNat, R.n.toNat ≤ c.1 ∧ C.key.row c = a ∧ C.val.row c = b) ↔ S.Holds a b) := by
  unfold Tab.concat at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  split at h; · cases h
  rename_i p hp
  obtain ⟨n, off⟩ := p
  split at h; · cases h
  rename_i K hK
  split at h; · cases h
  rename_i V hV
  cases h
  obtain ⟨hn, hoff⟩ := catPlan_ok hp
  have rk := Vals.concat_row hn hoff R.key S.key hK
  have rv := Vals.concat_row hn hoff R.val S.val hV
  simp only [Tab.Holds]
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · rintro ⟨c, hl, ha, hb⟩
    rw [rk, dif_pos hl] at ha; rw [rv, dif_pos hl] at hb; exact ⟨_, ha, hb⟩
  · rintro ⟨i, ha, hb⟩
    exact ⟨⟨i.1, by omega⟩, i.2, by rw [rk, dif_pos i.2]; exact ha, by rw [rv, dif_pos i.2]; exact hb⟩
  · rintro ⟨c, hl, ha, hb⟩
    rw [rk, dif_neg (by omega)] at ha; rw [rv, dif_neg (by omega)] at hb; exact ⟨_, ha, hb⟩
  · rintro ⟨j, ha, hb⟩
    refine ⟨⟨R.n.toNat + j.1, by omega⟩, by simp, ?_, ?_⟩
    · rw [rk, dif_neg (by simp)]; simpa using ha
    · rw [rv, dif_neg (by simp)]; simpa using hb

/-- **What `select keep R S` answers**, `keep` answering per group a `0`/`1` word that is `1` iff
`κ (and = 0) (or = 1)`: the pairs of `R ∪ S` whose flags pass `κ`, and, in `Tab.canon_sorted`'s form over
`C = R.concat S`, its rows ascending with unequal codes. A group is a run of equal rows (`Vals.row_of_codes`,
`Vals.codes_of_row`), its `and` of the tags is `0` iff it holds a row of `R` and its `or` is `1` iff one of `S`
(`scatterWords_fold`), the kept groups are `whereCol_spec`'s positions, ascending, and answer row `j` is the first input
row `ps[F[sel[j]]]` of its group (`Vals.gather_row`), which ascend with `sel` (`Verify.firsts_sorted`). -/
theorem select_ok {keep : USize → Enc → Enc → Except String Enc} {κ : Prop → Prop → Prop}
    (hk : ∀ M mn mx o, keep M mn mx = .ok o → (Enc.raw .i64 M o).size = M.toNat ∧ ∀ G < M.toNat,
      (Enc.raw .i64 M mn)[G]?.getD 0 < 2 → (Enc.raw .i64 M mx)[G]?.getD 0 < 2 →
      (Enc.raw .i64 M o)[G]?.getD 0 < 2 ∧ ((Enc.raw .i64 M o)[G]?.getD 0 ≠ 0 ↔
        κ ((Enc.raw .i64 M mn)[G]?.getD 0 = 0) ((Enc.raw .i64 M mx)[G]?.getD 0 = 1)))
    {R S U : Tab k v} (h : select keep R S = .ok U) :
    (∀ a b, U.Holds a b ↔ (R.Holds a b ∨ S.Holds a b) ∧ κ (R.Holds a b) (S.Holds a b)) ∧
    ∃ C es, R.concat S = .ok C ∧ Vals.cols (A := .prod k v) (C.key, C.val) = .ok es ∧
      ∃ sel : Fin U.n.toNat → Fin C.n.toNat,
        (∀ j, (U.key.row j, U.val.row j) = (C.key.row (sel j), C.val.row (sel j))) ∧
        ∀ j j' : Fin U.n.toNat, j.1 < j'.1 → lexLe (ascKeys C.n es) (sel j) (sel j') = true ∧
          seenKey C.n es (sel j) ≠ seenKey C.n es (sel j') := by
  unfold select at h
  simp only [bind, Except.bind, Functor.map, Except.map] at h
  repeat (split at h; · cases h)
  rename_i _ Ct hCt _ es hes _ vp hvp _ r hr _ ts hts _ mn hmn _ mx hmx _ kb hkb _ Ks hKs _ ix1 hix1 _ ix hix _ y hy
  obtain ⟨C, tag⟩ := Ct; obtain ⟨vs, p⟩ := vp; obtain ⟨mm, g, f⟩ := r; obtain ⟨K, sel⟩ := Ks
  injection h with h; subst h
  dsimp only at *
  have hU : USize.size ≤ 2 ^ 64 := by rcases USize.size_eq with h | h <;> omega
  have hn := C.n.toNat_lt_size
  obtain ⟨hcat, hCn, htsz, htag⟩ := tagged_ok hCt
  have hsplit := fun (a : k.El) (b : v.El) => concat_split hcat (a := a) (b := b)
  -- the sorted rows: `ps`, and the sorted rows' keys are the input's at `ps`
  obtain ⟨ps, hp, hperm, hvl, hcol⟩ := asc_perm _ _ _ _ hvp
  obtain ⟨cs, hc, -⟩ := kasc_ok hvp
  have hlen : ps.length = C.n.toNat := by simpa using hperm.length_eq
  have hpsl : ∀ q (hq : q < ps.length), ps[q] < C.n.toNat := fun q hq =>
    List.mem_range.1 (hperm.mem_iff.1 (List.getElem_mem hq))
  have hc64 : ∀ a, a < C.n.toNat → a.toUInt64.toNat = a := fun a ha => by simp; omega
  have hkey : ∀ q (hq : q < ps.length), seenKey C.n ((es.map (·.1)).zip vs) q = seenKey C.n es ps[q] := by
    intro q hq
    refine ascKeys_row (by simp [List.map_fst_zip, hvl]) fun c h1 h2 => ?_
    obtain ⟨ws, hv, hws, hwq⟩ := hcol c es[c] (vs[c]'(by simp at h1; omega)) (List.getElem?_eq_getElem h2)
      (List.getElem?_eq_getElem _)
    simp only [List.getElem_zip, hv, (wordsFoR_closed ws hws.symm).2.1, hwq q hq]
  obtain ⟨hmm, hg, hf⟩ := kseen_ok hr
  generalize seenKey C.n ((es.map (·.1)).zip vs) = Kf at hmm hg hf hkey
  generalize hF : firstsOf Kf C.n.toNat = F at hmm hg hf
  have hsp := firsts_spec Kf C.n.toNat; rw [hF] at hsp
  have hFlt : ∀ G (hG : G < F.length), F[G] < C.n.toNat := fun G hG => ((hsp.2.1 _).1 (List.getElem_mem hG)).1
  have hmn' : mm ≤ C.n.toNat := by rw [hmm, ← hF]; unfold firstsOf; exact Nat.le_trans (List.length_filter_le _ _) (by simp)
  have hmU : mm.toUSize.toNat = mm := USize.toNat_ofNat_of_lt' (by omega)
  -- rows in one group are equal rows
  have hgrp : ∀ q (hq : q < ps.length) G (hG : G < F.length),
      Verify.groupOf Kf C.n.toNat q = G ↔ Vals.row (A := .prod k v) (C.key, C.val) ⟨ps[q], hpsl q hq⟩ =
        Vals.row (A := .prod k v) (C.key, C.val) ⟨ps[F[G]]'(by have := hFlt G hG; omega), hpsl _ _⟩ := by
    intro q hq G hG
    rw [(hsp.2.2.2.2.1 q (by omega) G), exists_prop_of_true hG, hkey _ (by have := hFlt G hG; omega), hkey q hq]
    exact ⟨fun e => Vals.row_of_codes _ hes hc _ _ e.symm, fun e => (Vals.codes_of_row _ hes hc _ _ e).symm⟩
  -- the tags in sorted order, and their `and`/`or` per group
  obtain ⟨-, -, -, hts'⟩ := raw_kgather _ _ _ _ _ hts
  have hrp : Enc.raw .i64 C.n p = (ps.map Nat.toUInt64).toArray := by
    rw [hp]; exact (wordsFoR_closed _ (by simp [hlen])).2.1
  have htv : ∀ q (hq : q < ps.length), (Enc.raw .i64 C.n ts)[q]?.getD 0 = if R.n.toNat ≤ ps[q] then 1 else 0 := by
    intro q hq
    rw [hts', (wordsFoR_closed _ (by simp [hrp, hlen])).2.1, hrp]
    simp only [Array.getElem?_map, List.getElem?_toArray, List.getElem?_map, List.getElem?_eq_getElem hq,
      Option.map_some, Option.getD_some, hc64 _ (hpsl q hq)]
    exact htag _ (hpsl q hq)
  have hgr : Enc.raw .i64 C.n g = Array.ofFn (n := C.n.toNat) fun i => (Verify.groupOf Kf C.n.toNat i.1).toUInt64 := by
    rw [hg]; exact (wordsFoR_closed _ (by simp)).2.1
  have hgv : ∀ q < C.n.toNat, ((Enc.raw .i64 C.n g)[q]?.getD 0).toNat = Verify.groupOf Kf C.n.toNat q := by
    intro q hq
    obtain ⟨hgl, -⟩ := hsp.2.2.2.2.2 q hq
    rw [hgr, Array.getElem?_ofFn, dif_pos hq, Option.getD_some]; exact hc64 (Verify.groupOf Kf C.n.toNat q) (by omega)
  have hand : ∀ (l : List UInt64), (∀ x ∈ l, x = 0 ∨ x = 1) → ∀ acc : UInt64, (acc = 0 ∨ acc = 1) →
      (l.foldl (· &&& ·) acc = 0 ∨ l.foldl (· &&& ·) acc = 1) ∧ (l.foldl (· &&& ·) acc = 0 ↔ acc = 0 ∨ 0 ∈ l) := by
    intro l; induction l with
    | nil => intro _ acc hacc; simp only [List.foldl_nil]; exact ⟨hacc, by simp⟩
    | cons x l ih =>
      intro hl acc hacc
      have hx := hl x (.head _)
      have := ih (fun y hy => hl y (.tail _ hy)) (acc &&& x)
        (by rcases hx with rfl | rfl <;> rcases hacc with rfl | rfl <;> decide)
      simp only [List.foldl_cons]
      refine ⟨this.1, ?_⟩
      rw [this.2]
      rcases hx with rfl | rfl <;> rcases hacc with rfl | rfl <;> simp
  have hor : ∀ (l : List UInt64), (∀ x ∈ l, x = 0 ∨ x = 1) → ∀ acc : UInt64, (acc = 0 ∨ acc = 1) →
      (l.foldl (· ||| ·) acc = 0 ∨ l.foldl (· ||| ·) acc = 1) ∧ (l.foldl (· ||| ·) acc = 1 ↔ acc = 1 ∨ 1 ∈ l) := by
    intro l; induction l with
    | nil => intro _ acc hacc; simp only [List.foldl_nil]; exact ⟨hacc, by simp⟩
    | cons x l ih =>
      intro hl acc hacc
      have hx := hl x (.head _)
      have := ih (fun y hy => hl y (.tail _ hy)) (acc ||| x)
        (by rcases hx with rfl | rfl <;> rcases hacc with rfl | rfl <;> decide)
      simp only [List.foldl_cons]
      refine ⟨this.1, ?_⟩
      rw [this.2]
      rcases hx with rfl | rfl <;> rcases hacc with rfl | rfl <;> simp
  obtain ⟨hgs, hts2, hwmn⟩ := kscatter_words hmn
  obtain ⟨-, -, hwmx⟩ := kscatter_words hmx
  have hfmn := scatterWords_fold (f := (· &&& ·)) (fun _ _ => rfl) hwmn
  have hfmx := scatterWords_fold (f := (· ||| ·)) (fun _ _ => rfl) hwmx
  -- the list a group's fold reads, and its members
  have hl01 : ∀ G, ∀ x ∈ ((List.range (Enc.raw .i64 C.n g).size).filter fun q =>
      ((Enc.raw .i64 C.n g)[q]?.getD 0).toNat = G).map ((Enc.raw .i64 C.n ts)[·]?.getD 0), x = 0 ∨ x = 1 := by
    intro G x hx
    obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hx
    have hq' : q < ps.length := by rw [hlen, ← hgs]; exact List.mem_range.1 (List.mem_filter.1 hq).1
    rw [htv q hq']; split <;> simp
  have hmem : ∀ G (w : UInt64), w ∈ ((List.range (Enc.raw .i64 C.n g).size).filter fun q =>
      ((Enc.raw .i64 C.n g)[q]?.getD 0).toNat = G).map ((Enc.raw .i64 C.n ts)[·]?.getD 0) ↔
      ∃ q, ∃ hq : q < ps.length, Verify.groupOf Kf C.n.toNat q = G ∧ (if R.n.toNat ≤ ps[q] then 1 else 0) = w := by
    intro G w
    simp only [List.mem_map, List.mem_filter, List.mem_range, decide_eq_true_eq, hgs]
    constructor
    · rintro ⟨q, ⟨hq, hqG⟩, rfl⟩; exact ⟨q, by omega, by rw [← hgv q hq, hqG], (htv q (by omega)).symm⟩
    · rintro ⟨q, hq, hqG, rfl⟩; exact ⟨q, ⟨by omega, by rw [hgv q (by omega), hqG]⟩, htv q hq⟩
  -- per group: `mn = 0` iff it holds a row of `R`, `mx = 1` iff one of `S`
  have hR0 : ∀ G < mm, ((Enc.raw .i64 mm.toUSize mn)[G]?.getD 0 = 0 ∨ (Enc.raw .i64 mm.toUSize mn)[G]?.getD 0 = 1) ∧
      ((Enc.raw .i64 mm.toUSize mn)[G]?.getD 0 = 0 ↔
        ∃ q, ∃ hq : q < ps.length, Verify.groupOf Kf C.n.toNat q = G ∧ ps[q] < R.n.toNat) := by
    intro G hG
    rw [hfmn.2 G (by omega)]
    obtain ⟨h1, h2⟩ := hand _ (hl01 G) 1 (.inr rfl)
    refine ⟨h1, h2.trans ?_⟩
    rw [hmem]
    simp only [show (1 : UInt64) ≠ 0 by decide, false_or]
    exact exists_congr fun q => exists_congr fun hq => and_congr_right fun _ => by split <;> simp <;> omega
  have hS1 : ∀ G < mm, ((Enc.raw .i64 mm.toUSize mx)[G]?.getD 0 = 0 ∨ (Enc.raw .i64 mm.toUSize mx)[G]?.getD 0 = 1) ∧
      ((Enc.raw .i64 mm.toUSize mx)[G]?.getD 0 = 1 ↔
        ∃ q, ∃ hq : q < ps.length, Verify.groupOf Kf C.n.toNat q = G ∧ R.n.toNat ≤ ps[q]) := by
    intro G hG
    rw [hfmx.2 G (by omega)]
    obtain ⟨h1, h2⟩ := hor _ (hl01 G) 0 (.inl rfl)
    refine ⟨h1, h2.trans ?_⟩
    rw [hmem]
    simp only [show (0 : UInt64) ≠ 1 by decide, false_or]
    exact exists_congr fun q => exists_congr fun hq => and_congr_right fun _ => by split <;> simp <;> omega
  -- a group's flags say whether `R` and `S` hold its row
  have hgrpR : ∀ G (hG : G < F.length) (w : (Obj.prod k v).El),
      Vals.row (A := .prod k v) (C.key, C.val) ⟨ps[F[G]]'(by have := hFlt G hG; omega), hpsl _ _⟩ = w →
      ((∃ q, ∃ hq : q < ps.length, Verify.groupOf Kf C.n.toNat q = G ∧ ps[q] < R.n.toNat) ↔ R.Holds w.1 w.2) ∧
      ((∃ q, ∃ hq : q < ps.length, Verify.groupOf Kf C.n.toNat q = G ∧ R.n.toNat ≤ ps[q]) ↔ S.Holds w.1 w.2) := by
    intro G hG w hw
    have key : ∀ (P : Nat → Prop), (∃ q, ∃ hq : q < ps.length, Verify.groupOf Kf C.n.toNat q = G ∧ P ps[q]) ↔
        ∃ c : Fin C.n.toNat, P c.1 ∧ C.key.row c = w.1 ∧ C.val.row c = w.2 := by
      intro P
      constructor
      · rintro ⟨q, hq, hqG, hP⟩
        have e := (hgrp q hq G hG).1 hqG
        rw [hw] at e
        exact ⟨⟨ps[q], hpsl q hq⟩, hP, congrArg Prod.fst e, congrArg Prod.snd e⟩
      · rintro ⟨c, hP, h1, h2⟩
        obtain ⟨q, hq, hqc⟩ := List.getElem_of_mem (hperm.mem_iff.2 (List.mem_range.2 c.2))
        refine ⟨q, hq, (hgrp q hq G hG).2 ?_, hqc ▸ hP⟩
        rw [hw]
        have : (⟨ps[q], hpsl q hq⟩ : Fin C.n.toNat) = c := Fin.ext hqc
        rw [this]; exact Prod.ext h1 h2
    exact ⟨(key (· < R.n.toNat)).trans (hsplit w.1 w.2).1, (key (R.n.toNat ≤ ·)).trans (hsplit w.1 w.2).2⟩
  -- the kept groups, ascending (`whereCol_spec`)
  obtain ⟨-, hbits⟩ := hk _ _ _ _ hkb
  have hbit : ∀ G < mm, ((Enc.raw .i64 mm.toUSize kb)[G]?.getD 0 ≠ 0 ↔
      κ (∃ q, ∃ hq : q < ps.length, Verify.groupOf Kf C.n.toNat q = G ∧ ps[q] < R.n.toNat)
        (∃ q, ∃ hq : q < ps.length, Verify.groupOf Kf C.n.toNat q = G ∧ R.n.toNat ≤ ps[q])) ∧
      (Enc.raw .i64 mm.toUSize kb)[G]?.getD 0 < 2 := by
    intro G hG
    have b2 : ∀ w : UInt64, w = 0 ∨ w = 1 → w < 2 := fun w hw => by rcases hw with rfl | rfl <;> decide
    obtain ⟨h2, hiff⟩ := hbits G (by omega) (b2 _ (hR0 G hG).1) (b2 _ (hS1 G hG).1)
    rw [← propext (hR0 G hG).2, ← propext (hS1 G hG).2]
    exact ⟨hiff, h2⟩
  have hsel := whereCol_spec hKs fun G hG => (hbit G (by omega)).2
  -- row `j` of the answer is input row `ps[F[sel[j]]]`
  obtain ⟨his1, -, -, hix1'⟩ := raw_kgather _ _ _ _ _ hix1
  obtain ⟨his2, -, -, hix'⟩ := raw_kgather _ _ _ _ _ hix
  have hrf : Enc.raw .i64 mm.toUSize f = (F.map Nat.toUInt64).toArray := by
    rw [hf]; exact (wordsFoR_closed _ (by rw [hmU, hmm]; simp)).2.1
  have hrix : Enc.raw .i64 K ix = ((Enc.raw .i64 K sel).map fun i => (Enc.raw .i64 mm.toUSize f)[i.toNat]?.getD 0).map
      fun i => (Enc.raw .i64 C.n p)[i.toNat]?.getD 0 := by
    rw [hix', (wordsFoR_closed _ (by rw [Array.size_map, his2])).2.1, hix1',
      (wordsFoR_closed _ (by rw [Array.size_map, his1])).2.1]
  have hixv : ∀ j (hj : j < K.toNat) G (hG : G < F.length), ((Enc.raw .i64 K sel)[j]?.getD 0).toNat = G →
      ((Enc.raw .i64 K ix)[j]?.getD 0).toNat = ps[F[G]]'(by have := hFlt G hG; omega) := by
    intro j hj G hG hjG
    have hj' : j < (Enc.raw .i64 K sel).size := by rw [his1]; exact hj
    rw [Array.getElem?_eq_getElem hj', Option.getD_some] at hjG
    have hpj : F[G] < ps.length := by have := hFlt G hG; omega
    rw [hrix, Array.getElem?_map, Array.getElem?_map, Array.getElem?_eq_getElem hj', Option.map_some,
      Option.map_some, Option.getD_some, hjG, hrf, hrp]
    simp only [List.getElem?_toArray, List.getElem?_map, List.getElem?_eq_getElem hG, Option.map_some,
      Option.getD_some, hc64 _ (hFlt G hG), List.getElem?_eq_getElem hpj, hc64 _ (hpsl _ hpj)]
  refine ⟨fun a b => ?_, ?_⟩
  rotate_left
  · -- answer row `j` is input row `ps[F[G]]`, `G = sel[j]` ascending (`whereCol_spec`)
    have hrow : ∀ j : Fin K.toNat, ∃ i : Fin C.n.toNat, Vals.row y j = Vals.row (A := .prod k v) (C.key, C.val) i ∧
        F[((Enc.raw .i64 K sel)[j.1]'(by rw [his1]; exact j.2)).toNat]?.bind (ps[·]?) = some i.1 := by
      intro j
      obtain ⟨i, hi, hyi⟩ := Vals.gather_row _ hy j
      have hj : j.1 < (Enc.raw .i64 K sel).size := by rw [his1]; exact j.2
      have hGm := List.mem_map_of_mem (f := UInt64.toNat) (Array.getElem_mem_toList hj)
      rw [hsel, List.mem_filter, List.mem_range, decide_eq_true_eq] at hGm
      have hGF : ((Enc.raw .i64 K sel)[j.1]).toNat < F.length := by have := hGm.1; rw [hmU] at this; omega
      have hiv := hixv j j.2 _ hGF (by rw [Array.getElem?_eq_getElem hj, Option.getD_some])
      rw [hi] at hiv
      refine ⟨i, hyi, ?_⟩
      rw [List.getElem?_eq_getElem hGF, Option.bind_some,
        List.getElem?_eq_getElem (by have := hFlt _ hGF; omega), hiv]
    obtain ⟨sl, hs⟩ := Classical.axiomOfChoice hrow
    refine ⟨C, es, hcat, hes, sl, fun j => (hs j).1, fun j j' hjj => ?_⟩
    have hpw : ((Enc.raw .i64 K sel).toList.map UInt64.toNat).Pairwise (· < ·) := by
      rw [hsel]; exact List.pairwise_lt_range.filter _
    have hGG := List.pairwise_iff_getElem.1 hpw j j' (by simp [his1]) (by simp [his1]) hjj
    simp only [List.getElem_map, Array.getElem_toList] at hGG
    have e := (hs j).2; have e' := (hs j').2
    have hpsg := asc_perm_grade hvp hp hperm
    subst hF hpsg
    exact Verify.firsts_sorted hkey hGG e e'
  have hCH := concat_holds hcat a b
  simp only [Tab.Holds]
  constructor
  · rintro ⟨j, ha, hb⟩
    obtain ⟨i, hi, hyi⟩ := Vals.gather_row _ hy j
    have hj : j.1 < (Enc.raw .i64 K sel).size := by rw [his1]; exact j.2
    have hGm := List.mem_map_of_mem (f := UInt64.toNat) (Array.getElem_mem_toList hj)
    rw [hsel, List.mem_filter, List.mem_range, decide_eq_true_eq] at hGm
    obtain ⟨hGlt, hGbit⟩ := hGm
    rw [hmU] at hGlt
    have hGF : ((Enc.raw .i64 K sel)[j.1]).toNat < F.length := by omega
    have hiv := hixv j j.2 _ hGF (by rw [Array.getElem?_eq_getElem hj, Option.getD_some])
    rw [hi] at hiv
    have hxi : Vals.row (A := .prod k v) (C.key, C.val) i = (a, b) := by
      rw [← hyi]; show (Vals.row _ j, Vals.row _ j) = (a, b); rw [ha, hb]
    have hw : Vals.row (A := .prod k v) (C.key, C.val) ⟨ps[F[((Enc.raw .i64 K sel)[j.1]).toNat]]'(by
        have := hFlt _ hGF; omega), hpsl _ _⟩ = (a, b) := by
      rw [← hxi]; exact congrArg _ (Fin.ext hiv.symm)
    have hκ := ((hbit _ hGlt).1).1 hGbit
    rw [propext (hgrpR _ hGF _ hw).1, propext (hgrpR _ hGF _ hw).2] at hκ
    exact ⟨hCH.1 ⟨i, congrArg Prod.fst hxi, congrArg Prod.snd hxi⟩, hκ⟩
  · rintro ⟨hRS, hκ⟩
    obtain ⟨c, hca, hcb⟩ := hCH.2 hRS
    obtain ⟨q, hq, hqc⟩ := List.getElem_of_mem (hperm.mem_iff.2 (List.mem_range.2 c.2))
    obtain ⟨hGF, -, -, -⟩ := hsp.2.2.2.2.2 q (by omega)
    generalize hG : Verify.groupOf Kf C.n.toNat q = G at hGF
    have hw : Vals.row (A := .prod k v) (C.key, C.val) ⟨ps[F[G]]'(by have := hFlt G hGF; omega), hpsl _ _⟩ =
        (a, b) := by
      rw [← (hgrp q hq G hGF).1 hG]
      have : (⟨ps[q], hpsl q hq⟩ : Fin C.n.toNat) = c := Fin.ext hqc
      rw [this]; exact Prod.ext hca hcb
    have hGm : G < mm := by omega
    have hbG := ((hbit G hGm).1).2 (by
      rw [propext (hgrpR _ hGF _ hw).1, propext (hgrpR _ hGF _ hw).2]; exact hκ)
    have hmemG : G ∈ (Enc.raw .i64 K sel).toList.map UInt64.toNat := by
      rw [hsel, List.mem_filter, List.mem_range, decide_eq_true_eq, hmU]; exact ⟨hGm, hbG⟩
    obtain ⟨j, hj, hjG⟩ := List.mem_iff_getElem.1 hmemG
    have hjK : j < K.toNat := by simp at hj; omega
    obtain ⟨i, hi, hyi⟩ := Vals.gather_row _ hy ⟨j, hjK⟩
    have hiv := hixv j hjK G hGF (by
      rw [← hjG, List.getElem_map, Array.getElem_toList, Array.getElem?_eq_getElem (by rw [his1]; exact hjK),
        Option.getD_some])
    rw [hi] at hiv
    have : i = ⟨ps[F[G]]'(by have := hFlt G hGF; omega), hpsl _ _⟩ := Fin.ext hiv
    rw [this, hw] at hyi
    exact ⟨⟨j, hjK⟩, congrArg Prod.fst hyi, congrArg Prod.snd hyi⟩

/-- A word below `2` is `0` or `1`. -/
private theorem bit01 {w : UInt64} (hw : w < 2) : w = 0 ∨ w = 1 := by
  have : w.toNat < 2 := hw
  rcases (show w.toNat = 0 ∨ w.toNat = 1 by omega) with h | h
  · exact .inl (UInt64.toNat_inj.1 h)
  · exact .inr (UInt64.toNat_inj.1 h)

/-- `inter`'s `keep`, `and < or` (`colMap .lt`), is `1` exactly where a group holds a row of each side. -/
theorem inter_keep (M : USize) (mn mx o : Enc) (ho : colMap .lt M mn mx = .ok o) :
    (Enc.raw .i64 M o).size = M.toNat ∧ ∀ G < M.toNat,
      (Enc.raw .i64 M mn)[G]?.getD 0 < 2 → (Enc.raw .i64 M mx)[G]?.getD 0 < 2 →
      (Enc.raw .i64 M o)[G]?.getD 0 < 2 ∧ ((Enc.raw .i64 M o)[G]?.getD 0 ≠ 0 ↔
        ((Enc.raw .i64 M mn)[G]?.getD 0 = 0) ∧ ((Enc.raw .i64 M mx)[G]?.getD 0 = 1)) := by
  obtain ⟨-, -, hs, hrow⟩ := colMap_raw ho
  refine ⟨hs, fun G hG h1 h2 => ?_⟩
  have e := hrow G hG
  generalize (Enc.raw .i64 M mn)[G]?.getD 0 = x at h1 e ⊢
  generalize (Enc.raw .i64 M mx)[G]?.getD 0 = y at h2 e ⊢
  generalize (Enc.raw .i64 M o)[G]?.getD 0 = z at e ⊢
  rcases bit01 h1 with rfl | rfl <;> rcases bit01 h2 with rfl | rfl <;>
    (simp only [Op.eval, Except.ok.injEq] at e; subst e; (try dsimp only); decide)

/-- **`R.inter S` denotes `R ∩ S`**: `select` keeping the groups with `and < or`, a row of each. -/
theorem inter_holds {R S U : Tab k v} (h : R.inter S = .ok U) (a : k.El) (b : v.El) :
    U.Holds a b ↔ R.Holds a b ∧ S.Holds a b := by
  rw [(select_ok (κ := (· ∧ ·)) inter_keep h).1 a b]
  exact ⟨fun h => h.2, fun h => ⟨.inl h.1, h⟩⟩

/-- **`R.inter S` is sorted and duplicate-free**, in `Tab.canon_sorted`'s form over `R.concat S` (`select_ok`). -/
theorem inter_sorted {R S U : Tab k v} (h : R.inter S = .ok U) :
    ∃ C es, R.concat S = .ok C ∧ Vals.cols (A := .prod k v) (C.key, C.val) = .ok es ∧
      ∃ sel : Fin U.n.toNat → Fin C.n.toNat,
        (∀ j, (U.key.row j, U.val.row j) = (C.key.row (sel j), C.val.row (sel j))) ∧
        ∀ j j' : Fin U.n.toNat, j.1 < j'.1 → lexLe (ascKeys C.n es) (sel j) (sel j') = true ∧
          seenKey C.n es (sel j) ≠ seenKey C.n es (sel j') :=
  (select_ok (κ := (· ∧ ·)) inter_keep h).2

/-- `diff`'s `keep`, `not` of the `or` (`colMap .not`), is `1` exactly where a group holds no row of `S`. -/
theorem diff_keep (M : USize) (mn mx o : Enc) (ho : colMap .not M mx mx = .ok o) :
    (Enc.raw .i64 M o).size = M.toNat ∧ ∀ G < M.toNat,
      (Enc.raw .i64 M mn)[G]?.getD 0 < 2 → (Enc.raw .i64 M mx)[G]?.getD 0 < 2 →
      (Enc.raw .i64 M o)[G]?.getD 0 < 2 ∧ ((Enc.raw .i64 M o)[G]?.getD 0 ≠ 0 ↔
        ¬((Enc.raw .i64 M mx)[G]?.getD 0 = 1)) := by
  obtain ⟨-, -, hs, hrow⟩ := colMap_raw ho
  refine ⟨hs, fun G hG _ h2 => ?_⟩
  have e := hrow G hG
  generalize (Enc.raw .i64 M mx)[G]?.getD 0 = y at h2 e ⊢
  generalize (Enc.raw .i64 M o)[G]?.getD 0 = z at e ⊢
  rcases bit01 h2 with rfl | rfl <;>
    (simp only [Op.eval, Except.ok.injEq] at e; subst e; (try dsimp only); decide)

/-- **`R.diff S` denotes `R − S`**: `select` keeping the groups with `or = 0`, no row of `S`. -/
theorem diff_holds {R S U : Tab k v} (h : R.diff S = .ok U) (a : k.El) (b : v.El) :
    U.Holds a b ↔ R.Holds a b ∧ ¬S.Holds a b := by
  rw [(select_ok (κ := fun _ s => ¬s) diff_keep h).1 a b]
  exact ⟨fun h => ⟨h.1.resolve_right h.2, h.2⟩, fun h => ⟨.inl h.1, h.2⟩⟩

/-- **`R.diff S` is sorted and duplicate-free**, in `Tab.canon_sorted`'s form over `R.concat S` (`select_ok`). -/
theorem diff_sorted {R S U : Tab k v} (h : R.diff S = .ok U) :
    ∃ C es, R.concat S = .ok C ∧ Vals.cols (A := .prod k v) (C.key, C.val) = .ok es ∧
      ∃ sel : Fin U.n.toNat → Fin C.n.toNat,
        (∀ j, (U.key.row j, U.val.row j) = (C.key.row (sel j), C.val.row (sel j))) ∧
        ∀ j j' : Fin U.n.toNat, j.1 < j'.1 → lexLe (ascKeys C.n es) (sel j) (sel j') = true ∧
          seenKey C.n es (sel j) ≠ seenKey C.n es (sel j') :=
  (select_ok (κ := fun _ s => ¬s) diff_keep h).2

/-- **`R.le S` answers `R ⊑ S`**: `R.diff S` has no row iff every pair of `R` is one of `S` (`diff_holds`). -/
theorem le_holds {R S : Tab k v} {r : Bool} (h : R.le S = .ok r) : r = true ↔ ∀ a b, R.Holds a b → S.Holds a b := by
  unfold Tab.le at h
  cases hd : R.diff S with
  | error s => simp [hd, Functor.map, Except.map] at h
  | ok D =>
    simp only [hd, Functor.map, Except.map, Except.ok.injEq] at h
    subst h
    have hD := diff_holds hd
    rw [beq_iff_eq, ← USize.toNat_inj, USize.toNat_zero]
    constructor
    · intro h0 a b hR; refine Classical.byContradiction fun hS => ?_
      obtain ⟨i, -⟩ := (hD a b).2 ⟨hR, hS⟩
      exact absurd i.2 (by omega)
    · intro hall
      refine Classical.byContradiction fun hn => ?_
      have hpos : 0 < D.n.toNat := by omega
      obtain ⟨hR, hS⟩ := (hD (D.key.row ⟨0, hpos⟩) (D.val.row ⟨0, hpos⟩)).1 ⟨⟨0, hpos⟩, rfl, rfl⟩
      exact hS (hall _ _ hR)

end Tab

/-! ## Checks on `foR` tables -/

section Checks


private def T₁ : List (Int64 × Int64) := [(3, 1), (1, 2), (3, 1), (-1, 2), (1, 2), (2, 7), (-5, -5), (0, 0)]
private def T₂ : List (Int64 × Int64) := [(-2, 9), (-2, 9), (1, 2), (7, -3), (-5, -5), (3, 1)]
private def T₃ : List (Int64 × Int64) := [(0, 0), (9, 9)]

#guard ((tab T₁).union (tab T₂)).toOption.map Tab.toList ==
  some [(-5, -5), (-2, 9), (-1, 2), (0, 0), (1, 2), (2, 7), (3, 1), (7, -3)]
#guard ((tab T₁).inter (tab T₂)).toOption.map Tab.toList == some [(-5, -5), (1, 2), (3, 1)]
#guard ((tab T₁).diff (tab T₂)).toOption.map Tab.toList == some [(-1, 2), (0, 0), (2, 7)]
#guard ((tab T₂).diff (tab T₁)).toOption.map Tab.toList == some [(-2, 9), (7, -3)]
#guard ((tab []).inter (tab T₁)).toOption.map Tab.toList == some []
#guard ((tab T₁).diff (tab [])).toOption.map Tab.toList == some [(-5, -5), (-1, 2), (0, 0), (1, 2), (2, 7), (3, 1)]
#guard ((tab T₁).le (tab T₁)).toOption == some true
#guard ((tab T₁).le (tab T₂)).toOption == some false
#guard ((tab []).le (tab [])).toOption == some true
/-- The five-kernel `∪`, `∩`, `−`, `⊑` of `R` and `S`, each answering `.ok`, against their denotations on the rows of
`R` and `S` as sets, each row once. -/
private def setOk {k v : Obj} [BEq k.El] [BEq v.El] (R S : Tab k v) : Bool :=
  let r := R.toList; let s := S.toList
  let is (x : Except String (Tab k v)) (sp : List (k.El × v.El)) := match x with
    | .ok T => let a := T.toList; let b := sp.eraseDups; a.length == b.length && a.all b.contains && b.all a.contains
    | .error _ => false
  is (R.union S) (r ++ s) && is (R.inter S) (r.filter s.contains) && is (R.diff S) (r.filter (!s.contains ·)) &&
  (R.le S).toOption == some (r.all s.contains)

-- both orders of every pair of tables
#guard [T₁, T₂, T₃, []].all fun ps => [T₁, T₂, T₃, []].all fun qs => setOk (tab ps) (tab qs)

/-- Cells over the payload `9 5 1 5`, the second part of each pair being shifted past `arrPay` by `Vals.concat`:
`[5]` and `[5,1]` (in `arrCells` too, from other ranges), the empty cell, `[1,5]`, and `[5]` from `[-4,2)` clamped. -/
private def arrCells₂ : List (Int64 × Int64 × Int64) := [(1, 2, 1), (1, 3, 7), (0, 0, 2), (2, 4, 1), (3, 4, 5), (-4, 2, 9)]
private def arrPay₂ : List Int64 := [9, 5, 1, 5]

-- `arr` sides as the key and as the value: cells over different payloads, a side of no payload rows, a table of no
-- rows; tuple elements (`arr (long × long)`) and nested arrays (`arr (arr long)`)
#guard let As := [arrTab arrCells arrPay, arrTab arrCells₂ arrPay₂, arrTab [(0, 0, 1), (3, 1, 2)] [], arrTab [] arrPay]
  As.all fun R => As.all fun S => setOk R S && setOk (Tab.mk R.n R.val R.key) (Tab.mk S.n S.val S.key)
#guard let P (cs : List (Int64 × Int64 × Int64)) (ps qs : List Int64) (h : qs.length = ps.length) :
    Tab (.arr (.prod .long .long)) .long := arrOn cs (B := .prod .long .long) (Alg.col ps, h ▸ Alg.col qs)
  let As := [P arrCells arrPay [0, 1, 0, 0, 2] rfl, P arrCells₂ arrPay₂ [0, 1, 1, 1] rfl, P [] [] [] rfl]
  As.all fun R => As.all fun S => setOk R S
#guard let As := [arrOn arrCells (arrTab arrCells₂ arrPay₂).key, arrOn arrCells₂ (arrTab arrCells arrPay).key,
    arrOn [(0, 2, 1)] (arrTab [] arrPay).key]
  As.all fun R => As.all fun S => setOk R S && setOk (Tab.mk R.n R.val R.key) (Tab.mk S.n S.val S.key)

/-- Sum rows `(tag, position, value)`: left payload positions holding one value, a clamped position `5`. -/
private def sumRows₁ : List (Bool × Int64 × Int64) :=
  [(false, 0, 1), (true, 1, 2), (false, 2, 1), (false, 1, 1), (true, 0, 2), (true, 1, 2), (false, 5, 3)]
private def sumRows₂ : List (Bool × Int64 × Int64) := [(true, 0, 2), (false, 1, 1), (false, 0, 9), (true, 1, 3)]

-- `sum` sides as the key and as the value, with long and with `arr` summands
#guard let Ss := [sumTab sumRows₁ [5, 7, 5] [9, 4], sumTab sumRows₂ [7, 5] [9, 8]]
  Ss.all fun R => Ss.all fun S => setOk R S && setOk (Tab.mk R.n R.val R.key) (Tab.mk S.n S.val S.key)
#guard let Ss := [sumOn sumRows₁ (arrTab arrCells arrPay).key (b := .long) (Alg.col [9, 4]),
    sumOn sumRows₂ (arrTab arrCells₂ arrPay₂).key (b := .long) (Alg.col [9, 8])]
  Ss.all fun R => Ss.all fun S => setOk R S && setOk (Tab.mk R.n R.val R.key) (Tab.mk S.n S.val S.key)
-- an all-`inl` and an all-`inr` side: each summand is empty on one side, where no row is tagged into it
#guard let Ss := [sumTab [(false, 0, 1), (false, 1, 2), (false, 0, 1)] [5, 7] [], sumTab [(true, 1, 3), (true, 0, 1)] [] [9, 4],
    sumTab [(true, 0, 1)] [] [5]]
  Ss.all fun R => Ss.all fun S => setOk R S && setOk (Tab.mk R.n R.val R.key) (Tab.mk S.n S.val S.key)
-- a row tagged into a summand empty on its side reads `Obj.dflt`, which no payload row holds: the error
#guard (sumTab [(false, 0, 1)] [] [9]).union (sumTab [(false, 0, 1)] [5] []) matches .error _

end Checks

end Rel
