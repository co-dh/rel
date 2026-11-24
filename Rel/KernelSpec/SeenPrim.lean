module

public import Rel.KernelSpec.KSeen
public import Rel.KernelSpec.Where
public import Rel.KernelSpec.Scan
public import Rel.KernelSpec.Scatter

-- exposed: every def body is a spec a downstream `rfl`/`decide`/`simp` may unfold (PLAN W.8)
@[expose] public section

/-! `seen` as a composition of the two primitives `scan` and `scatter` (design §4: "未写成 `scan` / `scatter` 的复合").
Rows in `lexLe` order, `key i` a row's codes across the columns `ks` (words, as `kseen` reads them), column `c`:
- `d[i] = [i = 0 ∨ key i ≠ key (i−1)]`: per column a `scan` map `.ne` of `c` and itself shifted one row down
  (`scatter` of `c` at the indices `1 … n−1`), the columns and the head row `[i = 0]` (one `scatter`) joined by `.or`;
- `p = prefix sum of d`: `scan .add`, one segment, and `g = p − 1` the groups, `k` the last row of `p`;
- `first = where(d)`: `whereCol`'s steps on `p`: destinations `p − d`, `scatter .last` of the positions, the first `k` cells.
The models are the words `kscan` and `kscatter` compute (`kscanRow`, `scatterWords`); no kernel and no `Op` is added. -/

namespace Rel.Verify
open Rel.Kernel Ext.Enc

-- noncomputable: these are models for proofs, never run; no IR means listban does not walk their `List`s

/-- `kscan`'s row fold over `n` rows at `rev = false`, as words: the body of `kscan`. -/
noncomputable def scanW (op : Op) (n : Nat) (seg seed : Array UInt64) (xs : List (Array UInt64)) : Except String (Array UInt64) :=
  (List.range n).foldlM (kscanRow op seg seed xs) #[]

/-- The indices `1 … n−1`: row `k` of a column `scatter`ed there lands at row `k + 1`, the column shifted one row down. -/
def shiftIx (n : Nat) : Array UInt64 := (Array.range (n - 1)).map fun k => UInt64.ofNat (k + 1)

/-- The index `0` (none at `n = 0`): `scatter` of `1` there into `n` cells of `0` is `[i = 0]`. -/
def headIx (n : Nat) : Array UInt64 := (Array.range (min n 1)).map UInt64.ofNat

/-- `[i = 0]` on `n` rows. -/
def headCol (n : Nat) : Except String (Array UInt64) := scatterWords .last (headIx n) (Array.replicate n 1) n 0

/-- `[c[i] ≠ c[i−1]]` on `n` rows (row 0 reads the shift's fill `0`): `scan` map `.ne` of `c` and `c` shifted down. -/
noncomputable def newCol (n : Nat) (c : Array UInt64) : Except String (Array UInt64) := do
  scanW .ne n (Array.replicate n 1) c [← scatterWords .last (shiftIx n) c n 0]

/-- **`seen` over code columns `ks` of `n` rows in `lexLe` order, as `scan` and `scatter`**: the number `k` of groups,
each row's group `g` and each group's first row, as words. -/
noncomputable def seenPrims (n : Nat) (ks : List (Array UInt64)) : Except String (Nat × Array UInt64 × Array UInt64) := do
  let one := Array.replicate n (1 : UInt64)
  let zero := Array.replicate n (0 : UInt64)
  let d ← scanW .or n one (← headCol n) (← ks.mapM (newCol n))
  let p ← scanW .add n zero zero [d]
  let K := (p.back?.getD 0).toNat
  let w ← scatterWords .last (← scanW .sub n one p [d]) ((Array.range n).map UInt64.ofNat) (K + 1) 0
  pure (K, ← scanW .sub n one p [one], w.extract 0 K)

/-! ## The models, row by row -/

theorem foldlM_eval_ok {op : Op} {f : UInt64 → UInt64 → UInt64} (hf : ∀ a x, op.eval a x = .ok (f a x))
    (xs : List (Array UInt64)) (i : Nat) (a : UInt64) :
    xs.foldlM (fun a x => op.eval a (x[i]?.getD 0)) a = .ok (xs.foldl (fun a x => f a (x[i]?.getD 0)) a) := by
  induction xs generalizing a with
  | nil => rfl
  | cons x xs ih => simp only [List.foldlM_cons]; rw [hf]; exact ih _

/-- A total op's `scanW` answers `n` words, row `i` the fold of `f` over the other columns' row `i` from the carry. -/
theorem scanW_spec {op : Op} {f : UInt64 → UInt64 → UInt64} (hf : ∀ a x, op.eval a x = .ok (f a x)) (n : Nat)
    (seg seed : Array UInt64) (xs : List (Array UInt64)) :
    ∃ out, scanW op n seg seed xs = .ok out ∧ out.size = n ∧ ∀ i < n, out[i]?.getD 0 =
      xs.foldl (fun a x => f a (x[i]?.getD 0)) (if 0 < i ∧ seg[i]?.getD 0 = 0 then out[i - 1]?.getD 0 else seed[i]?.getD 0) := by
  have hex : ∀ m, ∃ out, scanW op m seg seed xs = .ok out := by
    intro m
    induction m with
    | zero => exact ⟨#[], rfl⟩
    | succ m ih =>
      obtain ⟨o, ho⟩ := ih
      refine ⟨o.push (xs.foldl (fun a x => f a (x[m]?.getD 0))
        (if 0 < m ∧ seg[m]?.getD 0 = 0 then o[m - 1]?.getD 0 else seed[m]?.getD 0)), ?_⟩
      rw [scanW] at ho ⊢
      rw [List.range_succ, List.foldlM_append, ho]
      simp only [bind, Except.bind, List.foldlM_cons, List.foldlM_nil, kscanRow, foldlM_eval_ok hf, Functor.map, Except.map]
      rfl
  obtain ⟨out, ho⟩ := hex n
  obtain ⟨hs, hi⟩ := foldlM_kscanRow op seg seed xs n out ho
  refine ⟨out, ho, hs, fun i hn => ?_⟩
  have := hi i (by omega)
  rw [foldlM_eval_ok hf] at this
  rw [Array.getElem?_eq_getElem (by omega), Option.getD_some]
  exact (Except.ok.inj this).symm

theorem u01 {a : UInt64} (h : a ≤ 1) : a = 0 ∨ a = 1 := by
  have := UInt64.le_iff_toNat_le.1 h
  rw [show (1 : UInt64).toNat = 1 from rfl] at this
  rcases Nat.lt_or_ge a.toNat 1 with h0 | h1
  · left; exact UInt64.toNat_inj.1 (by simpa using (by omega : a.toNat = 0))
  · right; exact UInt64.toNat_inj.1 (by simpa using (by omega : a.toNat = 1))

/-- `c` shifted one row down by `scatter`: row `i ≥ 1` holds `c[i−1]`. -/
theorem shift_ok {n : Nat} (hn : n < 2 ^ 64) (c : Array UInt64) :
    ∃ s, scatterWords .last (shiftIx n) c n 0 = .ok s ∧ s.size = n ∧
      ∀ i, 0 < i → i < n → s[i]?.getD 0 = c[i - 1]?.getD 0 := by
  have hix : ∀ k, k < (shiftIx n).size → ixAt (shiftIx n) k = k + 1 := fun k hk => by
    simp only [shiftIx, Array.size_map, Array.size_range] at hk
    simp [ixAt, shiftIx, hk, UInt64.toNat_ofNat, Nat.mod_eq_of_lt (show k + 1 < 2 ^ 64 by omega)]
  have hsz : (shiftIx n).size = n - 1 := by simp [shiftIx]
  obtain ⟨hex, hsp⟩ := scatterWords_spec (shiftIx n) c n 0
  obtain ⟨s, hs⟩ := hex.2 fun k hk => by rw [hix k hk]; omega
  refine ⟨s, hs, (hsp s hs).1, fun i hi hin => ?_⟩
  have := (hsp s hs).2.2 (i - 1) (by omega) fun k' h1 h2 => by rw [hix k' h2, hix _ (by omega)]; omega
  rw [hix _ (by omega), show i - 1 + 1 = i by omega] at this
  rw [this]; rfl

/-- `[i = 0]` by `scatter`. -/
theorem head_ok {n : Nat} (hn : n < 2 ^ 64) :
    ∃ h, headCol n = .ok h ∧ h.size = n ∧ ∀ i < n, h[i]?.getD 0 = if i = 0 then 1 else 0 := by
  have hix : ∀ k, k < (headIx n).size → ixAt (headIx n) k = k := fun k hk => by
    simp only [headIx, Array.size_map, Array.size_range] at hk
    simp [ixAt, headIx, hk, Nat.mod_eq_of_lt (show k < 2 ^ 64 by omega)]
  have hsz : (headIx n).size = min n 1 := by simp [headIx]
  obtain ⟨hex, hsp⟩ := scatterWords_spec (headIx n) (Array.replicate n 1) n 0
  obtain ⟨h, hh⟩ := hex.2 fun k hk => by rw [hix k hk]; omega
  refine ⟨h, hh, (hsp h hh).1, fun i hi => ?_⟩
  by_cases h0 : i = 0
  · subst h0
    have := (hsp h hh).2.2 0 (by omega) fun k' h1 h2 => by omega
    rw [hix _ (by omega)] at this
    simp [this, hi]
  · have := (hsp h hh).2.1 i hi fun k hk => by rw [hix k hk]; omega
    simp [this, h0]

theorem newCol_ok {n : Nat} (hn : n < 2 ^ 64) (c : Array UInt64) :
    ∃ dc, newCol n c = .ok dc ∧ dc.size = n ∧ ∀ i < n, dc[i]?.getD 0 ≤ 1 ∧
      (0 < i → (dc[i]?.getD 0 = 1 ↔ c[i]?.getD 0 ≠ c[i - 1]?.getD 0)) := by
  obtain ⟨s, hs, hsz, hsh⟩ := shift_ok hn c
  obtain ⟨dc, hd, hdz, hdi⟩ := scanW_spec (op := .ne) (f := fun a x => Op.w (a != x)) (fun _ _ => rfl) n
    (Array.replicate n 1) c [s]
  refine ⟨dc, by simp only [newCol, hs, bind, Except.bind]; exact hd, hdz, fun i hi => ?_⟩
  have e := hdi i hi
  have h1 : (Array.replicate n (1 : UInt64))[i]?.getD 0 = 1 := by simp [hi]
  simp only [List.foldl_cons, List.foldl_nil, h1, show ¬ (1 : UInt64) = 0 by decide, and_false, if_false] at e
  rw [e]
  refine ⟨by unfold Op.w; split <;> decide, fun h0 => ?_⟩
  rw [hsh i h0 hi]
  unfold Op.w
  by_cases hne : c[i]?.getD 0 = c[i - 1]?.getD 0 <;> simp [hne]

/-! ## The runs: `d`, `p`, `g`, `first` -/

/-- A row's key: its codes across the columns, as `kseen` reads them. -/
abbrev keyAt (ks : List (Array UInt64)) (i : Nat) : List UInt64 := ks.map (·[i]?.getD 0)

/-- Row `i` starts a run: it is the first row or its key differs from the row before. -/
def isNew (ks : List (Array UInt64)) (i : Nat) : Bool := i == 0 || keyAt ks i != keyAt ks (i - 1)

/-- The runs started below row `i`. -/
noncomputable def cnt (ks : List (Array UInt64)) (i : Nat) : Nat := ((List.range i).filter (isNew ks)).length

theorem cnt_succ (ks : List (Array UInt64)) (i : Nat) : cnt ks (i + 1) = cnt ks i + if isNew ks i then 1 else 0 := by
  unfold cnt; rw [List.range_succ, List.filter_append]; cases hb : isNew ks i <;> simp [hb]

theorem cnt_mono (ks : List (Array UInt64)) {i j : Nat} (h : i ≤ j) : cnt ks i ≤ cnt ks j := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  induction d with
  | zero => exact Nat.le_refl _
  | succ d ih => rw [← Nat.add_assoc, cnt_succ]; have := ih (by omega); omega

theorem cnt_le (ks : List (Array UInt64)) (i : Nat) : cnt ks i ≤ i := by
  unfold cnt; simpa using List.length_filter_le (isNew ks) (List.range i)

/-- Each `newCol` of `ks`, as `newCol_ok` states it. -/
inductive NewRows (n : Nat) : List (Array UInt64) → List (Array UInt64) → Prop
  | nil : NewRows n [] []
  | cons {c dc : Array UInt64} {ks ds : List (Array UInt64)} :
    (∀ i < n, dc[i]?.getD 0 ≤ 1 ∧ (0 < i → (dc[i]?.getD 0 = 1 ↔ c[i]?.getD 0 ≠ c[i - 1]?.getD 0))) →
      NewRows n ks ds → NewRows n (c :: ks) (dc :: ds)

theorem or01 {a b : UInt64} (ha : a ≤ 1) (hb : b ≤ 1) :
    a ||| b ≤ 1 ∧ (a ||| b = 1 ↔ a = 1 ∨ b = 1) := by
  rcases u01 ha with rfl | rfl <;> rcases u01 hb with rfl | rfl <;> decide

/-- Folding `.or` over the columns' `newCol`s from `a ≤ 1`: still `≤ 1`, kept at `1`, and at a row `i > 0` it is `1`
exactly when `a = 1` or some column differs from the row before. -/
theorem orFold {n : Nat} {ks ds : List (Array UInt64)}
    (hF : NewRows n ks ds) {i : Nat} (hi : i < n) :
    ∀ a : UInt64, a ≤ 1 → ds.foldl (fun a x => a ||| x[i]?.getD 0) a ≤ 1 ∧
      (a = 1 → ds.foldl (fun a x => a ||| x[i]?.getD 0) a = 1) ∧
      (0 < i → (ds.foldl (fun a x => a ||| x[i]?.getD 0) a = 1 ↔ a = 1 ∨ keyAt ks i ≠ keyAt ks (i - 1))) := by
  induction hF with
  | nil => intro a ha; exact ⟨ha, id, fun _ => by simp⟩
  | @cons c dc ks ds hc _ ih =>
    intro a ha
    obtain ⟨hb, hb1⟩ := hc i hi
    obtain ⟨h1, h2⟩ := or01 ha hb
    obtain ⟨r1, r2, r3⟩ := ih (a ||| dc[i]?.getD 0) h1
    refine ⟨r1, fun e => r2 (h2.2 (.inl e)), fun hp => ?_⟩
    rw [List.foldl_cons, r3 hp, h2, hb1 hp]
    simp only [keyAt, List.map_cons, ne_eq, List.cons.injEq, not_and]
    constructor
    · rintro ((h | h) | h)
      · exact .inl h
      · exact .inr (by by_cases e : c[i]?.getD 0 = c[i - 1]?.getD 0 <;> simp_all)
      · exact .inr (by by_cases e : c[i]?.getD 0 = c[i - 1]?.getD 0 <;> simp_all)
    · rintro (h | h)
      · exact .inl (.inl h)
      · by_cases e : c[i]?.getD 0 = c[i - 1]?.getD 0
        · exact .inr (by simpa [e] using h)
        · exact .inl (.inr e)

theorem newCols_ok {n : Nat} (hn : n < 2 ^ 64) (ks : List (Array UInt64)) :
    ∃ ds, ks.mapM (newCol n) = .ok ds ∧ NewRows n ks ds := by
  induction ks with
  | nil => exact ⟨[], rfl, .nil⟩
  | cons c ks ih =>
    obtain ⟨dc, hd, -, hdi⟩ := newCol_ok hn c
    obtain ⟨ds, hds, hF⟩ := ih
    exact ⟨dc :: ds, by simp only [List.mapM_cons, hd, hds, bind, Except.bind, pure, Except.pure], .cons hdi hF⟩

/-- `d[i] = [i = 0 ∨ key i ≠ key (i−1)]`. -/
theorem d_ok {n : Nat} (hn : n < 2 ^ 64) (ks : List (Array UInt64)) :
    ∃ h ds d, headCol n = .ok h ∧ ks.mapM (newCol n) = .ok ds ∧ scanW .or n (Array.replicate n 1) h ds = .ok d ∧
      d.size = n ∧ ∀ i < n, d[i]?.getD 0 = if isNew ks i then 1 else 0 := by
  obtain ⟨h, hh, -, hhi⟩ := head_ok hn
  obtain ⟨ds, hds, hF⟩ := newCols_ok hn ks
  obtain ⟨d, hd, hdz, hdi⟩ := scanW_spec (op := .or) (f := fun a x => a ||| x) (fun _ _ => rfl) n
    (Array.replicate n 1) h ds
  refine ⟨h, ds, d, hh, hds, hd, hdz, fun i hi => ?_⟩
  have e := hdi i hi
  have h1 : (Array.replicate n (1 : UInt64))[i]?.getD 0 = 1 := by simp [hi]
  simp only [h1, show ¬ (1 : UInt64) = 0 by decide, and_false, if_false] at e
  rw [e]
  by_cases h0 : i = 0
  · subst h0
    have := (orFold hF hi 1 (by decide)).2.1 rfl
    simp [hhi 0 hi, this, isNew]
  · obtain ⟨hle, -, hiff⟩ := orFold hF hi 0 (by decide)
    have hiff := hiff (by omega)
    have h0' : h[i]?.getD 0 = 0 := by simp [hhi i hi, h0]
    have h0b : (i == 0) = false := by simpa using h0
    have hn : isNew ks i = decide (keyAt ks i ≠ keyAt ks (i - 1)) := by
      simp only [isNew, h0b, Bool.false_or]; rw [Bool.eq_iff_iff]; simp only [bne_iff_ne, decide_eq_true_eq]
    rw [h0', hn]
    rcases u01 hle with hr | hr
    · rw [hr] at hiff ⊢
      have : ¬ keyAt ks i ≠ keyAt ks (i - 1) := fun hd => absurd (hiff.2 (.inr hd)) (by decide)
      simp [this]
    · rw [hr] at hiff ⊢
      rcases hiff.1 rfl with h | h
      · exact absurd h (by decide)
      · simp [h]

theorem p_ok {n : Nat} {ks : List (Array UInt64)} {d : Array UInt64}
    (hd : ∀ i < n, d[i]?.getD 0 = if isNew ks i then 1 else 0) :
    ∃ p, scanW .add n (Array.replicate n 0) (Array.replicate n 0) [d] = .ok p ∧ p.size = n ∧
      ∀ i < n, p[i]?.getD 0 = UInt64.ofNat (cnt ks (i + 1)) := by
  obtain ⟨p, hp, hpz, hpi⟩ := scanW_spec (op := .add) (f := fun a x => a + x) (fun _ _ => rfl) n
    (Array.replicate n 0) (Array.replicate n 0) [d]
  refine ⟨p, hp, hpz, fun i => ?_⟩
  induction i using Nat.strongRecOn with
  | _ i ih =>
    intro hi
    have e := hpi i hi
    have z : (Array.replicate n (0 : UInt64))[i]?.getD 0 = 0 := by simp [hi]
    simp only [List.foldl_cons, List.foldl_nil, z, and_true] at e
    rw [e, hd i hi, cnt_succ]
    rcases Nat.eq_zero_or_pos i with rfl | hpos
    · simp [isNew, cnt]
    · rw [if_pos hpos, ih (i - 1) (by omega) (by omega), show i - 1 + 1 = i by omega]
      split <;> simp [UInt64.ofNat_add]

theorem g_ok {n : Nat} {p : Array UInt64} :
    ∃ g, scanW .sub n (Array.replicate n 1) p [Array.replicate n 1] = .ok g ∧ g.size = n ∧
      ∀ i < n, g[i]?.getD 0 = p[i]?.getD 0 - 1 := by
  obtain ⟨g, hg, hgz, hgi⟩ := scanW_spec (op := .sub) (f := fun a x => a - x) (fun _ _ => rfl) n
    (Array.replicate n 1) p [Array.replicate n 1]
  refine ⟨g, hg, hgz, fun i hi => ?_⟩
  simp [hgi i hi, hi]

theorem dst_ok {n : Nat} {p d : Array UInt64} :
    ∃ q, scanW .sub n (Array.replicate n 1) p [d] = .ok q ∧ q.size = n ∧
      ∀ i < n, q[i]?.getD 0 = p[i]?.getD 0 - d[i]?.getD 0 := by
  obtain ⟨q, hq, hqz, hqi⟩ := scanW_spec (op := .sub) (f := fun a x => a - x) (fun _ _ => rfl) n
    (Array.replicate n 1) p [d]
  refine ⟨q, hq, hqz, fun i hi => ?_⟩
  simp [hqi i hi, hi]

/-- The `i`th kept index (`f`) of `range m` for a kept `i`, at the number of kept indices below it. -/
theorem filter_range_rank (f : Nat → Bool) : ∀ m i, i < m → f i = true →
    ((List.range m).filter f)[((List.range i).filter f).length]? = some i
  | 0, i, hi, _ => absurd hi (Nat.not_lt_zero _)
  | m + 1, i, hi, hf => by
    rw [List.range_succ, List.filter_append]
    by_cases him : i = m
    · subst him
      rw [List.getElem?_append_right (Nat.le_refl _)]
      simp [hf]
    · rw [List.getElem?_append_left, filter_range_rank f m i (by omega) hf]
      obtain ⟨h, _⟩ := List.getElem?_eq_some_iff.1 (filter_range_rank f m i (by omega) hf)
      exact h

theorem u64_ofNat_sub_one {c : Nat} (hc : 1 ≤ c) : UInt64.ofNat c - 1 = UInt64.ofNat (c - 1) := by
  obtain ⟨c, rfl⟩ : ∃ c', c = c' + 1 := ⟨c - 1, by omega⟩
  simp [UInt64.ofNat_add]

/-- **`seenPrims` is `seen`'s answer** on rows in `lexLe` order (`kseen_sorted`): `k = fs.length`, each row's group and
each group's first row, `fs` and `groups` as `kseen`'s body states them. -/
theorem seenPrims_eq {n : Nat} (hn : n < 2 ^ 64) (ks : List (Array UInt64))
    (hs : ∀ i, i + 1 < n → lexLe ks i (i + 1) = true) :
    seenPrims n ks = .ok ((Order.firstsBy n (keyAt ks)).length,
      Array.ofFn (n := n) fun i => (Order.groupIn (Order.firstsBy n (keyAt ks)) (keyAt ks) i.1).toUInt64,
      ((Order.firstsBy n (keyAt ks)).map Nat.toUInt64).toArray) := by
  simp only [groupIn_firstsBy]
  simp only [firstsBy_eq]
  have hrun := lexLe_runs ks hs
  have hF : firstsOf (keyAt ks) n = (List.range n).filter (isNew ks) := by
    unfold firstsOf
    apply List.filter_congr
    intro p hp
    have hp' := List.mem_range.1 hp
    have h1 := firsts_runs (g := keyAt ks) (m := n) hrun p
    have h2 : p ∈ firstsOf (keyAt ks) n ↔ ((List.range p).all fun j => !decide (keyAt ks j = keyAt ks p)) = true := by
      unfold firstsOf; simp [List.mem_filter, hp]
    rw [Bool.eq_iff_iff, ← h2, h1]
    rcases Nat.eq_zero_or_pos p with rfl | hpos
    · exact ⟨fun _ => by simp [isNew], fun _ => ⟨hp', fun q hq => absurd hq (by omega)⟩⟩
    · have hb : isNew ks p = true ↔ keyAt ks p ≠ keyAt ks (p - 1) := by
        have : (p == 0) = false := by simpa using (by omega : p ≠ 0)
        simp only [isNew, this, Bool.false_or, bne_iff_ne]
      refine ⟨fun ⟨_, h⟩ => hb.2 fun e => h (p - 1) (by omega) e.symm, fun hnew => ⟨hp', fun q hq e => ?_⟩⟩
      obtain rfl : q = p - 1 := by omega
      exact hb.1 hnew e.symm
  have hlen : (firstsOf (keyAt ks) n).length = cnt ks n := by rw [hF]; rfl
  have hget : ∀ i : Nat, (firstsOf (keyAt ks) n)[i]? = ((List.range n).filter (isNew ks))[i]? := fun i => by rw [hF]
  have hrank : ∀ i < n, isNew ks i = true → (firstsOf (keyAt ks) n)[cnt ks i]? = some i := fun i hi hn' => by
    rw [hget]; exact filter_range_rank _ n i hi hn'
  have hnodup : (firstsOf (keyAt ks) n).Nodup := ((firsts_spec (keyAt ks) n).1).imp Nat.ne_of_lt
  have hrank' : ∀ r i : Nat, (firstsOf (keyAt ks) n)[r]? = some i → i < n ∧ isNew ks i = true ∧ cnt ks i = r := by
    intro r i h
    have hm : i ∈ firstsOf (keyAt ks) n := List.mem_of_getElem? h
    rw [hF, List.mem_filter, List.mem_range] at hm
    refine ⟨hm.1, hm.2, ?_⟩
    have := hrank i hm.1 hm.2
    exact (List.getElem?_inj (List.getElem?_eq_some_iff.1 h).1 hnodup (h.trans this.symm)).symm
  have hG : ∀ i < n, groupOf (keyAt ks) n i = cnt ks (i + 1) - 1 := by
    intro i
    induction i using Nat.strongRecOn with
    | _ i ih =>
      intro hi
      by_cases hnew : isNew ks i = true
      · have hr := hrank i hi hnew
        obtain ⟨hj, hFi⟩ := List.getElem?_eq_some_iff.1 hr
        have := (firsts_spec (keyAt ks) n).2.2.2.1 (cnt ks i) hj
        rw [hFi] at this
        rw [this, cnt_succ, if_pos hnew]; rfl
      · have h0 : i ≠ 0 := fun e => hnew (by simp [isNew, e])
        have hk : keyAt ks i = keyAt ks (i - 1) := by simpa [isNew, h0] using hnew
        rw [(firsts_spec (keyAt ks) n).2.2.1 i hi (i - 1) (by omega) |>.2 hk, ih (i - 1) (by omega) (by omega),
          show i - 1 + 1 = i by omega, cnt_succ, if_neg hnew]
        rfl
  -- the pipeline
  obtain ⟨h, ds, d, hh, hds, hd, hdz, hdi⟩ := d_ok hn ks
  obtain ⟨p, hp, hpz, hpi⟩ := p_ok hdi
  obtain ⟨g, hg, hgz, hgi⟩ := g_ok (n := n) (p := p)
  obtain ⟨q, hq, hqz, hqi⟩ := dst_ok (n := n) (p := p) (d := d)
  have hcn : cnt ks n < 2 ^ 64 := Nat.lt_of_le_of_lt (cnt_le ks n) hn
  have hK : (p.back?.getD 0).toNat = cnt ks n := by
    rcases Nat.eq_zero_or_pos n with rfl | hpos
    · simp [Array.back?_eq_getElem?, show p.size = 0 from hpz, cnt]
    · rw [Array.back?_eq_getElem?, hpz, hpi _ (by omega), show n - 1 + 1 = n by omega, UInt64.toNat_ofNat',
        Nat.mod_eq_of_lt hcn]
  have hqv : ∀ i < n, q[i]?.getD 0 = UInt64.ofNat (cnt ks i) := fun i hi => by
    rw [hqi i hi, hpi i hi, hdi i hi, cnt_succ]
    split <;> simp [UInt64.ofNat_add]
  have hqn : ∀ i, i < n → ixAt q i = cnt ks i := fun i hi => by
    simp only [ixAt, hqv i hi, UInt64.toNat_ofNat']
    exact Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (cnt_le ks i) (by omega))
  obtain ⟨hex, hsp⟩ := scatterWords_spec q ((Array.range n).map UInt64.ofNat) (cnt ks n + 1) 0
  obtain ⟨w, hw⟩ := hex.2 fun k hk => by
    rw [hqz] at hk; rw [hqn k hk]; have := cnt_mono ks (show k ≤ n by omega); omega
  have hwsz := (hsp w hw).1
  have hwr : ∀ i < n, isNew ks i = true → w[cnt ks i]? = some (UInt64.ofNat i) := fun i hi hnew => by
    have := (hsp w hw).2.2 i (by rw [hqz]; exact hi) fun k' h1 h2 => by
      rw [hqz] at h2; rw [hqn k' h2, hqn i hi]
      have := cnt_mono ks (show i + 1 ≤ k' by omega); rw [cnt_succ, if_pos hnew] at this; omega
    rw [hqn i hi] at this
    simpa [hi] using this
  simp only [seenPrims, hh, hds, hd, hp, hq, hw, hg, hK, bind, Except.bind, pure, Except.pure]
  congr 1
  refine Prod.ext hlen.symm (Prod.ext ?_ ?_)
  · apply Array.ext
    · simp [hgz]
    · intro i h1 h2
      simp only [Array.getElem_ofFn]
      have hi : i < n := by simpa [hgz] using h1
      have := hgi i hi
      rw [Array.getElem?_eq_getElem h1, Option.getD_some] at this
      rw [this, hpi i hi, hG i hi]
      have h11 : cnt ks 1 = 1 := by simp [cnt, isNew]
      exact u64_ofNat_sub_one (by have := cnt_mono ks (show 1 ≤ i + 1 by omega); omega)
  · have hsz : (w.extract 0 (cnt ks n)).size = cnt ks n := by simp [hwsz]
    apply Array.ext
    · simp [hsz, hlen]
    · intro r h1 h2
      have hlt : r < (firstsOf (keyAt ks) n).length := by rw [hlen]; simpa [hsz] using h1
      obtain ⟨hin, hnw, hc⟩ := hrank' r _ (List.getElem?_eq_getElem hlt)
      have := hwr _ hin hnw
      rw [hc, Array.getElem?_eq_getElem (by omega)] at this
      simp only [Array.getElem_extract, List.getElem_toArray, List.getElem_map, Nat.zero_add]
      exact Option.some.inj this

/-- **`kseen` is `seenPrims`** through `wordsFoR`: where `kseen` answers, its count is `seenPrims`' and its two columns
are `wordsFoR` of `seenPrims`' words, over `kasc`'s codes `ascKeys` (`kseen_ok`, `kseen_sorted`). So `seen` is a
composition of `scan` and `scatter`. -/
theorem kseen_eq_prims {n : USize} {es : List (AscKey × Enc)} {r : Nat × Enc × Enc} (h : kseen n es = .ok r) :
    ∃ p, seenPrims n.toNat (ascKeys n es) = .ok p ∧ r = (p.1, wordsFoR p.2.1, wordsFoR p.2.2) := by
  obtain ⟨k, g, f⟩ := r
  obtain ⟨hk, hg, hf⟩ := kseen_ok h
  have hn : n.toNat < 2 ^ 64 := by
    have := n.toNat_lt_size
    rcases USize.size_eq with h | h <;> omega
  refine ⟨_, seenPrims_eq hn _ (kseen_sorted h), ?_⟩
  simp only [groupIn_firstsBy]
  simp only [firstsBy_eq]
  exact Prod.ext hk (Prod.ext hg hf)

end Rel.Verify
