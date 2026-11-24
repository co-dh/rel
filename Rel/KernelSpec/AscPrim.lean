module

public import Rel.KernelSpec.Asc
public import Rel.KernelSpec.Scatter
public import Rel.KernelSpec.Scan

-- exposed: every def body is a spec a downstream `rfl`/`decide`/`simp` may unfold (PLAN W.8)
@[expose] public section

/-! `asc` from the two primitives (`doc/rel-architecture.zh.typ` §4: radix sort is per digit a `scan` (histogram,
prefix offsets) then a `scatter`). `countPass` is one stable counting pass of a permutation `p` by the digit column `k`:
the histogram is `scatterWords .add`, the offsets are the prefix sum of it, a row's rank among the equal digits before it
is one segmented prefix sum over `B` one-hot columns (one segment per digit), and `scatterWords .last` writes row `p[r]`
at offset plus rank. `countPass_stable` says the answer is `p` stably sorted by `k`; `ascGrade`'s LSD induction (the sort of
`c :: cs` is the pass by `c` of the sort of `cs`) is built on it. -/

namespace Rel.Kernel

/-- The prefix sums of `x` inside the segments `seg` starts: `kscan .add`'s row fold (`kscanRow`, which `kscan` runs, seed
`0`), so the scan law `foldlM_kscanRow` states it. -/
def scanAdd (seg x : Array UInt64) : Except String (Array UInt64) :=
  (List.range x.size).foldlM (kscanRow .add seg (Array.replicate x.size 0) [x]) #[]

/-- `1` where a row starts the segment of its digit: the `B` digit blocks of `n` rows are `B * n` rows of one scan. -/
def rankSeg (n B : Nat) : Array UInt64 :=
  ((List.range (B * n)).map fun t => if t % n = 0 then (1 : UInt64) else 0).toArray

/-- The `B` one-hot columns of the digits `ds`, one after the other: row `n * e + i` is `1` iff row `i` has digit `e`. -/
def rankCol (ds : Array UInt64) (n B : Nat) : Array UInt64 :=
  ((List.range (B * n)).map fun t => if (ds[t % n]?.getD 0).toNat = t / n then (1 : UInt64) else 0).toArray

/-- The digit of each row of `p` (a gather of the digit column `k` by `p`), one word per position. -/
def digitCol (k : Array UInt64) (p : List Nat) : Array UInt64 := (p.map fun i => k[i]?.getD 0).toArray

/-- The place of each position `r`: `c[e] - h[e]` (digit `e`'s first place, `c` the prefix sums of the histogram `h`) plus
`s[n * e + r] - 1` (the rank among its digit, `s` the rank scan). -/
def placeWords (n : Nat) (ds h c s : Array UInt64) : Array UInt64 :=
  ((List.range n).map fun r =>
    let e := (ds[r]?.getD 0).toNat
    c[e]?.getD 0 - h[e]?.getD 0 + s[n * e + r]?.getD 0 - 1).toArray

/-- One stable counting pass: `p` (row indices) stably sorted by the digit `k[i]` of row `i`, every digit below `B`.
Histogram `h` of the digits; `c` its prefix sums, so `c[e] - h[e]` is digit `e`'s first place; `s[n * e + r]` counts the
rows up to `r` of digit `e`, so a row's place is `c[e] - h[e] + s[n * e + r] - 1`; the row index goes there. A digit
`≥ B` is the `scatterWords` error. The `getD`s read inside the arrays' sizes (`countPass_stable`). -/
def countPass (B : Nat) (k : Array UInt64) (p : List Nat) : Except String (List Nat) := do
  let n := p.length
  let ds := digitCol k p
  let h ← scatterWords .add ds (Array.replicate n 1) B 0
  let c ← scanAdd (Array.replicate B 0) h
  let s ← scanAdd (rankSeg n B) (rankCol ds n B)
  let q ← scatterWords .last (placeWords n ds h c s) (p.map Nat.toUInt64).toArray n 0
  pure (q.toList.map (·.toNat))

/-- The digit of row `i` in the column `k`. -/
def dig (k : Array UInt64) (i : Nat) : Nat := (k[i]?.getD 0).toNat

-- the column `2 0 2 1` has the grade `1 3 0 2`; a second pass by `1 0 1 0` (LSD) gives `1 3 0 2` again, with ties in order
#guard countPass 3 #[2, 0, 2, 1] [0, 1, 2, 3] matches .ok [1, 3, 0, 2]
#guard countPass 2 #[1, 0, 1, 0] [1, 3, 0, 2] matches .ok [1, 3, 0, 2]

end Rel.Kernel

namespace Rel.Verify
open Rel.Kernel

/-! ### Counting on `Nat` -/

/-- How many of the rows `< m` satisfy `P`. -/
def cp (P : Nat → Bool) (m : Nat) : Nat := (List.range m).countP P

theorem cp_succ (P : Nat → Bool) (m : Nat) : cp P (m + 1) = cp P m + if P m then 1 else 0 := by
  unfold cp; rw [List.range_succ, List.countP_append]; cases h : P m <;> simp [h]

theorem cp_mono (P : Nat → Bool) {m n : Nat} (h : m ≤ n) : cp P m ≤ cp P n := by
  induction h with
  | refl => exact Nat.le_refl _
  | step _ ih => show _ ≤ cp P (_ + 1); rw [cp_succ]; split <;> omega

theorem cp_le (P : Nat → Bool) (m : Nat) : cp P m ≤ m := by
  induction m with
  | zero => simp [cp]
  | succ m ih => rw [cp_succ]; split <;> omega

theorem cp_zero (P : Nat → Bool) : cp P 0 = 0 := by simp [cp]

theorem cp_false (m : Nat) : cp (fun _ => false) m = 0 := by
  induction m with
  | zero => exact cp_zero _
  | succ m ih => rw [cp_succ, ih]; simp

section Place
variable (d : Nat → Nat) (n : Nat)

/-- The rows `< n` of digit `e`. -/
def cntD (e : Nat) : Nat := cp (fun s => decide (d s = e)) n

/-- The first place of digit `e`: the rows of the smaller digits. -/
def offD (e : Nat) : Nat := (List.range e).foldl (fun a x => a + cntD d n x) 0

/-- The rows before `r` with `r`'s digit. -/
def rkD (r : Nat) : Nat := cp (fun s => decide (d s = d r)) r

/-- Where the pass puts row `r`. -/
def placeD (r : Nat) : Nat := offD d n (d r) + rkD d r

theorem offD_succ (e : Nat) : offD d n (e + 1) = offD d n e + cntD d n e := by
  simp [offD, List.range_succ, List.foldl_append]

theorem offD_mono {e e' : Nat} (h : e ≤ e') : offD d n e ≤ offD d n e' := by
  induction h with
  | refl => exact Nat.le_refl _
  | step _ ih => show _ ≤ offD d n (_ + 1); rw [offD_succ]; omega

theorem cp_lt_succ (e m : Nat) : cp (fun s => decide (d s < e + 1)) m =
    cp (fun s => decide (d s < e)) m + cp (fun s => decide (d s = e)) m := by
  induction m with
  | zero => simp [cp_zero]
  | succ m ih =>
    rw [cp_succ, cp_succ, cp_succ, ih]
    simp only [decide_eq_true_eq]
    repeat' split
    all_goals omega

theorem offD_eq (e : Nat) : offD d n e = cp (fun s => decide (d s < e)) n := by
  induction e with
  | zero =>
    have : (fun s => decide (d s < 0)) = fun _ => false := by funext s; simp
    rw [this, cp_false]; simp [offD]
  | succ e ih => rw [offD_succ, ih, cp_lt_succ]; rfl

theorem rk_lt_cnt {r : Nat} (hr : r < n) : rkD d r < cntD d n (d r) := by
  have h1 : cp (fun s => decide (d s = d r)) (r + 1) = cp (fun s => decide (d s = d r)) r + 1 := by
    rw [cp_succ]; simp
  have h2 := cp_mono (fun s => decide (d s = d r)) (show r + 1 ≤ n from hr)
  unfold rkD cntD; omega

theorem rk_lt_rk {r s : Nat} (hrs : r < s) (hd : d r = d s) : rkD d r < rkD d s := by
  have h1 : cp (fun x => decide (d x = d r)) (r + 1) = cp (fun x => decide (d x = d r)) r + 1 := by
    rw [cp_succ]; simp
  have h2 := cp_mono (fun x => decide (d x = d r)) (show r + 1 ≤ s from hrs)
  unfold rkD; rw [← hd]; omega

theorem place_lt {r : Nat} (hr : r < n) : placeD d n r < n := by
  have h1 := rk_lt_cnt d n hr
  have h2 := offD_succ d n (d r)
  have h3 := offD_eq d n (d r + 1)
  have h4 := cp_le (fun s => decide (d s < d r + 1)) n
  unfold placeD; omega

theorem place_lt_of_key {r s : Nat} (hr : r < n) (h : d r < d s ∨ (d r = d s ∧ r < s)) :
    placeD d n r < placeD d n s := by
  rcases h with h | ⟨h, hrs⟩
  · have h1 := rk_lt_cnt d n hr
    have h2 := offD_succ d n (d r)
    have h3 := offD_mono d n (show d r + 1 ≤ d s by omega)
    unfold placeD; omega
  · have h1 := rk_lt_rk d hrs h
    unfold placeD; rw [← h]; omega

theorem place_inj {r s : Nat} (hr : r < n) (hs : s < n) (h : placeD d n r = placeD d n s) : r = s := by
  refine Classical.byContradiction fun hne => ?_
  have : (d r < d s ∨ (d r = d s ∧ r < s)) ∨ (d s < d r ∨ (d s = d r ∧ s < r)) := by omega
  rcases this with k | k
  · have := place_lt_of_key d n hr k; omega
  · have := place_lt_of_key d n hs k; omega

theorem place_stable {r s : Nat} (hr : r < n) (hs : s < n) (h : placeD d n r < placeD d n s) :
    d r ≤ d s ∧ (d s ≤ d r → r < s) := by
  refine Classical.byContradiction fun hc => ?_
  have : (d s < d r ∨ (d s = d r ∧ s < r)) ∨ r = s := by omega
  rcases this with k | rfl
  · have := place_lt_of_key d n hs k; omega
  · omega

end Place

/-! ### A pigeonhole and an index, both without Mathlib -/

theorem nodup_lt_length : ∀ (n : Nat) (l : List Nat), l.Nodup → (∀ x ∈ l, x < n) → l.length ≤ n
  | 0, l, _, h => by
    cases l with
    | nil => simp
    | cons x l => exact absurd (h x (by simp)) (by omega)
  | n + 1, l, hnd, h => by
    by_cases hm : n ∈ l
    · have h1 : (l.erase n).length = l.length - 1 := List.length_erase_of_mem hm
      have h2 := nodup_lt_length n (l.erase n) (hnd.erase n) fun x hx => by
        have hxl := List.mem_of_mem_erase hx
        have : x ≠ n := fun e => (List.Nodup.not_mem_erase hnd) (e ▸ hx)
        have := h x hxl; omega
      have : 0 < l.length := List.length_pos_of_mem hm
      omega
    · have := nodup_lt_length n l hnd fun x hx => by
        have := h x hx
        have : x ≠ n := fun e => hm (e ▸ hx)
        omega
      omega

/-- A duplicate-free list of `n` numbers below `n` is a permutation of `range n`. -/
theorem nodup_perm_range : ∀ (n : Nat) (l : List Nat), l.Nodup → (∀ x ∈ l, x < n) → l.length = n →
    l.Perm (List.range n)
  | 0, l, _, _, hl => by
    cases l with
    | nil => simp
    | cons x l => simp at hl
  | n + 1, l, hnd, h, hl => by
    have hm : n ∈ l := by
      refine Classical.byContradiction fun hm => ?_
      have := nodup_lt_length n l hnd fun x hx => by
        have := h x hx
        have : x ≠ n := fun e => hm (e ▸ hx)
        omega
      omega
    have ih := nodup_perm_range n (l.erase n) (hnd.erase n)
      (fun x hx => by
        have hxl := List.mem_of_mem_erase hx
        have : x ≠ n := fun e => (List.Nodup.not_mem_erase hnd) (e ▸ hx)
        have := h x hxl; omega)
      (by rw [List.length_erase_of_mem hm]; omega)
    rw [List.range_succ]
    exact (List.perm_cons_erase hm).trans ((ih.cons n).trans (List.perm_append_singleton n _).symm)

theorem idxOf_getElem' {p : List Nat} (hnd : p.Nodup) {r : Nat} (hr : r < p.length) : p.idxOf p[r] = r := by
  induction p generalizing r with
  | nil => simp at hr
  | cons a l ih =>
    cases r with
    | zero => simp [List.idxOf_cons]
    | succ r =>
      obtain ⟨ha, hl⟩ := List.nodup_cons.mp hnd
      have hr' : r < l.length := by simpa using hr
      have hne : (a == l[r]) = false := by
        simp only [beq_eq_false_iff_ne, ne_eq]; exact fun h => ha (h ▸ List.getElem_mem hr')
      simp only [List.getElem_cons_succ]
      rw [List.idxOf_cons, hne]
      simp [ih hl hr']

/-! ### The scans and the scatter on words -/

theorem foldlM_ok {step : Array UInt64 → Nat → Except String (Array UInt64)} (o : Array UInt64) :
    ∀ m : Nat, (∀ o k, k < m → ∃ o', step o k = .ok o') → ∃ ws, (List.range m).foldlM step o = .ok ws
  | 0, _ => ⟨o, rfl⟩
  | m + 1, hs => by
    obtain ⟨w, hw⟩ := foldlM_ok o m fun o k hk => hs o k (by omega)
    obtain ⟨o', ho⟩ := hs w m (by omega)
    exact ⟨o', by rw [List.range_succ, List.foldlM_append, hw]; simpa [List.foldlM] using ho⟩

theorem scatterWords_ok {op : Op} {f : UInt64 → UInt64 → UInt64} (hf : ∀ a x, op.eval a x = .ok (f a x))
    {is es : Array UInt64} {n : Nat} {fill : UInt64} (hi : ∀ k < is.size, (is[k]?.getD 0).toNat < n) :
    ∃ ws, scatterWords op is es n fill = .ok ws := by
  unfold scatterWords
  refine foldlM_ok _ _ fun o k hk => ?_
  simp only [hi k hk, hf, if_true]
  exact ⟨_, rfl⟩

theorem foldl_add_one (g : Nat → UInt64) (l : List Nat) (hg : ∀ x ∈ l, g x = 1) (a : UInt64) :
    ((l.map g).foldl (· + ·) a).toNat = (a.toNat + l.length) % 2 ^ 64 := by
  induction l generalizing a with
  | nil =>
    have : a.toNat < 2 ^ 64 := a.toBitVec.isLt
    simp [Nat.mod_eq_of_lt this]
  | cons x l ih =>
    simp only [List.map_cons, List.foldl_cons, List.length_cons]
    rw [ih (fun y hy => hg y (List.mem_cons_of_mem _ hy)), UInt64.toNat_add, hg x (List.mem_cons_self)]
    simp
    omega

/-- The histogram: `h[e]` counts the rows of digit `e`. -/
theorem hist_spec (ds : Array UInt64) (n B : Nat) (hsz : ds.size = n) (hn : n < 2 ^ 64)
    (hB : ∀ r < n, (ds[r]?.getD 0).toNat < B) :
    ∃ h, scatterWords .add ds (Array.replicate n 1) B 0 = .ok h ∧ h.size = B ∧
      ∀ e < B, (h[e]?.getD 0).toNat = cp (fun s => decide ((ds[s]?.getD 0).toNat = e)) n := by
  have hf : ∀ a x, Op.add.eval a x = .ok (a + x) := fun _ _ => rfl
  obtain ⟨h, hh⟩ := scatterWords_ok (op := .add) hf (is := ds) (es := Array.replicate n 1) (n := B) (fill := 0)
    (fun k hk => hB k (hsz ▸ hk))
  obtain ⟨hs, hv⟩ := scatterWords_fold hf hh
  refine ⟨h, hh, hs, fun e he => ?_⟩
  rw [hv e he, foldl_add_one _ _ ?_ 0]
  · rw [hsz] at *
    have h1 : (List.filter (fun k => decide ((ds[k]?.getD 0).toNat = e)) (List.range n)).length ≤ n := by
      simpa using List.length_filter_le _ (List.range n)
    simp only [UInt64.toNat_zero, Nat.zero_add]
    rw [Nat.mod_eq_of_lt (by omega), cp, List.countP_eq_length_filter]
  · intro x hx
    simp only [List.mem_filter, List.mem_range] at hx
    simp [hsz ▸ hx.1]

theorem kscanRow_add (seg seed x out : Array UInt64) (i : Nat) :
    kscanRow .add seg seed [x] out i = .ok (out.push
      ((if 0 < i ∧ seg[i]?.getD 0 = 0 then out[i - 1]?.getD 0 else seed[i]?.getD 0) + x[i]?.getD 0)) := by
  simp [kscanRow, List.foldlM, Op.eval]
  rfl

/-- `scanAdd`'s law: a prefix sum that restarts at each `seg` mark, as `foldlM_kscanRow` states `kscan`'s. -/
theorem scanAdd_spec (seg x : Array UInt64) : ∃ out, scanAdd seg x = .ok out ∧ out.size = x.size ∧
    ∀ i < x.size, out[i]?.getD 0 =
      (if 0 < i ∧ seg[i]?.getD 0 = 0 then out[i - 1]?.getD 0 else 0) + x[i]?.getD 0 := by
  obtain ⟨out, h⟩ := foldlM_ok (step := kscanRow .add seg (Array.replicate x.size 0) [x]) #[] x.size
    fun o k _ => ⟨_, kscanRow_add _ _ _ _ _⟩
  refine ⟨out, h, ?_⟩
  obtain ⟨hs, hrow⟩ := foldlM_kscanRow .add seg (Array.replicate x.size 0) [x] x.size out h
  refine ⟨hs, fun i hi => ?_⟩
  have hi' : i < out.size := by omega
  have h1 := hrow i hi'
  have hz : (Array.replicate x.size (0 : UInt64))[i]?.getD 0 = 0 := by
    rw [Array.getElem?_replicate]; split <;> rfl
  simp only [List.foldlM, Op.eval, hz] at h1
  have h2 : out[i]?.getD 0 = out[i] := by rw [Array.getElem?_eq_getElem hi']; rfl
  simp at h1
  rw [h2, ← h1]

theorem scanAdd_toNat {seg x out : Array UInt64} (S : Nat → Nat)
    (hout : ∀ i < x.size, out[i]?.getD 0 =
      (if 0 < i ∧ seg[i]?.getD 0 = 0 then out[i - 1]?.getD 0 else 0) + x[i]?.getD 0)
    (hS : ∀ i < x.size, S i = (if 0 < i ∧ seg[i]?.getD 0 = 0 then S (i - 1) else 0) + (x[i]?.getD 0).toNat)
    (hb : ∀ i < x.size, S i < 2 ^ 64) : ∀ i < x.size, (out[i]?.getD 0).toNat = S i := by
  intro i
  induction i with
  | zero =>
    intro hi
    rw [hout 0 hi, hS 0 hi]; simp
  | succ i ih =>
    intro hi
    have ih' := ih (by omega)
    rw [hout _ hi, UInt64.toNat_add]
    have hb' := hb _ hi
    rw [hS _ hi] at hb' ⊢
    by_cases hc : 0 < i + 1 ∧ seg[i + 1]?.getD 0 = 0
    · simp only [hc, and_self, if_true] at hb' ⊢
      simp only [Nat.add_sub_cancel] at hb' ⊢
      rw [ih']; exact Nat.mod_eq_of_lt hb'
    · simp only [hc, if_false] at hb' ⊢
      simp only [UInt64.toNat_zero, Nat.zero_add] at hb' ⊢
      exact Nat.mod_eq_of_lt hb'

theorem div_mod_idx {n e i : Nat} (hi : i < n) : (n * e + i) % n = i ∧ (n * e + i) / n = e := by
  have hn : 0 < n := by omega
  exact ⟨by rw [Nat.mul_add_mod]; exact Nat.mod_eq_of_lt hi,
    by rw [Nat.mul_add_div hn, Nat.div_eq_of_lt hi, Nat.add_zero]⟩

theorem rankSeg_get {n B t : Nat} (ht : t < B * n) : (rankSeg n B)[t]?.getD 0 = if t % n = 0 then 1 else 0 := by
  simp [rankSeg, ht]

theorem rankCol_get {ds : Array UInt64} {n B t : Nat} (ht : t < B * n) :
    (rankCol ds n B)[t]?.getD 0 = if (ds[t % n]?.getD 0).toNat = t / n then 1 else 0 := by
  simp [rankCol, ht]

/-- The rank scan: row `r` of digit `e` reads the count of the rows up to `r` of digit `e`. -/
theorem rank_spec (ds : Array UInt64) (n B : Nat) (hn : n < 2 ^ 64) :
    ∃ s, scanAdd (rankSeg n B) (rankCol ds n B) = .ok s ∧
      ∀ e < B, ∀ i < n, (s[n * e + i]?.getD 0).toNat = cp (fun x => decide ((ds[x]?.getD 0).toNat = e)) (i + 1) := by
  obtain ⟨s, hs, hsz, hrow⟩ := scanAdd_spec (rankSeg n B) (rankCol ds n B)
  have hcsz : (rankCol ds n B).size = B * n := by simp [rankCol]
  refine ⟨s, hs, ?_⟩
  have key := scanAdd_toNat (seg := rankSeg n B) (x := rankCol ds n B) (out := s)
    (fun t => cp (fun x => decide ((ds[x]?.getD 0).toNat = t / n)) (t % n + 1)) hrow ?_ ?_
  · intro e he i hi
    have h1 : n * (e + 1) ≤ n * B := Nat.mul_le_mul_left n he
    rw [Nat.mul_succ] at h1
    have h2 : B * n = n * B := Nat.mul_comm B n
    have := key (n * e + i) (by rw [hcsz]; omega)
    obtain ⟨hm, hv⟩ := div_mod_idx (e := e) hi
    simpa [hm, hv] using this
  · intro t ht
    rw [hcsz] at ht
    have hn0 : 0 < n := by
      rcases Nat.eq_zero_or_pos n with h | h
      · simp [h] at ht
      · exact h
    obtain ⟨e, i, hi, rfl⟩ : ∃ e i, i < n ∧ t = n * e + i :=
      ⟨t / n, t % n, Nat.mod_lt _ hn0, (Nat.div_add_mod t n).symm⟩
    obtain ⟨hm, hv⟩ := div_mod_idx (e := e) hi
    dsimp only
    rw [rankSeg_get ht, rankCol_get ht, hm, hv]
    by_cases hi0 : i = 0
    · subst hi0
      by_cases hd : (ds[0]?.getD 0).toNat = e <;> simp [cp_succ, cp_zero, hd]
    · have ht1 : n * e + i - 1 = n * e + (i - 1) := by omega
      obtain ⟨hm1, hv1⟩ := div_mod_idx (n := n) (e := e) (i := i - 1) (by omega)
      rw [ht1, hm1, hv1, Nat.sub_add_cancel (by omega : 1 ≤ i)]
      have hpos : 0 < n * e + i := by omega
      by_cases hd : (ds[i]?.getD 0).toNat = e <;> simp [cp_succ, hd, hi0, hpos]
  · intro t ht
    rw [hcsz] at ht
    have hn0 : 0 < n := by
      rcases Nat.eq_zero_or_pos n with h | h
      · simp [h] at ht
      · exact h
    have := cp_le (fun x => decide ((ds[x]?.getD 0).toNat = t / n)) (t % n + 1)
    have := Nat.mod_lt t hn0
    dsimp only
    omega

/-- The words `placeWords` computes are `placeD`. -/
theorem place_words (ds h c s : Array UInt64) (n B : Nat) (d : Nat → Nat) (hd : ∀ r, d r = (ds[r]?.getD 0).toNat)
    (hn : n < 2 ^ 64) (hdB : ∀ r < n, d r < B)
    (hhv : ∀ e < B, (h[e]?.getD 0).toNat = cntD d n e) (hcv : ∀ e < B, (c[e]?.getD 0).toNat = offD d n (e + 1))
    (hsv : ∀ e < B, ∀ i < n, (s[n * e + i]?.getD 0).toNat = cp (fun x => decide (d x = e)) (i + 1)) :
    (placeWords n ds h c s).size = n ∧ ∀ r < n, ((placeWords n ds h c s)[r]?.getD 0).toNat = placeD d n r := by
  refine ⟨by simp [placeWords], fun r hr => ?_⟩
  simp only [placeWords, List.getElem?_toArray, List.getElem?_map, List.getElem?_range, hr, Option.map_some,
    Option.getD_some]
  rw [← hd r]
  have he := hdB r hr
  have hA := hcv (d r) he
  have hH := hhv (d r) he
  have hS := hsv (d r) he r hr
  have hS' : (s[n * d r + r]?.getD 0).toNat = rkD d r + 1 := by rw [hS, cp_succ]; simp [rkD]
  have h1 := offD_succ d n (d r)
  have h2 := place_lt d n hr
  unfold placeD at h2
  have hle : h[d r]?.getD 0 ≤ c[d r]?.getD 0 := by rw [UInt64.le_iff_toNat_le, hA, hH]; omega
  have hsub : (c[d r]?.getD 0 - h[d r]?.getD 0).toNat = offD d n (d r) := by
    rw [UInt64.toNat_sub_of_le _ _ hle, hA, hH]; omega
  have hadd : (c[d r]?.getD 0 - h[d r]?.getD 0 + s[n * d r + r]?.getD 0).toNat = offD d n (d r) + rkD d r + 1 := by
    rw [UInt64.toNat_add, hsub, hS']
    exact Nat.mod_eq_of_lt (by omega)
  have hone : (1 : UInt64) ≤ c[d r]?.getD 0 - h[d r]?.getD 0 + s[n * d r + r]?.getD 0 := by
    rw [UInt64.le_iff_toNat_le, hadd]; simp
  rw [UInt64.toNat_sub_of_le _ _ hone, hadd]
  simp [placeD]

/-- **`countPass` is a stable sort by the digit** (design §4's radix pass): for a duplicate-free `p` of row indices whose
digits are below `B`, it answers `q`, a permutation of `p` in which row `i` comes before row `j` only if `i`'s digit is no
larger and, on equal digits, `i` stands before `j` in `p` (`p.idxOf`). With `p = ascGrade m cs` and the digit column
of `c`, that is `ascGrade m (c :: cs)` (LSD): both are the unique such permutation of `range m`. -/
theorem countPass_stable (B : Nat) (k : Array UInt64) (p : List Nat) (hn : p.length < 2 ^ 64)
    (hp : ∀ i ∈ p, i < 2 ^ 64) (hnd : p.Nodup) (hB : ∀ i ∈ p, dig k i < B) :
    ∃ q, countPass B k p = .ok q ∧ q.Perm p ∧
      q.Pairwise fun i j => dig k i ≤ dig k j ∧ (dig k j ≤ dig k i → p.idxOf i < p.idxOf j) := by
  have hdsz : (digitCol k p).size = p.length := by simp [digitCol]
  have hdg : ∀ r (hr : r < p.length), ((digitCol k p)[r]?.getD 0).toNat = dig k p[r] := by
    intro r hr; simp [digitCol, dig, hr]
  obtain ⟨d, hd⟩ : ∃ d : Nat → Nat, ∀ r, d r = ((digitCol k p)[r]?.getD 0).toNat := ⟨_, fun _ => rfl⟩
  have hdB : ∀ r < p.length, d r < B := fun r hr => by
    rw [hd, hdg r hr]; exact hB _ (List.getElem_mem hr)
  obtain ⟨h, hh, hhs, hhv⟩ := hist_spec (digitCol k p) p.length B hdsz hn (fun r hr => by rw [← hd]; exact hdB r hr)
  have hhv' : ∀ e < B, (h[e]?.getD 0).toNat = cntD d p.length e := fun e he => by
    rw [hhv e he]; simp only [cntD, hd]
  obtain ⟨c, hc, hcs, hcr⟩ := scanAdd_spec (Array.replicate B 0) h
  have hcv : ∀ e < B, (c[e]?.getD 0).toNat = offD d p.length (e + 1) := by
    have key := scanAdd_toNat (seg := Array.replicate B 0) (x := h) (out := c)
      (fun e => offD d p.length (e + 1)) hcr ?_ ?_
    · intro e he; exact key e (by omega)
    · intro i hi
      have hseg : (Array.replicate B (0 : UInt64))[i]?.getD 0 = 0 := by
        rw [Array.getElem?_replicate]; split <;> rfl
      dsimp only
      rw [hhv' i (by omega), offD_succ, hseg]
      by_cases h0 : i = 0
      · subst h0; simp [offD]
      · rw [if_pos ⟨by omega, rfl⟩, Nat.sub_add_cancel (by omega)]
    · intro i hi
      dsimp only
      rw [offD_eq]
      have := cp_le (fun s => decide (d s < i + 1)) p.length
      omega
  obtain ⟨s, hs, hsv⟩ := rank_spec (digitCol k p) p.length B hn
  have hsv' : ∀ e < B, ∀ i < p.length, (s[p.length * e + i]?.getD 0).toNat = cp (fun x => decide (d x = e)) (i + 1) :=
    fun e he i hi => by rw [hsv e he i hi]; simp only [hd]
  obtain ⟨hplsz, hplv⟩ := place_words (digitCol k p) h c s p.length B d hd hn hdB hhv' hcv hsv'
  have hplix : ∀ r < p.length, ixAt (placeWords p.length (digitCol k p) h c s) r = placeD d p.length r :=
    fun r hr => hplv r hr
  obtain ⟨hex, hq⟩ := scatterWords_spec (placeWords p.length (digitCol k p) h c s) (p.map Nat.toUInt64).toArray
    p.length 0
  obtain ⟨ws, hw⟩ := hex.mpr fun r hr => by
    rw [hplsz] at hr; rw [hplix r hr]; exact place_lt d p.length hr
  obtain ⟨hwsz, -, hwv⟩ := hq ws hw
  have hwr : ∀ r (hr : r < p.length), (ws[placeD d p.length r]?.getD 0).toNat = p[r] := by
    intro r hr
    have := hwv r (by rw [hplsz]; exact hr) (fun k' hk1 hk2 => by
      rw [hplsz] at hk2
      rw [hplix k' hk2, hplix r hr]
      exact fun he => by have := place_inj d p.length hk2 hr he; omega)
    rw [hplix r hr] at this
    rw [this]
    simp [Nat.mod_eq_of_lt (hp _ (List.getElem_mem hr)), hr]
  refine ⟨ws.toList.map (·.toNat), ?_, ?_⟩
  · unfold countPass
    simp only [hh, hc, hs, hw, bind, Except.bind, pure, Except.pure]
  obtain ⟨g, hg⟩ : ∃ g : Nat → Nat, ∀ j, g j = (ws[j]?.getD 0).toNat := ⟨_, fun _ => rfl⟩
  have hqe : ws.toList.map (·.toNat) = (List.range p.length).map g := by
    refine List.ext_getElem (by simp [hwsz]) fun i h1 h2 => ?_
    simp [hg, Array.getElem?_eq_getElem (show i < ws.size by simpa using h1)]
  have hgp : ∀ r (hr : r < p.length), g (placeD d p.length r) = p[r] := fun r hr => by rw [hg]; exact hwr r hr
  have hPn : ((List.range p.length).map (placeD d p.length)).Perm (List.range p.length) := by
    refine nodup_perm_range _ _ ?_ ?_ (by simp)
    · rw [List.Nodup, List.pairwise_map]
      exact List.nodup_range.imp_of_mem fun {a b} ha hb hab he =>
        hab (place_inj d p.length (List.mem_range.mp ha) (List.mem_range.mp hb) he)
    · intro x hx
      obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hx
      exact place_lt d p.length (List.mem_range.mp hr)
  rw [hqe]
  refine ⟨?_, ?_⟩
  · have hmap : ((List.range p.length).map (placeD d p.length)).map g = p := by
      refine List.ext_getElem (by simp) fun i h1 h2 => ?_
      simp only [List.getElem_map, List.getElem_range]
      exact hgp i h2
    have := (hPn.symm).map g
    rwa [hmap] at this
  · rw [List.pairwise_map]
    refine List.pairwise_lt_range.imp_of_mem fun {a b} ha hb hab => ?_
    obtain ⟨r, hr, hra⟩ := List.mem_map.mp ((hPn.mem_iff).mpr ha)
    obtain ⟨s, hs', hsb⟩ := List.mem_map.mp ((hPn.mem_iff).mpr hb)
    have hr' := List.mem_range.mp hr
    have hs'' := List.mem_range.mp hs'
    subst hra hsb
    obtain ⟨h1, h2⟩ := place_stable d p.length hr' hs'' hab
    rw [hgp r hr', hgp s hs'', idxOf_getElem' hnd hr', idxOf_getElem' hnd hs'', ← hdg r hr', ← hdg s hs'', ← hd,
      ← hd]
    exact ⟨h1, h2⟩

end Rel.Verify
