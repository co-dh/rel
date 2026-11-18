import Rel.Kernel.Distinct
import Rel.KernelSpec.Scan
import Rel.KernelSpec.Scatter
import Rel.KernelSpec.Group

/-! `distinct`'s laws (design §4): `distinct_first` (the answer is the rows that start a run of equal rows, each once,
in input order) and `distinct_cover` (every row equals the run start before it, every row between them too), on the
words `Enc.raw` reads from the columns. On a sorted input equal rows are contiguous, so a run start is the first
occurrence of its row. `distinctWords_scans` evaluates the scans of the body, so the answer is one `scatterWords`. -/

namespace Rel.Verify
open Rel.Kernel Ext.Enc

/-- A `kscanRow` fold whose row `i` answers `v i` from the carry `v (i - 1)` answers the rows `v 0, …, v (m - 1)`. -/
theorem foldlM_kscanRow_ofFn (op : Op) (g seed : Array UInt64) (xs : List (Array UInt64)) (v : Nat → UInt64) :
    ∀ m, (∀ i < m, xs.foldlM (fun a x => op.eval a (x[i]?.getD 0))
        (if 0 < i ∧ g[i]?.getD 0 = 0 then v (i - 1) else seed[i]?.getD 0) = .ok (v i)) →
      (List.range m).foldlM (kscanRow op g seed xs) #[] = .ok (Array.ofFn (n := m) fun i => v i.1)
  | 0, _ => rfl
  | m + 1, h => by
    rw [List.range_succ, List.foldlM_append, foldlM_kscanRow_ofFn op g seed xs v m fun i hi => h i (by omega)]
    have hc : (if 0 < m ∧ g[m]?.getD 0 = 0 then (Array.ofFn (n := m) fun i => v i.1)[m - 1]?.getD 0
        else seed[m]?.getD 0) = (if 0 < m ∧ g[m]?.getD 0 = 0 then v (m - 1) else seed[m]?.getD 0) := by
      by_cases h0 : 0 < m
      · simp [h0, show m - 1 < m by omega]
      · simp [h0]
    simp only [bind, Except.bind, List.foldlM_cons, List.foldlM_nil, kscanRow, hc, h m (by omega), Functor.map,
      Except.map, pure, Except.pure, Array.ofFn_succ]
    rfl

-- the four steps `distinctWords` scans with, out of `Op.eval`'s private `w`
private theorem eval_ne (a x : UInt64) : Op.ne.eval a x = .ok (if a != x then 1 else 0) := rfl
private theorem eval_or (a x : UInt64) : Op.or.eval a x = .ok (a ||| x) := rfl
private theorem eval_add (a x : UInt64) : Op.add.eval a x = .ok (a + x) := rfl
private theorem eval_last (a x : UInt64) : Op.last.eval a x = .ok x := rfl

private theorem mapM_ok {α β : Type} (f : α → Except String β) (D : α → β) :
    ∀ l : List α, (∀ x ∈ l, f x = .ok (D x)) → l.mapM f = .ok (l.map D)
  | [], _ => rfl
  | x :: l, h => by
    rw [List.mapM_cons, h x (by simp), mapM_ok f D l fun y hy => h y (by simp [hy])]; rfl

/-! The count and the start of a row's run, for any marking `st` of the rows that start one (row 0 among them). -/

/-- How many of the rows `0 … i` start a run: one more than the index of row `i`'s run. -/
def runCount (st : Nat → Bool) (i : Nat) : Nat := ((List.range (i + 1)).filter st).length

/-- The row that starts row `i`'s run: the last marked row `≤ i`. -/
def runStart (st : Nat → Bool) : Nat → Nat
  | 0 => 0
  | i + 1 => if st (i + 1) then i + 1 else runStart st i

section runs
variable {st : Nat → Bool}

theorem runCount_succ (i : Nat) : runCount st (i + 1) = runCount st i + if st (i + 1) then 1 else 0 := by
  unfold runCount
  rw [List.range_succ, List.filter_append, List.length_append]
  cases h : st (i + 1) <;> simp [List.filter, h]

theorem runCount_mono {i i' : Nat} (h : i ≤ i') : runCount st i ≤ runCount st i' := by
  induction h with
  | refl => exact Nat.le_refl _
  | step _ ih => rw [runCount_succ]; omega

theorem runCount_le (i : Nat) : runCount st i ≤ i + 1 := by
  unfold runCount; exact Nat.le_trans (List.length_filter_le _ _) (by simp)

theorem runCount_pos (h0 : st 0 = true) (i : Nat) : 1 ≤ runCount st i :=
  (show runCount st 0 = 1 by simp [runCount, List.filter, h0]) ▸ runCount_mono (Nat.zero_le i)

/-- A row's run start is at or before it, marked, and in the same run. -/
theorem runStart_spec (h0 : st 0 = true) :
    ∀ i, runStart st i ≤ i ∧ st (runStart st i) = true ∧ runCount st (runStart st i) = runCount st i
  | 0 => ⟨Nat.le_refl 0, h0, rfl⟩
  | i + 1 => by
    unfold runStart
    cases h : st (i + 1)
    · obtain ⟨a, b, c⟩ := runStart_spec h0 i
      exact ⟨by simp; omega, by simpa using b, by simp [c, runCount_succ, h]⟩
    · simp [h]

/-- Rows of one run count alike and share their start: from `i` to `i + d` with no new run, none is marked. -/
theorem runStart_eq : ∀ d i, runCount st i = runCount st (i + d) → runStart st (i + d) = runStart st i
  | 0, _, _ => rfl
  | d + 1, i, h => by
    have h1 := runCount_mono (st := st) (Nat.le_add_right i d)
    have h2 := runCount_succ (st := st) (i + d)
    rw [← Nat.add_assoc] at h
    have hs : st (i + d + 1) = false := by cases hc : st (i + d + 1) <;> simp_all <;> omega
    rw [← Nat.add_assoc]
    simp only [runStart, hs]
    exact runStart_eq d i (by simp [hs] at h2; omega)

/-- No row after a run's start and up to `i` is marked. -/
theorem not_st_of_run (h0 : st 0 = true) (i q : Nat) (h1 : runStart st i < q) (h2 : q ≤ i) : st q = false := by
  obtain ⟨-, -, hc⟩ := runStart_spec h0 i
  have a := runCount_mono (st := st) (show runStart st i ≤ q - 1 by omega)
  have b := runCount_mono (st := st) h2
  have c := runCount_succ (st := st) (q - 1)
  rw [show q - 1 + 1 = q by omega] at c
  cases hq : st q <;> simp_all <;> omega

/-- Every run index below `runCount st i` is the index of a row `≤ i`. -/
theorem runCount_surj (h0 : st 0 = true) : ∀ i j, j < runCount st i → ∃ q ≤ i, runCount st q = j + 1
  | 0, j, h => ⟨0, Nat.le_refl 0, by simp [runCount, List.filter, h0] at h ⊢; omega⟩
  | i + 1, j, h => by
    rw [runCount_succ] at h
    by_cases hj : j < runCount st i
    · obtain ⟨q, hq, e⟩ := runCount_surj h0 i j hj; exact ⟨q, by omega, e⟩
    · refine ⟨i + 1, Nat.le_refl _, ?_⟩
      rw [runCount_succ]; split at h <;> simp_all <;> omega

end runs

/-- The last row below `n` with a property, from one that has it. -/
private theorem lastOf (P : Nat → Prop) (n : Nat) :
    ∀ d i, n - i ≤ d → i < n → P i → ∃ r, i ≤ r ∧ r < n ∧ P r ∧ ∀ q, r < q → q < n → ¬ P q
  | 0, _, h, hi, _ => absurd hi (by omega)
  | d + 1, i, h, hi, hp => by
    by_cases hq : ∃ q, i < q ∧ q < n ∧ P q
    · obtain ⟨q, a, b, c⟩ := hq
      obtain ⟨r, e, f, g, k⟩ := lastOf P n d q (by omega) b c
      exact ⟨r, by omega, f, g, k⟩
    · exact ⟨i, Nat.le_refl i, hi, hp, fun q a b c => hq ⟨q, a, b, c⟩⟩

/-- Row `i` starts a run of the columns `xs`: row 0, or some column changes there. -/
abbrev startsRun (xs : List (Array UInt64)) (i : Nat) : Bool :=
  i == 0 || xs.any fun x => x[i]?.getD 0 != x[i - 1]?.getD 0

/-- **The scans of `distinctWords`, evaluated**: the body is `scatterWords` of each row's run index into the run
count, each cell receiving its run's start. -/
theorem distinctWords_scans (n : Nat) (xs : List (Array UInt64)) (hx : ∀ x ∈ xs, x.size = n) :
    distinctWords n xs =
      let ix := Array.ofFn (n := n) fun i => UInt64.ofNat (runCount (startsRun xs) i.1 - 1)
      let k := (ix.back?.map (·.toNat + 1)).getD 0
      (k, ·) <$> scatterWords ix (Array.ofFn (n := n) fun i => (runStart (startsRun xs) i.1).toUInt64) k 0 := by
  let D : Array UInt64 → Array UInt64 := fun x =>
    Array.ofFn (n := n) fun i => if x[i.1]?.getD 0 != x[i.1 - 1]?.getD 0 then 1 else 0
  have hD : ∀ i < n, ∀ x, (D x)[i]?.getD 0 = if x[i]?.getD 0 != x[i - 1]?.getD 0 then 1 else 0 := by
    intro i hi x; simp [D, hi]
  have hds : xs.mapM (fun x => (List.range n).foldlM
      (kscanRow .ne (Array.replicate n 1) x [Array.ofFn (n := x.size) fun i => x[i.1 - 1]?.getD 0]) #[]) =
      .ok (xs.map D) := by
    refine mapM_ok _ D xs fun x hxs => foldlM_kscanRow_ofFn .ne _ _ _
      (fun i => if x[i]?.getD 0 != x[i - 1]?.getD 0 then 1 else 0) n fun i hi => ?_
    have hs := hx x hxs
    simp [hi, hs, List.foldlM_cons, bind, Except.bind, eval_ne]; rfl
  have hor : ∀ i < n, ∀ (l : List (Array UInt64)) (b : Bool),
      (l.map D).foldlM (fun a x => Op.or.eval a (x[i]?.getD 0)) (if b then 1 else 0) =
        .ok (if b || l.any (fun x => x[i]?.getD 0 != x[i - 1]?.getD 0) then 1 else 0) := by
    intro i hi l
    induction l with
    | nil => intro b; simp; rfl
    | cons x l ih =>
      intro b
      rw [List.map_cons, List.foldlM_cons, hD i hi]
      have e : Op.or.eval (if b then 1 else 0) (if x[i]?.getD 0 != x[i - 1]?.getD 0 then 1 else 0) =
          .ok (if (b || (x[i]?.getD 0 != x[i - 1]?.getD 0)) then 1 else 0) := by
        cases b <;> cases (x[i]?.getD 0 != x[i - 1]?.getD 0) <;> rfl
      rw [e]
      simp only [bind, Except.bind]
      rw [ih]
      simp [Bool.or_assoc]
  have h0 : startsRun xs 0 = true := by simp [startsRun]
  have hst : (List.range n).foldlM (kscanRow .or (Array.replicate n 1)
      (Array.ofFn (n := n) fun i => if i.1 = 0 then 1 else 0) (xs.map D)) #[] =
      .ok (Array.ofFn (n := n) fun i => if startsRun xs i.1 then 1 else 0) := by
    refine foldlM_kscanRow_ofFn .or _ _ _ (fun i => if startsRun xs i then 1 else 0) n fun i hi => ?_
    have hc : (if 0 < i ∧ (Array.replicate n (1 : UInt64))[i]?.getD 0 = 0 then
        (if startsRun xs (i - 1) then 1 else 0)
        else (Array.ofFn (n := n) fun i => if i.1 = 0 then (1 : UInt64) else 0)[i]?.getD 0) =
        if (i == 0) then 1 else 0 := by
      simp [hi]
    rw [hc, hor i hi xs (i == 0)]
  have hix : (List.range n).foldlM (kscanRow .add #[] (Array.replicate n (0 - 1))
      [Array.ofFn (n := n) fun i => if startsRun xs i.1 then 1 else 0]) #[] =
      .ok (Array.ofFn (n := n) fun i => UInt64.ofNat (runCount (startsRun xs) i.1 - 1)) := by
    refine foldlM_kscanRow_ofFn .add _ _ _ (fun i => UInt64.ofNat (runCount (startsRun xs) i - 1)) n fun i hi => ?_
    simp only [List.foldlM_cons, List.foldlM_nil, Array.getElem?_ofFn, hi, dif_pos]
    cases i with
    | zero => simp [h0, runCount, List.filter, hi, eval_add]; decide
    | succ j =>
      have hp := runCount_pos h0 j
      simp only [show 0 < j + 1 by omega, Array.getElem?_empty, Option.getD_none, and_true, if_true,
        Nat.add_sub_cancel, Option.getD_some, runCount_succ]
      cases hs : startsRun xs (j + 1)
      · simp [eval_add]
      · simp only [if_true, eval_add]
        rw [show runCount (startsRun xs) j + 1 - 1 = (runCount (startsRun xs) j - 1) + 1 by omega, UInt64.ofNat_add]
        rfl
  have hfst : (List.range n).foldlM (kscanRow .last (Array.ofFn (n := n) fun i => if startsRun xs i.1 then 1 else 0)
      (Array.ofFn (n := n) fun i => i.1.toUInt64) []) #[] =
      .ok (Array.ofFn (n := n) fun i => (runStart (startsRun xs) i.1).toUInt64) := by
    refine foldlM_kscanRow_ofFn .last _ _ _ (fun i => (runStart (startsRun xs) i).toUInt64) n fun i hi => ?_
    simp only [List.foldlM_nil, Array.getElem?_ofFn, hi, dif_pos, Option.getD_some]
    cases i with
    | zero => rfl
    | succ j => cases hs : startsRun xs (j + 1) <;> simp [runStart, hs] <;> rfl
  unfold distinctWords
  simp only [hds, bind, Except.bind, hst, hix, hfst]

section rows
variable (xs : List (Array UInt64))

/-- Row `q` of the columns `xs`. -/
private abbrev row (q : Nat) : List UInt64 := xs.map (·[q]?.getD 0)

private theorem row_of_not_start (q : Nat) (h : startsRun xs q = false) : row xs q = row xs (q - 1) := by
  simp only [startsRun, Bool.or_eq_false_iff, beq_eq_false_iff_ne, List.any_eq_false, bne_iff_ne, ne_eq,
    Decidable.not_not] at h
  exact List.map_inj_left.mpr h.2

private theorem start_row (p : Nat) (h : startsRun xs p = true) : p = 0 ∨ row xs p ≠ row xs (p - 1) := by
  by_cases hp : p = 0
  · exact .inl hp
  · refine .inr fun e => ?_
    simp only [startsRun, hp, Bool.or_eq_true, beq_iff_eq, false_or, List.any_eq_true, bne_iff_ne] at h
    obtain ⟨x, hx, hne⟩ := h
    exact hne (List.map_inj_left.mp e x hx)

/-- No run starts after `a` up to `a + d`: the rows there are row `a`. -/
private theorem row_const (a : Nat) :
    ∀ d, (∀ q, a < q → q ≤ a + d → startsRun xs q = false) → row xs (a + d) = row xs a
  | 0, _ => rfl
  | d + 1, h => by
    rw [← Nat.add_assoc, row_of_not_start xs _ (h _ (by omega) (by omega)), Nat.add_sub_cancel]
    exact row_const a d fun q a' b => h q a' (by omega)

end rows

/-- **`distinctWords`' law** on `n` words a column: its `k` words are the rows that start a run (row 0, or one some
column changes at), strictly ascending; and every row lies in the run of one of them, the rows between equal. -/
theorem distinctWords_spec (n : Nat) (hn : n < 2 ^ 64) (xs : List (Array UInt64)) (hx : ∀ x ∈ xs, x.size = n)
    (k : Nat) (ws : Array UInt64) (h : distinctWords n xs = .ok (k, ws)) :
    let row := fun q => xs.map (·[q]?.getD 0)
    ws.size = k ∧
      (∀ j (hj : j < ws.size), ws[j].toNat < n ∧ (ws[j].toNat = 0 ∨ row ws[j].toNat ≠ row (ws[j].toNat - 1))) ∧
      (∀ j j' (hj : j < ws.size) (hj' : j' < ws.size), j < j' → ws[j] < ws[j']) ∧
      ∀ i < n, ∃ j, ∃ hj : j < ws.size, ws[j].toNat ≤ i ∧ ∀ q, ws[j].toNat ≤ q → q ≤ i → row q = row i := by
  intro row'
  have h0 : startsRun xs 0 = true := by simp [startsRun]
  rw [distinctWords_scans n xs hx] at h
  simp only at h
  generalize hK : ((Array.ofFn (n := n) fun i => UInt64.ofNat (runCount (startsRun xs) i.1 - 1)).back?.map
    (·.toNat + 1)).getD 0 = K at h
  have hc : ∀ q < n, (UInt64.ofNat (runCount (startsRun xs) q - 1)).toNat = runCount (startsRun xs) q - 1 := by
    intro q hq
    have := runCount_le (st := startsRun xs) q
    rw [UInt64.toNat_ofNat_of_lt' (by unfold UInt64.size; omega)]
  have hK' : ∀ q < n, runCount (startsRun xs) q ≤ K ∧ K = runCount (startsRun xs) (n - 1) := by
    intro q hq
    have e : K = runCount (startsRun xs) (n - 1) := by
      rw [← hK]
      simp [Array.back?, show n - 1 < n by omega, hc (n - 1) (by omega)]
      have := runCount_pos h0 (st := startsRun xs) (n - 1); omega
    exact ⟨e ▸ runCount_mono (by omega), e⟩
  cases hs : scatterWords (Array.ofFn (n := n) fun i => UInt64.ofNat (runCount (startsRun xs) i.1 - 1))
      (Array.ofFn (n := n) fun i => (runStart (startsRun xs) i.1).toUInt64) K 0 with
  | error e => rw [hs] at h; cases h
  | ok ws' =>
    rw [hs] at h
    obtain ⟨rfl, rfl⟩ : K = k ∧ ws' = ws := by cases h; exact ⟨rfl, rfl⟩
    obtain ⟨-, hw⟩ := scatterWords_spec (Array.ofFn (n := n) fun i => UInt64.ofNat (runCount (startsRun xs) i.1 - 1))
      (Array.ofFn (n := n) fun i => (runStart (startsRun xs) i.1).toUInt64) K 0
    obtain ⟨hsz, -, hlast⟩ := hw ws' hs
    have hix : ∀ q < n, ((Array.ofFn (n := n) fun i => UInt64.ofNat (runCount (startsRun xs) i.1 - 1))[q]?.getD 0).toNat
        = runCount (startsRun xs) q - 1 := fun q hq => by simp [hq, hc q hq]
    have hstart : ∀ q < n, runStart (startsRun xs) q < 2 ^ 64 := fun q hq => by
      have := (runStart_spec h0 q).1; omega
    -- every row of a run reads its start at the run's cell: the last row of the run wrote it
    have key : ∀ q < n, ws'[runCount (startsRun xs) q - 1]? = some (runStart (startsRun xs) q).toUInt64 := by
      intro q hq
      obtain ⟨r, hqr, hrn, hr, hlt⟩ := lastOf (fun r => runCount (startsRun xs) r = runCount (startsRun xs) q) n n q
        (by omega) hq rfl
      have := hlast r (by simp; omega) fun k' a b e => hlt k' a (by simpa using b) (by
        -- `e` is stated through `scatterWords_spec`'s private `ixAt`, an abbrev for this
        have e' : ((Array.ofFn (n := n) fun i => UInt64.ofNat (runCount (startsRun xs) i.1 - 1))[k']?.getD 0).toNat =
            ((Array.ofFn (n := n) fun i => UInt64.ofNat (runCount (startsRun xs) i.1 - 1))[r]?.getD 0).toNat := e
        rw [hix k' (by simpa using b), hix r hrn] at e'
        have := runCount_pos h0 (st := startsRun xs) k'; have := runCount_pos h0 (st := startsRun xs) r; omega)
      have this' : ws'[((Array.ofFn (n := n) fun i => UInt64.ofNat (runCount (startsRun xs) i.1 - 1))[r]?.getD 0).toNat]?
          = some ((Array.ofFn (n := n) fun i => (runStart (startsRun xs) i.1).toUInt64)[r]?.getD 0) := this
      rw [hix r hrn, hr] at this'
      rw [this']
      have hs := runStart_eq (st := startsRun xs) (r - q) q (by rw [Nat.add_sub_cancel' hqr, hr])
      rw [Nat.add_sub_cancel' hqr] at hs
      simp [hrn, hs]
    have hget : ∀ j (hj : j < ws'.size), ∃ q < n, runCount (startsRun xs) q = j + 1 ∧
        ws'[j] = (runStart (startsRun xs) q).toUInt64 := by
      intro j hj
      have hn0 : n ≠ 0 := by intro e; subst e; simp [Array.back?] at hK; omega
      obtain ⟨-, e⟩ := hK' 0 (by omega)
      obtain ⟨q, hq, hcq⟩ := runCount_surj h0 (n - 1) j (by omega)
      have := key q (by omega)
      rw [hcq, Nat.add_sub_cancel, Array.getElem?_eq_getElem hj] at this
      exact ⟨q, by omega, hcq, Option.some.inj this⟩
    have hnat : ∀ q < n, (runStart (startsRun xs) q).toUInt64.toNat = runStart (startsRun xs) q := fun q hq => by
      have := hstart q hq
      simp [Nat.toUInt64, UInt64.toNat_ofNat_of_lt' (show runStart (startsRun xs) q < UInt64.size by unfold UInt64.size; omega)]
    refine ⟨hsz, fun j hj => ?_, fun j j' hj hj' hjj => ?_, fun i hi => ?_⟩
    · obtain ⟨q, hq, -, e⟩ := hget j hj
      obtain ⟨a, b, -⟩ := runStart_spec h0 q
      rw [e, hnat q hq]
      exact ⟨by omega, start_row xs _ b⟩
    · obtain ⟨q, hq, cq, e⟩ := hget j hj
      obtain ⟨q', hq', cq', e'⟩ := hget j' hj'
      rw [e, e', UInt64.lt_iff_toNat_lt, hnat q hq, hnat q' hq']
      obtain ⟨-, -, c⟩ := runStart_spec h0 q
      obtain ⟨-, -, c'⟩ := runStart_spec h0 q'
      refine Nat.lt_of_not_le fun hle => ?_
      have := runCount_mono (st := startsRun xs) hle
      omega
    · obtain ⟨hle, -⟩ := hK' i hi
      have hp := runCount_pos h0 (st := startsRun xs) i
      have hj : runCount (startsRun xs) i - 1 < ws'.size := by omega
      have e := key i hi
      rw [Array.getElem?_eq_getElem hj] at e
      have e2 := Option.some.inj e
      obtain ⟨a, -, -⟩ := runStart_spec h0 i
      refine ⟨_, hj, ?_, fun q h1 h2 => ?_⟩
      · rw [e2, hnat i hi]; exact a
      · rw [e2, hnat i hi] at h1
        have nq := not_st_of_run h0 i
        obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h1
        obtain ⟨d', hd'⟩ := Nat.exists_eq_add_of_le h2
        have r1 := row_const xs (runStart (startsRun xs) i) d fun q' a' b' => nq q' a' (by omega)
        have r2 := row_const xs (runStart (startsRun xs) i) (d + d') fun q' a' b' => nq q' a' (by omega)
        rw [← Nat.add_assoc, ← hd'] at r2
        exact r1.trans r2.symm

private theorem mapM_foRWords (n : USize) : ∀ (l : List (Enc × Nat)) (cs : List (Array UInt64)),
    l.mapM (fun p => foRWords s!"distinct: es[{p.2}]" n p.1) = .ok cs →
      cs = l.map (fun p => raw .long n p.1) ∧ ∀ p ∈ l, (raw .long n p.1).size = n.toNat
  | [], cs, h => by cases h; simp
  | p :: l, cs, h => by
    rw [List.mapM_cons] at h
    cases ha : foRWords s!"distinct: es[{p.2}]" n p.1 with
    | error m => rw [ha] at h; cases h
    | ok a =>
      cases hb : l.mapM (fun p => foRWords s!"distinct: es[{p.2}]" n p.1) with
      | error m => rw [ha, hb] at h; cases h
      | ok bs =>
        rw [ha, hb] at h; cases h
        obtain ⟨rfl, hs⟩ := foRWords_raw _ _ _ _ ha
        obtain ⟨rfl, hr⟩ := mapM_foRWords n l bs hb
        exact ⟨rfl, by simpa [hs] using hr⟩

/-- An answer of `kdistinct` is `distinctWords` of the words `Enc.raw` reads from its columns, `n` a column, encoded
as `wordsFoR`. -/
theorem kdistinct_words (n : USize) (es : List Enc) (k : Nat) (o : Enc) (h : kdistinct n es = .ok (k, o)) :
    ∃ ws : Array UInt64, distinctWords n.toNat (es.map (raw .long n)) = .ok (k, ws) ∧
      (∀ x ∈ es.map (raw .long n), x.size = n.toNat) ∧
      o = wordsFoR ws := by
  unfold kdistinct at h
  cases hc : es.zipIdx.mapM (fun p => foRWords s!"distinct: es[{p.2}]" n p.1) with
  | error s => simp [hc, bind, Except.bind] at h
  | ok cs =>
    obtain ⟨rfl, hs⟩ := mapM_foRWords n _ cs hc
    have hm : es.zipIdx.map (fun p => raw .long n p.1) = es.map (raw .long n) := by
      rw [← List.zipIdx_map_fst 0 es, List.map_map]; simp [List.zipIdx_map_fst]
    rw [hm] at hc
    cases hw : distinctWords n.toNat (es.map (raw .long n)) with
    | error s => simp [hc, hw, bind, Except.bind] at h
    | ok kw =>
      obtain ⟨k', ws⟩ := kw
      simp only [hc, hw, bind, Except.bind, pure, Except.pure] at h
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj h)
      refine ⟨ws, rfl, fun x hx => ?_, rfl⟩
      rw [← hm] at hx
      obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hx
      exact hs p hp

/-- **`distinct_first`** (design §4): an answer of `kdistinct` is the `foR` of `k` words `ws`, each a row of the
columns read by `Enc.raw` that starts a run of equal rows (row 0, or one that differs from the row before), strictly
ascending: on a sorted input, the first occurrence of each row, in input order. -/
theorem distinct_first (n : USize) (es : List Enc) (k : Nat) (o : Enc) (h : kdistinct n es = .ok (k, o)) :
    let row := fun q => (es.map (raw .long n)).map (·[q]?.getD 0)
    ∃ ws : Array UInt64,
      o = wordsFoR ws ∧
      ws.size = k ∧
      (∀ j (hj : j < ws.size), ws[j].toNat < n.toNat ∧ (ws[j].toNat = 0 ∨ row ws[j].toNat ≠ row (ws[j].toNat - 1))) ∧
      ∀ j j' (hj : j < ws.size) (hj' : j' < ws.size), j < j' → ws[j] < ws[j'] := by
  obtain ⟨ws, hw, hx, ho⟩ := kdistinct_words n es k o h
  obtain ⟨a, b, c, -⟩ := distinctWords_spec n.toNat (usize_lt n) _ hx k ws hw
  exact ⟨ws, ho, a, b, c⟩

/-- **`distinct_cover`** (design §4): every row `i` of the columns read by `Enc.raw` has a word `ws[j] ≤ i` of the
answer, and every row from `ws[j]` to `i` equals row `i`: no row is lost, and each lies in the run its start names. -/
theorem distinct_cover (n : USize) (es : List Enc) (k : Nat) (o : Enc) (h : kdistinct n es = .ok (k, o)) :
    let row := fun q => (es.map (raw .long n)).map (·[q]?.getD 0)
    ∃ ws : Array UInt64,
      o = wordsFoR ws ∧
      ws.size = k ∧
      ∀ i < n.toNat, ∃ j, ∃ hj : j < ws.size, ws[j].toNat ≤ i ∧ ∀ q, ws[j].toNat ≤ q → q ≤ i → row q = row i := by
  obtain ⟨ws, hw, hx, ho⟩ := kdistinct_words n es k o h
  obtain ⟨a, -, -, d⟩ := distinctWords_spec n.toNat (usize_lt n) _ hx k ws hw
  exact ⟨ws, ho, a, d⟩

end Rel.Verify
