import Rel.Kernel.Gather
import Rel.KernelSpec.Scatter
-- `Scatter` for `scatterWords_spec`, the law of the composition's `scatter` step

/-! `gather`'s laws (design §4: `out[i] = e[ix[i]]`), on the words `Enc.raw` reads from its arguments:
`gatherWords_eq`, the composition concat → asc → scan fill → scatter equals the fused one-read-per-row form that
`crate/src/gather.rs` runs, and `raw_kgather`, the law `raw_permute` of PLAN 6.6. -/

namespace Rel.Verify
open Rel.Kernel Ext.Enc

private theorem rowLe_trans (a b c : GatherRow) (h₁ : a.le b) (h₂ : b.le c) : a.le c := by
  obtain ⟨a1, a2, a3, a4⟩ := a; obtain ⟨b1, b2, b3, b4⟩ := b; obtain ⟨c1, c2, c3, c4⟩ := c
  simp only [GatherRow.le, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at *; omega

private theorem rowLe_total (a b : GatherRow) (h : ¬ a.le b) : b.le a := by
  obtain ⟨a1, a2, a3, a4⟩ := a; obtain ⟨b1, b2, b3, b4⟩ := b
  simp only [GatherRow.le, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at *; omega

private theorem ins_perm (x : GatherRow) : ∀ l, (GatherRow.ins x l).Perm (x :: l)
  | [] => .refl _
  | y :: ys => by
    unfold GatherRow.ins; split
    · exact .refl _
    · exact ((ins_perm x ys).cons y).trans (.swap x y ys)

private theorem asc_perm : ∀ l, (GatherRow.asc l).Perm l
  | [] => .refl _
  | x :: xs => (ins_perm x _).trans ((asc_perm xs).cons x)

private theorem ins_sorted (x : GatherRow) : ∀ l, l.Pairwise (fun a b => a.le b) →
    (GatherRow.ins x l).Pairwise (fun a b => a.le b)
  | [] => fun _ => List.pairwise_singleton _ _
  | y :: ys => fun h => by
    rw [List.pairwise_cons] at h
    unfold GatherRow.ins; split
    · rename_i hxy
      refine List.Pairwise.cons (fun z hz => ?_) (List.Pairwise.cons h.1 h.2)
      rcases List.mem_cons.mp hz with rfl | hz
      · exact hxy
      · exact rowLe_trans _ _ _ hxy (h.1 z hz)
    · rename_i hxy
      refine List.Pairwise.cons (fun z hz => ?_) (ins_sorted x ys h.2)
      rcases List.mem_cons.mp ((ins_perm x ys).mem_iff.mp hz) with rfl | hz
      · exact rowLe_total _ _ hxy
      · exact h.1 z hz

private theorem asc_sorted : ∀ l, (GatherRow.asc l).Pairwise (fun a b => a.le b)
  | [] => .nil
  | x :: xs => ins_sorted x _ (asc_sorted xs)

/-- The fill `gatherWords` runs: `kscanRow` with no column to fold keeps a segment start's seed and copies the row before
otherwise. -/
private theorem fillFold (seg seed : Array UInt64) : ∀ N, ∃ F, (List.range N).foldlM (kscanRow .first seg seed []) #[] = .ok F ∧
    F.size = N ∧ ∀ p < N, F[p]? = some (if 0 < p ∧ seg[p]?.getD 0 = 0 then F[p-1]?.getD 0 else seed[p]?.getD 0)
  | 0 => ⟨#[], rfl, rfl, fun _ h => absurd h (Nat.not_lt_zero _)⟩
  | N + 1 => by
    obtain ⟨F, hF, hs, hp⟩ := fillFold seg seed N
    refine ⟨F.push (if 0 < N ∧ seg[N]?.getD 0 = 0 then F[N-1]?.getD 0 else seed[N]?.getD 0), ?_, by simp [hs],
      fun p hp' => ?_⟩
    · rw [List.range_succ, List.foldlM_append, hF]; rfl
    · rcases Nat.lt_succ_iff_lt_or_eq.mp hp' with h | rfl
      · simp [Array.getElem?_push, hs, show p ≠ N by omega, show p - 1 ≠ N by omega, hp p h]
      · subst hs
        by_cases h0 : 0 < F.size
        · simp [Array.getElem?_push, show F.size - 1 ≠ F.size by omega]
        · simp [h0]

/-- A row `q + d` reached from the segment start `q` through rows that start none holds `q`'s seed. -/
private theorem fillBack (seg seed F : Array UInt64) (N q : Nat)
    (hp : ∀ p < N, F[p]? = some (if 0 < p ∧ seg[p]?.getD 0 = 0 then F[p-1]?.getD 0 else seed[p]?.getD 0))
    (hq : seg[q]?.getD 0 ≠ 0) :
    ∀ d, q + d < N → (∀ t, q < t → t ≤ q + d → seg[t]?.getD 0 = 0) → F[q + d]? = some (seed[q]?.getD 0)
  | 0, h, _ => by rw [Nat.add_zero, hp q (by omega)]; simp [hq]
  | d + 1, h, hs => by
    rw [show q + (d + 1) = q + d + 1 by omega, hp _ (by omega), if_pos ⟨by omega, hs _ (by omega) (by omega)⟩,
      show q + d + 1 - 1 = q + d by omega, fillBack seg seed F N q hp hq d (by omega) fun t a b => hs t a (by omega)]
    rfl

private theorem getD_toArray_map {α : Type} (L : List GatherRow) (f : GatherRow → α) (d : α) (t : Nat)
    (h : t < L.length) : (L.map f).toArray[t]?.getD d = f L[t] := by
  simp [h]

private theorem nodup_idx {L : List GatherRow} (hN : L.Nodup) {a b : Nat} (ha : a < L.length) (hb : b < L.length)
    (h : L[a] = L[b]) : a = b := by
  rcases Nat.lt_trichotomy a b with x | x | x
  · exact absurd h (List.pairwise_iff_getElem.mp hN a b ha hb x)
  · exact x
  · exact absurd h.symm (List.pairwise_iff_getElem.mp hN b a hb ha x)

private theorem rows_nodup (is es : Array UInt64) : (gatherRows is es).Nodup := by
  unfold gatherRows
  refine List.nodup_append.mpr ⟨List.Pairwise.map _ (fun a b hab h => hab (Prod.mk.inj h).1) List.nodup_range,
    List.Pairwise.map _ (fun a b hab h => hab (Prod.mk.inj (Prod.mk.inj (Prod.mk.inj h).2).2).1) List.nodup_range, ?_⟩
  intro a ha b hb hab
  simp only [List.mem_map, List.mem_range] at ha hb
  obtain ⟨j, -, rfl⟩ := ha; obtain ⟨i, -, rfl⟩ := hb
  simpa using congrArg (·.2.1) hab

private theorem mem_rows {is es : Array UInt64} {r : GatherRow} (h : r ∈ gatherRows is es) :
    (r.2.1 = 0 ∧ r.1 < es.size ∧ r = (r.1, 0, r.1, es[r.1]?.getD 0)) ∨
    (r.2.1 = 1 ∧ r.2.2.1 < is.size ∧ r = ((is[r.2.2.1]?.getD 0).toNat, 1, r.2.2.1, 0)) := by
  simp only [gatherRows, List.mem_append, List.mem_map, List.mem_range] at h
  rcases h with ⟨j, hj, rfl⟩ | ⟨i, hi, rfl⟩
  · exact .inl ⟨rfl, hj, rfl⟩
  · exact .inr ⟨rfl, hi, rfl⟩

/-- The composition on any sorted permutation `L` of the rows (`GatherRow.asc` is one): each query row's filled value is
the source row its index names, written to its own cell. -/
private theorem compose (is es : Array UInt64) (hm : is.size < 2 ^ 64)
    (hall : ∀ k < is.size, (is[k]?.getD 0).toNat < es.size) (L : List GatherRow)
    (hP : L.Perm (gatherRows is es)) (hS : L.Pairwise fun a b => a.le b) :
    (do
      let F ← (List.range L.length).foldlM (kscanRow .first (L.map fun r => if r.2.1 = 0 then (1 : UInt64) else 0).toArray
        (L.map (·.2.2.2)).toArray []) #[]
      let o ← scatterWords (L.map fun r => UInt64.ofNat (if r.2.1 = 0 then is.size else r.2.2.1)).toArray F
        (is.size + 1) 0
      pure (o.extract 0 is.size) : Except String (Array UInt64)) = .ok (is.map fun i => es[i.toNat]?.getD 0) := by
  have hN := hP.nodup_iff.mpr (rows_nodup is es)
  have memL : ∀ {r}, r ∈ L → _ := fun {r} h => mem_rows (hP.mem_iff.mp h)
  have ord : ∀ a b (ha : a < L.length) (hb : b < L.length), a < b → L[a].le L[b] :=
    fun a b ha hb hab => List.pairwise_iff_getElem.mp hS a b ha hb hab
  let seg := (L.map fun r => if r.2.1 = 0 then (1 : UInt64) else 0).toArray
  let seed := (L.map (·.2.2.2)).toArray
  let D := (L.map fun r => UInt64.ofNat (if r.2.1 = 0 then is.size else r.2.2.1)).toArray
  obtain ⟨F, hF, hFs, hFp⟩ := fillFold seg seed L.length
  -- a cell's destination as `scatterWords` reads it
  have hD : ∀ t (ht : t < L.length), (D[t]?.getD 0).toNat = if L[t].2.1 = 0 then is.size else L[t].2.2.1 := by
    intro t ht
    simp only [D, getD_toArray_map _ _ _ _ ht]
    rcases memL (List.getElem_mem ht) with ⟨h0, -⟩ | ⟨h1, hi, -⟩
    · simp only [h0, if_true]; exact UInt64.toNat_ofNat_of_lt' hm
    · simp only [h1, Nat.one_ne_zero, if_false]; exact UInt64.toNat_ofNat_of_lt' (Nat.lt_trans hi hm)
  have hDsz : D.size = L.length := by simp [D]
  obtain ⟨hx, hw⟩ := scatterWords_spec D F (is.size + 1) 0
  have hok : ∀ k < D.size, (D[k]?.getD 0).toNat < is.size + 1 := by
    intro t ht
    rw [hDsz] at ht
    rw [hD t ht]
    rcases memL (List.getElem_mem ht) with ⟨h0, -⟩ | ⟨h1, hi, -⟩
    · simp [h0]
    · simp only [h1, Nat.one_ne_zero, if_false]; omega
  obtain ⟨o, ho⟩ := hx.mpr hok
  obtain ⟨hos, -, hlast⟩ := hw o ho
  show (do
      let F ← (List.range L.length).foldlM (kscanRow .first seg seed []) #[]
      let o ← scatterWords D F (is.size + 1) 0
      pure (o.extract 0 is.size) : Except String (Array UInt64)) = _
  rw [hF]; simp only [bind, Except.bind]; rw [ho]; simp only [pure, Except.pure, Except.ok.injEq]
  apply Array.ext (by simp [hos])
  intro i h1 h2
  simp only [Array.size_map] at h2
  simp only [Array.getElem_extract, Nat.zero_add, Array.getElem_map]
  -- the query row `i` at position `p`, its source row at `q`
  have hk := hall i h2
  have hQ : ((is[i]?.getD 0).toNat, 1, i, (0 : UInt64)) ∈ L :=
    hP.mem_iff.mpr (by simp only [gatherRows, List.mem_append, List.mem_map, List.mem_range]; exact .inr ⟨i, h2, rfl⟩)
  have hSrc : ((is[i]?.getD 0).toNat, 0, (is[i]?.getD 0).toNat, es[(is[i]?.getD 0).toNat]?.getD 0) ∈ L :=
    hP.mem_iff.mpr (by simp only [gatherRows, List.mem_append, List.mem_map, List.mem_range]; exact .inl ⟨_, hk, rfl⟩)
  obtain ⟨p, hp, hLp⟩ := List.getElem_of_mem hQ
  obtain ⟨q, hq, hLq⟩ := List.getElem_of_mem hSrc
  have hqp : q < p := by
    rcases Nat.lt_trichotomy q p with h | rfl | h
    · exact h
    · rw [hLp] at hLq; simp at hLq
    · have := ord p q hp hq h; rw [hLp, hLq] at this; simp [GatherRow.le] at this
  -- every row strictly between them is a query naming the same source
  have hbetween : ∀ t, q < t → t ≤ p → seg[t]?.getD 0 = 0 := by
    intro t a b
    have ht : t < L.length := by omega
    simp only [seg, getD_toArray_map _ _ _ _ ht]
    rcases memL (List.getElem_mem ht) with ⟨h0, hj, hr⟩ | ⟨h1, -⟩
    · exfalso
      have k1 := ord q t hq ht a
      have k2 : L[t].le L[p] := by
        rcases Nat.lt_or_eq_of_le b with b | rfl
        · exact ord t p ht hp b
        · simp [GatherRow.le]
      rw [hLq] at k1; rw [hLp] at k2
      have hkey : L[t].1 = (is[i]?.getD 0).toNat := by
        generalize L[t] = r at k1 k2 h0 ⊢
        obtain ⟨t1, t2, t3, t4⟩ := r
        simp only [GatherRow.le, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at k1 k2 h0
        omega
      have : L[t] = L[q] := by rw [hLq, hr, hkey]
      exact absurd (nodup_idx hN _ _ this) (by omega)
    · simp [h1]
  have hseg : seg[q]?.getD 0 ≠ 0 := by simp only [seg]; rw [getD_toArray_map _ _ _ _ hq, hLq]; simp
  have hfill := fillBack seg seed F L.length q hFp hseg (p - q) (by omega) (fun t a b => hbetween t a (by omega))
  rw [show q + (p - q) = p by omega] at hfill
  -- no later row names cell `i`
  have hpi : (D[p]?.getD 0).toNat = i := by rw [hD p hp, hLp]; simp
  have hcell := hlast p (by omega) fun k' a b hc => by
    change (D[k']?.getD 0).toNat = (D[p]?.getD 0).toNat at hc
    rw [hDsz] at b
    rw [hD k' b, hpi] at hc
    rcases memL (List.getElem_mem b) with ⟨h0, -⟩ | ⟨h1, hi, hr⟩
    · simp [h0] at hc; omega
    · simp only [h1, Nat.one_ne_zero, if_false] at hc
      have : L[k'] = L[p] := by rw [hLp, hr, hc]
      exact absurd (nodup_idx hN _ _ this) (by omega)
  change o[(D[p]?.getD 0).toNat]? = some (F[p]?.getD 0) at hcell
  rw [hpi, hfill] at hcell
  have := (Array.getElem?_eq_some_iff.mp hcell).2
  rw [this]
  simp only [Option.getD_some, seed]
  rw [getD_toArray_map _ _ _ _ hq, hLq]
  simp [h2]

/-- **gather = its composition** (design §4's table): when every index is below `es.size`, the composition
`gatherWords` runs — concatenate, `asc`, fill forward, `scatter` — answers the fused form, one read per row. -/
theorem gatherWords_eq (is es : Array UInt64) (hm : is.size < 2 ^ 64)
    (hall : ∀ k < is.size, (is[k]?.getD 0).toNat < es.size) :
    gatherWords is es = .ok (is.map fun i => es[i.toNat]?.getD 0) := by
  unfold gatherWords
  rw [(List.find?_eq_none.mpr fun k hk => by simpa using hall k (List.mem_range.mp hk))]
  exact compose is es hm hall _ (asc_perm _) (asc_sorted _)

/-- An index not below `es.size` is `gatherWords`' error, never a fill. -/
theorem gatherWords_error (is es : Array UInt64) (k : Nat) (hk : k < is.size) (h : es.size ≤ (is[k]?.getD 0).toNat) :
    ∃ s, gatherWords is es = .error s := by
  unfold gatherWords
  cases hf : (List.range is.size).find? fun k => es.size ≤ (is[k]?.getD 0).toNat with
  | some k' => exact ⟨_, rfl⟩
  | none => exact absurd (by simpa using List.find?_eq_none.mp hf k (List.mem_range.mpr hk)) (by omega)

/-- Design §4's `gather` law (`raw_permute`): an answer of `kgather` is the `foR` that `Coc.encodeAt` at `lgEnc` writes
of `es[is[i]]` for each of the `m` words `is` that `Enc.raw` reads from `ix`, `es` being the `n` words it reads from
`e`; every index is below `n`. -/
theorem raw_kgather (m : USize) (ix : Enc) (n : USize) (e : Enc) (o : Enc) (h : kgather m ix n e = .ok o) :
    let is := raw .long m ix
    let es := raw .long n e
    let p := Coc.encodeAt Column.lgEnc 8 ((is.map fun i => es[i.toNat]?.getD 0).foldl (init := .empty)
        fun acc w => Column.pushBits acc w 8)
    is.size = m.toNat ∧ es.size = n.toNat ∧ (∀ k < m.toNat, (is[k]?.getD 0).toNat < n.toNat) ∧ o = .foR p.1 p.2 := by
  dsimp only
  unfold kgather at h
  cases hi : foRWords "gather: ix" m ix with
  | error s => simp [hi, bind, Except.bind] at h
  | ok is =>
    cases he : foRWords "gather: e" n e with
    | error s => simp [hi, he, bind, Except.bind] at h
    | ok es =>
      simp only [hi, he, bind, Except.bind] at h
      obtain ⟨rfl, hisz⟩ := foRWords_raw _ _ _ _ hi
      obtain ⟨rfl, hesz⟩ := foRWords_raw _ _ _ _ he
      generalize raw .long m ix = is at h hisz ⊢
      generalize raw .long n e = es at h hesz ⊢
      have hall : ∀ k < m.toNat, (is[k]?.getD 0).toNat < n.toNat := by
        intro k hk
        refine Nat.lt_of_not_le fun hle => ?_
        obtain ⟨s, hs⟩ := gatherWords_error is es k (by omega) (by omega)
        simp [hs] at h
      have hm : is.size < 2 ^ 64 := hisz ▸ Nat.lt_of_lt_of_le m.toNat_lt_size USize.size_le
      rw [gatherWords_eq is es hm fun k hk => by have := hall k (by omega); omega] at h
      simp only [pure, Except.pure] at h
      have h8 : USize.ofNat32 8 (by decide) = 8 := USize.toNat_inj.mp (by simp)
      rw [h8] at h
      exact ⟨hisz, hesz, hall, (Except.ok.inj h).symm⟩

end Rel.Verify
