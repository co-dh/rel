import Rel.Kernel.Gather
import Rel.KernelSpec.Asc
-- `Asc` for `ascGrade_spec`, the law of the composition's sort step; it imports `Scatter`'s `scatterWords_spec`

/-! `gather`'s laws (design §4: `out[i] = e[ix[i]]`), on the words `Enc.raw` reads from its arguments:
`gatherWords_eq`, the composition concat → asc → scan fill → scatter equals the fused one-read-per-row form that
`crate/src/gather.rs` runs, and `raw_kgather`, the law `raw_permute` of PLAN 6.6. -/

namespace Rel.Verify
open Rel.Kernel Ext.Enc

/-- The lexicographic order on a row's `(key, tag, idx)`: the order `compose` needs of the sorted rows. -/
private def rowLe (a b : GatherRow) : Bool :=
  a.1 < b.1 || (a.1 == b.1 && (a.2.1 < b.2.1 || (a.2.1 == b.2.1 && a.2.2.1 ≤ b.2.2.1)))

/-- Row `t` of the concatenation: a source row below `es.size`, a query row from there. -/
private theorem rows_get (is es : Array UInt64) (t : Nat) (ht : t < (gatherRows is es).length) :
    (t < es.size ∧ (gatherRows is es)[t] = (t, 0, t, es[t]?.getD 0)) ∨
      (es.size ≤ t ∧ (gatherRows is es)[t] = ((is[t - es.size]?.getD 0).toNat, 1, t - es.size, 0)) := by
  by_cases h : t < es.size
  · exact .inl ⟨h, by simp [gatherRows, h]⟩
  · exact .inr ⟨by omega, by simp [gatherRows, List.getElem_append, h]⟩

/-- `gatherAsc` is a `rowLe`-sorted permutation of the rows: `ascGrade_spec` on `key` and `tag`, whose ties keep row
order, and row order within one `(key, tag)` is `idx` order. -/
private theorem gatherAsc_spec (is es : Array UInt64) (he : es.size < 2 ^ 64) :
    (gatherAsc (gatherRows is es)).Perm (gatherRows is es) ∧
      (gatherAsc (gatherRows is es)).Pairwise fun a b => rowLe a b := by
  obtain ⟨hp, hs⟩ := ascGrade_spec (gatherRows is es).length
    [((gatherRows is es).map (·.1.toUInt64)).toArray, ((gatherRows is es).map (·.2.1.toUInt64)).toArray]
  refine ⟨(hp.map _).trans (.of_eq (List.ext_getElem (by simp) fun n h1 h2 => by simp [List.getElem?_eq_getElem h2])), ?_⟩
  refine List.pairwise_map.2 (hs.imp_of_mem fun {i j} hi hj hij => ?_)
  have hi' := List.mem_range.1 (hp.mem_iff.1 hi)
  have hj' := List.mem_range.1 (hp.mem_iff.1 hj)
  obtain ⟨h1, h2⟩ := hij
  simp only [lexLe, List.getElem?_toArray, List.getElem?_map, List.getElem?_eq_getElem hi',
    List.getElem?_eq_getElem hj', Option.map_some, Option.getD_some, Bool.and_true, Bool.or_eq_true,
    Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, UInt64.lt_iff_toNat_lt, ← UInt64.toNat_inj,
    Nat.toUInt64_eq, UInt64.toNat_ofNat'] at h1 h2 ⊢
  have bi := UInt64.toNat_lt (is[i - es.size]?.getD 0)
  have bj := UInt64.toNat_lt (is[j - es.size]?.getD 0)
  rcases rows_get is es i hi' with ⟨a1, a2⟩ | ⟨a1, a2⟩ <;> rcases rows_get is es j hj' with ⟨b1, b2⟩ | ⟨b1, b2⟩ <;>
    rw [a2, b2] at h1 h2 ⊢ <;>
    simp only [rowLe, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, Decidable.imp_iff_not_or,
      Nat.lt_irrefl, Nat.zero_mod, and_true, true_and, or_true, false_or] at h1 h2 ⊢ <;>
    omega

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

/-- The composition on any sorted permutation `L` of the rows (`gatherAsc` is one): each query row's filled value is
the source row its index names, written to its own cell. -/
private theorem compose (is es : Array UInt64) (hm : is.size < 2 ^ 64)
    (hall : ∀ k < is.size, (is[k]?.getD 0).toNat < es.size) (L : List GatherRow)
    (hP : L.Perm (gatherRows is es)) (hS : L.Pairwise fun a b => rowLe a b) :
    (do
      let F ← (List.range L.length).foldlM (kscanRow .first (L.map fun r => if r.2.1 = 0 then (1 : UInt64) else 0).toArray
        (L.map (·.2.2.2)).toArray []) #[]
      let o ← scatterWords .last (L.map fun r => UInt64.ofNat (if r.2.1 = 0 then is.size else r.2.2.1)).toArray F
        (is.size + 1) 0
      pure (o.extract 0 is.size) : Except String (Array UInt64)) = .ok (is.map fun i => es[i.toNat]?.getD 0) := by
  have hN := hP.nodup_iff.mpr (rows_nodup is es)
  have memL : ∀ {r}, r ∈ L → _ := fun {r} h => mem_rows (hP.mem_iff.mp h)
  have ord : ∀ a b (ha : a < L.length) (hb : b < L.length), a < b → rowLe L[a] L[b] :=
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
      let o ← scatterWords .last D F (is.size + 1) 0
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
    · have := ord p q hp hq h; rw [hLp, hLq] at this; simp [rowLe] at this
  -- every row strictly between them is a query naming the same source
  have hbetween : ∀ t, q < t → t ≤ p → seg[t]?.getD 0 = 0 := by
    intro t a b
    have ht : t < L.length := by omega
    simp only [seg, getD_toArray_map _ _ _ _ ht]
    rcases memL (List.getElem_mem ht) with ⟨h0, hj, hr⟩ | ⟨h1, -⟩
    · exfalso
      have k1 := ord q t hq ht a
      have k2 : rowLe L[t] L[p] := by
        rcases Nat.lt_or_eq_of_le b with b | rfl
        · exact ord t p ht hp b
        · simp [rowLe]
      rw [hLq] at k1; rw [hLp] at k2
      have hkey : L[t].1 = (is[i]?.getD 0).toNat := by
        generalize L[t] = r at k1 k2 h0 ⊢
        obtain ⟨t1, t2, t3, t4⟩ := r
        simp only [rowLe, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at k1 k2 h0
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
theorem gatherWords_eq (is es : Array UInt64) (hm : is.size < 2 ^ 64) (he : es.size < 2 ^ 64)
    (hall : ∀ k < is.size, (is[k]?.getD 0).toNat < es.size) :
    gatherWords is es = .ok (is.map fun i => es[i.toNat]?.getD 0) := by
  unfold gatherWords
  rw [(List.find?_eq_none.mpr fun k hk => by simpa using hall k (List.mem_range.mp hk))]
  exact compose is es hm hall _ (gatherAsc_spec is es he).1 (gatherAsc_spec is es he).2

/-- An index not below `es.size` is `gatherWords`' error, never a fill. -/
theorem gatherWords_error (is es : Array UInt64) (k : Nat) (hk : k < is.size) (h : es.size ≤ (is[k]?.getD 0).toNat) :
    ∃ s, gatherWords is es = .error s := by
  unfold gatherWords
  cases hf : (List.range is.size).find? fun k => es.size ≤ (is[k]?.getD 0).toNat with
  | some k' => exact ⟨_, rfl⟩
  | none => exact absurd (by simpa using List.find?_eq_none.mp hf k (List.mem_range.mpr hk)) (by omega)

/-- Design §4's `gather` law (`raw_permute`): an answer of `kgather` is `wordsFoR` of `es[is[i]]` for each of the `m`
words `is` that `Enc.raw` reads from `ix`, `es` being the `n` words it reads from `e`; every index is below `n`. -/
theorem raw_kgather (m : USize) (ix : Enc) (n : USize) (e : Enc) (o : Enc) (h : kgather m ix n e = .ok o) :
    let is := raw .i64 m ix
    let es := raw .i64 n e
    is.size = m.toNat ∧ es.size = n.toNat ∧ (∀ k < m.toNat, (is[k]?.getD 0).toNat < n.toNat) ∧
      o = wordsFoR (is.map fun i => es[i.toNat]?.getD 0) := by
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
      generalize raw .i64 m ix = is at h hisz ⊢
      generalize raw .i64 n e = es at h hesz ⊢
      have hall : ∀ k < m.toNat, (is[k]?.getD 0).toNat < n.toNat := by
        intro k hk
        refine Nat.lt_of_not_le fun hle => ?_
        obtain ⟨s, hs⟩ := gatherWords_error is es k (by omega) (by omega)
        simp [hs, Functor.map, Except.map] at h
      have hm : is.size < 2 ^ 64 := hisz ▸ Nat.lt_of_lt_of_le m.toNat_lt_size USize.size_le
      have he : es.size < 2 ^ 64 := hesz ▸ Nat.lt_of_lt_of_le n.toNat_lt_size USize.size_le
      rw [gatherWords_eq is es hm he fun k hk => by have := hall k (by omega); omega] at h
      simp only [Functor.map, Except.map] at h
      exact ⟨hisz, hesz, hall, (Except.ok.inj h).symm⟩

/-- Law G2 (PLAN 6.13): gathering from the positions `e = pos` answers the indices themselves, `e[ix[i]] = ix[i]`; so a
caller holding `pos` as the source skips the call, and `crate/src/gather.rs`'s `of_pos` only checks the bounds. -/
theorem kgather_pos_e {m n : USize} {ix o : Enc} (h : kgather m ix n .pos = .ok o) : o = wordsFoR (raw .i64 m ix) := by
  obtain ⟨hs, -, hb, rfl⟩ := raw_kgather m ix n .pos o h
  congr 1
  apply Array.ext (by simp)
  intro k h1 h2
  have hk := hb k (by simpa [hs] using h2)
  simp only [Array.getElem?_eq_getElem h2, Option.getD_some] at hk
  have hp : raw .i64 n (.pos : Enc) = (Array.range n.toNat).map UInt64.ofNat := rfl
  simp [hp, Array.getElem?_range, hk]

/-- Law G1 (PLAN 6.13): gathering at the positions `ix = pos` answers the first `m` words of `e`, every one of them
when `m = n`; so a caller holding `pos` as the index skips the call. -/
theorem kgather_pos_ix {m n : USize} {e o : Enc} (h : kgather m .pos n e = .ok o) :
    m.toNat ≤ n.toNat ∧ o = wordsFoR ((raw .i64 n e).extract 0 m.toNat) := by
  obtain ⟨hs, he, hb, rfl⟩ := raw_kgather m .pos n e o h
  have hm : m.toNat < 2 ^ 64 := Nat.lt_of_lt_of_le m.toNat_lt_size USize.size_le
  -- row `k` of `pos` is `k`, and the last row `m - 1` is below `n`
  have hrow : ∀ k < m.toNat, ((raw .i64 m (.pos : Enc))[k]?.getD 0).toNat = k := fun k hk => by
    simp [raw, Array.getElem?_range, hk, Nat.mod_eq_of_lt (Nat.lt_trans hk hm)]
  have hle : m.toNat ≤ n.toNat := by
    rcases Nat.eq_zero_or_pos m.toNat with h0 | h0
    · omega
    · have := hb (m.toNat - 1) (by omega); rw [hrow _ (by omega)] at this; omega
  refine ⟨hle, congrArg wordsFoR (Array.ext (by simp [hs, he, hle]) fun k h1 h2 => ?_)⟩
  have hk : k < m.toNat := by simpa [hs] using h1
  have := hrow k hk
  rw [Array.getElem?_eq_getElem (by omega), Option.getD_some] at this
  simp [Array.getElem_map, this, Array.getElem_extract, Array.getElem?_eq_getElem (by omega : k < (raw .i64 n e).size)]

end Rel.Verify
