import Rel.Run.SetOps
import Rel.RepCols
import Rel.Run.CRelFoldDef

/-! The laws of `Tab.union`, `Tab.inter`, `Tab.diff` and `Tab.le` (`Rel/Run/SetOps.lean`), from the five kernels' laws
and `Tab.canon`'s (`Rel/RepCanon.lean`). -/

namespace Rel
open Rel.Ext Rel.Kernel Rel.Verify

/-! ## WHERE -/

/-- **`whereCol m b` answers the positions of `b`'s `1` words, ascending**, `b` holding `0`/`1` words: `d = b · (i + 1)`
and a `0` cell, sorted (`asc_perm`, ascending by `kseen_sorted` since the signed code of a word below `2^63` is the word
`+ 2^63`); the first rows of its runs (`firsts_spec`) are the `0` run's, then each kept position alone. -/
theorem whereCol_spec {m K : USize} {b o : Enc} (h : whereCol m b = .ok (K, o))
    (hb : ∀ i < m.toNat, (Enc.raw .i64 m b)[i]?.getD 0 < 2) :
    (Enc.raw .i64 K o).toList.map UInt64.toNat =
      (List.range m.toNat).filter fun i => (Enc.raw .i64 m b)[i]?.getD 0 ≠ 0 := by
  unfold whereCol at h
  have hB : m.toNat < min (USize.size - 1) (2 ^ 63) := by
    refine Classical.byContradiction fun hn => ?_; simp only [hn, if_false] at h; cases h
  simp only [hB, if_true, bind, Except.bind, Functor.map, Except.map] at h
  repeat (split at h; · cases h)
  rename_i _ s hs _ d hd _ e he _ vp hvp _ r hr _ sh hsh _ fs hfs _ o' ho'
  obtain ⟨vs, p⟩ := vp
  obtain ⟨c, g, f⟩ := r
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj h).symm
  dsimp only at hr hsh hfs ho'
  have hU : USize.size ≤ 2 ^ 64 := by rcases USize.size_eq with h | h <;> omega
  have hM' : (m.toNat + 1).toUSize.toNat = m.toNat + 1 := USize.toNat_ofNat_of_lt' (by omega)
  have hc64 : ∀ a, a < m.toNat + 1 → a.toUInt64.toNat = a := fun a ha => by simp; omega
  -- `d[i] = b[i] · (i + 1)`
  have hdv : ∀ i < m.toNat, (Enc.raw .i64 m d)[i]?.getD 0 = (Enc.raw .i64 m b)[i]?.getD 0 * (i.toUInt64 + 1) := by
    intro i hi
    have := (colMap_raw hd).2.2.2 i hi
    rw [shiftCol_raw hs i hi] at this
    simp only [Op.eval, Except.ok.injEq] at this
    exact this.symm
  -- `e` is `d` and a `0` cell
  obtain ⟨-, -, -, hws, -, hfill, hlast⟩ := raw_scatter m .pos d _ 0 e he
  have hpos : ∀ k < m.toNat, (Enc.raw .i64 m (.pos : Enc))[k]?.getD 0 = k.toUInt64 := fun k hk => by
    simp only [Enc.raw, Array.getElem?_map, Array.getElem?_range, hk, if_true, Option.map_some, Option.getD_some]
  have ev_lt : ∀ q < m.toNat,
      (Enc.raw .i64 (m.toNat + 1).toUSize e)[q]?.getD 0 = (Enc.raw .i64 m d)[q]?.getD 0 := fun q hq => by
    have := hlast q hq fun k' h1 h2 e' => by
      rw [hpos k' h2, hpos q hq] at e'
      have := congrArg UInt64.toNat e'; rw [hc64 _ (by omega), hc64 _ (by omega)] at this; omega
    rw [hpos q hq, hc64 _ (by omega)] at this
    rw [this, Option.getD_some]
  have ev_m : (Enc.raw .i64 (m.toNat + 1).toUSize e)[m.toNat]?.getD 0 = 0 := by
    rw [hfill m.toNat (by rw [hM']; omega) fun k hk e' => by rw [hpos k hk, hc64 _ (by omega)] at e'; omega,
      Option.getD_some]
  have hE : ∀ q < m.toNat + 1, ((Enc.raw .i64 (m.toNat + 1).toUSize e)[q]?.getD 0 = 0 ∧
      ¬(q < m.toNat ∧ (Enc.raw .i64 m b)[q]?.getD 0 ≠ 0)) ∨
      (((Enc.raw .i64 (m.toNat + 1).toUSize e)[q]?.getD 0).toNat = q + 1 ∧ q < m.toNat ∧
        (Enc.raw .i64 m b)[q]?.getD 0 ≠ 0) := by
    intro q hq
    by_cases hqm : q < m.toNat
    · rw [ev_lt q hqm, hdv q hqm]
      have hb2 : ((Enc.raw .i64 m b)[q]?.getD 0).toNat < 2 := hb q hqm
      rcases (show ((Enc.raw .i64 m b)[q]?.getD 0).toNat = 0 ∨ ((Enc.raw .i64 m b)[q]?.getD 0).toNat = 1 by omega)
        with h0 | h1
      · have : (Enc.raw .i64 m b)[q]?.getD 0 = 0 := UInt64.toNat_inj.1 h0
        left; rw [this]; simp
      · have : (Enc.raw .i64 m b)[q]?.getD 0 = 1 := UInt64.toNat_inj.1 h1
        right; rw [this]; refine ⟨?_, hqm, by decide⟩; simp; omega
    · left; rw [show q = m.toNat by omega, ev_m]; exact ⟨rfl, fun h => absurd h.1 (by omega)⟩
  -- the sorted words `ws`: `ws[q] = e[ps[q]]`
  obtain ⟨ps, hp, hperm, hvl, hcol⟩ := asc_perm _ _ _ _ hvp
  have hlen : ps.length = m.toNat + 1 := by have := hperm.length_eq; rw [List.length_range, hM'] at this; exact this
  have hpsl : ∀ q (hq : q < ps.length), ps[q] < m.toNat + 1 := fun q hq => by
    have := List.mem_range.1 (hperm.mem_iff.1 (List.getElem_mem hq)); omega
  rcases vs with _ | ⟨v0, _ | ⟨_, _⟩⟩ <;> simp at hvl
  obtain ⟨ws, rfl, hwsz, hwq⟩ := hcol 0 _ v0 rfl rfl
  rw [hM'] at hwsz
  simp only [List.map_cons, List.map_nil, List.zip_cons_cons, List.zip_nil_right] at hr
  have hwr : Enc.raw .i64 (m.toNat + 1).toUSize (wordsFoR ws) = ws := (wordsFoR_closed ws (by rw [hM', hwsz])).2.1
  have hsv : ∀ q (hq : q < ps.length), ws[q]?.getD 0 = (Enc.raw .i64 (m.toNat + 1).toUSize e)[ps[q]]?.getD 0 :=
    fun q hq => by rw [hwq q hq]
  have hbound : ∀ q < m.toNat + 1, (ws[q]?.getD 0).toNat < 2 ^ 63 := fun q hq => by
    rw [hsv q (by omega)]
    rcases hE _ (hpsl q (by omega)) with h | h
    · rw [h.1]; decide
    · have := hpsl q (by omega); omega
  have hcode : ∀ v : UInt64, v.toNat < 2 ^ 63 → (ordCode 8 false true v).toNat = v.toNat + 2 ^ 63 := fun v hv => by
    have := ordKey_signed (w := 8) (by omega) (by omega) v
    have hs : sx 8 v = v.toNat := by unfold sx; simp; omega
    rw [hs] at this
    change ((ordCode 8 false true v).toNat : Int) = _ at this
    omega
  have hkey : ∀ q < m.toNat + 1, seenKey (m.toNat + 1).toUSize [(.atom .i64, wordsFoR ws)] q =
      [ordCode 8 false true (ws[q]?.getD 0)] := fun q hq => by
    have hq' : q < ws.size := by omega
    simp only [seenKey, ascKeys, ascKey, List.append_nil, List.map_cons, List.map_nil, hwr, Array.getElem?_map, Array.getElem?_eq_getElem hq',
      Option.map_some, Option.getD_some]
    rfl
  have hK : ∀ q < m.toNat + 1, ∀ q' < m.toNat + 1,
      seenKey (m.toNat + 1).toUSize [(.atom .i64, wordsFoR ws)] q = seenKey (m.toNat + 1).toUSize [(.atom .i64, wordsFoR ws)] q' ↔
        (ws[q]?.getD 0).toNat = (ws[q']?.getD 0).toNat := by
    intro q hq q' hq'
    rw [hkey q hq, hkey q' hq', List.cons.injEq, and_iff_left rfl, ← UInt64.toNat_inj, hcode _ (hbound q hq),
      hcode _ (hbound q' hq')]
    exact Nat.add_right_cancel_iff
  have hmono1 : ∀ q, q + 1 < m.toNat + 1 → (ws[q]?.getD 0).toNat ≤ (ws[q + 1]?.getD 0).toNat := fun q hq => by
    have hl := kseen_sorted hr q (by rw [hM']; exact hq)
    simp only [ascKeys, ascKey, List.append_nil, List.map_cons, List.map_nil, hwr, lexLe, Array.getElem?_map,
      Array.getElem?_eq_getElem (show q < ws.size by omega), Array.getElem?_eq_getElem (show q + 1 < ws.size by omega),
      Option.map_some, Option.getD_some, Bool.or_eq_true, Bool.and_true, decide_eq_true_eq, beq_iff_eq] at hl
    change ordCode 8 false true _ < ordCode 8 false true _ ∨ ordCode 8 false true _ = ordCode 8 false true _ at hl
    have ha := hbound q (by omega); have hb' := hbound (q + 1) hq
    simp only [Array.getElem?_eq_getElem (show q < ws.size by omega),
      Array.getElem?_eq_getElem (show q + 1 < ws.size by omega), Option.getD_some] at ha hb' ⊢
    rcases hl with hl | hl
    · have := UInt64.lt_iff_toNat_lt.1 hl; rw [hcode _ ha, hcode _ hb'] at this; omega
    · have := congrArg UInt64.toNat hl; rw [hcode _ ha, hcode _ hb'] at this; omega
  have hmono : ∀ q k, q + k < m.toNat + 1 → (ws[q]?.getD 0).toNat ≤ (ws[q + k]?.getD 0).toNat := by
    intro q k
    induction k with
    | zero => intro _; exact Nat.le_refl _
    | succ k ih => intro hk; exact Nat.le_trans (ih (by omega)) (hmono1 (q + k) (by omega))
  -- the first rows `F` of the sorted words' runs
  obtain ⟨hc, -, hf⟩ := kseen_ok hr
  rw [hM'] at hc hf
  have hcl : c ≤ m.toNat + 1 := by rw [hc]; unfold firstsOf; exact Nat.le_trans (List.length_filter_le _ _) (by simp)
  generalize hKf : seenKey (m.toNat + 1).toUSize [(.atom .i64, wordsFoR ws)] = Kf at hc hf hK hkey
  generalize hF : firstsOf Kf (m.toNat + 1) = F at hc hf
  have hsp := firsts_spec Kf (m.toNat + 1); rw [hF] at hsp
  have hFinj : ∀ j j' (hj : j < F.length) (hj' : j' < F.length), Kf F[j] = Kf F[j'] → j = j' := by
    subst hF; exact fun j j' hj hj' => firsts_inj hj hj'
  have hFlt : ∀ j (hj : j < F.length), F[j] < m.toNat + 1 := fun j hj => ((hsp.2.1 _).1 (List.getElem_mem hj)).1
  have h0F : 0 ∈ F := (hsp.2.1 0).2 ⟨by omega, fun q hq => absurd hq (by omega)⟩
  have hF0 : 0 < F.length := List.length_pos_of_mem h0F
  have hF00 : F[0] = 0 := by
    obtain ⟨t, ht, e0⟩ := List.getElem_of_mem h0F
    rcases Nat.eq_zero_or_pos t with rfl | tp
    · exact e0
    · have := List.pairwise_iff_getElem.1 hsp.1 0 t hF0 ht tp; omega
  -- the sorted word at row 0 is `0`: the appended cell is somewhere and `ws` ascends
  have hws0 : (ws[0]?.getD 0).toNat = 0 := by
    obtain ⟨qz, hqz, eqz⟩ := List.getElem_of_mem
      (hperm.mem_iff.2 (List.mem_range.2 (show m.toNat < (m.toNat + 1).toUSize.toNat by omega)))
    have := hmono 0 qz (by omega)
    rw [Nat.zero_add, hsv qz hqz, eqz, ev_m] at this
    simp only [UInt64.toNat_zero] at this; omega
  -- every first row but the first is a kept position
  have hkept : ∀ j (hj : j + 1 < F.length), (ws[F[j + 1]]?.getD 0).toNat = ps[F[j + 1]]?.getD 0 + 1 ∧
      ps[F[j + 1]]?.getD 0 < m.toNat ∧ (Enc.raw .i64 m b)[ps[F[j + 1]]?.getD 0]?.getD 0 ≠ 0 := by
    intro j hj
    have hlt := hFlt _ hj
    have hne : (ws[F[j + 1]]?.getD 0).toNat ≠ (ws[F[0]]?.getD 0).toNat := fun e' =>
      absurd (hFinj _ _ hj hF0 ((hK _ hlt _ (hFlt 0 hF0)).2 e')) (by omega)
    rw [hF00, hws0, hsv _ (by omega)] at hne
    have hpj : F[j + 1] < ps.length := by omega
    rw [hsv _ hpj, List.getElem?_eq_getElem hpj, Option.getD_some]
    rcases hE _ (hpsl (F[j + 1]) hpj) with h' | h'
    · rw [h'.1] at hne; simp at hne
    · exact h'
  have hinc : ∀ j j' (hj : j + 1 < F.length) (hj' : j' + 1 < F.length), j < j' →
      ps[F[j + 1]]?.getD 0 < ps[F[j' + 1]]?.getD 0 := by
    intro j j' hj hj' hjj
    have hlt := List.pairwise_iff_getElem.1 hsp.1 (j + 1) (j' + 1) hj hj' (by omega)
    have hm := hmono F[j + 1] (F[j' + 1] - F[j + 1]) (by have := hFlt _ hj'; omega)
    rw [Nat.add_sub_cancel' (Nat.le_of_lt hlt)] at hm
    have hne : (ws[F[j + 1]]?.getD 0).toNat ≠ (ws[F[j' + 1]]?.getD 0).toNat := fun e' =>
      absurd (hFinj _ _ hj hj' ((hK _ (hFlt _ hj) _ (hFlt _ hj')).2 e')) (by omega)
    have a := (hkept j hj).1; have a' := (hkept j' hj').1
    omega
  -- the answer's words: `o[j] = ps[F[j + 1]]`
  have hK1 : (c - 1).toUSize.toNat = c - 1 := USize.toNat_ofNat_of_lt' (by omega)
  have hcU : c.toUSize.toNat = c := USize.toNat_ofNat_of_lt' (by omega)
  obtain ⟨his1, -, -, hfs'⟩ := raw_kgather _ _ _ _ _ hfs
  obtain ⟨his2, -, -, ho''⟩ := raw_kgather _ _ _ _ _ ho'
  have hrf : Enc.raw .i64 c.toUSize f = (F.map Nat.toUInt64).toArray := by
    rw [hf]; exact (wordsFoR_closed _ (by rw [hcU, hc]; simp)).2.1
  have hrp : Enc.raw .i64 (m.toNat + 1).toUSize p = (ps.map Nat.toUInt64).toArray := by
    rw [hp]; exact (wordsFoR_closed _ (by rw [hM']; simp [hlen])).2.1
  have hrfs : Enc.raw .i64 (c - 1).toUSize fs = (Enc.raw .i64 (c - 1).toUSize sh).map fun i =>
      (Enc.raw .i64 c.toUSize f)[i.toNat]?.getD 0 := by
    rw [hfs', (wordsFoR_closed _ (by rw [Array.size_map, his1])).2.1]
  have hro : Enc.raw .i64 (c - 1).toUSize o = (Enc.raw .i64 (c - 1).toUSize fs).map fun i =>
      (Enc.raw .i64 (m.toNat + 1).toUSize p)[i.toNat]?.getD 0 := by
    rw [ho'', (wordsFoR_closed _ (by rw [Array.size_map, his2])).2.1]
  have hsz : (Enc.raw .i64 (c - 1).toUSize o).size = c - 1 := by rw [hro, Array.size_map, his2, hK1]
  have hel : ∀ j (hj : j + 1 < F.length), ((Enc.raw .i64 (c - 1).toUSize o)[j]?.getD 0).toNat = ps[F[j + 1]]?.getD 0 := by
    intro j hj
    have hsj := shiftCol_raw hsh j (by rw [hK1]; omega)
    have hjs : j < (Enc.raw .i64 (c - 1).toUSize sh).size := by rw [his1, hK1]; omega
    rw [Array.getElem?_eq_getElem hjs, Option.getD_some] at hsj
    have hj1 : (j.toUInt64 + 1).toNat = j + 1 := by simp; omega
    have hFj := hFlt _ hj
    have hpj : F[j + 1] < ps.length := by omega
    rw [hro, Array.getElem?_map, hrfs, Array.getElem?_map, Array.getElem?_eq_getElem hjs, hsj, hrf, hrp]
    simp only [Option.map_some, Option.getD_some, hj1, List.getElem?_toArray, List.getElem?_map,
      List.getElem?_eq_getElem hj, hc64 _ hFj, List.getElem?_eq_getElem hpj, hc64 _ (hpsl _ hpj)]
  -- the answer as a list: ascending, and exactly the kept positions
  have hLlen : ((Enc.raw .i64 (c - 1).toUSize o).toList.map UInt64.toNat).length = c - 1 := by simp [hsz]
  have hLget : ∀ j (hj : j < ((Enc.raw .i64 (c - 1).toUSize o).toList.map UInt64.toNat).length),
      ((Enc.raw .i64 (c - 1).toUSize o).toList.map UInt64.toNat)[j] = ps[F[j + 1]]?.getD 0 := fun j hj => by
    rw [← hel j (by omega), List.getElem_map, Array.getElem_toList, Array.getElem?_eq_getElem (by omega),
      Option.getD_some]
  have hpw : ((Enc.raw .i64 (c - 1).toUSize o).toList.map UInt64.toNat).Pairwise (· < ·) :=
    List.pairwise_iff_getElem.2 fun j j' hj hj' hjj => by
      rw [hLget j hj, hLget j' hj']; exact hinc j j' (by omega) (by omega) hjj
  have hmem : ∀ x, x ∈ (Enc.raw .i64 (c - 1).toUSize o).toList.map UInt64.toNat ↔
      x ∈ (List.range m.toNat).filter fun i => (Enc.raw .i64 m b)[i]?.getD 0 ≠ 0 := by
    intro x
    simp only [List.mem_filter, List.mem_range, decide_eq_true_eq]
    constructor
    · intro hx
      obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.1 hx
      rw [hLget j hj]
      exact (hkept j (by omega)).2
    · intro hx
      rcases hE x (by omega) with h' | h'
      · exact absurd hx h'.2
      obtain ⟨q, hq, eq⟩ := List.getElem_of_mem
        (hperm.mem_iff.2 (List.mem_range.2 (show x < (m.toNat + 1).toUSize.toNat by omega)))
      obtain ⟨hG, -, hGk, -⟩ := hsp.2.2.2.2.2 q (by omega)
      generalize Verify.groupOf Kf (m.toNat + 1) q = G at hG hGk
      have hv := (hK _ (hFlt _ hG) _ (by omega)).1 hGk
      rw [hsv q hq, eq, h'.1] at hv
      obtain ⟨j, rfl⟩ : ∃ j, G = j + 1 := ⟨G - 1, by
        refine (Nat.succ_pred_eq_of_ne_zero fun e0 => ?_).symm
        subst e0; rw [hF00, hws0] at hv; omega⟩
      have a := (hkept j hG).1
      exact List.mem_iff_getElem.2 ⟨j, by omega, by rw [hLget j (by omega)]; omega⟩
  have hnd : ∀ {l : List Nat}, l.Pairwise (· < ·) → l.Nodup := fun h => List.nodup_iff_pairwise_ne.2 (h.imp Nat.ne_of_lt)
  have hpw' := (List.pairwise_lt_range (n := m.toNat)).filter fun i => decide ((Enc.raw .i64 m b)[i]?.getD 0 ≠ 0)
  refine List.Perm.eq_of_pairwise (fun a b _ _ h1 h2 => absurd (Nat.lt_trans h1 h2) (Nat.lt_irrefl _)) hpw hpw'
    (List.perm_iff_count.2 fun a => ?_)
  rw [(hnd hpw).count, (hnd hpw').count]
  simp only [hmem]

/-! ## CONCAT and `∪` -/
namespace Tab
variable {k v : Obj}

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
/-- The five-kernel `∪`, `∩`, `−`, `⊑` of `R` and `S`, each answering `.ok`, against the old `CRel.union`, `CRel.inter`,
`CRel.diff`, `Alg.leC`; the old `∩`/`−` keep `R`'s order, so their answer is compared after `Alg.canonC`. -/
private def setOk {k v : Obj} [BEq k.El] [BEq v.El] (R S : Tab k v) : Bool :=
  let old (c : CRel k v) := c.bind fun t => let c := Alg.canonC t; if c.2 then some c.1.toList else none
  let new (r : Except String (Tab k v)) := match r with | .ok t => some t.toList | .error _ => none
  (new (R.union S)).isSome && (new (R.inter S)).isSome && (new (R.diff S)).isSome && (R.le S).toOption.isSome &&
  new (R.union S) == old (CRel.union (some R) (some S)) && new (R.inter S) == old (CRel.inter (some R) (some S)) &&
  new (R.diff S) == old (CRel.diff (some R) (some S)) &&
  (R.le S).toOption == (let c := Alg.leC R S; if c.2 then some c.1 else none)

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

end Checks

end Rel
