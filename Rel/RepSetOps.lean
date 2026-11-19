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
  have hkey : ∀ q < m.toNat + 1, seenKey (m.toNat + 1).toUSize [(.i64, wordsFoR ws)] q =
      [ordCode 8 false true (ws[q]?.getD 0)] := fun q hq => by
    have hq' : q < ws.size := by omega
    simp only [seenKey, ascKeys, List.map_cons, List.map_nil, hwr, Array.getElem?_map, Array.getElem?_eq_getElem hq',
      Option.map_some, Option.getD_some]
    rfl
  have hK : ∀ q < m.toNat + 1, ∀ q' < m.toNat + 1,
      seenKey (m.toNat + 1).toUSize [(.i64, wordsFoR ws)] q = seenKey (m.toNat + 1).toUSize [(.i64, wordsFoR ws)] q' ↔
        (ws[q]?.getD 0).toNat = (ws[q']?.getD 0).toNat := by
    intro q hq q' hq'
    rw [hkey q hq, hkey q' hq', List.cons.injEq, and_iff_left rfl, ← UInt64.toNat_inj, hcode _ (hbound q hq),
      hcode _ (hbound q' hq')]
    exact Nat.add_right_cancel_iff
  have hmono1 : ∀ q, q + 1 < m.toNat + 1 → (ws[q]?.getD 0).toNat ≤ (ws[q + 1]?.getD 0).toNat := fun q hq => by
    have hl := kseen_sorted hr q (by rw [hM']; exact hq)
    simp only [ascKeys, List.map_cons, List.map_nil, hwr, lexLe, Array.getElem?_map,
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
  generalize hKf : seenKey (m.toNat + 1).toUSize [(.i64, wordsFoR ws)] = Kf at hc hf hK hkey
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
theorem canon_sorted {R U : Tab k v} (h : R.canon = .ok U) {es : List (QAtomicType × Enc)}
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
-- the five-kernel operators against the old `CRel.union`, `CRel.inter`, `CRel.diff`, `Alg.leC` on the same tables,
-- both orders; the old `∩`/`−` keep `R`'s order, so their answer is compared after `Alg.canonC`
#guard [T₁, T₂, T₃, []].all fun ps => [T₁, T₂, T₃, []].all fun qs =>
  let R := tab ps; let S := tab qs
  let old (c : CRel .long .long) := c.bind fun t => let c := Alg.canonC t; if c.2 then some c.1.toList else none
  ((R.union S).toOption.map Tab.toList) == old (CRel.union (some R) (some S)) &&
  ((R.inter S).toOption.map Tab.toList) == old (CRel.inter (some R) (some S)) &&
  ((R.diff S).toOption.map Tab.toList) == old (CRel.diff (some R) (some S)) &&
  (R.le S).toOption == (let c := Alg.leC R S; if c.2 then some c.1 else none)

end Checks

end Rel
