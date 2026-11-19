import Rel.Run.Bits
import Rel.RepTabComp
import Rel.RepSetOps
import Rel.KernelSpec.BitRows

/-! The laws of `Tab.compBits` and `Tab.ldivBits` (`Rel/Run/Bits.lean`), from the kernels' laws and `raw_kbitrows`:
each step's words first (`Vals.code`), then the answers against `Tab.comp_holds` and `Tab.ldiv_holds`. -/

namespace Rel
open Rel.Ext Rel.Kernel Rel.Verify Ext.Enc
variable {A B C : Obj}

/-- **`Vals.code` numbers the rows of `x` by value**: `k ≤ n` numbers, row `i`'s number `c[i]` below `k`, two rows
numbered alike exactly when equal, and number `G`'s row `rep[G]` a row numbered `G`. -/
theorem Vals.code_spec {n : USize} {x : Vals A n} {k : USize} {c rep : Enc} (h : Vals.code x = .ok (k, c, rep)) :
    k.toNat ≤ n.toNat ∧ (∀ i < n.toNat, ((raw .i64 n c)[i]?.getD 0).toNat < k.toNat) ∧
    (∀ G < k.toNat, ∃ i : Fin n.toNat, ((raw .i64 k rep)[G]?.getD 0).toNat = i.1 ∧
      ((raw .i64 n c)[i.1]?.getD 0).toNat = G) ∧
    ∀ i i' : Fin n.toNat, (raw .i64 n c)[i.1]?.getD 0 = (raw .i64 n c)[i'.1]?.getD 0 ↔ x.row i = x.row i' := by
  simp only [Vals.code, bind] at h
  rw [Except.bind_eq_ok'] at h; obtain ⟨es, hes, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨⟨vs, p⟩, hasc, h⟩ := h; try dsimp only at h
  rw [Except.bind_eq_ok'] at h; obtain ⟨⟨k', g, f⟩, hseen, h⟩ := h; try dsimp only at h
  rw [Except.bind_eq_ok'] at h; obtain ⟨c', hc, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨rep', hrep, h⟩ := h
  simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl, rfl⟩ := h
  obtain ⟨π, gr, fs, hkN, hp, hinj, hsur, -, hg, hf, hrow⟩ := group_rows hes hasc hseen
  have hU64 : USize.size ≤ 2 ^ 64 := by rcases USize.size_eq with h | h <;> omega
  have hNU := n.toNat_lt_size
  have hK : k'.toUSize.toNat = k' := USize.toNat_ofNat_of_lt' (by omega)
  have hcq : ∀ q < n.toNat, (raw .i64 n c')[π q]?.getD 0 = (gr q).toUInt64 := fun q hq => by
    rw [scatter_last_at hc π (fun q hq => (hp q hq).1) (fun q hq => (hp q hq).2) hinj q hq, (hg q hq).1]
  have hgr : ∀ q < n.toNat, ((gr q).toUInt64).toNat = gr q := fun q hq =>
    toNat_toUInt64 (by have := (hg q hq).2; omega)
  refine ⟨by rw [hK]; exact hkN, fun i hi => ?_, fun G hG => ?_, fun i i' => ?_⟩
  · obtain ⟨q, hq, rfl⟩ := hsur i hi
    rw [hcq q hq, hgr q hq, hK]; exact (hg q hq).2
  · rw [hK] at hG
    obtain ⟨hfw, hfs, hfG⟩ := hf G hG
    have hw := (kgather_word hrep G (by rw [hK]; exact hG)).2
    rw [hfw, toNat_toUInt64 (by omega), (hp _ hfs).1] at hw
    refine ⟨⟨π (fs G), (hp _ hfs).2⟩, by rw [hw, toNat_toUInt64 (by have := (hp _ hfs).2; omega)], ?_⟩
    rw [hcq _ hfs, hgr _ hfs, hfG]
  · obtain ⟨q, hq, e⟩ := hsur i.1 i.2
    obtain ⟨q', hq', e'⟩ := hsur i'.1 i'.2
    obtain rfl : i = ⟨π q, (hp q hq).2⟩ := Fin.ext e.symm
    obtain rfl : i' = ⟨π q', (hp q' hq').2⟩ := Fin.ext e'.symm
    rw [hcq q hq, hcq q' hq']
    constructor
    · intro hw
      have := congrArg UInt64.toNat hw
      rw [hgr q hq, hgr q' hq'] at this
      exact (hrow q hq q' hq').1 this _ _
    · intro hx; rw [(hrow q hq q' hq').2 fun _ _ => hx]

/-- A `P` below `N` has a last one: no later `k'` below `N` is a `P`. -/
private theorem last_of_exists {P : Nat → Prop} {N : Nat} :
    ∀ {k}, k < N → P k → ∃ k, k < N ∧ P k ∧ ∀ k', k < k' → k' < N → ¬P k' := by
  intro k hk hP
  suffices H : ∀ d k, N - k ≤ d → k < N → P k → ∃ k, k < N ∧ P k ∧ ∀ k', k < k' → k' < N → ¬P k' from
    H _ k (Nat.le_refl _) hk hP
  intro d
  induction d with
  | zero => intro k h1 h2; omega
  | succ d ih =>
    intro k hd hk hP
    by_cases hm : ∃ k', k < k' ∧ k' < N ∧ P k'
    · obtain ⟨k', h1, h2, h3⟩ := hm; exact ih k' (by omega) h2 h3
    · exact ⟨k, hk, hP, fun k' h1 h2 h3 => hm ⟨k', h1, h2, h3⟩⟩

/-- **`bitMatrix` sets bit `r[k]·w + c[k]` for each row `k`** and no other: bit `a·w + j` is `1` exactly when some
row is `(a, j)`. -/
theorem bitMatrix_spec {n na w : USize} {r c o : Enc} (h : bitMatrix n na w r c = .ok o)
    (hnw : (na * w).toNat = na.toNat * w.toNat)
    (hr : ∀ k < n.toNat, ((raw .i64 n r)[k]?.getD 0).toNat < na.toNat)
    (hc : ∀ k < n.toNat, ((raw .i64 n c)[k]?.getD 0).toNat < w.toNat) :
    ∀ a < na.toNat, ∀ j < w.toNat, (raw .i64 (na * w) o)[a * w.toNat + j]?.getD 0 =
      if ∃ k < n.toNat, ((raw .i64 n r)[k]?.getD 0).toNat = a ∧ ((raw .i64 n c)[k]?.getD 0).toNat = j
      then 1 else 0 := by
  simp only [bitMatrix, bind] at h
  rw [Except.bind_eq_ok'] at h; obtain ⟨wc, hwc, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨m1, hm1, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨ix, hix, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨one, hone, h⟩ := h
  have hU64 : USize.size ≤ 2 ^ 64 := by rcases USize.size_eq with h | h <;> omega
  have hNU := (na * w).toNat_lt_size
  have hw0 : ∀ a' j, j < w.toNat → ∀ a q, q < w.toNat → (a * w.toNat + q = a' * w.toNat + j ↔ a = a' ∧ q = j) := by
    intro a' j hj a q hq
    constructor
    · intro e
      have h1 := congrArg (· / w.toNat) e; have h2 := congrArg (· % w.toNat) e
      simp only [Nat.add_comm (_ * w.toNat), Nat.add_mul_div_right _ _ (show 0 < w.toNat by omega),
        Nat.div_eq_of_lt hq, Nat.div_eq_of_lt hj, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hq,
        Nat.mod_eq_of_lt hj, Nat.zero_add] at h1 h2
      exact ⟨h1, h2⟩
    · rintro ⟨rfl, rfl⟩; rfl
  have hixk : ∀ k < n.toNat, ((raw .i64 n ix)[k]?.getD 0).toNat =
      ((raw .i64 n r)[k]?.getD 0).toNat * w.toNat + ((raw .i64 n c)[k]?.getD 0).toNat := fun k hk => by
    have e1 := (colMap_raw hm1).2.2.2 k hk
    rw [colConst_raw hwc, Array.getElem?_replicate, if_pos hk, Option.getD_some] at e1
    have e2 := (colMap_raw hix).2.2.2 k hk
    simp only [Op.eval, Except.ok.injEq] at e1 e2
    have hb := Nat.mul_le_mul_right w.toNat (hr k hk)
    have hck := hc k hk
    rw [Nat.succ_mul] at hb
    rw [← e2, ← e1, UInt64.toNat_add, UInt64.toNat_mul, USize.toNat_toUInt64,
      Nat.mod_eq_of_lt (show _ < 2 ^ 64 by omega), Nat.mod_eq_of_lt (show _ < 2 ^ 64 by omega)]
  obtain ⟨hs, -, hw⟩ := kscatter_words h
  obtain ⟨-, hfill, hlast⟩ := (scatterWords_spec _ _ _ _).2 _ hw
  intro a ha j hj
  have hJ : a * w.toNat + j < (na * w).toNat := by
    have := Nat.mul_le_mul_right w.toNat ha; rw [Nat.succ_mul] at this; omega
  have uniq : ∀ k < n.toNat, ((raw .i64 n ix)[k]?.getD 0).toNat = a * w.toNat + j ↔
      ((raw .i64 n r)[k]?.getD 0).toNat = a ∧ ((raw .i64 n c)[k]?.getD 0).toNat = j := fun k hk => by
    rw [hixk k hk]; exact hw0 a j hj _ _ (hc k hk)
  by_cases hex : ∃ k < n.toNat, ((raw .i64 n r)[k]?.getD 0).toNat = a ∧ ((raw .i64 n c)[k]?.getD 0).toNat = j
  · rw [if_pos hex]
    obtain ⟨k0, hk0, hP⟩ := hex
    obtain ⟨k, hk, hPk, hl⟩ := last_of_exists (P := fun k => ((raw .i64 n ix)[k]?.getD 0).toNat = a * w.toNat + j)
      hk0 ((uniq k0 hk0).2 hP)
    have := hlast k (by rw [hs]; exact hk) fun k' h1 h2 e => hl k' h1 (by rw [hs] at h2; exact h2) (e.trans hPk)
    have this' : (raw .i64 (na * w) o)[((raw .i64 n ix)[k]?.getD 0).toNat]? =
      some ((raw .i64 n one)[k]?.getD 0) := this
    rw [hPk] at this'
    rw [this', Option.getD_some, colConst_raw hone, Array.getElem?_replicate, if_pos hk]; rfl
  · rw [if_neg hex, hfill _ hJ fun k hk e => hex ⟨k, by rw [hs] at hk; exact hk, (uniq k (by rw [hs] at hk; exact hk)).1 e⟩]
    rfl

/-- **`Tab.ofBits` reads the set bits back as rows**: with bit `a·w + j` of `o` set exactly when `P a j`, the rows of
the answer are `(x[ra[a]], y[rc[j]])` for the `(a, j)` with `P a j`. -/
theorem Tab.ofBits_holds {n m g w : USize} {o ra rc : Enc} {x : Vals A n} {y : Vals C m} {X : Tab A C}
    (h : Tab.ofBits g w o x ra y rc = .ok X) (P : Nat → Nat → Prop)
    (hgw : (g * w).toNat = g.toNat * w.toNat) (hb : g.toNat * w.toNat < 2 ^ 63)
    (ho : ∀ a < g.toNat, ∀ j < w.toNat, ∃ v : UInt64, (raw .i64 (g * w) o)[a * w.toNat + j]? = some v ∧ v < 2 ∧
      (v = 1 ↔ P a j)) (u : A.El) (v : C.El) :
    X.Holds u v ↔ ∃ a < g.toNat, ∃ j < w.toNat, P a j ∧ (∃ i : Fin n.toNat,
      ((raw .i64 g ra)[a]?.getD 0).toNat = i.1 ∧ x.row i = u) ∧ ∃ i : Fin m.toNat,
      ((raw .i64 w rc)[j]?.getD 0).toNat = i.1 ∧ y.row i = v := by
  simp only [Tab.ofBits, bind] at h
  rw [Except.bind_eq_ok'] at h; obtain ⟨⟨M, sel⟩, hM, h⟩ := h; try dsimp only at h
  rw [Except.bind_eq_ok'] at h; obtain ⟨wc, hwc, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨dv, hdv, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨ix, hix, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨md, hmd, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨iy, hiy, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨X1, hX1, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨Y1, hY1, h⟩ := h
  cases h
  have hwpos : ∀ i < g.toNat * w.toNat, 0 < w.toNat := fun i hi =>
    Nat.pos_of_ne_zero fun e => by rw [e, Nat.mul_zero] at hi; omega
  have hwle : ∀ i < g.toNat * w.toNat, w.toNat ≤ g.toNat * w.toNat := fun i hi => by
    have := Nat.mul_le_mul_right w.toNat (show 1 ≤ g.toNat from Nat.pos_of_ne_zero fun e => by
      rw [e, Nat.zero_mul] at hi; omega)
    rwa [Nat.one_mul] at this
  -- every bit `i` of `o`, as the pair `(i / w, i % w)`
  have hbit : ∀ i < g.toNat * w.toNat, (raw .i64 (g * w) o)[i]?.getD 0 < 2 ∧
      ((raw .i64 (g * w) o)[i]?.getD 0 ≠ 0 ↔ P (i / w.toNat) (i % w.toNat)) := fun i hi => by
    have hw0 := hwpos i hi
    obtain ⟨v, hv, hv2, hvP⟩ := ho (i / w.toNat) ((Nat.div_lt_iff_lt_mul hw0).2 hi) (i % w.toNat) (Nat.mod_lt _ hw0)
    rw [Nat.div_add_mod'] at hv
    rw [hv, Option.getD_some, ← hvP]
    have : v.toNat < 2 := by have := UInt64.lt_iff_toNat_lt.1 hv2; simpa using this
    refine ⟨hv2, ?_⟩
    rw [ne_eq, ← UInt64.toNat_inj, ← UInt64.toNat_inj, UInt64.toNat_zero, UInt64.toNat_one]
    omega
  have hsel := whereCol_spec hM fun i hi => (hbit i (hgw ▸ hi)).1
  have hMs := whereCol_size hM
  -- row `t` of the answer is bit `L[t]`
  have hL : ∀ t < M.toNat, ∃ i < g.toNat * w.toNat, P (i / w.toNat) (i % w.toNat) ∧
      (raw .i64 M sel)[t]?.getD 0 = i.toUInt64 := fun t ht => by
    have e := congrArg (·[t]?) hsel
    simp only [List.getElem?_map, Array.getElem?_toList, getElem?_pos (raw .i64 M sel) t (by omega),
      Option.map_some] at e
    have hm := List.mem_of_getElem? e.symm
    rw [List.mem_filter, List.mem_range] at hm
    refine ⟨_, hgw ▸ hm.1, (hbit _ (hgw ▸ hm.1)).2.1 (by simpa using hm.2), ?_⟩
    rw [getElem?_pos (raw .i64 M sel) t (by omega), Option.getD_some]; exact UInt64.toNat_inj.mp (by simp)
  -- row `t` holding bit `i` is `(x[ra[i / w]], y[rc[i % w]])`
  have hrow : ∀ t (ht : t < M.toNat), ∀ i < g.toNat * w.toNat, (raw .i64 M sel)[t]?.getD 0 = i.toUInt64 →
      (∃ i0 : Fin n.toNat, ((raw .i64 g ra)[i / w.toNat]?.getD 0).toNat = i0.1 ∧ X1.row ⟨t, ht⟩ = x.row i0) ∧
      ∃ i1 : Fin m.toNat, ((raw .i64 w rc)[i % w.toNat]?.getD 0).toNat = i1.1 ∧ Y1.row ⟨t, ht⟩ = y.row i1 := by
    intro t ht i hi e
    have hw0 := hwpos i hi
    have hwg := hwle i hi
    have wcw : (raw .i64 M wc)[t]?.getD 0 = w.toNat.toUInt64 := by
      rw [colConst_raw hwc, Array.getElem?_replicate, if_pos ht, Option.getD_some]
      exact UInt64.toNat_inj.mp (by simp)
    have e1 := (colMap_raw hdv).2.2.2 t ht
    rw [e, wcw, eval_div_nat (by omega) (by omega) hw0, Except.ok.injEq] at e1
    have e2 := (colMap_raw hmd).2.2.2 t ht
    rw [e, wcw, eval_mod_nat (by omega) (by omega) hw0, Except.ok.injEq] at e2
    have hdl : i / w.toNat < 2 ^ 64 := Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (by omega)
    have hml : i % w.toNat < 2 ^ 64 := Nat.lt_of_lt_of_le (Nat.mod_lt _ hw0) (by omega)
    have gx := (kgather_word hix t ht).2
    rw [← e1, toNat_toUInt64 hdl] at gx
    have gy := (kgather_word hiy t ht).2
    rw [← e2, toNat_toUInt64 hml] at gy
    obtain ⟨i0, h0, r0⟩ := Vals.gather_row x hX1 ⟨t, ht⟩
    obtain ⟨i1, h1, r1⟩ := Vals.gather_row y hY1 ⟨t, ht⟩
    exact ⟨⟨i0, by rw [← gx]; exact h0, r0⟩, ⟨i1, by rw [← gy]; exact h1, r1⟩⟩
  show (∃ t, X1.row t = u ∧ Y1.row t = v) ↔ _
  constructor
  · rintro ⟨⟨t, ht⟩, hu, hv⟩
    obtain ⟨i, hi, hP, e⟩ := hL t ht
    obtain ⟨⟨i0, h0, r0⟩, ⟨i1, h1, r1⟩⟩ := hrow t ht i hi e
    have hw0 := hwpos i hi
    exact ⟨_, (Nat.div_lt_iff_lt_mul hw0).2 hi, _, Nat.mod_lt _ hw0, hP, ⟨i0, h0, by rw [← r0]; exact hu⟩,
      ⟨i1, h1, by rw [← r1]; exact hv⟩⟩
  · rintro ⟨a, ha, j, hj, hP, ⟨i0, h0, r0⟩, ⟨i1, h1, r1⟩⟩
    have hw0 : 0 < w.toNat := by omega
    have hi : a * w.toNat + j < g.toNat * w.toNat := by
      have := Nat.mul_le_mul_right w.toNat ha; rw [Nat.succ_mul] at this; omega
    have hdiv : (a * w.toNat + j) / w.toNat = a := by
      rw [Nat.add_comm, Nat.add_mul_div_right _ _ hw0, Nat.div_eq_of_lt hj, Nat.zero_add]
    have hmod : (a * w.toNat + j) % w.toNat = j := by
      rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hj]
    have hmem : a * w.toNat + j ∈ (List.range (g * w).toNat).filter
        (fun i : Nat => decide ((raw .i64 (g * w) o)[i]?.getD 0 ≠ 0)) :=
      List.mem_filter.2 ⟨List.mem_range.2 (by omega), by simpa using (hbit _ hi).2.2 (by rw [hdiv, hmod]; exact hP)⟩
    rw [← hsel, List.mem_iff_getElem?] at hmem
    obtain ⟨t, ht⟩ := hmem
    simp only [List.getElem?_map, Array.getElem?_toList] at ht
    obtain ⟨wd, hwd, hwi⟩ := Option.map_eq_some_iff.1 ht
    have htM : t < M.toNat := by
      rw [← hMs]; exact Classical.byContradiction fun hc => by rw [Array.getElem?_eq_none_iff.2 (Nat.le_of_not_lt hc)] at hwd; cases hwd
    have e : (raw .i64 M sel)[t]?.getD 0 = (a * w.toNat + j).toUInt64 := by
      rw [hwd, Option.getD_some, ← hwi]; exact UInt64.toNat_inj.mp (by simp)
    obtain ⟨⟨i0', h0', r0'⟩, ⟨i1', h1', r1'⟩⟩ := hrow t htM _ hi e
    rw [hdiv] at h0'; rw [hmod] at h1'
    obtain rfl : i0' = i0 := Fin.ext (h0'.symm.trans h0)
    obtain rfl : i1' = i1 := Fin.ext (h1'.symm.trans h1)
    exact ⟨⟨t, htM⟩, by rw [r0', r0], by rw [r1', r1]⟩

end Rel
