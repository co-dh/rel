import Rel.Lang.GenKSpec

/-! The laws of `Tab.keepBits` and `Tab.compTabMat` (`Rel/Run/Bits.lean`), the two ops `GenKSpec` reads a bit matrix
    through. Both hold only for a matrix as its producers (`compMat`, `compTabMat`) build it: `0`/`1` words, `g · w`
    not wrapping, and each side's rows `x[ra[·]]`, `y[rc[·]]` distinct (`Vals.code`'s `rep`). -/

namespace Rel
open Rel.Ext Rel.Kernel Rel.Verify Ext.Enc Rel.Rep
open scoped Rel.Core.Rel
variable {A B C : Obj}

/-- **`colIota n` holds `0 … n-1`**. -/
theorem Tab.colIota_raw {n : USize} {e : Enc} (h : Tab.colIota n = .ok e) :
    ∀ i < n.toNat, (raw .i64 n e)[i]?.getD 0 = i.toUInt64 := by
  simp only [Tab.colIota, bind] at h
  rw [Except.bind_eq_ok'] at h; obtain ⟨one, hone, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨P, hP, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨one', hone', h⟩ := h
  have hU64 : USize.size ≤ 2 ^ 64 := by rcases USize.size_eq with h | h <;> omega
  have hNU := n.toNat_lt_size
  have hs := colPrefix_add_sum hP (fun _ => 1) fun G hG => by
    rw [colConst_raw hone, Array.getElem?_replicate, if_pos hG, Option.getD_some]; rfl
  intro i hi
  have e1 := (colMap_raw h).2.2.2 i hi
  rw [hs i hi, colConst_raw hone', Array.getElem?_replicate, if_pos hi, Option.getD_some] at e1
  have hsum : ∀ k, ((List.range k).map fun _ => (1 : Nat)).sum = k := by
    intro k; induction k with
    | zero => rfl
    | succ k ih =>
      rw [List.range_succ_eq_map, List.map_cons, List.sum_cons, List.map_map]
      exact (congrArg (1 + ·) ih).trans (Nat.add_comm 1 k)
  rw [hsum] at e1
  simp only [Op.eval, Except.ok.injEq] at e1
  rw [← e1]
  apply UInt64.toNat_inj.mp
  rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le, toNat_toUInt64 (by omega)]; simp),
    toNat_toUInt64 (by omega), toNat_toUInt64 (by omega)]
  simp

/-- **`index xr v` finds each row of `v` among the `g` rows of `xr`**: row `j`'s word is a position `a` of `xr` holding
    `v`'s row `j`, or `g` where no row of `xr` holds it. -/
theorem Tab.index_spec {g n : USize} {xr : Vals A g} {v : Vals A n} {e : Enc} (h : Tab.index xr v = .ok e)
    (j : Fin n.toNat) :
    (∃ a : Fin g.toNat, ((raw .i64 n e)[j.1]?.getD 0).toNat = a.1 ∧ xr.row a = v.row j) ∨
      (((raw .i64 n e)[j.1]?.getD 0).toNat = g.toNat ∧ ∀ a : Fin g.toNat, xr.row a ≠ v.row j) := by
  simp only [Tab.index, bind] at h
  rw [Except.bind_eq_ok'] at h; obtain ⟨⟨k, cx, cv, Z⟩, hc, h⟩ := h; try dsimp only at h
  rw [Except.bind_eq_ok'] at h; obtain ⟨io, hio, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨sc, hsc, h⟩ := h
  obtain ⟨fx, fv, -, hfx, hfv, -, -, hxv, -⟩ := Vals.code2_spec hc
  have hU64 : USize.size ≤ 2 ^ 64 := by rcases USize.size_eq with h | h <;> omega
  have hGU := g.toNat_lt_size
  have hkU := k.toNat_lt_size
  obtain ⟨hs, -, hw⟩ := kscatter_words hsc
  obtain ⟨-, hfill, hlast⟩ := (scatterWords_spec _ _ _ _).2 _ hw
  have hix : ∀ q < g.toNat, ((raw .i64 g cx)[q]?.getD 0).toNat = fx q := fun q hq => by
    rw [(hfx q hq).1, toNat_toUInt64 (by have := (hfx q hq).2; omega)]
  have gj := (kgather_word h j.1 j.2).2
  rw [(hfv j.1 j.2).1, toNat_toUInt64 (by have := (hfv j.1 j.2).2; omega)] at gj
  rw [gj]
  by_cases hex : ∃ q < g.toNat, fx q = fv j.1
  · obtain ⟨q0, hq0, e0⟩ := hex
    obtain ⟨q, hq, eq, hl⟩ := last_of_exists (P := fun q => fx q = fv j.1) hq0 e0
    have := hlast q (by rw [hs]; exact hq) fun q' h1 h2 e' => hl q' h1 (by rw [hs] at h2; exact h2)
      (by rw [← hix q' (by rw [hs] at h2; exact h2), ← eq, ← hix q hq]; exact e')
    have this' : (raw .i64 k sc)[((raw .i64 g cx)[q]?.getD 0).toNat]? = some ((raw .i64 g io)[q]?.getD 0) := this
    rw [hix q hq, eq, Tab.colIota_raw hio q hq] at this'
    rw [this', Option.getD_some, toNat_toUInt64 (by omega)]
    exact .inl ⟨⟨q, hq⟩, rfl, (hxv ⟨q, hq⟩ j).1 eq⟩
  · have hf := hfill (fv j.1) (hfv j.1 j.2).2 fun q hq e' => hex ⟨q, by rw [hs] at hq; exact hq, by
      rw [← hix q (by rw [hs] at hq; exact hq)]; exact e'⟩
    rw [hf, Option.getD_some, USize.toNat_toUInt64]
    exact .inr ⟨rfl, fun a e' => hex ⟨a.1, a.2, (hxv a j).2 e'⟩⟩

/-- `index`'s words are at most `g`. -/
theorem Tab.index_le {g n : USize} {xr : Vals A g} {v : Vals A n} {e : Enc} (h : Tab.index xr v = .ok e)
    (j : Fin n.toNat) : ((raw .i64 n e)[j.1]?.getD 0).toNat ≤ g.toNat := by
  rcases Tab.index_spec h j with ⟨a, ea, -⟩ | ⟨ea, -⟩
  · rw [ea]; exact Nat.le_of_lt a.2
  · exact Nat.le_of_eq ea

/-- `Tab.ofBits` answering bounds its matrix: `whereCol` refuses `2^63` cells or more. -/
theorem Tab.ofBits_lt {n m g w : USize} {o ra rc : Enc} {x : Vals A n} {y : Vals C m} {X : Tab A C}
    (h : Tab.ofBits g w o x ra y rc = .ok X) : (g * w).toNat < 2 ^ 63 := by
  simp only [Tab.ofBits, bind] at h
  rw [Except.bind_eq_ok'] at h; obtain ⟨_, hM, -⟩ := h
  unfold whereCol at hM; dsimp only at hM
  split at hM
  · rename_i hlt; exact Nat.lt_of_lt_of_le hlt (Nat.min_le_right _ _)
  · cases hM

/-- **`whereCol` lists the positions of the `1` words**: some answer row holds `i` exactly when `b[i]` is set. -/
theorem whereCol_mem {m K : USize} {b o : Enc} (h : whereCol m b = .ok (K, o))
    (hb : ∀ i < m.toNat, (raw .i64 m b)[i]?.getD 0 < 2) (i : Nat) :
    (∃ k < K.toNat, ((raw .i64 K o)[k]?.getD 0).toNat = i) ↔ i < m.toNat ∧ (raw .i64 m b)[i]?.getD 0 ≠ 0 := by
  have hsz := whereCol_size h
  have hmem : i ∈ (raw .i64 K o).toList.map UInt64.toNat ↔ i < m.toNat ∧ (raw .i64 m b)[i]?.getD 0 ≠ 0 := by
    rw [whereCol_spec h hb, List.mem_filter, List.mem_range, decide_eq_true_eq]
  rw [← hmem, List.mem_map]
  constructor
  · rintro ⟨k, hk, rfl⟩
    refine ⟨_, Array.getElem_mem_toList (by rw [hsz]; exact hk : k < (raw .i64 K o).size), ?_⟩
    rw [getElem?_pos (raw .i64 K o) k (by omega), Option.getD_some]
  · rintro ⟨v, hv, rfl⟩
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hv
    rw [Array.length_toList] at hk
    refine ⟨k, hsz ▸ hk, ?_⟩
    rw [Array.getElem_toList, getElem?_pos (raw .i64 K o) k hk, Option.getD_some]

/-- **`Tab.keepBits` is `T ∩ M`** for a matrix `M` as `compMat` and `compTabMat` build it: `0`/`1` words, `g · w` not
    wrapping, and the rows `x[ra[·]]` distinct, as `y[rc[·]]` (else `index` finds one of two equal rows and its bit). -/
theorem Tab.keepBits_law {n m : USize} {T : Tab A C} {g w : USize} {o : Enc} {x : Vals A n} {ra : Enc}
    {y : Vals C m} {rc : Enc} {u s : Tab A C} (h : Tab.keepBits T g w o x ra y rc = .ok u)
    (hs : Tab.ofBits g w o x ra y rc = .ok s) (hgw : (g * w).toNat = g.toNat * w.toNat)
    (ho : ∀ i < g.toNat * w.toNat, ∃ v : UInt64, (raw .i64 (g * w) o)[i]? = some v ∧ v < 2)
    (hx : ∀ a a' : Fin g.toNat, ∀ i i' : Fin n.toNat, ((raw .i64 g ra)[a.1]?.getD 0).toNat = i.1 →
      ((raw .i64 g ra)[a'.1]?.getD 0).toNat = i'.1 → x.row i = x.row i' → a = a')
    (hy : ∀ c c' : Fin w.toNat, ∀ i i' : Fin m.toNat, ((raw .i64 w rc)[c.1]?.getD 0).toNat = i.1 →
      ((raw .i64 w rc)[c'.1]?.getD 0).toNat = i'.1 → y.row i = y.row i' → c = c') :
    rep u = rep T ∩ rep s := by
  simp only [Tab.keepBits, bind] at h
  rw [Except.bind_eq_ok'] at h; obtain ⟨t, ht, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨X', hX', h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨ia, hia, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨Y', hY', h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨ic, hic, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨c1, hc1, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨l1, hl1, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨c2, hc2, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨l2, hl2, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨ok, hok, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨⟨M, sel⟩, hM, h⟩ := h; try dsimp only at h
  rw [Except.bind_eq_ok'] at h; obtain ⟨u0, hu0, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨ga, hga, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨cw, hcw, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨mu, hmu, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨gc, hgc, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨ps, hpos, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨bw, hbw, h⟩ := h
  have hU64 : USize.size ≤ 2 ^ 64 := by rcases USize.size_eq with h | h <;> omega
  have hb := hgw ▸ Tab.ofBits_lt hs
  -- `s` by `ofBits_holds`, bit `a·w + j` set when its word is `1`
  have hS := Tab.ofBits_holds hs (fun a j => (raw .i64 (g * w) o)[a * w.toNat + j]?.getD 0 = 1) hgw hb
    fun a ha j hj => by
      have hi : a * w.toNat + j < g.toNat * w.toNat := by
        have := Nat.mul_le_mul_right w.toNat ha; rw [Nat.succ_mul] at this; omega
      obtain ⟨v, hv, hv2⟩ := ho _ hi
      exact ⟨v, hv, hv2, by simp only [hv, Option.getD_some]⟩
  -- `u0` row `k` is `t` row `sel[k]`
  unfold Tab.keep at hu0; rw [hM] at hu0
  simp only [bind, Except.bind] at hu0
  split at hu0; · cases hu0
  rename_i K0 hK0
  split at hu0; · cases hu0
  rename_i V0 hV0
  cases hu0
  have hTn := t.n.toNat_lt_size
  have hMn := M.toNat_lt_size
  apply Core.Rel.ext; intro a c
  show u.Holds a c ↔ T.Holds a c ∧ s.Holds a c
  rw [hS a c, ← Tab.canon_holds ht a c]
  -- no bit: `kgather` reads no row of an empty matrix, so `u` is empty, and so is `s`
  rcases Nat.eq_zero_or_pos (g.toNat * w.toNat) with h0 | hgw0
  · have hM0 : M.toNat = 0 := Nat.eq_zero_of_not_pos fun hM => by
      have := (kgather_word hbw 0 hM).1; omega
    rw [Tab.keep_holds h (fun i hi => by simp only at hi; omega)]
    constructor
    · rintro ⟨⟨k, hk⟩, -⟩; simp only at hk; omega
    · rintro ⟨-, a0, ha0, j, hj, -⟩
      have := Nat.mul_pos (show 0 < g.toNat by omega) (show 0 < w.toNat by omega); omega
  have hg1 : 0 < g.toNat := Nat.pos_of_mul_pos_right hgw0
  have hw1 : 0 < w.toNat := Nat.pos_of_mul_pos_left hgw0
  have hg63 : g.toNat < 2 ^ 63 := by have := Nat.le_mul_of_pos_right g.toNat hw1; omega
  have hw63 : w.toNat < 2 ^ 63 := by have := Nat.le_mul_of_pos_left w.toNat hg1; omega
  have hmulb : ∀ a0 < g.toNat, ∀ j < w.toNat, a0 * w.toNat + j < g.toNat * w.toNat := fun a0 ha j hj => by
    have := Nat.mul_le_mul_right w.toNat ha; rw [Nat.succ_mul] at this; omega
  -- each side's position: `index` against the gathered sides
  have hcol : ∀ {N : USize} {e c' l : Enc}, colConst t.n N.toUInt64 = .ok c' → colMap .lt t.n e c' = .ok l →
      N.toNat < 2 ^ 63 → ∀ i < t.n.toNat, ((raw .i64 t.n e)[i]?.getD 0).toNat ≤ N.toNat →
      (raw .i64 t.n l)[i]?.getD 0 = if ((raw .i64 t.n e)[i]?.getD 0).toNat < N.toNat then 1 else 0 :=
    fun {N e c' l} hc hl hN i hi hle => by
      have e1 := (colMap_raw hl).2.2.2 i hi
      rw [colConst_raw hc, Array.getElem?_replicate, if_pos hi, Option.getD_some,
        show (raw .i64 t.n e)[i]?.getD 0 = ((raw .i64 t.n e)[i]?.getD 0).toNat.toUInt64 from
          UInt64.toNat_inj.mp (by simp),
        show N.toUInt64 = N.toNat.toUInt64 from UInt64.toNat_inj.mp (by simp),
        eval_lt_nat (by omega) hN, Except.ok.injEq] at e1
      exact e1.symm
  have hokw : ∀ i < t.n.toNat, (raw .i64 t.n ok)[i]?.getD 0 < 2 ∧ ((raw .i64 t.n ok)[i]?.getD 0 ≠ 0 ↔
      ((raw .i64 t.n ia)[i]?.getD 0).toNat < g.toNat ∧ ((raw .i64 t.n ic)[i]?.getD 0).toNat < w.toNat) :=
    fun i hi => by
      have e3 := (colMap_raw hok).2.2.2 i hi
      rw [hcol hc1 hl1 hg63 i hi (Tab.index_le hia ⟨i, hi⟩), hcol hc2 hl2 hw63 i hi (Tab.index_le hic ⟨i, hi⟩)] at e3
      simp only [Op.eval, Except.ok.injEq] at e3
      rw [← e3]
      by_cases p : ((raw .i64 t.n ia)[i]?.getD 0).toNat < g.toNat <;>
        by_cases q : ((raw .i64 t.n ic)[i]?.getD 0).toNat < w.toNat <;> simp only [p, q, if_true, if_false] <;> decide
  -- answer row `k` of `u0` is row `sel[k]` of `t`, at bit `ia·w + ic` of `o`
  have hrow : ∀ k (hk : k < M.toNat), ∃ i : Fin t.n.toNat, ((raw .i64 M sel)[k]?.getD 0).toNat = i.1 ∧
      K0.row ⟨k, hk⟩ = t.key.row i ∧ V0.row ⟨k, hk⟩ = t.val.row i ∧
      ((raw .i64 M ps)[k]?.getD 0).toNat =
        ((raw .i64 t.n ia)[i.1]?.getD 0).toNat * w.toNat + ((raw .i64 t.n ic)[i.1]?.getD 0).toNat ∧
      ((raw .i64 t.n ia)[i.1]?.getD 0).toNat < g.toNat ∧ ((raw .i64 t.n ic)[i.1]?.getD 0).toNat < w.toNat := by
    intro k hk
    obtain ⟨i, hi, rk⟩ := Vals.gather_row _ hK0 ⟨k, hk⟩
    obtain ⟨i', hi', rv⟩ := Vals.gather_row _ hV0 ⟨k, hk⟩
    have e : i' = i := Fin.ext (hi'.symm.trans hi)
    rw [e] at rv
    have hin := (whereCol_mem hM (fun i hi => (hokw i hi).1) i.1).1 ⟨k, hk, hi⟩
    obtain ⟨hA, hC⟩ := (hokw i.1 i.2).2.1 hin.2
    refine ⟨i, hi, rk, rv, ?_, hA, hC⟩
    have g1 := (kgather_word hga k hk).2; rw [hi] at g1
    have g2 := (kgather_word hgc k hk).2; rw [hi] at g2
    have e1 := (colMap_raw hmu).2.2.2 k hk
    rw [g1, colConst_raw hcw, Array.getElem?_replicate, if_pos hk, Option.getD_some] at e1
    have e2 := (colMap_raw hpos).2.2.2 k hk
    simp only [Op.eval, Except.ok.injEq] at e1 e2
    rw [← e2, ← e1, g2, UInt64.toNat_add, UInt64.toNat_mul, USize.toNat_toUInt64]
    have := hmulb _ hA _ hC
    have hm : ((raw .i64 t.n ia)[i.1]?.getD 0).toNat * w.toNat < 2 ^ 64 := by omega
    rw [Nat.mod_eq_of_lt hm, Nat.mod_eq_of_lt (by omega)]
  have hbw : ∀ k < M.toNat, (raw .i64 M bw)[k]?.getD 0 = (raw .i64 (g * w) o)[((raw .i64 M ps)[k]?.getD 0).toNat]?.getD 0 :=
    fun k hk => (kgather_word hbw k hk).2
  have hbw2 : ∀ k < M.toNat, (raw .i64 M bw)[k]?.getD 0 < 2 := fun k hk => by
    obtain ⟨i, -, -, -, ep, hA, hC⟩ := hrow k hk
    obtain ⟨v, hv, hv2⟩ := ho _ (hmulb _ hA _ hC)
    rw [hbw k hk, ep, hv, Option.getD_some]; exact hv2
  have one : ∀ v : UInt64, v < 2 → (v ≠ 0 ↔ v = 1) := fun v hv => by
    rw [ne_eq, ← UInt64.toNat_inj, ← UInt64.toNat_inj, UInt64.toNat_zero, UInt64.toNat_one]
    have := UInt64.lt_iff_toNat_lt.1 hv; simp at this; omega
  rw [Tab.keep_holds h hbw2]
  constructor
  · rintro ⟨⟨k, hk⟩, hb1, rfl, rfl⟩
    obtain ⟨i, -, rk, rv, ep, hA, hC⟩ := hrow k hk
    refine ⟨⟨i, rk.symm, rv.symm⟩, _, hA, _, hC, ?_, ?_, ?_⟩
    · dsimp only; rw [← ep, ← hbw k hk]; exact (one _ (hbw2 k hk)).1 hb1
    · rcases Tab.index_spec hia i with ⟨a', ea, ra'⟩ | ⟨ea, -⟩
      · obtain ⟨i0, h0, r0⟩ := Vals.gather_row _ hX' a'
        exact ⟨i0, by rw [ea]; exact h0, by rw [← r0, ra', ← rk]⟩
      · omega
    · rcases Tab.index_spec hic i with ⟨c', ec, rc'⟩ | ⟨ec, -⟩
      · obtain ⟨i1, h1, r1⟩ := Vals.gather_row _ hY' c'
        exact ⟨i1, by rw [ec]; exact h1, by rw [← r1, rc', ← rv]⟩
      · omega
  · rintro ⟨⟨i, rfl, rfl⟩, a0, ha0, j, hj, hP, ⟨i0, h0, r0⟩, ⟨i1, h1, r1⟩⟩
    have hA : ((raw .i64 t.n ia)[i.1]?.getD 0).toNat = a0 := by
      obtain ⟨i0', h0', r0'⟩ := Vals.gather_row _ hX' ⟨a0, ha0⟩
      have e : i0' = i0 := Fin.ext (h0'.symm.trans h0)
      rcases Tab.index_spec hia i with ⟨a', ea, ra'⟩ | ⟨-, hn⟩
      · obtain ⟨i2, h2, r2⟩ := Vals.gather_row _ hX' a'
        rw [ea]; exact congrArg Fin.val (hx a' ⟨a0, ha0⟩ i2 i0 h2 h0 (by rw [← r2, ra', ← r0]))
      · exact (hn ⟨a0, ha0⟩ (by rw [r0', e, r0])).elim
    have hC : ((raw .i64 t.n ic)[i.1]?.getD 0).toNat = j := by
      obtain ⟨i1', h1', r1'⟩ := Vals.gather_row _ hY' ⟨j, hj⟩
      have e : i1' = i1 := Fin.ext (h1'.symm.trans h1)
      rcases Tab.index_spec hic i with ⟨c', ec, rc'⟩ | ⟨-, hn⟩
      · obtain ⟨i2, h2, r2⟩ := Vals.gather_row _ hY' c'
        rw [ec]; exact congrArg Fin.val (hy c' ⟨j, hj⟩ i2 i1 h2 h1 (by rw [← r2, rc', ← r1]))
      · exact (hn ⟨j, hj⟩ (by rw [r1', e, r1])).elim
    obtain ⟨k, hk, hki⟩ := (whereCol_mem hM (fun i hi => (hokw i hi).1) i.1).2
      ⟨i.2, (hokw i.1 i.2).2.2 ⟨by omega, by omega⟩⟩
    obtain ⟨i', hi', rk, rv, ep, -⟩ := hrow k hk
    have e : i' = i := Fin.ext (hi'.symm.trans hki)
    rw [e] at rk rv ep
    refine ⟨⟨k, hk⟩, ?_, rk, rv⟩
    rw [hbw k hk, ep, hA, hC, hP]; decide

end Rel
