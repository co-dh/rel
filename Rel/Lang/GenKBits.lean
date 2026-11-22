import Rel.Lang.GenKSpec


/-! The laws of `Tab.keepBits` and `Tab.compTabMat` (`Rel/Run/Bits.lean`), the two ops `GenKSpec` reads a bit matrix
    through. Both hold only for a matrix as its producers (`compMat`, `compTabMat`) build it: `0`/`1` words, `g · w`
    not wrapping, and each side's rows `x[ra[·]]`, `y[rc[·]]` distinct (`Vals.code`'s `rep`). -/

namespace Rel
open Rel.Ext Rel.Kernel Rel.Verify Ext.Enc Rel.Rep
open scoped Rel.Core.Rel
variable {A B C : Obj}

/-- An `index` answer holds no null: a gather of a scatter of `shiftCol`, a `colMap` answer, which holds none. -/
theorem Tab.index_plain {g n : USize} {xr : Vals A g} {v : Vals A n} {e : Enc} (h : Tab.index xr v = .ok e) :
    hasNul e = false := by
  simp only [Tab.index, bind] at h
  rw [Except.bind_eq_ok'] at h; obtain ⟨⟨k, cx, cv, Z⟩, -, h⟩ := h; try dsimp only at h
  rw [Except.bind_eq_ok'] at h; obtain ⟨io, hio, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨sc, hsc, h⟩ := h
  exact kgather_noNul h (kscatter_plain hsc (colMap_plain hio))

/-- **`index xr v` finds each row of `v` among the `g` rows of `xr`**: row `j`'s word is a position `a` of `xr` holding
    `v`'s row `j`, or `g` where no row of `xr` holds it. -/
theorem Tab.index_spec {g n : USize} {xr : Vals A g} {v : Vals A n} {e : Enc} (h : Tab.index xr v = .ok e)
    (hxr : Vals.WF xr) (hv : Vals.WF v) (j : Fin n.toNat) :
    (∃ a : Fin g.toNat, ((raw .i64 n e)[j.1]?.getD 0).toNat = a.1 ∧ xr.row a = v.row j) ∨
      (((raw .i64 n e)[j.1]?.getD 0).toNat = g.toNat ∧ ∀ a : Fin g.toNat, xr.row a ≠ v.row j) := by
  simp only [Tab.index, bind] at h
  rw [Except.bind_eq_ok'] at h; obtain ⟨⟨k, cx, cv, Z⟩, hc, h⟩ := h; try dsimp only at h
  rw [Except.bind_eq_ok'] at h; obtain ⟨io, hio, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨sc, hsc, h⟩ := h
  obtain ⟨fx, fv, -, hfx, hfv, -, -, hxv, -⟩ := Vals.code2_spec hc hxr hv
  have hU64 : USize.size ≤ 2 ^ 64 := by rcases USize.size_eq with h | h <;> omega
  have hGU := g.toNat_lt_size
  have hkU := k.toNat_lt_size
  obtain ⟨hs, -, hw⟩ := kscatter_words hsc (colMap_plain hio)
  obtain ⟨-, hfill, hlast⟩ := (scatterWords_spec _ _ _ _).2 _ hw
  have hix : ∀ q < g.toNat, ((raw .i64 g cx)[q]?.getD 0).toNat = fx q := fun q hq => by
    rw [(hfx q hq).1, toNat_toUInt64 (by have := (hfx q hq).2; omega)]
  have gj := (kgather_word h (kscatter_plain hsc (colMap_plain hio)) j.1 j.2).2
  rw [(hfv j.1 j.2).1, toNat_toUInt64 (by have := (hfv j.1 j.2).2; omega)] at gj
  rw [gj]
  by_cases hex : ∃ q < g.toNat, fx q = fv j.1
  · obtain ⟨q0, hq0, e0⟩ := hex
    obtain ⟨q, hq, eq, hl⟩ := last_of_exists (P := fun q => fx q = fv j.1) hq0 e0
    have := hlast q (by rw [hs]; exact hq) fun q' h1 h2 e' => hl q' h1 (by rw [hs] at h2; exact h2)
      (by rw [← hix q' (by rw [hs] at h2; exact h2), ← eq, ← hix q hq]; exact e')
    have this' : (raw .i64 k sc)[((raw .i64 g cx)[q]?.getD 0).toNat]? = some ((raw .i64 g io)[q]?.getD 0) := this
    rw [hix q hq, eq, ((shiftCol_raw hio q hq).trans (UInt64.add_zero _))] at this'
    rw [this', Option.getD_some, toNat_toUInt64 (by omega)]
    exact .inl ⟨⟨q, hq⟩, rfl, (hxv ⟨q, hq⟩ j).1 eq⟩
  · have hf := hfill (fv j.1) (hfv j.1 j.2).2 fun q hq e' => hex ⟨q, by rw [hs] at hq; exact hq, by
      rw [← hix q (by rw [hs] at hq; exact hq)]; exact e'⟩
    rw [hf, Option.getD_some, USize.toNat_toUInt64]
    exact .inr ⟨rfl, fun a e' => hex ⟨a.1, a.2, (hxv a j).2 e'⟩⟩

/-- `index`'s words are at most `g`. -/
theorem Tab.index_le {g n : USize} {xr : Vals A g} {v : Vals A n} {e : Enc} (h : Tab.index xr v = .ok e)
    (hxr : Vals.WF xr) (hv : Vals.WF v) (j : Fin n.toNat) : ((raw .i64 n e)[j.1]?.getD 0).toNat ≤ g.toNat := by
  rcases Tab.index_spec h hxr hv j with ⟨a, ea, -⟩ | ⟨ea, -⟩
  · rw [ea]; exact Nat.le_of_lt a.2
  · exact Nat.le_of_eq ea

/-- `whereCol` refuses `2^63` words or more. -/
theorem whereCol_lt {m : USize} {b : Enc} {r : USize × Enc} (h : whereCol m b = .ok r) : m.toNat < 2 ^ 63 := by
  unfold whereCol at h; dsimp only at h
  split at h
  · rename_i hlt; exact Nat.lt_of_lt_of_le hlt (Nat.min_le_right _ _)
  · cases h

/-- `whereCol` answers at most one row per word. -/
theorem whereCol_le {m K : USize} {b o : Enc} (h : whereCol m b = .ok (K, o))
    (hb : ∀ i < m.toNat, (raw .i64 m b)[i]?.getD 0 < 2) : K.toNat ≤ m.toNat := by
  have e := congrArg List.length (whereCol_spec h hb)
  rw [List.length_map, Array.length_toList, whereCol_size h] at e
  rw [e]; exact Nat.le_trans (List.length_filter_le _ _) (by simp)

/-- Bit `a·w + j` of a `g`-row matrix of `w` bits is inside it. -/
theorem bit_lt {a g j w : Nat} (ha : a < g) (hj : j < w) : a * w + j < g * w := by
  have := Nat.mul_le_mul_right w ha; rw [Nat.succ_mul] at this; omega

/-- `x < N` as the post step `(.gt, N)`, `N` below `2^63`, is `1` exactly at the words below `N`. -/
theorem colMap_lt_const {n N : USize} {e l : Enc}
    (hl : colMap .first n e e .i64 .i64 [] [(.gt, N.toUInt64)] = .ok l) (hN : N.toNat < 2 ^ 63) : ∀ i < n.toNat,
    ((raw .i64 n e)[i]?.getD 0).toNat ≤ N.toNat →
      (raw .i64 n l)[i]?.getD 0 = if ((raw .i64 n e)[i]?.getD 0).toNat < N.toNat then 1 else 0 := fun i hi hle => by
  have e1 : Op.eval .lt ((raw .i64 n e)[i]?.getD 0) N.toUInt64 = _ := (colMap_post hl).2 i hi
  rw [show (raw .i64 n e)[i]?.getD 0 = ((raw .i64 n e)[i]?.getD 0).toNat.toUInt64 from UInt64.toNat_inj.mp (by simp),
    show N.toUInt64 = N.toNat.toUInt64 from UInt64.toNat_inj.mp (by simp), eval_lt_nat (by omega) hN,
    Except.ok.injEq] at e1
  exact e1.symm

/-- A word below `2` is odd exactly when it is `1`. -/
theorem odd_bit {v : UInt64} (hv : v < 2) : v % 2 = 1 ↔ v = 1 := by
  have h2 := UInt64.lt_iff_toNat_lt.1 hv
  have e2 : (2 : UInt64).toNat = 2 := rfl
  rw [e2] at h2
  rw [← UInt64.toNat_inj, ← UInt64.toNat_inj, UInt64.toNat_mod, UInt64.toNat_one, e2]; omega

/-- `Tab.ofBits` answering bounds its matrix: `whereCol` refuses `2^63` cells or more. -/
theorem Tab.ofBits_lt {n m g w : USize} {o ra rc : Enc} {x : Vals A n} {y : Vals C m} {X : Tab A C}
    (h : Tab.ofBits g w o x ra y rc = .ok X) : (g * w).toNat < 2 ^ 63 := by
  simp only [Tab.ofBits, bind] at h
  rw [Except.bind_eq_ok'] at h; obtain ⟨_, hM, -⟩ := h
  exact whereCol_lt hM

/-- **`Tab.ofBits` of a `0`/`1` matrix**: `ofBits_holds` with bit `a·w + j` set where its word is `1`. -/
theorem Tab.ofBits_set {n m g w : USize} {o ra rc : Enc} {x : Vals A n} {y : Vals C m} {X : Tab A C}
    (h : Tab.ofBits g w o x ra y rc = .ok X) (hra : hasNul ra = false) (hrc : hasNul rc = false)
    (hgw : (g * w).toNat = g.toNat * w.toNat)
    (ho : ∀ a < g.toNat, ∀ j < w.toNat, ∃ v : UInt64, (raw .i64 (g * w) o)[a * w.toNat + j]? = some v ∧ v < 2)
    (u : A.El) (v : C.El) :
    X.Holds u v ↔ ∃ a < g.toNat, ∃ j < w.toNat, (raw .i64 (g * w) o)[a * w.toNat + j]?.getD 0 = 1 ∧
      (∃ i : Fin n.toNat, ((raw .i64 g ra)[a]?.getD 0).toNat = i.1 ∧ x.row i = u) ∧ ∃ i : Fin m.toNat,
      ((raw .i64 w rc)[j]?.getD 0).toNat = i.1 ∧ y.row i = v :=
  Tab.ofBits_holds h hra hrc _ hgw (hgw ▸ Tab.ofBits_lt h) (fun a ha j hj => by
    obtain ⟨v, hv, hv2⟩ := ho a ha j hj; exact ⟨v, hv, hv2, by simp only [hv, Option.getD_some]⟩) u v

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
    (ho : ∀ a < g.toNat, ∀ j < w.toNat, ∃ v : UInt64, (raw .i64 (g * w) o)[a * w.toNat + j]? = some v ∧ v < 2)
    (hx : ∀ a a' : Fin g.toNat, ∀ i i' : Fin n.toNat, ((raw .i64 g ra)[a.1]?.getD 0).toNat = i.1 →
      ((raw .i64 g ra)[a'.1]?.getD 0).toNat = i'.1 → x.row i = x.row i' → a = a')
    (hy : ∀ c c' : Fin w.toNat, ∀ i i' : Fin m.toNat, ((raw .i64 w rc)[c.1]?.getD 0).toNat = i.1 →
      ((raw .i64 w rc)[c'.1]?.getD 0).toNat = i'.1 → y.row i = y.row i' → c = c')
    (hra : hasNul ra = false) (hrc : hasNul rc = false) (hoN : hasNul o = false)
    (hT : T.WF) (wx : Vals.WF x) (wy : Vals.WF y) : rep u = rep T ∩ rep s := by
  simp only [Tab.keepBits, bind] at h
  rw [Except.bind_eq_ok'] at h; obtain ⟨t, ht, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨X', hX', h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨ia, hia, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨Y', hY', h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨ic, hic, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨l1, hl1, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨l2, hl2, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨ok, hok, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨⟨M, sel⟩, hM, h⟩ := h; try dsimp only at h
  rw [Except.bind_eq_ok'] at h; obtain ⟨u0, hu0, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨ga, hga, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨mu, hmu, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨gc, hgc, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨ps, hpos, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨bw, hbw, h⟩ := h
  have wt := Tab.canon_wf ht hT
  have wX' := Vals.gather_wf hX' wx
  have wY' := Vals.gather_wf hY' wy
  have hU64 : USize.size ≤ 2 ^ 64 := by rcases USize.size_eq with h | h <;> omega
  have hS := Tab.ofBits_set hs hra hrc hgw ho
  have hb := hgw ▸ Tab.ofBits_lt hs
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
      have := (kgather_word hbw hoN _ hM).1; omega
    rw [Tab.keep_holds h (fun i hi => by simp only at hi; omega)]
    constructor
    · rintro ⟨⟨k, hk⟩, -⟩; simp only at hk; omega
    · rintro ⟨-, a0, ha0, j, hj, -⟩
      have := Nat.mul_pos (show 0 < g.toNat by omega) (show 0 < w.toNat by omega); omega
  have hg1 : 0 < g.toNat := Nat.pos_of_mul_pos_right hgw0
  have hw1 : 0 < w.toNat := Nat.pos_of_mul_pos_left hgw0
  have hg63 : g.toNat < 2 ^ 63 := by have := Nat.le_mul_of_pos_right g.toNat hw1; omega
  have hw63 : w.toNat < 2 ^ 63 := by have := Nat.le_mul_of_pos_left w.toNat hg1; omega
  have hokw : ∀ i < t.n.toNat, (raw .i64 t.n ok)[i]?.getD 0 < 2 ∧ ((raw .i64 t.n ok)[i]?.getD 0 ≠ 0 ↔
      ((raw .i64 t.n ia)[i]?.getD 0).toNat < g.toNat ∧ ((raw .i64 t.n ic)[i]?.getD 0).toNat < w.toNat) :=
    fun i hi => by
      have e3 := (colMap_raw hok).2.2.2 i hi
      rw [colMap_lt_const hl1 hg63 i hi (Tab.index_le hia wX' wt.1 ⟨i, hi⟩),
        colMap_lt_const hl2 hw63 i hi (Tab.index_le hic wY' wt.2 ⟨i, hi⟩)] at e3
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
    have g1 := (kgather_word hga (Tab.index_plain hia) k hk).2; rw [hi] at g1
    have g2 := (kgather_word hgc (Tab.index_plain hic) k hk).2; rw [hi] at g2
    have e1 := (colMap_post hmu).2 k hk
    rw [g1] at e1
    have e2 := (colMap_raw hpos).2.2.2 k hk
    simp only [Op.eval, Except.ok.injEq] at e1 e2
    rw [← e2, ← e1, g2, UInt64.mul_comm, UInt64.toNat_add, UInt64.toNat_mul, USize.toNat_toUInt64]
    have := bit_lt hA hC
    have hm : ((raw .i64 t.n ia)[i.1]?.getD 0).toNat * w.toNat < 2 ^ 64 := by omega
    rw [Nat.mod_eq_of_lt hm, Nat.mod_eq_of_lt (by omega)]
  have hbw : ∀ k < M.toNat, (raw .i64 M bw)[k]?.getD 0 = (raw .i64 (g * w) o)[((raw .i64 M ps)[k]?.getD 0).toNat]?.getD 0 :=
    fun k hk => (kgather_word hbw hoN k hk).2
  have hbw2 : ∀ k < M.toNat, (raw .i64 M bw)[k]?.getD 0 < 2 := fun k hk => by
    obtain ⟨i, -, -, -, ep, hA, hC⟩ := hrow k hk
    obtain ⟨v, hv, hv2⟩ := ho _ hA _ hC
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
    · rcases Tab.index_spec hia wX' wt.1 i with ⟨a', ea, ra'⟩ | ⟨ea, -⟩
      · obtain ⟨i0, h0, r0⟩ := Vals.gather_row _ hX' a'
        exact ⟨i0, by rw [ea]; exact h0, by rw [← r0, ra', ← rk]⟩
      · omega
    · rcases Tab.index_spec hic wY' wt.2 i with ⟨c', ec, rc'⟩ | ⟨ec, -⟩
      · obtain ⟨i1, h1, r1⟩ := Vals.gather_row _ hY' c'
        exact ⟨i1, by rw [ec]; exact h1, by rw [← r1, rc', ← rv]⟩
      · omega
  · rintro ⟨⟨i, rfl, rfl⟩, a0, ha0, j, hj, hP, ⟨i0, h0, r0⟩, ⟨i1, h1, r1⟩⟩
    have hA : ((raw .i64 t.n ia)[i.1]?.getD 0).toNat = a0 := by
      obtain ⟨i0', h0', r0'⟩ := Vals.gather_row _ hX' ⟨a0, ha0⟩
      have e : i0' = i0 := Fin.ext (h0'.symm.trans h0)
      rcases Tab.index_spec hia wX' wt.1 i with ⟨a', ea, ra'⟩ | ⟨-, hn⟩
      · obtain ⟨i2, h2, r2⟩ := Vals.gather_row _ hX' a'
        rw [ea]; exact congrArg Fin.val (hx a' ⟨a0, ha0⟩ i2 i0 h2 h0 (by rw [← r2, ra', ← r0]))
      · exact (hn ⟨a0, ha0⟩ (by rw [r0', e, r0])).elim
    have hC : ((raw .i64 t.n ic)[i.1]?.getD 0).toNat = j := by
      obtain ⟨i1', h1', r1'⟩ := Vals.gather_row _ hY' ⟨j, hj⟩
      have e : i1' = i1 := Fin.ext (h1'.symm.trans h1)
      rcases Tab.index_spec hic wY' wt.2 i with ⟨c', ec, rc'⟩ | ⟨-, hn⟩
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

/-- **`Tab.compTabMat` is `R ≫ M`** for a matrix `M` as `compMat` and `compTabMat` build it: `0`/`1` words and the
    rows `x[ra[·]]` distinct (else `index` sends `R`'s value to one of two equal rows and drops the other's bits).
    `g · w` not wrapping is `kbitrows`' own law (`raw_kbitrows`). -/
theorem Tab.compTabMat_law {n m M : USize} {r : Tab A B} {g w ka : USize} {o o' ra ra' rc : Enc}
    {x : Vals B n} {key : Vals A M} {y : Vals C m} {t : Tab A C} {s : Tab B C}
    (h : Tab.compTabMat r g w o x ra = .ok (ka, o', ⟨M, key⟩, ra')) (ht : Tab.ofBits ka w o' key ra' y rc = .ok t)
    (hs : Tab.ofBits g w o x ra y rc = .ok s)
    (ho : ∀ a < g.toNat, ∀ j < w.toNat, ∃ v : UInt64, (raw .i64 (g * w) o)[a * w.toNat + j]? = some v ∧ v < 2)
    (hx : ∀ a a' : Fin g.toNat, ∀ i i' : Fin n.toNat, ((raw .i64 g ra)[a.1]?.getD 0).toNat = i.1 →
      ((raw .i64 g ra)[a'.1]?.getD 0).toNat = i'.1 → x.row i = x.row i' → a = a')
    (hra : hasNul ra = false) (hrc : hasNul rc = false) (hr : r.WF) (wx : Vals.WF x) :
    rep t = rep r ≫ rep s := by
  simp only [Tab.compTabMat, bind] at h
  rw [Except.bind_eq_ok'] at h; obtain ⟨X', hX', h⟩ := h
  have wX' := Vals.gather_wf hX' wx
  rw [Except.bind_eq_ok'] at h; obtain ⟨ix, hix, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨lt, hl1, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨⟨M0, sel⟩, hwc, h⟩ := h; try dsimp only at h
  rw [Except.bind_eq_ok'] at h; obtain ⟨key0, hkey, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨⟨ka0, aR, ra0⟩, hcode, h⟩ := h; try dsimp only at h
  rw [Except.bind_eq_ok'] at h; obtain ⟨gi, hgi, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨⟨ends, idx⟩, hcsr, h⟩ := h; try dsimp only at h
  rw [Except.bind_eq_ok'] at h; obtain ⟨o0, hko, h⟩ := h
  simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
  obtain ⟨e1, e2, hS, e3⟩ := h
  subst ka0 o0 ra0
  obtain ⟨eM, eK⟩ := Sigma.mk.inj hS
  subst M0
  have eK' := eq_of_heq eK
  subst key0
  have hU64 : USize.size ≤ 2 ^ 64 := by rcases USize.size_eq with h | h <;> omega
  obtain ⟨hgw, hgw', -, -, -, -, -, hbit⟩ := raw_kbitrows hko
  have hT := Tab.ofBits_set ht (Vals.code_plain hcode).2.1 hrc hgw' fun a ha j hj => by
    obtain ⟨v, -, hv, hv2, -⟩ := hbit a ha j hj; exact ⟨v, hv, hv2⟩
  have hS := Tab.ofBits_set hs hra hrc hgw ho
  apply Core.Rel.ext; intro u v
  show t.Holds u v ↔ ∃ b, r.Holds u b ∧ s.Holds b v
  rw [hT u v]
  -- no column: neither side has a row
  rcases Nat.eq_zero_or_pos w.toNat with hw0 | hw1
  · constructor
    · rintro ⟨-, -, j, hj, -⟩; omega
    · rintro ⟨b, -, hsb⟩; obtain ⟨-, -, j, hj, -⟩ := (hS b v).1 hsb; omega
  have hg63 : g.toNat < 2 ^ 63 := by
    have := Nat.le_mul_of_pos_right g.toNat hw1; have := Tab.ofBits_lt hs; omega
  -- `R`'s rows whose value is a row of `M`, at `ix`
  have hlt : ∀ q < r.n.toNat, (raw .i64 r.n lt)[q]?.getD 0 =
      if ((raw .i64 r.n ix)[q]?.getD 0).toNat < g.toNat then 1 else 0 := fun q hq =>
    colMap_lt_const hl1 hg63 q hq (Tab.index_le hix wX' hr.2 ⟨q, hq⟩)
  have hltb : ∀ q < r.n.toNat, (raw .i64 r.n lt)[q]?.getD 0 < 2 := fun q hq => by
    rw [hlt q hq]; split <;> decide
  have hMr := whereCol_le hwc hltb
  have hr63 := whereCol_lt hwc
  have hselp : ∀ p (hp : p < M.toNat), ∃ q : Fin r.n.toNat, ((raw .i64 M sel)[p]?.getD 0).toNat = q.1 ∧
      key.row ⟨p, hp⟩ = r.key.row q ∧ ((raw .i64 r.n ix)[q.1]?.getD 0).toNat < g.toNat := fun p hp => by
    obtain ⟨q, hq, rk⟩ := Vals.gather_row _ hkey ⟨p, hp⟩
    refine ⟨q, hq, rk, ?_⟩
    have hne := ((whereCol_mem hwc hltb q.1).1 ⟨p, hp, hq⟩).2
    rw [hlt q q.2] at hne
    split at hne
    · assumption
    · exact absurd rfl hne
  -- `key` numbered by value: `gr p` is row `p`'s number, `ra'[a']` a row numbered `a'`
  obtain ⟨hkaM, hcw, hrep, hceq⟩ := Vals.code_spec hcode
  let gr := fun p : Nat => ((raw .i64 M aR)[p]?.getD 0).toNat
  have keyrow : ∀ a' < ka.toNat, ∀ i : Fin M.toNat, ((raw .i64 ka ra')[a']?.getD 0).toNat = i.1 →
      ∀ p : Fin M.toNat, gr p.1 = a' → key.row i = key.row p := fun a' ha i hi p hp => by
    obtain ⟨i2, h2, c2⟩ := hrep a' ha
    have e : i = i2 := Fin.ext (hi.symm.trans h2)
    rw [e]; exact (hceq i2 p).1 (UInt64.toNat_inj.mp (c2.trans hp.symm))
  obtain ⟨π, hπ, hsurj, hgrp⟩ := csr_spec hcsr (Vals.code_plain hcode).2.2 (Vals.code_plain hcode).1
    (kgather_noNul hgi (Tab.index_plain hix)) gr
    (fun q hq => ⟨UInt64.toNat_inj.mp (by simp [gr]), hcw q hq⟩) (by omega)
  have hidx : ∀ k < M.toNat, (raw .i64 M idx)[k]?.getD 0 =
      (raw .i64 r.n ix)[((raw .i64 M sel)[π k]?.getD 0).toNat]?.getD 0 := fun k hk =>
    ((hπ k hk).2).trans (kgather_word hgi (Tab.index_plain hix) (π k) (hπ k hk).1).2
  -- bit `(a', j)` of `o'`: some row `k` of group `a'` has bit `j` of its row of `o`
  have hob : ∀ a' < ka.toNat, ∀ j < w.toNat, ((raw .i64 (ka * w) o')[a' * w.toNat + j]?.getD 0 = 1 ↔
      ∃ k, k < M.toNat ∧ gr (π k) = a' ∧
        (raw .i64 (g * w) o)[((raw .i64 M idx)[k]?.getD 0).toNat * w.toNat + j]?.getD 0 % 2 = 1) :=
    fun a' ha j hj => by
      obtain ⟨v, -, hv, -, hvi⟩ := hbit a' ha j hj
      simp only [Bool.false_eq_true, if_false] at hvi
      rw [hv, Option.getD_some, hvi]
      exact ⟨fun ⟨k, h1, h2, h3⟩ => ⟨k, ((hgrp a' ha k).1 ⟨h1, h2⟩).1, ((hgrp a' ha k).1 ⟨h1, h2⟩).2, h3⟩,
        fun ⟨k, h1, h2, h3⟩ => ⟨k, ((hgrp a' ha k).2 ⟨h1, h2⟩).1, ((hgrp a' ha k).2 ⟨h1, h2⟩).2, h3⟩⟩
  constructor
  · rintro ⟨a', ha', j, hj, hP, ⟨i, hi, ru⟩, hv⟩
    obtain ⟨k, hk, hgk, hon⟩ := (hob a' ha' j hj).1 hP
    have hpk := (hπ k hk).1
    obtain ⟨q, hq, rkey, hqg⟩ := hselp (π k) hpk
    rcases Tab.index_spec hix wX' hr.2 q with ⟨a, ea, ra⟩ | ⟨ea, -⟩
    · obtain ⟨i0, h0, r0⟩ := Vals.gather_row _ hX' a
      refine ⟨r.val.row q, ⟨q, ?_, rfl⟩, (hS _ v).2 ⟨a.1, a.2, j, hj, ?_, ⟨i0, h0, by rw [← r0, ra]⟩, hv⟩⟩
      · rw [← rkey, ← keyrow a' ha' i hi ⟨π k, hpk⟩ hgk, ru]
      · rw [hidx k hk, hq, ea] at hon
        obtain ⟨v', hv', hv2⟩ := ho _ a.2 _ hj
        rw [hv', Option.getD_some] at hon ⊢
        exact (odd_bit hv2).1 hon
    · omega
  · rintro ⟨b, ⟨q, rfl, rfl⟩, hsb⟩
    obtain ⟨a, ha, j, hj, hP, ⟨i0, h0, r0⟩, hv⟩ := (hS _ v).1 hsb
    have hA : ((raw .i64 r.n ix)[q.1]?.getD 0).toNat = a := by
      obtain ⟨i0', h0', r0'⟩ := Vals.gather_row _ hX' ⟨a, ha⟩
      have e : i0' = i0 := Fin.ext (h0'.symm.trans h0)
      rcases Tab.index_spec hix wX' hr.2 q with ⟨a2, ea, ra2⟩ | ⟨-, hn⟩
      · obtain ⟨i2, h2, r2⟩ := Vals.gather_row _ hX' a2
        rw [ea]; exact congrArg Fin.val (hx a2 ⟨a, ha⟩ i2 i0 h2 h0 (by rw [← r2, ra2, ← r0]))
      · exact (hn ⟨a, ha⟩ (by rw [r0', e, r0])).elim
    have hqlt : (raw .i64 r.n lt)[q.1]?.getD 0 ≠ 0 := by
      rw [hlt q q.2, if_pos (by omega)]; decide
    obtain ⟨p, hp, hpq⟩ := (whereCol_mem hwc hltb q.1).2 ⟨q.2, hqlt⟩
    obtain ⟨k, hk, hkp⟩ := hsurj p hp
    have hgp : gr p < ka.toNat := hcw p hp
    obtain ⟨q', hq', rk, -⟩ := hselp p hp
    have eq' : q' = q := Fin.ext (hq'.symm.trans hpq)
    obtain ⟨i, hi, -⟩ := hrep (gr p) hgp
    refine ⟨gr p, hgp, j, hj, (hob _ hgp j hj).2 ⟨k, hk, by rw [hkp], ?_⟩,
      ⟨i, hi, by rw [keyrow (gr p) hgp i hi ⟨p, hp⟩ rfl, rk, eq']⟩, hv⟩
    rw [hidx k hk, hkp, hpq, hA, hP]; decide

/-- `BitsWf`'s word clause in the form `Tab.ofBits_set` reads. -/
theorem some_lt_two {xs : Array UInt64} {k : Nat} (h : (xs[k]?).any (· < 2) = true) :
    ∃ v : UInt64, xs[k]? = some v ∧ v < 2 := by
  cases hk : xs[k]? with
  | none => rw [hk] at h; cases h
  | some v => rw [hk] at h; exact ⟨v, rfl, of_decide_eq_true h⟩

/-- `Vals.code`'s `rep` names distinct rows: two numbers whose rows are equal are one. -/
theorem Vals.code_rep_inj {n k : USize} {x : Vals A n} {c rep : Enc} (h : Vals.code x = .ok (k, c, rep)) :
    ∀ a a' : Fin k.toNat, ∀ i i' : Fin n.toNat, ((raw .i64 k rep)[a.1]?.getD 0).toNat = i.1 →
      ((raw .i64 k rep)[a'.1]?.getD 0).toNat = i'.1 → x.row i = x.row i' → a = a' := by
  obtain ⟨-, -, hrep, hc⟩ := Vals.code_spec h
  intro a a' i i' hi hi' e
  obtain ⟨j, hj, hja⟩ := hrep a.1 a.2
  obtain ⟨j', hj', hja'⟩ := hrep a'.1 a'.2
  obtain rfl : j = i := Fin.ext (hj.symm.trans hi)
  obtain rfl : j' = i' := Fin.ext (hj'.symm.trans hi')
  exact Fin.ext (hja.symm.trans ((congrArg UInt64.toNat ((hc j j').2 e)).trans hja'))

/-- **`compSelM`'s matrix is `BitsWf`** where it reads back: `kbitrows` gives the `0`/`1` words and `g · w`, and
    `Vals.code` the distinct rows of each side. -/
theorem Tab.compSelM_wf {r : Tab A B} {s : Tab B C} {g w : USize} {o ra rc : Enc}
    (h : Tab.compSelM Tab.bitsMax r s = .ok (.inr (g, w, o, ra, rc)))
    (hr : ∀ e, Tab.ofBits g w o r.key ra s.val rc ≠ .error e) : BitsWf g w o r.key ra s.val rc := by
  simp only [Tab.compSelM, bind] at h
  rw [Except.bind_eq_ok'] at h; obtain ⟨_, -, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨_, -, h⟩ := h
  split at h
  · rw [Except.bind_eq_ok'] at h; obtain ⟨_, -, h⟩ := h; cases h
  rw [Except.bind_eq_ok'] at h; obtain ⟨_, -, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨_, -, h⟩ := h
  split at h
  · rw [Except.bind_eq_ok'] at h; obtain ⟨mm, hm, h⟩ := h
    simp only [pure, Except.pure, Except.ok.injEq, Sum.inr.injEq] at h; subst h
    simp only [Tab.compMat, bind] at hm
    rw [Except.bind_eq_ok'] at hm; obtain ⟨_, -, hm⟩ := hm
    rw [Except.bind_eq_ok'] at hm; obtain ⟨⟨ka, aR, ra'⟩, hca, hm⟩ := hm; try dsimp only at hm
    rw [Except.bind_eq_ok'] at hm; obtain ⟨⟨kc, cS, rc'⟩, hcc, hm⟩ := hm; try dsimp only at hm
    split at hm; · cases hm
    rw [Except.bind_eq_ok'] at hm; obtain ⟨_, -, hm⟩ := hm
    rw [Except.bind_eq_ok'] at hm; obtain ⟨_, -, hm⟩ := hm
    rw [Except.bind_eq_ok'] at hm; obtain ⟨_, -, hm⟩ := hm
    rw [Except.bind_eq_ok'] at hm; obtain ⟨o0, hko, hm⟩ := hm
    simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hm
    obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := hm
    obtain ⟨-, hgw, -, -, -, -, -, hbit⟩ := raw_kbitrows hko
    refine ⟨hr, hgw, fun a ha j hj => ?_, Vals.code_rep_inj hca, Vals.code_rep_inj hcc, (Vals.code_plain hca).2.1,
      (Vals.code_plain hcc).2.1, kbitrows_plain hko⟩
    obtain ⟨v, -, hv, hv2, -⟩ := hbit a ha j hj
    rw [hv]; exact decide_eq_true hv2
  · rw [Except.bind_eq_ok'] at h; obtain ⟨_, -, h⟩ := h; cases h

/-- **`compTabMat` keeps a matrix `BitsWf`** where its own reads back: its words and `g · w` from `kbitrows`, its rows
    `key[ra'[·]]` from `Vals.code`, and its columns `y[rc[·]]` unchanged. -/
theorem Tab.compTabMat_wf {n m M : USize} {r : Tab A B} {g w ka : USize} {o o' ra ra' rc : Enc}
    {x : Vals B n} {key : Vals A M} {y : Vals C m}
    (h : Tab.compTabMat r g w o x ra = .ok (ka, o', ⟨M, key⟩, ra'))
    (hr : ∀ e, Tab.ofBits ka w o' key ra' y rc ≠ .error e) (hw : BitsWf g w o x ra y rc) :
    BitsWf ka w o' key ra' y rc := by
  simp only [Tab.compTabMat, bind] at h
  rw [Except.bind_eq_ok'] at h; obtain ⟨_, -, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨_, -, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨_, -, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨⟨M0, sel⟩, -, h⟩ := h; try dsimp only at h
  rw [Except.bind_eq_ok'] at h; obtain ⟨key0, -, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨⟨ka0, aR, ra0⟩, hcode, h⟩ := h; try dsimp only at h
  rw [Except.bind_eq_ok'] at h; obtain ⟨_, -, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨_, -, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨o0, hko, h⟩ := h
  simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
  obtain ⟨e1, e2, hS, e3⟩ := h
  subst ka0 o0 ra0
  obtain ⟨eM, eK⟩ := Sigma.mk.inj hS
  subst M0
  have eK' := eq_of_heq eK
  subst key0
  obtain ⟨-, hgw, -, -, -, -, -, hbit⟩ := raw_kbitrows hko
  refine ⟨hr, hgw, fun a ha j hj => ?_, Vals.code_rep_inj hcode, hw.2.2.2.2.1, (Vals.code_plain hcode).2.1,
    hw.2.2.2.2.2.2.1, kbitrows_plain hko⟩
  obtain ⟨v, -, hv, hv2, -⟩ := hbit a ha j hj
  rw [hv]; exact decide_eq_true hv2

/-- **`kbitrows` over a `csr` grouping**: group `G`'s bit `j` is the `∧` (`all`) or the `∨` of bit `j` of the matrix
    rows `x[q]` of the input rows `q` with `gr q = G`, stated over the input rows rather than `csr`'s order. -/
theorem csr_kbitrows {all : Bool} {n g na w : USize} {gid x ends idx m o : Enc}
    (hc : csr n g gid x = .ok (ends, idx)) (hk : kbitrows all w na n g ends idx m = .ok o)
    (hgW : Ext.Enc.WF .i64 n gid) (hgN : hasNul gid = false) (hxN : hasNul x = false) (gr : Nat → Nat)
    (hg : ∀ q < n.toNat, (raw .i64 n gid)[q]?.getD 0 = (gr q).toUInt64 ∧ gr q < g.toNat) (hg63 : g.toNat ≤ 2 ^ 63) :
    (na * w).toNat = na.toNat * w.toNat ∧ (g * w).toNat = g.toNat * w.toNat ∧
    (∀ q < n.toNat, ((raw .i64 n x)[q]?.getD 0).toNat < na.toNat) ∧
    ∀ G < g.toNat, ∀ j < w.toNat, ∃ v : UInt64, (raw .i64 (g * w) o)[G * w.toNat + j]? = some v ∧ v < 2 ∧
      (v = 1 ↔ if all then ∀ q < n.toNat, gr q = G →
          (raw .i64 (na * w) m)[((raw .i64 n x)[q]?.getD 0).toNat * w.toNat + j]?.getD 0 % 2 = 1
        else ∃ q < n.toNat, gr q = G ∧
          (raw .i64 (na * w) m)[((raw .i64 n x)[q]?.getD 0).toNat * w.toNat + j]?.getD 0 % 2 = 1) := by
  obtain ⟨π, hπ, hsurj, hseg⟩ := csr_spec hc hgW hgN hxN gr hg hg63
  obtain ⟨hna, hgw, -, -, -, -, hidx, hbit⟩ := raw_kbitrows hk
  refine ⟨hna, hgw, fun q hq => ?_, fun G hG j hj => ?_⟩
  · obtain ⟨t, ht, rfl⟩ := hsurj q hq
    rw [← (hπ t ht).2]; exact hidx t ht
  obtain ⟨v, -, hv, hv2, hv1⟩ := hbit G hG j hj
  refine ⟨v, hv, hv2, hv1.trans ?_⟩
  cases all
  · simp only [Bool.false_eq_true, if_false]
    constructor
    · rintro ⟨t, h1, h2, h3⟩
      obtain ⟨ht, hgt⟩ := (hseg G hG t).1 ⟨h1, h2⟩
      exact ⟨π t, (hπ t ht).1, hgt, by rw [← (hπ t ht).2]; exact h3⟩
    · rintro ⟨q, hq, hgq, h3⟩
      obtain ⟨t, ht, rfl⟩ := hsurj q hq
      obtain ⟨h1, h2⟩ := (hseg G hG t).2 ⟨ht, hgq⟩
      exact ⟨t, h1, h2, by rw [(hπ t ht).2]; exact h3⟩
  · simp only [if_true]
    constructor
    · intro H q hq hgq
      obtain ⟨t, ht, rfl⟩ := hsurj q hq
      obtain ⟨h1, h2⟩ := (hseg G hG t).2 ⟨ht, hgq⟩
      have := H t h1 h2; rw [(hπ t ht).2] at this; exact this
    · intro H t h1 h2
      obtain ⟨ht, hgt⟩ := (hseg G hG t).1 ⟨h1, h2⟩
      rw [(hπ t ht).2]; exact H _ (hπ t ht).1 hgt

/-- `Vals.code2`'s `rep` names distinct rows of its CONCAT `z`: two numbers whose rows are equal are one. -/
theorem Vals.code2_rep_inj {n₁ n₂ k N : USize} {x : Vals A n₁} {y : Vals A n₂} {bx bY rep : Enc} {z : Vals A N}
    (h : Vals.code2 x y = .ok (k, bx, bY, ⟨N, z, rep⟩)) (wx : Vals.WF x) (wy : Vals.WF y) :
    ∀ a a' : Fin k.toNat, ∀ i i' : Fin N.toNat, ((raw .i64 k rep)[a.1]?.getD 0).toNat = i.1 →
      ((raw .i64 k rep)[a'.1]?.getD 0).toNat = i'.1 → z.row i = z.row i' → a = a' := fun a a' i i' hi hi' e => by
  obtain ⟨cx, cy, -, -, -, -, -, -, hrep⟩ := Vals.code2_spec h wx wy
  obtain ⟨t, ht, hex, hx, hy⟩ := hrep a a.2
  obtain ⟨t', ht', -, hx', hy'⟩ := hrep a' a'.2
  obtain rfl : t = i := Fin.ext (ht.symm.trans hi)
  obtain rfl : t' = i' := Fin.ext (ht'.symm.trans hi')
  apply Fin.ext
  rcases hex with ⟨q, hq⟩ | ⟨u, hu⟩
  · exact hq.symm.trans ((hx' q).2 (((hx q).1 hq).trans e))
  · exact hu.symm.trans ((hy' u).2 (((hy u).1 hu).trans e))

/-- **What `Tab.ldivTabMat` builds**, for a matrix `M` as `Tab.keepBits_law` reads it: `kb · kc` `0`/`1` words whose
    set bits `(G, jj)` (`PP`) read back through `zb[rb[·]]`, `zc[rc'[·]]` as `ldivDen r M ub uc`, both sides distinct.
    `Tab.ldivTabMat_law` and `Tab.ldivTabMat_wf` read it. -/
theorem Tab.ldivTabMat_spec {n m N N' : USize} {r : Tab A B} {ub : Tab B B} {uc : Tab C C} {g w kb kc : USize}
    {o o' ra rb rc rc' : Enc} {x : Vals A n} {y : Vals C m} {zb : Vals B N} {zc : Vals C N'} {s : Tab A C}
    (h : Tab.ldivTabMat r ub uc g w o x ra y rc = .ok (some (kb, kc, o', ⟨N, zb⟩, rb, ⟨N', zc⟩, rc')))
    (hs : Tab.ofBits g w o x ra y rc = .ok s)
    (ho : ∀ a < g.toNat, ∀ j < w.toNat, ∃ v : UInt64, (raw .i64 (g * w) o)[a * w.toNat + j]? = some v ∧ v < 2)
    (hx : ∀ a a' : Fin g.toNat, ∀ i i' : Fin n.toNat, ((raw .i64 g ra)[a.1]?.getD 0).toNat = i.1 →
      ((raw .i64 g ra)[a'.1]?.getD 0).toNat = i'.1 → x.row i = x.row i' → a = a')
    (hy : ∀ j j' : Fin w.toNat, ∀ i i' : Fin m.toNat, ((raw .i64 w rc)[j.1]?.getD 0).toNat = i.1 →
      ((raw .i64 w rc)[j'.1]?.getD 0).toNat = i'.1 → y.row i = y.row i' → j = j')
    (hraN : hasNul ra = false) (hrcN : hasNul rc = false) (hr : r.WF) (hub : ub.WF) (huc : uc.WF) (wx : Vals.WF x) (wy : Vals.WF y) :
    (kb * kc).toNat = kb.toNat * kc.toNat ∧ kb.toNat * kc.toNat < 2 ^ 63 ∧ ∃ PP : Nat → Nat → Prop,
      (∀ G < kb.toNat, ∀ jj < kc.toNat, ∃ v : UInt64,
        (raw .i64 (kb * kc) o')[G * kc.toNat + jj]? = some v ∧ v < 2 ∧ (v = 1 ↔ PP G jj)) ∧
      (∀ b c, (∃ G < kb.toNat, ∃ jj < kc.toNat, PP G jj ∧
        (∃ i : Fin N.toNat, ((raw .i64 kb rb)[G]?.getD 0).toNat = i.1 ∧ zb.row i = b) ∧
        ∃ i : Fin N'.toNat, ((raw .i64 kc rc')[jj]?.getD 0).toNat = i.1 ∧ zc.row i = c) ↔
        Lang.ldivDen r.Holds s.Holds ub.Holds uc.Holds b c) ∧
      (∀ a a' : Fin kb.toNat, ∀ i i' : Fin N.toNat, ((raw .i64 kb rb)[a.1]?.getD 0).toNat = i.1 →
        ((raw .i64 kb rb)[a'.1]?.getD 0).toNat = i'.1 → zb.row i = zb.row i' → a = a') ∧
      (∀ c c' : Fin kc.toNat, ∀ i i' : Fin N'.toNat, ((raw .i64 kc rc')[c.1]?.getD 0).toNat = i.1 →
        ((raw .i64 kc rc')[c'.1]?.getD 0).toNat = i'.1 → zc.row i = zc.row i' → c = c') ∧
      hasNul rb = false ∧ hasNul rc' = false ∧ hasNul o' = false := by
  classical
  simp only [Tab.ldivTabMat, bind] at h
  rw [Except.bind_eq_ok'] at h; obtain ⟨⟨kb0, bR, bU, Nb, zb0, rb0⟩, hb2, h⟩ := h; try dsimp only at h
  rw [Except.bind_eq_ok'] at h; obtain ⟨yM, hyM, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨⟨kc0, cM, cU, Nc, zc0, rc0⟩, hc2, h⟩ := h; try dsimp only at h
  split at h
  · cases h
  rename_i hov
  rw [Except.bind_eq_ok'] at h; obtain ⟨_, -, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨Xg, hXg, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨ix, hix, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨on, hon, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨⟨P, sel⟩, hP, h⟩ := h; try dsimp only at h
  rw [Except.bind_eq_ok'] at h; obtain ⟨gb, hgb, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨gi, hgi, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨⟨ends, idx⟩, hcsr, h⟩ := h; try dsimp only at h
  rw [Except.bind_eq_ok'] at h; obtain ⟨o1, hk, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨one, hone, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨cnt, hcnt, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨vac, hvac, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨cnt2, hcnt2, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨eq2, heq2, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨keep, hkeep, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨io, hio, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨rr, hrr, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨rm, hrm, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨im, him, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨gm, hgm, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨p1, hp1, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨gk, hgk, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨v1, hv1, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨s1, hs1, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨⟨E, eb⟩, hE, h⟩ := h; try dsimp only at h
  rw [Except.bind_eq_ok'] at h; obtain ⟨jo, hjo, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨jd, hjd, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨ge, hge, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨jm, hjm, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨gu, hgu, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨s2, hs2, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨out, hout, h⟩ := h
  simp only [pure, Except.pure, Except.ok.injEq, Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨e1, e2, e3, hzb, e4, hzc, e5⟩ := h
  subst kb0 kc0 out rb0 rc0
  obtain ⟨eN, eZ⟩ := Sigma.mk.inj hzb; subst Nb; have eZ' := eq_of_heq eZ; subst zb0
  obtain ⟨eN', eZ2⟩ := Sigma.mk.inj hzc; subst Nc; have eZ2' := eq_of_heq eZ2; subst zc0
  have hU64 : USize.size ≤ 2 ^ 64 := by rcases USize.size_eq with h | h <;> omega
  have hU32 : 2 ^ 32 ≤ USize.size := by rcases USize.size_eq with h | h <;> omega
  have hnb : 2 ^ System.Platform.numBits = USize.size := rfl
  simp only [not_or, Nat.not_lt, Tab.bitsMax] at hov
  obtain ⟨ov1, ov2, ov3⟩ := hov
  have hkbc : (kb * kc).toNat = kb.toNat * kc.toNat := by rw [USize.toNat_mul]; exact Nat.mod_eq_of_lt (by omega)
  have hkbw : (kb * w).toNat = kb.toNat * w.toNat := by rw [USize.toNat_mul]; exact Nat.mod_eq_of_lt (by omega)
  have u64eq : ∀ a b : Nat, a < 2 ^ 64 → b < 2 ^ 64 → (a.toUInt64 = b.toUInt64 ↔ a = b) := fun a b ha hb =>
    ⟨fun e => by have := congrArg UInt64.toNat e; rwa [toNat_toUInt64 ha, toNat_toUInt64 hb] at this,
      fun e => e ▸ rfl⟩
  have hev : ∀ a b : UInt64, Op.eval .eq a b = .ok (if a = b then 1 else 0) := fun a b => by
    show Except.ok (if (a == b) = true then 1 else 0) = _; by_cases h : a = b <;> simp [h]
  have hevlt : ∀ (p q : Prop) [Decidable p] [Decidable q],
      Op.eval .lt (if p then 1 else 0) (if q then 1 else 0) = .ok (if ¬p ∧ q then 1 else 0) := by
    intro p q _ _; by_cases hp : p <;> by_cases hq : q <;> simp [hp, hq] <;> rfl
  have hdm : ∀ {a b U : Nat}, b < U → (a * U + b) / U = a ∧ (a * U + b) % U = b := fun hb =>
    ⟨by rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt hb, Nat.zero_add],
      by rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hb]⟩
  have hdm2 : ∀ {a b x y U : Nat}, x < U → y < U → a * U + x = b * U + y → a = b ∧ x = y := fun {a b x y U} hx hy e => by
    have h1 := hdm (a := a) hx; have h2 := hdm (a := b) hy; rw [e] at h1
    exact ⟨h1.1.symm.trans h2.1, h1.2.symm.trans h2.2⟩
  have ifc : ∀ {p q : Prop} [Decidable p] [Decidable q], (p ↔ q) → (if p then (1 : UInt64) else 0) = if q then 1 else 0 :=
    fun {p q} _ _ h => if hp : p then by rw [if_pos hp, if_pos (h.1 hp)] else by rw [if_neg hp, if_neg fun hq => hp (h.2 hq)]
  have hcl : ∀ p : Nat → Bool, (List.range r.n.toNat).countP p < 2 ^ 64 := fun p =>
    Nat.lt_of_le_of_lt List.countP_le_length (by rw [List.length_range]; have := r.n.toNat_lt_size; omega)
  have hkb63 := whereCol_lt hE
  have wyM := Vals.gather_wf hyM wy
  have wXg := Vals.gather_wf hXg wx
  obtain ⟨bx, bu, -, hbx, hbu, -, -, -, hrb⟩ := Vals.code2_spec hb2 hr.2 hub.2
  obtain ⟨cm, cu, -, hcm, hcu, hcmi, -, -, hrc⟩ := Vals.code2_spec hc2 wyM huc.2
  obtain ⟨ixN, hixN⟩ : ∃ f : Nat → Nat, ∀ i, ((raw .i64 r.n ix)[i]?.getD 0).toNat = f i := ⟨_, fun _ => rfl⟩
  obtain ⟨selN, hselN⟩ : ∃ f : Nat → Nat, ∀ q, ((raw .i64 P sel)[q]?.getD 0).toNat = f q := ⟨_, fun _ => rfl⟩
  let Vac := fun G => ∀ i < r.n.toNat, bx i ≠ G
  let Kp := fun G => ∀ i < r.n.toNat, bx i = G → ixN i < g.toNat
  let Al := fun G j => ∀ i < r.n.toNat, bx i = G → ixN i < g.toNat →
    (raw .i64 (g * w) o)[ixN i * w.toNat + j]?.getD 0 = 1
  -- `o1`: each value's `∧` over its rows whose key is a row of `M`
  obtain ⟨hgw, -, -, hbit⟩ := csr_kbitrows hcsr hk ((kgather_closed hgb).2.2 rfl (by decide))
    (kgather_noNul hgb (Vals.code2_plain hb2).1) (kgather_noNul hgi (Tab.index_plain hix)) (fun q => bx (selN q)) (fun q hq => by
      obtain ⟨h1, h2⟩ := kgather_word hgb (Vals.code2_plain hb2).1 q hq; rw [h2, hselN]; rw [hselN] at h1; exact hbx _ h1) (by omega)
  have hS := Tab.ofBits_set hs hraN hrcN hgw ho
  -- `cm` is one-to-one: the columns `y[rc[·]]` are distinct
  have cminj : ∀ j j', j < w.toNat → j' < w.toNat → cm j = cm j' → j = j' := fun j j' hj hj' e => by
    obtain ⟨i, hi, ri⟩ := Vals.gather_row _ hyM ⟨j, hj⟩
    obtain ⟨i', hi', ri'⟩ := Vals.gather_row _ hyM ⟨j', hj'⟩
    have := (hcmi ⟨j, hj⟩ ⟨j', hj'⟩).1 e
    rw [ri, ri'] at this
    exact congrArg Fin.val (hy ⟨j, hj⟩ ⟨j', hj'⟩ i i' hi hi' this)
  -- column `j` of `M` is column `jj` of the answer exactly when `cm j = jj`
  have hcol : ∀ j < w.toNat, ∀ jj < kc.toNat, ∀ t' : Fin N'.toNat, ((raw .i64 kc rc')[jj]?.getD 0).toNat = t'.1 →
      ((∃ i : Fin m.toNat, ((raw .i64 w rc)[j]?.getD 0).toNat = i.1 ∧ y.row i = zc.row t') ↔ cm j = jj) :=
    fun j hj jj hjj t' ht' => by
      obtain ⟨t2, ht2, -, hxc, -⟩ := hrc jj hjj
      obtain rfl : t2 = t' := Fin.ext (ht2.symm.trans ht')
      obtain ⟨i, hi, ri⟩ := Vals.gather_row _ hyM ⟨j, hj⟩
      refine Iff.trans ?_ (hxc ⟨j, hj⟩).symm
      rw [ri]
      exact ⟨fun ⟨i', hi', e⟩ => by rw [show i = i' from Fin.ext (hi.symm.trans hi')]; exact e,
        fun e => ⟨i, hi, e⟩⟩
  -- `s` at row `i`'s key: row `ixN i` of `M`, none where the key is no row of `M`
  have hSrow : ∀ i : Fin r.n.toNat, ∀ c, s.Holds (r.key.row i) c ↔ ixN i < g.toNat ∧ ∃ j < w.toNat,
      (raw .i64 (g * w) o)[ixN i * w.toNat + j]?.getD 0 = 1 ∧
      ∃ i' : Fin m.toNat, ((raw .i64 w rc)[j]?.getD 0).toNat = i'.1 ∧ y.row i' = c := fun i c => by
    rw [hS]
    rcases Tab.index_spec hix wXg hr.1 i with ⟨a, ea, ra⟩ | ⟨ea, hn⟩
    · rw [hixN] at ea
      obtain ⟨i0, h0, r0⟩ := Vals.gather_row _ hXg a
      constructor
      · rintro ⟨a', ha', j, hj, hb, ⟨i1, h1, r1⟩, hc⟩
        have e := hx ⟨a', ha'⟩ a i1 i0 h1 h0 (by rw [r1, ← ra, r0])
        refine ⟨by rw [ea]; exact a.2, j, hj, ?_, hc⟩
        rw [ea, ← congrArg Fin.val e]; exact hb
      · rintro ⟨-, j, hj, hb, hc⟩
        rw [ea] at hb
        exact ⟨a.1, a.2, j, hj, hb, ⟨i0, h0, by rw [← r0, ra]⟩, hc⟩
    · rw [hixN] at ea
      constructor
      · rintro ⟨a', ha', j, hj, -, ⟨i1, h1, r1⟩, -⟩
        obtain ⟨i2, h2, r2⟩ := Vals.gather_row _ hXg ⟨a', ha'⟩
        obtain rfl : i2 = i1 := Fin.ext (h2.symm.trans h1)
        exact (hn ⟨a', ha'⟩ (by rw [r2, r1])).elim
      · rintro ⟨hlt, -⟩; omega
  -- `cnt[G]` counts `r`'s rows valued `G`; `vac[G]` is `1` exactly when there is none
  have hcntw := scatter_add_count hcnt (kscatter_plain hone rfl) bx (fun _ => true) (fun q hq => (hbx q hq).1) (fun q hq => by
    have := (hbx q hq).2; have := kb.toNat_lt_size; omega) (fun q hq => by rw [colConst_raw hone, Array.getElem?_replicate, if_pos hq, Option.getD_some]; rfl)
  have hvacw : ∀ G < kb.toNat, (raw .i64 kb vac)[G]?.getD 0 = if Vac G then 1 else 0 := fun G hG => by
    have e := (colMap_post hvac).2 G hG
    rw [hev, hcntw G hG, Except.ok.injEq] at e
    rw [← e]
    refine ifc ?_
    rw [eq_comm, show (0 : UInt64) = (0 : Nat).toUInt64 from rfl, u64eq _ _ (hcl _) (by omega)]
    simp only [Bool.and_true, List.countP_eq_zero, List.mem_range, beq_iff_eq, Vac]
  have hvacb : ∀ G < kb.toNat, (raw .i64 kb vac)[G]?.getD 0 < 2 := fun G hG => by
    rw [hvacw G hG]; split <;> decide
  have hEm : ∀ G, (∃ e < E.toNat, ((raw .i64 E eb)[e]?.getD 0).toNat = G) ↔ G < kb.toNat ∧ Vac G := fun G => by
    refine (whereCol_mem hE hvacb G).trans ⟨fun ⟨hG, hne⟩ => ⟨hG, ?_⟩, fun ⟨hG, hv⟩ => ⟨hG, ?_⟩⟩
    · rw [hvacw G hG] at hne; split at hne
      · assumption
      · exact absurd rfl hne
    · rw [hvacw G hG, if_pos hv]; decide
  have hEk := whereCol_le hE hvacb
  have hNU : (E * uc.n).toNat = E.toNat * uc.n.toNat := by
    rw [USize.toNat_mul]; exact Nat.mod_eq_of_lt (by have := Nat.mul_le_mul_right uc.n.toNat hEk; omega)
  -- `s2`: the vacant values by every column of `uc`
  have hs2w : ∀ G < kb.toNat, ∀ jj < kc.toNat, (raw .i64 (kb * kc) s2)[G * kc.toNat + jj]?.getD 0 =
      if Vac G ∧ ∃ u < uc.n.toNat, cu u = jj then 1 else 0 := fun G hG jj hjj => by
    have hkU : ∀ k < (E * uc.n).toNat, k / uc.n.toNat < E.toNat ∧ k % uc.n.toNat < uc.n.toNat ∧
        (raw .i64 (E * uc.n) ge)[k]?.getD 0 = (raw .i64 E eb)[k / uc.n.toNat]?.getD 0 ∧
        (raw .i64 (E * uc.n) gu)[k]?.getD 0 = (cu (k % uc.n.toNat)).toUInt64 := fun k hk' => by
      have hk := hk'; rw [hNU] at hk
      have hU0 : 0 < uc.n.toNat := Nat.pos_of_ne_zero fun h0 => by rw [h0, Nat.mul_zero] at hk; omega
      have hE0 : 0 < E.toNat := Nat.pos_of_ne_zero fun h0 => by rw [h0, Nat.zero_mul] at hk; omega
      have hU27 : uc.n.toNat ≤ 2 ^ 27 := by
        have := Nat.le_mul_of_pos_left uc.n.toNat (show 0 < kb.toNat by omega); omega
      have hk63 : k < 2 ^ 63 := by have := Nat.mul_le_mul_right uc.n.toNat hEk; omega
      have eU : uc.n.toUInt64 = uc.n.toNat.toUInt64 := UInt64.toNat_inj.mp (by simp)
      have ed : (raw .i64 (E * uc.n) jd)[k]?.getD 0 = (k / uc.n.toNat).toUInt64 := by
        have e := (colMap_post hjd).2 k hk'
        rw [((shiftCol_raw hjo k hk').trans (UInt64.add_zero _)), eU, eval_rdiv_nat hk63 (by omega) hU0, Except.ok.injEq] at e
        exact e.symm
      have em : (raw .i64 (E * uc.n) jm)[k]?.getD 0 = (k % uc.n.toNat).toUInt64 := by
        have e := (colMap_post hjm).2 k hk'
        rw [((shiftCol_raw hjo k hk').trans (UInt64.add_zero _)), eU, eval_rmod_nat hk63 (by omega) hU0, Except.ok.injEq] at e
        exact e.symm
      have hkm := Nat.mod_lt k hU0
      refine ⟨(Nat.div_lt_iff_lt_mul hU0).2 hk, hkm, ?_, ?_⟩
      · rw [(kgather_word hge (whereCol_plain hE) k hk').2, ed, toNat_toUInt64 (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (by omega))]
      · rw [(kgather_word hgu (Vals.code2_plain hc2).2.1 k hk').2, em, toNat_toUInt64 (by omega), (hcu _ hkm).1]
    have hcuk : ∀ u < uc.n.toNat, ((cu u).toUInt64).toNat = cu u := fun u hu =>
      toNat_toUInt64 (by have := (hcu u hu).2; have := kc.toNat_lt_size; omega)
    rw [bitMatrix_spec hs2 hkbc (fun k hk => by
        obtain ⟨hkd, -, eg, -⟩ := hkU k hk; rw [eg]; exact ((hEm _).1 ⟨_, hkd, rfl⟩).1)
      (fun k hk => by obtain ⟨-, hkm, -, eu⟩ := hkU k hk; rw [eu, hcuk _ hkm]; exact (hcu _ hkm).2) G hG jj hjj]
    refine ifc ⟨fun ⟨k, hk, e1, e2⟩ => ?_, fun ⟨hv, u, hu, e⟩ => ?_⟩
    · obtain ⟨hkd, hkm, eg, eu⟩ := hkU k hk
      rw [eg] at e1; rw [eu, hcuk _ hkm] at e2
      exact ⟨by rw [← e1]; exact ((hEm _).1 ⟨_, hkd, rfl⟩).2, k % uc.n.toNat, hkm, e2⟩
    · obtain ⟨e', he', hee⟩ := (hEm G).2 ⟨hG, hv⟩
      have hk : e' * uc.n.toNat + u < (E * uc.n).toNat := by rw [hNU]; exact bit_lt he' hu
      obtain ⟨hd, hm⟩ := hdm (a := e') hu
      obtain ⟨-, -, eg, eu⟩ := hkU _ hk
      exact ⟨_, hk, by rw [eg, hd]; exact hee, by rw [eu, hm, hcuk _ hu, e]⟩
  -- `s1`: bit `(G, cm j)` is `o1`'s bit `(G, j)` where `keep[G]`
  have hs1w : ∀ G < kb.toNat, ∀ jj < kc.toNat, (raw .i64 (kb * kc) s1)[G * kc.toNat + jj]?.getD 0 =
      if ¬Vac G ∧ Kp G ∧ ∃ j < w.toNat, cm j = jj ∧ Al G j then 1 else 0 := by
    intro G hG jj hjj
    obtain ⟨hsz, -, hsw⟩ := kscatter_words hs1 (colMap_plain hv1)
    obtain ⟨-, hfill, hlast⟩ := (scatterWords_spec _ _ _ _).2 _ hsw
    have hT : G * kc.toNat + jj < (kb * kc).toNat := by rw [hkbc]; exact bit_lt hG hjj
    rcases Nat.eq_zero_or_pos w.toNat with hw0 | hw1
    · rw [hfill _ hT fun k hk => absurd hk (by rw [hsz, hkbw, hw0, Nat.mul_zero]; exact Nat.not_lt_zero k),
        Option.getD_some, if_neg fun ⟨_, _, j, hj, _⟩ => by omega]
    have hw27 : w.toNat ≤ 2 ^ 27 := by
      have := Nat.le_mul_of_pos_left w.toNat (show 0 < kb.toNat by omega); omega
    have hg63 : g.toNat < 2 ^ 63 := by
      have := Nat.le_mul_of_pos_right g.toNat hw1; have := Tab.ofBits_lt hs; omega
    have honw : ∀ i < r.n.toNat, (raw .i64 r.n on)[i]?.getD 0 = if ixN i < g.toNat then 1 else 0 := fun i hi => by
      have := colMap_lt_const hon hg63 i hi (Tab.index_le hix wXg hr.1 ⟨i, hi⟩); rwa [hixN] at this
    have honb : ∀ i < r.n.toNat, (raw .i64 r.n on)[i]?.getD 0 < 2 := fun i hi => by
      rw [honw i hi]; split <;> decide
    have hsel : ∀ i, (∃ q < P.toNat, selN q = i) ↔ i < r.n.toNat ∧ ixN i < g.toNat := fun i => by
      have := whereCol_mem hP honb i; simp only [hselN] at this
      refine this.trans ⟨fun ⟨hi, hne⟩ => ⟨hi, ?_⟩, fun ⟨hi, hlt⟩ => ⟨hi, ?_⟩⟩
      · rw [honw i hi] at hne; split at hne
        · assumption
        · exact absurd rfl hne
      · rw [honw i hi, if_pos hlt]; decide
    have hAl : ∀ j < w.toNat, ∃ v : UInt64, (raw .i64 (kb * w) o1)[G * w.toNat + j]? = some v ∧ v < 2 ∧
        (v = 1 ↔ Al G j) := fun j hj => by
      obtain ⟨v, hv, hv2, hv1'⟩ := hbit G hG j hj
      refine ⟨v, hv, hv2, hv1'.trans ?_⟩
      simp only [↓reduceIte]
      constructor
      · intro H i hi hiG hlt
        obtain ⟨q, hq, hqi⟩ := (hsel i).2 ⟨hi, hlt⟩
        have := H q hq (by rw [hqi]; exact hiG)
        rw [(kgather_word hgi (Tab.index_plain hix) q hq).2, hselN, hqi, hixN] at this
        obtain ⟨v', hv', hv2'⟩ := ho _ hlt j hj
        rw [hv', Option.getD_some] at this ⊢; exact (odd_bit hv2').1 this
      · intro H q hq hgq
        obtain ⟨hi, hlt⟩ := (hsel _).1 ⟨q, hq, rfl⟩
        rw [(kgather_word hgi (Tab.index_plain hix) q hq).2, hselN, hixN, H _ hi hgq hlt]; decide
    have hcnt2w := scatter_add_count hcnt2 (colMap_plain hon) bx (fun q => decide (ixN q < g.toNat)) (fun q hq => (hbx q hq).1)
      (fun q hq => by have := (hbx q hq).2; have := kb.toNat_lt_size; omega) (fun q hq => by rw [honw q hq]; simp)
    have hkeepw : (raw .i64 kb keep)[G]?.getD 0 = if ¬Vac G ∧ Kp G then 1 else 0 := by
      have e := (colMap_raw hkeep).2.2.2 G hG
      have e2 := (colMap_raw heq2).2.2.2 G hG
      rw [hev, hcntw G hG, hcnt2w G hG, Except.ok.injEq] at e2
      rw [hvacw G hG, ← e2, hevlt, Except.ok.injEq] at e
      rw [← e]
      refine ifc (and_congr Iff.rfl ?_)
      rw [u64eq _ _ (hcl _) (hcl _)]
      have hsp := countP_split (fun q => bx q == G) (fun q => decide (ixN q < g.toNat)) (List.range r.n.toNat)
      simp only [Bool.and_true] at hsp ⊢
      constructor
      · intro e i hi hiG
        have hB : (List.range r.n.toNat).countP (fun q => (bx q == G) && !decide (ixN q < g.toNat)) = 0 := by omega
        rw [List.countP_eq_zero] at hB
        have := hB i (List.mem_range.2 hi)
        simp only [hiG, beq_self_eq_true, Bool.true_and, Bool.not_eq_eq_eq_not, Bool.not_true,
          decide_eq_false_iff_not, Classical.not_not] at this
        exact this
      · intro H
        have hB : (List.range r.n.toNat).countP (fun q => (bx q == G) && !decide (ixN q < g.toNat)) = 0 :=
          List.countP_eq_zero.2 fun i hi hh => by
            simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_eq_eq_not, Bool.not_true,
              decide_eq_false_iff_not] at hh
            exact hh.2 (H i (List.mem_range.1 hi) hh.1)
        omega
    have hpk : ∀ k < (kb * w).toNat, ((raw .i64 (kb * w) p1)[k]?.getD 0).toNat =
        k / w.toNat * kc.toNat + cm (k % w.toNat) ∧ k / w.toNat < kb.toNat ∧ k % w.toNat < w.toNat ∧
        (raw .i64 (kb * w) gk)[k]?.getD 0 = (raw .i64 kb keep)[k / w.toNat]?.getD 0 := fun k hk => by
      have hkw : k / w.toNat < kb.toNat := (Nat.div_lt_iff_lt_mul hw1).2 (by rw [← hkbw]; exact hk)
      have hkm : k % w.toNat < w.toNat := Nat.mod_lt _ hw1
      have hk63 : k < 2 ^ 63 := by omega
      have ew : w.toUInt64 = w.toNat.toUInt64 := UInt64.toNat_inj.mp (by simp)
      have erd : (raw .i64 (kb * w) rr)[k]?.getD 0 = (k / w.toNat).toUInt64 := by
        have e := (colMap_post hrr).2 k hk
        rw [((shiftCol_raw hio k hk).trans (UInt64.add_zero _)), ew, eval_rdiv_nat hk63 (by omega) hw1, Except.ok.injEq] at e
        exact e.symm
      have emd : (raw .i64 (kb * w) im)[k]?.getD 0 = (k % w.toNat).toUInt64 := by
        have e := (colMap_post him).2 k hk
        rw [((shiftCol_raw hio k hk).trans (UInt64.add_zero _)), ew, eval_rmod_nat hk63 (by omega) hw1, Except.ok.injEq] at e
        exact e.symm
      have egm := (kgather_word hgm (Vals.code2_plain hc2).1 k hk).2
      rw [emd, toNat_toUInt64 (by omega), (hcm _ hkm).1] at egm
      have erm := (colMap_post hrm).2 k hk
      rw [erd] at erm
      have ep := (colMap_raw hp1).2.2.2 k hk
      simp only [Op.eval, Except.ok.injEq] at erm ep
      rw [UInt64.mul_comm] at erm
      have hb := bit_lt hkw (hcm _ hkm).2
      refine ⟨?_, hkw, hkm, ?_⟩
      · rw [← ep, ← erm, egm, UInt64.toNat_add, UInt64.toNat_mul, toNat_toUInt64 (by omega), USize.toNat_toUInt64,
          toNat_toUInt64 (by omega), Nat.mod_eq_of_lt (show k / w.toNat * kc.toNat < 2 ^ 64 by omega)]
        exact Nat.mod_eq_of_lt (by omega : k / w.toNat * kc.toNat + cm (k % w.toNat) < 2 ^ 64)
      · have eg := (kgather_word hgk (colMap_plain hkeep) k hk).2; rw [erd, toNat_toUInt64 (by omega)] at eg; exact eg
    have hcmk : ∀ k < (kb * w).toNat, cm (k % w.toNat) < kc.toNat := fun k _ => (hcm _ (Nat.mod_lt _ hw1)).2
    by_cases hex : ∃ j < w.toNat, cm j = jj
    · obtain ⟨j, hj, hcj⟩ := hex
      obtain ⟨hd, hm⟩ := hdm (a := G) hj
      have hk : G * w.toNat + j < (kb * w).toNat := by rw [hkbw]; exact bit_lt hG hj
      obtain ⟨ep, -, -, egk⟩ := hpk _ hk
      rw [hd, hm, hcj] at ep
      have hl := hlast (G * w.toNat + j) (by rw [hsz]; exact hk) fun k' h1 h2 e => by
        rw [hsz] at h2
        obtain ⟨ep', -, hkm', -⟩ := hpk k' h2
        have e' : k' / w.toNat * kc.toNat + cm (k' % w.toNat) = G * kc.toNat + jj := by
          rw [← ep', ← ep]; exact e
        obtain ⟨e1, e2⟩ := hdm2 (hcmk k' h2) hjj e'
        have e3 := cminj _ _ hkm' hj (e2.trans hcj.symm)
        have := Nat.div_add_mod' k' w.toNat
        rw [e1, e3] at this; omega
      change (raw .i64 (kb * kc) s1)[((raw .i64 (kb * w) p1)[G * w.toNat + j]?.getD 0).toNat]? = _ at hl
      rw [ep] at hl
      rw [hl, Option.getD_some]
      have ev := (colMap_raw hv1).2.2.2 _ hk
      simp only [Op.eval, Except.ok.injEq] at ev
      rw [← ev, egk, hd, hkeepw]
      obtain ⟨v, hv, hv2, hvA⟩ := hAl j hj
      rw [hv, Option.getD_some]
      by_cases hc : ¬Vac G ∧ Kp G
      · rw [if_pos hc, UInt64.mul_one]
        by_cases hA : Al G j
        · rw [if_pos ⟨hc.1, hc.2, j, hj, hcj, hA⟩]; exact hvA.2 hA
        · rw [if_neg fun ⟨_, _, j', hj', hcj', hA'⟩ => hA (cminj j' j hj' hj (hcj'.trans hcj.symm) ▸ hA')]
          have := UInt64.lt_iff_toNat_lt.1 hv2
          have h1 : v.toNat ≠ 1 := fun e => hA (hvA.1 (UInt64.toNat_inj.mp e))
          exact UInt64.toNat_inj.mp (by simp at this ⊢; omega)
      · rw [if_neg hc, UInt64.mul_zero, if_neg fun ⟨a, b, _⟩ => hc ⟨a, b⟩]
    · rw [hfill _ hT fun k hk e => hex ⟨k % w.toNat, Nat.mod_lt _ hw1, by
          rw [hsz] at hk
          change ((raw .i64 (kb * w) p1)[k]?.getD 0).toNat = _ at e
          rw [(hpk k hk).1] at e
          exact (hdm2 (hcmk k hk) hjj e).2⟩, Option.getD_some,
        if_neg fun ⟨_, _, j, hj, hcj, _⟩ => hex ⟨j, hj, hcj⟩]
  -- the answer's words: `s1 + s2`, never both set
  let PP := fun G jj => (Vac G ∧ ∃ u < uc.n.toNat, cu u = jj) ∨
    (¬Vac G ∧ Kp G ∧ ∃ j < w.toNat, cm j = jj ∧ Al G j)
  have hout' : ∀ G < kb.toNat, ∀ jj < kc.toNat, ∃ v : UInt64,
      (raw .i64 (kb * kc) o')[G * kc.toNat + jj]? = some v ∧ v < 2 ∧ (v = 1 ↔ PP G jj) := fun G hG jj hjj => by
    have hT : G * kc.toNat + jj < (kb * kc).toNat := by rw [hkbc]; exact bit_lt hG hjj
    have e := (colMap_raw hout).2.2.2 _ hT
    simp only [Op.eval, Except.ok.injEq] at e
    rw [hs1w G hG jj hjj, hs2w G hG jj hjj] at e
    have hsome : (raw .i64 (kb * kc) o')[G * kc.toNat + jj]? =
        some ((raw .i64 (kb * kc) o')[G * kc.toNat + jj]?.getD 0) := by
      rw [getElem?_pos (raw .i64 (kb * kc) o') _ (by rw [(colMap_raw hout).2.2.1]; exact hT), Option.getD_some]
    refine ⟨_, hsome, ?_⟩
    rw [← e]
    by_cases hv : Vac G
    · rw [if_neg (show ¬(¬Vac G ∧ Kp G ∧ ∃ j < w.toNat, cm j = jj ∧ Al G j) from fun h => h.1 hv), UInt64.zero_add]
      by_cases hu : ∃ u < uc.n.toNat, cu u = jj
      · rw [if_pos ⟨hv, hu⟩]; exact ⟨by decide, iff_of_true rfl (.inl ⟨hv, hu⟩)⟩
      · rw [if_neg fun h => hu h.2]
        exact ⟨by decide, iff_of_false (by decide) fun h => h.elim (fun h => hu h.2) (fun h => h.1 hv)⟩
    · rw [if_neg (show ¬(Vac G ∧ ∃ u < uc.n.toNat, cu u = jj) from fun h => hv h.1), UInt64.add_zero]
      by_cases hq : ¬Vac G ∧ Kp G ∧ ∃ j < w.toNat, cm j = jj ∧ Al G j
      · rw [if_pos hq]; exact ⟨by decide, iff_of_true rfl (.inr hq)⟩
      · rw [if_neg hq]; exact ⟨by decide, iff_of_false (by decide) fun h => h.elim (fun h => hv h.1) hq⟩
  have hb63 : kb.toNat * kc.toNat < 2 ^ 63 := by omega
  refine ⟨hkbc, hb63, PP, hout', fun b c => ?_, Vals.code2_rep_inj hb2 hr.2 hub.2, Vals.code2_rep_inj hc2 wyM huc.2,
    (Vals.code2_plain hb2).2.2, (Vals.code2_plain hc2).2.2, colMap_plain hout⟩
  show _ ↔ (∀ a, r.Holds a b → s.Holds a c) ∧
    ((∃ a, r.Holds a b) ∨ ((∃ b', ub.Holds b' b) ∧ ∃ c', uc.Holds c' c))
  constructor
  · rintro ⟨G, hG, jj, hjj, hPP, ⟨i0, h0, r0⟩, ⟨i1, h1, r1⟩⟩
    obtain ⟨t0, ht0, hexb, hxb, hub⟩ := hrb G hG
    obtain rfl : t0 = i0 := Fin.ext (ht0.symm.trans h0)
    subst r0 r1
    rcases hPP with ⟨hv, u, hu, hcu'⟩ | ⟨hv, hkp, j, hj, hcj, hal⟩
    · refine ⟨fun a ⟨i, _, hi⟩ => absurd ((hxb i).2 hi) (hv i i.2), .inr ⟨?_, ?_⟩⟩
      · obtain ⟨u', hu'⟩ := hexb.resolve_left fun ⟨i, hi⟩ => hv i i.2 hi
        exact ⟨ub.key.row u', u', rfl, (hub u').1 hu'⟩
      · obtain ⟨t2, ht2, -, -, huc⟩ := hrc jj hjj
        obtain rfl : t2 = i1 := Fin.ext (ht2.symm.trans h1)
        exact ⟨uc.key.row ⟨u, hu⟩, ⟨u, hu⟩, rfl, (huc ⟨u, hu⟩).1 hcu'⟩
    · refine ⟨fun a ⟨i, hi1, hi2⟩ => ?_, .inl ?_⟩
      · subst hi1
        have hiG := (hxb i).2 hi2
        exact (hSrow i _).2 ⟨hkp i i.2 hiG, j, hj, hal i i.2 hiG (hkp i i.2 hiG), (hcol j hj jj hjj i1 h1).2 hcj⟩
      · exact Classical.byContradiction fun hno =>
          hv fun i hi e => hno ⟨r.key.row ⟨i, hi⟩, ⟨i, hi⟩, rfl, (hxb ⟨i, hi⟩).1 e⟩
  · rintro ⟨H1, H2⟩
    have hB : ∃ G < kb.toNat, (∃ i : Fin r.n.toNat, bx i = G ∧ r.val.row i = b) ∨
        ∃ u : Fin ub.n.toNat, bu u = G ∧ ub.val.row u = b := by
      rcases H2 with ⟨a, i, -, hi⟩ | ⟨⟨b', u, -, hu⟩, -⟩
      · exact ⟨bx i, (hbx i i.2).2, .inl ⟨i, rfl, hi⟩⟩
      · exact ⟨bu u, (hbu u u.2).2, .inr ⟨u, rfl, hu⟩⟩
    obtain ⟨G, hG, hGb⟩ := hB
    obtain ⟨t0, ht0, -, hxb, hub⟩ := hrb G hG
    have zb_b : zb.row t0 = b := by
      rcases hGb with ⟨i, hi, e⟩ | ⟨u, hu, e⟩
      · exact ((hxb i).1 hi).symm.trans e
      · exact ((hub u).1 hu).symm.trans e
    have hC : ∃ jj < kc.toNat, (∃ j : Fin w.toNat, cm j = jj ∧ yM.row j = c) ∨
        ∃ u : Fin uc.n.toNat, cu u = jj ∧ uc.val.row u = c := by
      rcases H2 with ⟨_, i, rfl, hi2⟩ | ⟨-, c', u, -, hu⟩
      · obtain ⟨-, j, hj, -, i', hi', ri'⟩ := (hSrow i c).1 (H1 _ ⟨i, rfl, hi2⟩)
        obtain ⟨i'', hi'', ri''⟩ := Vals.gather_row _ hyM ⟨j, hj⟩
        obtain rfl : i'' = i' := Fin.ext (hi''.symm.trans hi')
        exact ⟨cm j, (hcm j hj).2, .inl ⟨⟨j, hj⟩, rfl, ri''.trans ri'⟩⟩
      · exact ⟨cu u, (hcu u u.2).2, .inr ⟨u, rfl, hu⟩⟩
    obtain ⟨jj, hjj, hjc⟩ := hC
    obtain ⟨t1, ht1, -, hxc, huc⟩ := hrc jj hjj
    have zc_c : zc.row t1 = c := by
      rcases hjc with ⟨j, hj, e⟩ | ⟨u, hu, e⟩
      · exact ((hxc j).1 hj).symm.trans e
      · exact ((huc u).1 hu).symm.trans e
    refine ⟨G, hG, jj, hjj, ?_, ⟨t0, ht0, zb_b⟩, ⟨t1, ht1, zc_c⟩⟩
    subst zb_b zc_c
    by_cases hv : Vac G
    · refine .inl ⟨hv, ?_⟩
      rcases H2 with ⟨a, i, -, hi⟩ | ⟨-, c', u, -, hu⟩
      · exact absurd ((hxb i).2 hi) (hv i i.2)
      · exact ⟨u, u.2, (huc u).2 hu⟩
    · -- each row valued `G` has its key a row of `M`, and one column `j` of `M` that is `c`
      have hrow : ∀ i : Fin r.n.toNat, bx i = G → ixN i < g.toNat ∧ ∃ j < w.toNat,
          (raw .i64 (g * w) o)[ixN i * w.toNat + j]?.getD 0 = 1 ∧ cm j = jj := fun i hiG => by
        obtain ⟨hlt, j, hj, hb, hc⟩ := (hSrow i _).1 (H1 _ ⟨i, rfl, (hxb i).1 hiG⟩)
        exact ⟨hlt, j, hj, hb, (hcol j hj jj hjj t1 ht1).1 hc⟩
      obtain ⟨i0, hi0⟩ : ∃ i : Fin r.n.toNat, bx i = G :=
        Classical.byContradiction fun hno => hv fun i hi e => hno ⟨⟨i, hi⟩, e⟩
      obtain ⟨-, j, hj, -, hcj⟩ := hrow i0 hi0
      refine .inr ⟨hv, fun i hi hiG => (hrow ⟨i, hi⟩ hiG).1, j, hj, hcj, fun i hi hiG _ => ?_⟩
      obtain ⟨-, j', hj', hb, hcj'⟩ := hrow ⟨i, hi⟩ hiG
      rw [← cminj j' j hj' hj (hcj'.trans hcj.symm)]; exact hb

/-- **`Tab.ldivTabMat` is `r \ M` within `ub`, `uc`** (`ldivDen`) for a matrix `M` as `Tab.keepBits_law` reads it:
    `0`/`1` words and each side's rows `x[ra[·]]`, `y[rc[·]]` distinct (else `index` sends a key to one of two equal
    rows, and two equal columns are scattered onto one). -/
theorem Tab.ldivTabMat_law {n m N N' : USize} {r : Tab A B} {ub : Tab B B} {uc : Tab C C} {g w kb kc : USize}
    {o o' ra rb rc rc' : Enc} {x : Vals A n} {y : Vals C m} {zb : Vals B N} {zc : Vals C N'} {t : Tab B C}
    {s : Tab A C}
    (h : Tab.ldivTabMat r ub uc g w o x ra y rc = .ok (some (kb, kc, o', ⟨N, zb⟩, rb, ⟨N', zc⟩, rc')))
    (ht : Tab.ofBits kb kc o' zb rb zc rc' = .ok t) (hs : Tab.ofBits g w o x ra y rc = .ok s)
    (ho : ∀ a < g.toNat, ∀ j < w.toNat, ∃ v : UInt64, (raw .i64 (g * w) o)[a * w.toNat + j]? = some v ∧ v < 2)
    (hx : ∀ a a' : Fin g.toNat, ∀ i i' : Fin n.toNat, ((raw .i64 g ra)[a.1]?.getD 0).toNat = i.1 →
      ((raw .i64 g ra)[a'.1]?.getD 0).toNat = i'.1 → x.row i = x.row i' → a = a')
    (hy : ∀ j j' : Fin w.toNat, ∀ i i' : Fin m.toNat, ((raw .i64 w rc)[j.1]?.getD 0).toNat = i.1 →
      ((raw .i64 w rc)[j'.1]?.getD 0).toNat = i'.1 → y.row i = y.row i' → j = j')
    (hraN : hasNul ra = false) (hrcN : hasNul rc = false) (hr : r.WF) (hub : ub.WF) (huc : uc.WF) (wx : Vals.WF x) (wy : Vals.WF y) :
    rep t = Lang.ldivDen (rep r) (rep s) (rep ub) (rep uc) := by
  obtain ⟨hkbc, hb63, PP, hw, hden, -, -, hrb, hrc', -⟩ := Tab.ldivTabMat_spec h hs ho hx hy hraN hrcN hr hub huc wx wy
  apply Core.Rel.ext; intro b c
  exact (Tab.ofBits_holds ht hrb hrc' PP hkbc hb63 hw b c).trans (hden b c)

/-- **`ldivTabMat` keeps a matrix `BitsWf`** where its own reads back: its words, `kb · kc` and both sides' distinct
    rows from `Tab.ldivTabMat_spec`. -/
theorem Tab.ldivTabMat_wf {n m N N' : USize} {r : Tab A B} {ub : Tab B B} {uc : Tab C C} {g w kb kc : USize}
    {o o' ra rb rc rc' : Enc} {x : Vals A n} {y : Vals C m} {zb : Vals B N} {zc : Vals C N'}
    (h : Tab.ldivTabMat r ub uc g w o x ra y rc = .ok (some (kb, kc, o', ⟨N, zb⟩, rb, ⟨N', zc⟩, rc')))
    (hr : ∀ e, Tab.ofBits kb kc o' zb rb zc rc' ≠ .error e) (hw : BitsWf g w o x ra y rc) (hrw : r.WF)
    (hub : ub.WF) (huc : uc.WF) (wx : Vals.WF x) (wy : Vals.WF y) : BitsWf kb kc o' zb rb zc rc' := by
  obtain ⟨hr0, -, ho, hx, hy, hra, hrc, -⟩ := hw
  rcases hs : Tab.ofBits g w o x ra y rc with e | s
  · exact absurd hs (hr0 e)
  obtain ⟨hkbc, -, PP, hw', -, hxb, hyc, hrb, hrc', hoN'⟩ :=
    Tab.ldivTabMat_spec h hs (fun a ha j hj => some_lt_two (ho a ha j hj)) hx hy hra hrc hrw hub huc wx wy
  refine ⟨hr, hkbc, fun a ha j hj => ?_, hxb, hyc, hrb, hrc', hoN'⟩
  obtain ⟨v, hv, hv2, -⟩ := hw' a ha j hj
  rw [hv]; exact decide_eq_true hv2

/-- **`kgather` answers** on valid columns whose index holds no null and every index is below `n`. -/
theorem kgather_ok {m n : USize} {ix e : Enc} (hi : Enc.Valid m ix) (he : Enc.Valid n e) (hiN : hasNul ix = false)
    (hr : ∀ k < m.toNat, ((raw .i64 m ix)[k]?.getD 0).toNat < n.toNat) : ∃ o, kgather m ix n e = .ok o := by
  have h1 := (foRWords_valid "gather: ix" m ix).1 hi
  have h2 := (foRWords_valid "gather: e" n e).1 he
  have s1 := (foRWords_raw _ _ _ _ h1).2
  have s2 := (foRWords_raw _ _ _ _ h2).2
  have hU : USize.size ≤ 2 ^ 64 := by rcases USize.size_eq with h | h <;> omega
  have := m.toNat_lt_size; have := n.toNat_lt_size
  unfold kgather
  rw [h1, h2]
  simp only [bind, Except.bind, noNul, hiN, Bool.false_eq_true, ↓reduceIte]
  rw [gatherWords_eq _ _ (by omega) (by omega) (fun k hk => by rw [s2]; exact hr k (by omega))]
  cases hN : hasNul e
  · simp only [Bool.false_eq_true, ↓reduceIte, pure, Except.pure]; exact ⟨_, rfl⟩
  · simp only [↓reduceIte, Functor.map, Except.map]
    rw [gatherWords_eq _ (foRNuls n e) (by omega) (by rw [foRNuls_size]; omega)
      (fun k hk => by rw [foRNuls_size]; exact hr k (by omega))]
    exact ⟨_, rfl⟩

/-- **`scatterWords` answers** where every index is below `n` and `op` answers on every row's word. -/
theorem scatterWords_ok {op : Op} {is es : Array UInt64} {n : Nat} {fill : UInt64}
    (hop : ∀ k < is.size, ∀ a, ∃ v, op.eval a (es[k]?.getD 0) = .ok v)
    (hi : ∀ k < is.size, (is[k]?.getD 0).toNat < n) : ∃ o, scatterWords op is es n fill = .ok o := by
  unfold scatterWords
  have hl : ∀ k ∈ List.range is.size, k < is.size := fun k hk => List.mem_range.1 hk
  generalize List.range is.size = l at hl
  generalize Array.replicate n fill = a0
  induction l generalizing a0 with
  | nil => exact ⟨_, rfl⟩
  | cons k t ih =>
    have hk := hl k List.mem_cons_self
    obtain ⟨v, hv⟩ := hop k hk (a0[(is[k]?.getD 0).toNat]?.getD 0)
    simp only [List.foldlM_cons, bind, Except.bind, if_pos (hi k hk), hv]
    exact ih (fun k' h' => hl k' (List.mem_cons_of_mem _ h')) _

/-- **`kscatter` answers** on valid columns with no null whose every index is below `n`, `op` answering on every row's
    word. -/
theorem kscatter_ok {op : Op} {m n : USize} {ix e : Enc} {fill : UInt64} (hix : Enc.Valid m ix) (he : Enc.Valid m e)
    (hixN : hasNul ix = false) (heN : hasNul e = false)
    (hop : ∀ k < m.toNat, ∀ a, ∃ v, op.eval a ((raw .i64 m e)[k]?.getD 0) = .ok v)
    (hi : ∀ k < m.toNat, ((raw .i64 m ix)[k]?.getD 0).toNat < n.toNat) : ∃ o, kscatter op m ix e n fill = .ok o := by
  have h1 := (foRWords_valid "scatter: ix" m ix).1 hix
  have h2 := (foRWords_valid "scatter: e" m e).1 he
  have s1 := (foRWords_raw _ _ _ _ h1).2
  obtain ⟨o, ho⟩ := scatterWords_ok (is := raw .i64 m ix) (es := raw .i64 m e) (op := op) (n := n.toNat)
    (fill := fill) (fun k hk => hop k (by omega)) (fun k hk => hi k (by omega))
  -- `hop` at a row and the cell 0 rules out an op reading its divisor from the cell
  have hd : (op.readsDivisor && m != 0) = false := by
    rcases Nat.eq_zero_or_pos m.toNat with h0 | h0
    · simp [USize.toNat_inj.mp (show m.toNat = (0 : USize).toNat by simpa using h0)]
    · obtain ⟨v, hv⟩ := hop 0 h0 0
      cases op <;> simp [Op.readsDivisor] <;> simp [Op.eval] at hv
  unfold kscatter; simp only [hd, Bool.false_eq_true, ↓reduceIte]; rw [h1, h2]
  cases op <;> simp only [bind, Except.bind, noNul, hixN, heN, Bool.false_eq_true, ↓reduceIte, ho, pure,
    Except.pure] <;> exact ⟨_, rfl⟩

/-- **`colConst` answers**, a `foR` column. -/
theorem colConst_ok (n : USize) (w : UInt64) : ∃ md pk, colConst n w = .ok (.foR md pk) := by
  simp [colConst, kscatter, noNul, hasNul, Op.readsDivisor, foRWords, scatterWords, Enc.raw, bind, Except.bind, pure,
    Except.pure]

/-- **A chain with no step `Op.stepFails` answers** on every word: only `div`, `mod`, `rdiv`, `rmod` fail. -/
theorem chainAll_ok {c : List (Op × UInt64)} (h : ∀ p ∈ c, p.1.stepFails p.2 = false) (a : Array UInt64) :
    ∃ b, chainAll c a = .ok b := by
  have hc : ∀ x, ∃ v, chain c x = .ok v := by
    induction c with
    | nil => exact fun x => ⟨x, rfl⟩
    | cons p c ih =>
      intro x
      obtain ⟨v, hv⟩ : ∃ v, p.1.eval p.2 x = .ok v := by
        have hp := h p List.mem_cons_self; obtain ⟨o, k⟩ := p
        cases o <;> simp_all [Op.stepFails, Op.readsDivisor, Op.eval]
      obtain ⟨w, hw⟩ := ih (fun q hq => h q (List.mem_cons_of_mem _ hq)) v
      exact ⟨w, by simp only [chain, List.foldlM_cons, hv, bind, Except.bind]; exact hw⟩
  have hl : ∀ l : List UInt64, ∃ b, l.mapM (chain c) = .ok b := by
    intro l; induction l with
    | nil => exact ⟨[], rfl⟩
    | cons x l ih =>
      obtain ⟨v, hv⟩ := hc x; obtain ⟨b, hb⟩ := ih
      exact ⟨v :: b, by simp [List.mapM_cons, hv, hb, bind, Except.bind, pure, Except.pure]⟩
  obtain ⟨b, hb⟩ := hl a.toList
  exact ⟨b.toArray, by simp [chainAll, hb, Functor.map, Except.map]⟩

/-- **`kscan` with a `post` chain answers** on columns of `n` raw words, a seed column first, at a type of fixed width,
    where `op` answers on every row's word of every column after the seed and, where a row exists, no step of `post`
    `Op.stepFails`. -/
theorem kscan_post_ok {op : Op} {rev : Bool} {s t : QAtomicType} {n : USize} {seg : Option Enc} {c : Enc}
    {cs : List Enc} {post : List (Op × UInt64)}
    (hseg : ∀ e, seg = some e → (e.raw .u1 n).size = n.toNat) (hes : ∀ x ∈ c :: cs, (x.raw s n).size = n.toNat)
    (ht : t.width.isSome) (hop : ∀ x ∈ cs, ∀ i < n.toNat, ∀ a, ∃ v, op.eval a ((x.raw s n)[i]?.getD 0) = .ok v)
    (hpost : n.toNat ≠ 0 → ∀ p ∈ post, p.1.stepFails p.2 = false) :
    ∃ r, kscan op rev s t n seg (c :: cs) [] post = .ok r := by
  have hm : ∀ l : List Enc, (∀ x ∈ l, (x.raw s n).size = n.toNat) → l.mapM (rawAll s n) = .ok (l.map (·.raw s n)) := by
    intro l hl; induction l with
    | nil => rfl
    | cons x l ih =>
      simp only [List.mapM_cons, rawAll, hl x List.mem_cons_self, if_true, ih (fun y hy => hl y (List.mem_cons_of_mem _ hy)),
        bind, Except.bind, pure, Except.pure, List.map_cons]
  -- every column after the seed folds at every row
  have hx : ∀ i < n.toNat, ∀ a, ∃ v, ((cs.map (·.raw s n)).map fun a => if rev then a.reverse else a).foldlM
      (fun a x => op.eval a (x[i]?.getD 0)) a = .ok v := by
    intro i hi
    have hcs : ∀ x ∈ cs, (x.raw s n).size = n.toNat := fun x hx => hes x (List.mem_cons_of_mem _ hx)
    clear hes hm
    induction cs with
    | nil => exact fun a => ⟨a, rfl⟩
    | cons x cs ih =>
      intro a
      have hrow : ∃ v, op.eval a (((if rev then (x.raw s n).reverse else x.raw s n))[i]?.getD 0) = .ok v := by
        cases rev
        · exact hop x List.mem_cons_self i hi a
        · simp only [if_true, Array.getElem?_reverse, hcs x List.mem_cons_self, hi, if_true]
          exact hop x List.mem_cons_self _ (by omega) a
      obtain ⟨v, hv⟩ := hrow
      simp only [List.map_cons, List.foldlM_cons, hv, bind, Except.bind]
      exact ih (fun y hy => hop y (List.mem_cons_of_mem _ hy)) (fun y hy => hcs y (List.mem_cons_of_mem _ hy)) v
  have hf : ∀ (L : List Nat), (∀ i ∈ L, i < n.toNat) → ∀ (g sd : Array UInt64) (acc : Array UInt64), ∃ out,
      L.foldlM (kscanRow op g sd ((cs.map (·.raw s n)).map fun a => if rev then a.reverse else a)) acc = .ok out := by
    intro L hL g sd
    induction L with
    | nil => exact fun acc => ⟨acc, rfl⟩
    | cons i L ih =>
      intro acc
      obtain ⟨v, hv⟩ := hx i (hL i List.mem_cons_self) (if 0 < i ∧ g[i]?.getD 0 = 0 then acc[i - 1]?.getD 0 else sd[i]?.getD 0)
      simp only [List.foldlM_cons, kscanRow, hv, bind, Except.bind, Functor.map, Except.map]
      exact ih (fun j hj => hL j (List.mem_cons_of_mem _ hj)) _
  obtain ⟨w, hw⟩ := Option.isSome_iff_exists.1 ht
  obtain ⟨g, hg⟩ : ∃ g, segAll n seg = .ok g := by
    cases seg with
    | none => exact ⟨_, rfl⟩
    | some e => exact ⟨_, by simp only [segAll, rawAll, hseg e rfl, if_true]; rfl⟩
  have hm' : (c :: cs).mapM (fun e => rawAll s n e >>= chainAll []) = .ok ((c :: cs).map (·.raw s n)) := by
    simp only [chainAll_nil, bind_pure]; exact hm _ hes
  -- `hop` at a row and the carry 0 rules out a folded op reading its divisor from the carry
  have hd : kscanRefuses op n (c :: cs) [] post = false := by
    unfold kscanRefuses
    rcases Nat.eq_zero_or_pos n.toNat with h0 | h0
    · simp [USize.toNat_inj.mp (show n.toNat = (0 : USize).toNat by simpa using h0)]
    have hrd : (op.readsDivisor && 1 < (c :: cs).length) = false := by
      rcases cs with _ | ⟨x, cs⟩
      · simp
      obtain ⟨v, hv⟩ := hop x List.mem_cons_self 0 h0 0
      cases op <;> simp [Op.readsDivisor] <;> simp [Op.eval] at hv
    have hp : post.any (fun p => p.1.stepFails p.2) = false := by
      simpa [List.any_eq_false] using hpost (by omega)
    simp only [List.nil_append, hrd, hp, Bool.false_or, Bool.and_false]
  unfold kscan
  simp only [hd, Bool.false_eq_true, if_false]
  rw [hg, hm']
  obtain ⟨out, hout⟩ := hf (List.range n.toNat) (fun i hi => List.mem_range.1 hi)
    (if rev then g.reverse else g) (if rev then (c.raw s n).reverse else c.raw s n) #[]
  obtain ⟨o2, ho2⟩ : ∃ o2, chainAll post out = .ok o2 := by
    rcases Nat.eq_zero_or_pos n.toNat with h0 | h0
    · rw [h0] at hout
      simp only [List.range_zero, List.foldlM_nil, pure, Except.pure, Except.ok.injEq] at hout
      subst hout; exact ⟨_, rfl⟩
    · exact chainAll_ok (hpost (by omega)) out
  simp only [bind, Except.bind, List.map_cons, pure, Except.pure]
  rw [hout]; simp only [ho2, Except.pure, hw]; exact ⟨_, rfl⟩

/-- **`kscan` answers** on columns of `n` raw words, a seed column first, at a type of fixed width, where `op` answers
    on every row's word of every column after the seed. -/
theorem kscan_ok {op : Op} {rev : Bool} {s t : QAtomicType} {n : USize} {seg : Option Enc} {c : Enc} {cs : List Enc}
    (hseg : ∀ e, seg = some e → (e.raw .u1 n).size = n.toNat) (hes : ∀ x ∈ c :: cs, (x.raw s n).size = n.toNat)
    (ht : t.width.isSome) (hop : ∀ x ∈ cs, ∀ i < n.toNat, ∀ a, ∃ v, op.eval a ((x.raw s n)[i]?.getD 0) = .ok v) :
    ∃ r, kscan op rev s t n seg (c :: cs) = .ok r :=
  kscan_post_ok (post := []) hseg hes ht hop fun _ _ h => by cases h

/-- **`colMap` answers** on columns of `n` raw words where `op` answers on every word of `b` (`kscan` reads raw words,
    not a layout). -/
theorem colMap_ok {op : Op} {n : USize} {a b : Enc} {t : QAtomicType} (ht : t.width.isSome)
    (sa : (raw .i64 n a).size = n.toNat) (sb : (raw .i64 n b).size = n.toNat)
    (hop : ∀ i < n.toNat, ∀ c, ∃ v, op.eval c ((raw .i64 n b)[i]?.getD 0) = .ok v) :
    ∃ o, colMap op n a b t = .ok o := by
  obtain ⟨r, hr⟩ := kscan_ok (op := op) (rev := false) (s := .i64) (t := t) (n := n) (seg := none) (c := a)
    (cs := [b]) (fun _ h => by cases h) (by simp [sa, sb]) ht (by simpa using hop)
  unfold colMap; simp only [hr, bind, Except.bind, pure, Except.pure]; exact ⟨_, rfl⟩

/-- **`whereCol` answers** on `m` raw `0`/`1` words within its bound, a valid column. -/
theorem whereCol_ok {m : USize} {b : Enc} (hm : m.toNat < min (USize.size - 1) (2 ^ 63))
    (sb : (raw .i64 m b).size = m.toNat) (hb : ∀ i < m.toNat, (raw .i64 m b)[i]?.getD 0 < 2) :
    ∃ K o, whereCol m b = .ok (K, o) ∧ Enc.Valid K o := by
  have hU : USize.size ≤ 2 ^ 64 := by rcases USize.size_eq with h | h <;> omega
  have hc64 : ∀ a, a < 2 ^ 63 → a.toUInt64.toNat = a := fun a ha => by simp; omega
  obtain ⟨md, pk, hz⟩ := colConst_ok m 0
  have zv : Enc.Valid m (.foR md pk) := (kscatter_closed hz).1
  have sz := (foRWords_raw _ _ _ _ ((foRWords_valid "" m _).1 zv)).2
  obtain ⟨sk, hsk⟩ := kscan_ok (op := .add) (rev := false) (s := .i64) (t := .i64) (n := m) (seg := some (.foR md pk))
    (c := .foR md pk) (cs := [b]) (fun _ h => by cases h; simp [Enc.raw]) (by simp [sz, sb]) rfl (by simp [Op.eval])
  have hP : colPrefix .add m b = .ok sk.1 := by
    unfold colPrefix; simp only [hz, hsk, bind, Except.bind, pure, Except.pure]
  obtain ⟨f, hf⟩ : ∃ f : Nat → Bool, f = fun i => decide ((raw .i64 m b)[i]?.getD 0 ≠ 0) := ⟨_, rfl⟩
  obtain ⟨C, hC⟩ : ∃ C : Nat → Nat, C = fun a => ((List.range a).filter f).length := ⟨_, rfl⟩
  have hbit : ∀ i < m.toNat, (raw .i64 m b)[i]?.getD 0 = if f i then 1 else 0 := by
    intro i hi
    have h2 := UInt64.lt_iff_toNat_lt.1 (hb i hi)
    rw [hf]
    by_cases h0 : (raw .i64 m b)[i]?.getD 0 = 0
    · simp [h0]
    · simp only [h0, ne_eq, not_false_eq_true, decide_true, if_true]
      have : ((raw .i64 m b)[i]?.getD 0).toNat ≠ 0 := fun e0 => h0 (UInt64.toNat_inj.1 (by simpa using e0))
      apply UInt64.toNat_inj.1; simp at h2 ⊢; omega
  have hstep : ∀ a, C (a + 1) = C a + if f a then 1 else 0 := fun a => by
    rw [hC]; dsimp only; rw [List.range_succ, List.filter_append, List.length_append]; by_cases hfa : f a <;> simp [hfa]
  have hCle : ∀ a, C a ≤ a := fun a => by
    rw [hC]; exact Nat.le_trans (List.length_filter_le _ _) (by simp)
  have hmono : ∀ a a', a ≤ a' → C a ≤ C a' := fun a a' h => by
    rw [hC]; exact (List.IsPrefix.filter f (List.prefix_iff_eq_take.2
      (by rw [List.length_range, List.take_range, Nat.min_eq_left h]))).length_le
  have hsum : ∀ a, ((List.range a).map fun G => if f G then 1 else 0).sum = C a := by
    intro a; induction a with
    | zero => rw [hC]; rfl
    | succ a ih => rw [hstep, ← ih, List.range_succ, List.map_append, sum_append_nat]; simp
  have hs : ∀ i < m.toNat, (raw .i64 m sk.1)[i]?.getD 0 = (C (i + 1)).toUInt64 := fun i hi => by
    rw [colPrefix_add_sum hP (fun G => if f G then 1 else 0)
      (fun G hG => by rw [hbit G hG]; by_cases hfg : f G <;> simp [hfg]) i hi, hsum]
  have hk : sk.2.getD 0 = (C m.toNat).toUInt64 := by
    rw [kscan_last (w := 8) rfl hsk]
    simp only [Bool.false_eq_true, if_false]
    rcases Nat.eq_zero_or_pos m.toNat with h0 | h0
    · rw [h0, hC]; simp [(colPrefix_raw hP).2.1, h0]
    · have := hs (m.toNat - 1) (by omega)
      rw [Nat.sub_add_cancel h0] at this
      rw [← this, Array.getElem?_eq_getElem (by rw [(colPrefix_raw hP).2.1]; omega)]
  have hKn : (sk.2.getD 0).toNat.toUSize.toNat = C m.toNat := by
    rw [hk, hc64 _ (by have := hCle m.toNat; omega)]
    exact USize.toNat_ofNat_of_lt' (by have := hCle m.toNat; omega)
  obtain ⟨d, hd⟩ := colMap_ok (op := .sub) (n := m) (a := sk.1) (b := b) (t := .i64) rfl (colPrefix_raw hP).2.1 sb
    (fun _ _ _ => ⟨_, rfl⟩)
  have hdv : ∀ i < m.toNat, (raw .i64 m d)[i]?.getD 0 = (C i).toUInt64 := by
    intro i hi
    have := (colMap_raw hd).2.2.2 i hi
    rw [hs i hi, hbit i hi, hstep] at this
    simp only [Op.eval, Except.ok.injEq] at this
    rw [← this]
    cases f i
    · simp
    · show UInt64.ofNat (C i + 1) - 1 = UInt64.ofNat (C i); rw [UInt64.ofNat_add]; simp
  have hK1 : ((sk.2.getD 0).toNat.toUSize.toNat + 1).toUSize.toNat = C m.toNat + 1 := by
    rw [hKn]; exact USize.toNat_ofNat_of_lt' (by have := hCle m.toNat; omega)
  obtain ⟨e, he⟩ := kscatter_ok (op := .last) (m := m) (ix := d) (e := .pos)
    (n := ((sk.2.getD 0).toNat.toUSize.toNat + 1).toUSize) (fill := 0) (colMap_closed hd).1 trivial (colMap_plain hd) rfl
    (fun _ _ _ => ⟨_, rfl⟩) (fun k hk => by
      rw [hdv k hk, hc64 _ (by have := hCle k; omega), hK1]; have := hmono k m.toNat (by omega); omega)
  obtain ⟨o, ho⟩ := kgather_ok (m := (sk.2.getD 0).toNat.toUSize) (ix := .pos) (e := e) trivial (kscatter_closed he).1 rfl
    (fun k hk => by
      simp only [Enc.raw, Array.getElem?_map, Array.getElem?_range, hk, if_true, Option.map_some, Option.getD_some]
      rw [hK1, hc64 _ (by rw [hKn] at hk; have := hCle m.toNat; omega)]; rw [hKn] at hk; omega)
  unfold whereCol; dsimp only; rw [if_pos hm]
  simp only [hz, hsk, hd, he, ho, bind, Except.bind, Functor.map, Except.map]
  exact ⟨_, _, rfl, (kgather_closed ho).1⟩

/-- A list `mapM` answered on answers on each of its elements. -/
theorem mapM_ok_mem {α β : Type} {f : α → Except String β} {l : List α} {cs : List β} (h : l.mapM f = .ok cs) :
    ∀ x ∈ l, ∃ c, f x = .ok c := fun x hx => by
  obtain ⟨hl, hf⟩ := mapM_ok h
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
  exact ⟨cs[i]'(by omega), hf i _ _ (List.getElem?_eq_getElem hi) (List.getElem?_eq_getElem (by omega))⟩

/-- **`Arr.gather` answers** on a valid column at valid positions below its length. -/
theorem Arr.gather_ok {t : QAtomicType} {n M : USize} {ix : Enc} (x : Arr t n) (hx : Enc.Valid n x.enc)
    (hi : Enc.Valid M ix) (hiN : hasNul ix = false) (hr : ∀ k < M.toNat, ((raw .i64 M ix)[k]?.getD 0).toNat < n.toNat) :
    ∃ v, Arr.gather M ix x = .ok v := by
  obtain ⟨o, ho⟩ := kgather_ok hi hx hiN hr
  unfold Arr.gather; split
  · exact ⟨_, rfl⟩
  · rename_i h; rw [ho] at h; cases h

/-- A column `Arr.gather` read is valid. -/
theorem Arr.valid_of_gather {t : QAtomicType} {n M : USize} {ix : Enc} {x : Arr t n} {v : Arr t M}
    (h : Arr.gather M ix x = .ok v) : Enc.Valid n x.enc := by
  unfold Arr.gather at h; split at h
  · rename_i hk; exact kgather_valid hk
  · cases h

/-- **A side gathered once is gathered at any valid positions below its length**: `Vals.gather` reads the same
    columns at every `ix`. -/
theorem Vals.gather_ok_of_ok {M M' : USize} {ix ix' : Enc} (hi : Enc.Valid M' ix') (hiN : hasNul ix' = false) :
    {A : Obj} → {n : USize} → (x : Vals A n) → {v : Vals A M} → Vals.gather M ix x = .ok v →
    (∀ k < M'.toNat, ((raw .i64 M' ix')[k]?.getD 0).toNat < n.toNat) → ∃ v', Vals.gather M' ix' x = .ok v'
  | .atom _, _, x, _, h, hr => Arr.gather_ok x (Arr.valid_of_gather h) hi hiN hr
  | .prod _ _, _, x, _, h, hr => by
    simp only [Vals.gather, bind] at h
    rw [Except.bind_eq_ok'] at h; obtain ⟨a, ha, h⟩ := h
    rw [Except.bind_eq_ok'] at h; obtain ⟨b, hb, -⟩ := h
    obtain ⟨a', ha'⟩ := Vals.gather_ok_of_ok hi hiN x.1 ha hr
    obtain ⟨b', hb'⟩ := Vals.gather_ok_of_ok hi hiN x.2 hb hr
    simp only [Vals.gather, ha', hb', bind, Except.bind, pure, Except.pure]; exact ⟨_, rfl⟩
  | .arr _, _, ⟨c, lo, hi', f⟩, _, h, hr => by
    simp only [Vals.gather, bind] at h
    rw [Except.bind_eq_ok'] at h; obtain ⟨a, ha, h⟩ := h
    rw [Except.bind_eq_ok'] at h; obtain ⟨b, hb, -⟩ := h
    obtain ⟨a', ha'⟩ := Arr.gather_ok lo (Arr.valid_of_gather ha) hi hiN hr
    obtain ⟨b', hb'⟩ := Arr.gather_ok hi' (Arr.valid_of_gather hb) hi hiN hr
    simp only [Vals.gather, ha', hb', bind, Except.bind, pure, Except.pure]; exact ⟨_, rfl⟩
  | .sum _ _, _, ⟨l, r, tag, idx, x, y⟩, _, h, hr => by
    simp only [Vals.gather, bind] at h
    rw [Except.bind_eq_ok'] at h; obtain ⟨a, ha, h⟩ := h
    rw [Except.bind_eq_ok'] at h; obtain ⟨b, hb, -⟩ := h
    obtain ⟨a', ha'⟩ := Arr.gather_ok tag (Arr.valid_of_gather ha) hi hiN hr
    obtain ⟨b', hb'⟩ := Arr.gather_ok idx (Arr.valid_of_gather hb) hi hiN hr
    simp only [Vals.gather, ha', hb', bind, Except.bind, pure, Except.pure]; exact ⟨_, rfl⟩
  | .one, n, _, _, _, hr => by
    obtain ⟨p, hp⟩ := Arr.gather_ok (Arr.mk (t := .i64) (n := n) .pos trivial rfl) trivial hi hiN hr
    simp only [Vals.gather, hp, bind, Except.bind, pure, Except.pure]; exact ⟨(), trivial⟩

/-- `ascCol` of a `cells` key answered: its `lo` and `hi` are valid at its `n` cells. -/
theorem ascCol_cells_valid {m n c : USize} {lo hi e : Enc} {els : List (AscKey × Enc)} {xk}
    (h : ascCol m (.cells n c lo hi els, e) = .ok xk) : Enc.Valid n lo ∧ Enc.Valid n hi := by
  rw [ascCol] at h
  cases hix : foRWords "asc: cells" m e with
  | error s => simp [hix, bind, Except.bind] at h
  | ok ix =>
    cases hn : noNul "asc: cells" m e with
    | error s => simp [hix, hn, bind, Except.bind] at h
    | ok u =>
    cases hf : ix.find? (n.toNat ≤ ·.toNat) with
    | some r => simp [hix, hn, hf, bind, Except.bind] at h
    | none =>
      cases hl : foRWords "asc: cells lo" n lo with
      | error s => simp [hix, hn, hf, hl, bind, Except.bind] at h
      | ok l =>
        cases hnl : noNul "asc: cells lo" n lo with
        | error s => simp [hix, hn, hf, hl, hnl, bind, Except.bind] at h
        | ok u' =>
        cases hh : foRWords "asc: cells hi" n hi with
        | error s => simp [hix, hn, hf, hl, hnl, hh, bind, Except.bind] at h
        | ok l' => exact ⟨(foRWords_valid _ _ _).2 _ hl, (foRWords_valid _ _ _).2 _ hh⟩

/-- **A side `kasc` reads is gathered at any valid positions below its length**: `ascCol` answering on each of its
    key columns (`Vals.cols`) makes every column `Vals.gather` reads valid. -/
theorem Vals.gather_ok_of_cols {M : USize} {ix : Enc} (hi : Enc.Valid M ix) (hiN : hasNul ix = false) :
    {A : Obj} → {n : USize} → (x : Vals A n) → {es : List (AscKey × Enc)} → Vals.cols x = .ok es →
    (∀ e ∈ es, ∃ c, ascCol n e = .ok c) →
    (∀ k < M.toNat, ((raw .i64 M ix)[k]?.getD 0).toNat < n.toNat) → ∃ v, Vals.gather M ix x = .ok v
  | .atom _, _, x, _, hes, hc, hr => by
    simp only [Vals.cols, Except.ok.injEq] at hes; subst hes
    obtain ⟨c, hc⟩ := hc _ List.mem_cons_self
    exact Arr.gather_ok x (ascCol_valid hc) hi hiN hr
  | .prod _ _, _, x, _, hes, hc, hr => by
    simp only [Vals.cols, bind] at hes
    rw [Except.bind_eq_ok'] at hes; obtain ⟨e1, h1, hes⟩ := hes
    rw [Except.bind_eq_ok'] at hes; obtain ⟨e2, h2, hes⟩ := hes
    simp only [pure, Except.pure, Except.ok.injEq] at hes; subst hes
    obtain ⟨a', ha'⟩ := Vals.gather_ok_of_cols hi hiN x.1 h1 (fun e he => hc e (List.mem_append_left _ he)) hr
    obtain ⟨b', hb'⟩ := Vals.gather_ok_of_cols hi hiN x.2 h2 (fun e he => hc e (List.mem_append_right _ he)) hr
    simp only [Vals.gather, ha', hb', bind, Except.bind, pure, Except.pure]; exact ⟨_, rfl⟩
  | .arr _, _, ⟨c, lo, hi', f⟩, _, hes, hc, hr => by
    simp only [Vals.cols, bind] at hes
    rw [Except.bind_eq_ok'] at hes; obtain ⟨fs, -, hes⟩ := hes
    simp only [pure, Except.pure, Except.ok.injEq] at hes; subst hes
    obtain ⟨k, hk⟩ := hc _ List.mem_cons_self
    obtain ⟨vl, vh⟩ := ascCol_cells_valid hk
    obtain ⟨a', ha'⟩ := Arr.gather_ok lo vl hi hiN hr
    obtain ⟨b', hb'⟩ := Arr.gather_ok hi' vh hi hiN hr
    simp only [Vals.gather, ha', hb', bind, Except.bind, pure, Except.pure]; exact ⟨_, rfl⟩
  | .sum _ _, n, ⟨l, r, tag, idx, x, y⟩, es, hes, hc, hr => by
    have hidx : Enc.Valid n idx.enc := by
      unfold Vals.cols at hes
      split at hes; · cases hes
      split at hes; · cases hes
      rename_i h
      exact (foRWords_valid "" _ _).2 _ (by unfold foRWords; rw [if_pos (by simpa using h)])
    obtain ⟨xs, ys, rfl, -⟩ := Vals.cols_sum hes
    obtain ⟨k, hk⟩ := hc _ List.mem_cons_self
    obtain ⟨a', ha'⟩ := Arr.gather_ok tag (ascCol_valid hk) hi hiN hr
    obtain ⟨b', hb'⟩ := Arr.gather_ok idx hidx hi hiN hr
    simp only [Vals.gather, ha', hb', bind, Except.bind, pure, Except.pure]; exact ⟨_, rfl⟩
  | .one, n, _, _, _, _, hr => by
    obtain ⟨p, hp⟩ := Arr.gather_ok (Arr.mk (t := .i64) (n := n) .pos trivial rfl) trivial hi hiN hr
    simp only [Vals.gather, hp, bind, Except.bind, pure, Except.pure]; exact ⟨(), trivial⟩

/-- **A side `Vals.code` numbers is gathered at any valid positions below its length**. -/
theorem Vals.gather_ok_of_code {n M k : USize} {x : Vals A n} {c rep ix : Enc} (h : Vals.code x = .ok (k, c, rep))
    (hi : Enc.Valid M ix) (hiN : hasNul ix = false) (hr : ∀ k < M.toNat, ((raw .i64 M ix)[k]?.getD 0).toNat < n.toNat) :
    ∃ v, Vals.gather M ix x = .ok v := by
  simp only [Vals.code, bind] at h
  rw [Except.bind_eq_ok'] at h; obtain ⟨es, hes, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨⟨vs, p⟩, hk, -⟩ := h
  obtain ⟨cs, hcs, -⟩ := kasc_ok hk
  exact Vals.gather_ok_of_cols hi hiN x hes (mapM_ok_mem hcs) hr

/-- `Vals.code`'s `rep` is a valid column of its `k` numbers. -/
theorem Vals.code_valid {n k : USize} {x : Vals A n} {c rep : Enc} (h : Vals.code x = .ok (k, c, rep)) :
    Enc.Valid k rep := by
  simp only [Vals.code, bind] at h
  rw [Except.bind_eq_ok'] at h; obtain ⟨_, -, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨_, -, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨⟨k0, g0, f0⟩, -, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨_, -, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨r0, hr0, h⟩ := h
  simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, -, rfl⟩ := h
  exact (kgather_closed hr0).1

/-- `Vals.code2` is `Vals.code` of its CONCAT `z`, with the same count and `rep`. -/
theorem Vals.code2_code {n₁ n₂ k N : USize} {x : Vals A n₁} {y : Vals A n₂} {bx bY rep : Enc} {z : Vals A N}
    (h : Vals.code2 x y = .ok (k, bx, bY, ⟨N, z, rep⟩)) : ∃ c, Vals.code z = .ok (k, c, rep) := by
  simp only [Vals.code2, bind] at h
  rw [Except.bind_eq_ok'] at h; obtain ⟨⟨N0, sh⟩, -, h⟩ := h; try dsimp only at h
  rw [Except.bind_eq_ok'] at h; obtain ⟨z0, -, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨⟨k0, c0, rep0⟩, hc, h⟩ := h; try dsimp only at h
  rw [Except.bind_eq_ok'] at h; obtain ⟨_, -, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨_, -, h⟩ := h
  simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, -, -, hS⟩ := h
  obtain ⟨eN, eZ⟩ := Sigma.mk.inj hS; subst eN
  have e := eq_of_heq eZ; simp only [Prod.mk.injEq] at e; obtain ⟨rfl, rfl⟩ := e
  exact ⟨_, hc⟩

/-- An `i64` column read at `n` holds `n` words or none: every form of fixed width is read at each of `n` rows. -/
theorem raw_size_or {n : USize} (e : Enc) : (raw .i64 n e).size = n.toNat ∨ (raw .i64 n e).size = 0 := by
  cases e <;> simp [Enc.raw, QAtomicType.width]

/-- A matrix with a word at each of its `g · w` bits holds `g · w` words. -/
theorem raw_size_of_bits {g w : USize} {o : Enc} (hgw : (g * w).toNat = g.toNat * w.toNat)
    (hv : ∀ a < g.toNat, ∀ j < w.toNat, ∃ v, (raw .i64 (g * w) o)[a * w.toNat + j]? = some v) :
    (raw .i64 (g * w) o).size = (g * w).toNat := by
  rcases raw_size_or (n := g * w) o with h1 | h1
  · exact h1
  rcases Nat.eq_zero_or_pos (g * w).toNat with h0 | h0
  · rw [h1, h0]
  rw [hgw] at h0
  obtain ⟨v, hv⟩ := hv 0 (Nat.pos_of_mul_pos_right h0) 0 (Nat.pos_of_mul_pos_left h0)
  rw [Array.getElem?_eq_none (by rw [h1]; omega)] at hv; cases hv

/-- **`ofBits`' positions**: the `M` selected words `sel`, each below `2^63`, divided by `w` (`colMap .div`) and
    taken modulo `w` (`colMap .mod`) against the constant `w`, positive and below `2^63` wherever a row is. -/
theorem colMap_div_mod {M w : USize} {sel : Enc}
    (hs : ∀ k < M.toNat, ((raw .i64 M sel)[k]?.getD 0).toNat < 2 ^ 63)
    (hw : ∀ k < M.toNat, 0 < w.toNat ∧ w.toNat < 2 ^ 63) :
    (∀ {dv : Enc}, colMap .first M sel sel .i64 .i64 [] [(.rdiv, w.toUInt64)] = .ok dv → ∀ k < M.toNat,
      (raw .i64 M dv)[k]?.getD 0 = (((raw .i64 M sel)[k]?.getD 0).toNat / w.toNat).toUInt64) ∧
    (∀ {mv : Enc}, colMap .first M sel sel .i64 .i64 [] [(.rmod, w.toUInt64)] = .ok mv → ∀ k < M.toNat,
      (raw .i64 M mv)[k]?.getD 0 = (((raw .i64 M sel)[k]?.getD 0).toNat % w.toNat).toUInt64) := by
  have hsn : ∀ k < M.toNat, (raw .i64 M sel)[k]?.getD 0 = ((raw .i64 M sel)[k]?.getD 0).toNat.toUInt64 :=
    fun k hk => UInt64.toNat_inj.mp (by simp)
  have ew : w.toUInt64 = w.toNat.toUInt64 := UInt64.toNat_inj.mp (by simp)
  refine ⟨fun hdv k hk => ?_, fun hmv k hk => ?_⟩
  · have e1 := (colMap_post hdv).2 k hk
    rw [hsn k hk, ew, eval_rdiv_nat (hs k hk) (hw k hk).2 (hw k hk).1] at e1
    exact (Except.ok.inj e1).symm
  · have e1 := (colMap_post hmv).2 k hk
    rw [hsn k hk, ew, eval_rmod_nat (hs k hk) (hw k hk).2 (hw k hk).1] at e1
    exact (Except.ok.inj e1).symm

/-- Position `p` of a `g · w` matrix is bit `(p / w, p % w)`. -/
theorem bit_dec {g w p : Nat} (hp : p < g * w) : p / w < g ∧ p % w < w ∧ p / w * w + p % w = p := by
  have hw : 0 < w := Nat.pos_of_ne_zero fun h0 => by rw [h0, Nat.mul_zero] at hp; omega
  exact ⟨(Nat.div_lt_iff_lt_mul hw).2 hp, Nat.mod_lt _ hw, Nat.div_add_mod' p w⟩

/-- A selected position `p < g · w` has `0 < w ≤ p + 1 ≤ g · w`. -/
theorem bit_w {g w p : Nat} (hp : p < g * w) : 0 < w ∧ w ≤ g * w := by
  have hw : 0 < w := Nat.pos_of_ne_zero fun h0 => by rw [h0, Nat.mul_zero] at hp; omega
  have hg : 0 < g := Nat.pos_of_ne_zero fun h0 => by rw [h0, Nat.zero_mul] at hp; omega
  exact ⟨hw, Nat.le_mul_of_pos_left w hg⟩

/-- **`Tab.ofBits` answers** on a matrix of `g · w` `0`/`1` words, `g · w` within `whereCol`'s bound and not wrapping,
    whose every set bit `(a, j)` names rows `ra[a]`, `rc[j]` of `x`, `y`, sides `Vals.gather` reads at any valid
    positions below their lengths. -/
theorem Tab.ofBits_ok {n m g w : USize} {o ra rc : Enc} {x : Vals A n} {y : Vals C m}
    (hgw : (g * w).toNat = g.toNat * w.toNat) (hB : g.toNat * w.toNat < min (USize.size - 1) (2 ^ 63))
    (hos : (raw .i64 (g * w) o).size = (g * w).toNat)
    (h2 : ∀ a < g.toNat, ∀ j < w.toNat, (raw .i64 (g * w) o)[a * w.toNat + j]?.getD 0 < 2)
    (hra : Enc.Valid g ra) (hrc : Enc.Valid w rc) (hraN : hasNul ra = false) (hrcN : hasNul rc = false)
    (hin : ∀ a < g.toNat, ∀ j < w.toNat, (raw .i64 (g * w) o)[a * w.toNat + j]?.getD 0 ≠ 0 →
      ((raw .i64 g ra)[a]?.getD 0).toNat < n.toNat ∧ ((raw .i64 w rc)[j]?.getD 0).toNat < m.toNat)
    (hx : ∀ (M : USize) (ix : Enc), Enc.Valid M ix → hasNul ix = false →
      (∀ k < M.toNat, ((raw .i64 M ix)[k]?.getD 0).toNat < n.toNat) → ∃ v, Vals.gather M ix x = .ok v)
    (hy : ∀ (M : USize) (ix : Enc), Enc.Valid M ix → hasNul ix = false →
      (∀ k < M.toNat, ((raw .i64 M ix)[k]?.getD 0).toNat < m.toNat) → ∃ v, Vals.gather M ix y = .ok v) :
    ∀ e, Tab.ofBits g w o x ra y rc ≠ .error e := by
  have hb2 : ∀ p < (g * w).toNat, (raw .i64 (g * w) o)[p]?.getD 0 < 2 := fun p hp => by
    obtain ⟨h1, h2', h3⟩ := bit_dec (hgw ▸ hp); have := h2 _ h1 _ h2'; rwa [h3] at this
  obtain ⟨M, sel, hsel, -⟩ := whereCol_ok (m := g * w) (b := o) (by omega) hos hb2
  have hp : ∀ k < M.toNat, ((raw .i64 M sel)[k]?.getD 0).toNat < g.toNat * w.toNat ∧
      (raw .i64 (g * w) o)[((raw .i64 M sel)[k]?.getD 0).toNat]?.getD 0 ≠ 0 := fun k hk => by
    have := (whereCol_mem hsel hb2 _).1 ⟨k, hk, rfl⟩; rwa [hgw] at this
  obtain ⟨hdw, hmw⟩ := colMap_div_mod (M := M) (w := w) (sel := sel) (fun k hk => by have := (hp k hk).1; omega)
    (fun k hk => by have := bit_w (hp k hk).1; omega)
  -- a row selects a bit, so `w ≠ 0` wherever the post step `rdiv`/`rmod` by `w` runs
  have hwM : M.toNat ≠ 0 → w.toUInt64 ≠ 0 := fun h0 e => by
    have := bit_w (hp 0 (by omega)).1
    rw [show w.toUInt64 = w.toNat.toUInt64 from UInt64.toNat_inj.mp (by simp)] at e
    have := congrArg UInt64.toNat e; rw [toNat_toUInt64 (by omega)] at this; simp at this; omega
  have hss : (raw .i64 M sel).size = M.toNat := whereCol_size hsel
  obtain ⟨⟨dv, _⟩, hdv'⟩ := kscan_post_ok (op := .first) (rev := false) (s := .i64) (t := .i64) (n := M) (seg := none)
    (c := sel) (cs := [sel]) (post := [(.rdiv, w.toUInt64)]) (fun _ h => by cases h) (by simp [hss]) rfl
    (by simp [Op.eval]) (fun h0 => by simp [Op.stepFails, Op.readsDivisor, hwM h0])
  obtain ⟨⟨mv, _⟩, hmv'⟩ := kscan_post_ok (op := .first) (rev := false) (s := .i64) (t := .i64) (n := M) (seg := none)
    (c := sel) (cs := [sel]) (post := [(.rmod, w.toUInt64)]) (fun _ h => by cases h) (by simp [hss]) rfl
    (by simp [Op.eval]) (fun h0 => by simp [Op.stepFails, Op.readsDivisor, hwM h0])
  have hdv : colMap .first M sel sel .i64 .i64 [] [(.rdiv, w.toUInt64)] = .ok dv := by
    unfold colMap; simp only [hdv', bind, Except.bind, pure, Except.pure]
  have hmv : colMap .first M sel sel .i64 .i64 [] [(.rmod, w.toUInt64)] = .ok mv := by
    unfold colMap; simp only [hmv', bind, Except.bind, pure, Except.pure]
  have hd : ∀ k < M.toNat, ((raw .i64 M dv)[k]?.getD 0).toNat < g.toNat ∧
      ((raw .i64 M mv)[k]?.getD 0).toNat < w.toNat ∧
      (raw .i64 (g * w) o)[((raw .i64 M dv)[k]?.getD 0).toNat * w.toNat +
        ((raw .i64 M mv)[k]?.getD 0).toNat]?.getD 0 ≠ 0 := fun k hk => by
    obtain ⟨h1, h2', h3⟩ := bit_dec (hp k hk).1
    have := g.toNat_lt_size; have := w.toNat_lt_size; have := (hp k hk).1
    have hU64 : USize.size ≤ 2 ^ 64 := by rcases USize.size_eq with h | h <;> omega
    rw [hdw hdv k hk, hmw hmv k hk, toNat_toUInt64 (by omega), toNat_toUInt64 (by omega), h3]
    exact ⟨h1, h2', (hp k hk).2⟩
  obtain ⟨ix, hix⟩ := kgather_ok (colMap_closed hdv).1 hra (colMap_plain hdv) fun k hk => (hd k hk).1
  obtain ⟨iy, hiy⟩ := kgather_ok (colMap_closed hmv).1 hrc (colMap_plain hmv) fun k hk => (hd k hk).2.1
  obtain ⟨vx, hvx⟩ := hx M ix (kgather_closed hix).1 (kgather_noNul hix hraN) fun k hk => by
    rw [(kgather_word hix hraN k hk).2]; exact (hin _ (hd k hk).1 _ (hd k hk).2.1 (hd k hk).2.2).1
  obtain ⟨vy, hvy⟩ := hy M iy (kgather_closed hiy).1 (kgather_noNul hiy hrcN) fun k hk => by
    rw [(kgather_word hiy hrcN k hk).2]; exact (hin _ (hd k hk).1 _ (hd k hk).2.1 (hd k hk).2.2).2
  intro e; unfold Tab.ofBits
  simp only [hsel, hdv, hix, hmv, hiy, hvx, hvy, bind, Except.bind, pure, Except.pure]
  nofun

/-- **A set bit of a matrix `Tab.ofBits` read back names rows of both sides**: `ofBits` gathered `x` at `ra[a]` and
    `y` at `rc[j]`. -/
theorem Tab.ofBits_in {n m g w : USize} {o ra rc : Enc} {x : Vals A n} {y : Vals C m} {X : Tab A C}
    (h : Tab.ofBits g w o x ra y rc = .ok X) (hraN : hasNul ra = false) (hrcN : hasNul rc = false)
    (hgw : (g * w).toNat = g.toNat * w.toNat)
    (h2 : ∀ a < g.toNat, ∀ j < w.toNat, (raw .i64 (g * w) o)[a * w.toNat + j]?.getD 0 < 2)
    {a j : Nat} (ha : a < g.toNat) (hj : j < w.toNat) (hs : (raw .i64 (g * w) o)[a * w.toNat + j]?.getD 0 ≠ 0) :
    ((raw .i64 g ra)[a]?.getD 0).toNat < n.toNat ∧ ((raw .i64 w rc)[j]?.getD 0).toNat < m.toNat := by
  have hb2 : ∀ p < (g * w).toNat, (raw .i64 (g * w) o)[p]?.getD 0 < 2 := fun p hp => by
    obtain ⟨h1, h2', h3⟩ := bit_dec (hgw ▸ hp); have := h2 _ h1 _ h2'; rwa [h3] at this
  simp only [Tab.ofBits, bind] at h
  rw [Except.bind_eq_ok'] at h; obtain ⟨⟨M, sel⟩, hsel, h⟩ := h; try dsimp only at h
  rw [Except.bind_eq_ok'] at h; obtain ⟨dv, hdv, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨ix, hix, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨mv, hmv, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨iy, hiy, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨vx, hvx, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨vy, hvy, -⟩ := h
  have hap := bit_lt ha hj
  have hT := whereCol_lt hsel
  obtain ⟨k, hk, hkp⟩ := (whereCol_mem hsel hb2 _).2 ⟨by omega, hs⟩
  have hp : ∀ k < M.toNat, ((raw .i64 M sel)[k]?.getD 0).toNat < g.toNat * w.toNat := fun k hk => by
    have := ((whereCol_mem hsel hb2 _).1 ⟨k, hk, rfl⟩).1; omega
  obtain ⟨hdw, hmw⟩ := colMap_div_mod (M := M) (w := w) (sel := sel) (fun k hk => by have := hp k hk; omega)
    (fun k hk => by have := bit_w (hp k hk); omega)
  have := g.toNat_lt_size; have := w.toNat_lt_size
  have hU64 : USize.size ≤ 2 ^ 64 := by rcases USize.size_eq with h | h <;> omega
  have e1 : ((raw .i64 M dv)[k]?.getD 0).toNat = a := by
    rw [hdw hdv k hk, hkp, Nat.add_comm, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt hj, Nat.zero_add]
    exact toNat_toUInt64 (x := a) (by omega)
  have e2 : ((raw .i64 M mv)[k]?.getD 0).toNat = j := by
    rw [hmw hmv k hk, hkp, Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hj]
    exact toNat_toUInt64 (x := j) (by omega)
  obtain ⟨i, hi, -⟩ := Vals.gather_row x hvx ⟨k, hk⟩
  obtain ⟨i', hi', -⟩ := Vals.gather_row y hvy ⟨k, hk⟩
  rw [(kgather_word hix hraN k hk).2, e1] at hi
  rw [(kgather_word hiy hrcN k hk).2, e2] at hi'
  exact ⟨hi ▸ i.2, hi' ▸ i'.2⟩

/-- **What a `Tab.ofBits` that answered read**: `ra`, `rc` valid, and each side gathered once. -/
theorem Tab.ofBits_reads {n m g w : USize} {o ra rc : Enc} {x : Vals A n} {y : Vals C m} {X : Tab A C}
    (h : Tab.ofBits g w o x ra y rc = .ok X) : Enc.Valid g ra ∧ Enc.Valid w rc ∧
      (∃ M ix v, Vals.gather M ix x = .ok v) ∧ ∃ M iy v, Vals.gather M iy y = .ok v := by
  simp only [Tab.ofBits, bind] at h
  rw [Except.bind_eq_ok'] at h; obtain ⟨⟨M, sel⟩, -, h⟩ := h; try dsimp only at h
  rw [Except.bind_eq_ok'] at h; obtain ⟨_, -, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨ix, hix, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨_, -, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨iy, hiy, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨vx, hvx, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨vy, hvy, -⟩ := h
  exact ⟨kgather_valid hix, kgather_valid hiy, ⟨_, _, _, hvx⟩, ⟨_, _, _, hvy⟩⟩

/-- **`Tab.ofBits` reads back every matrix `compSelM` builds**. -/
theorem Tab.compSelM_reads {r : Tab A B} {s : Tab B C} {g w : USize} {o ra rc : Enc}
    (h : Tab.compSelM Tab.bitsMax r s = .ok (.inr (g, w, o, ra, rc))) :
    ∀ e, Tab.ofBits g w o r.key ra s.val rc ≠ .error e := by
  have hU : 2 ^ 32 ≤ USize.size := by rcases USize.size_eq with h | h <;> omega
  simp only [Tab.compSelM, bind] at h
  rw [Except.bind_eq_ok'] at h; obtain ⟨_, -, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨_, -, h⟩ := h
  split at h
  · rw [Except.bind_eq_ok'] at h; obtain ⟨_, -, h⟩ := h; cases h
  rw [Except.bind_eq_ok'] at h; obtain ⟨⟨ka1, aR1, ra1⟩, hca1, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨⟨kc1, cS1, rc1⟩, hcc1, h⟩ := h
  split at h
  · rename_i hwin
    rw [Except.bind_eq_ok'] at h; obtain ⟨mm, hm, h⟩ := h
    simp only [pure, Except.pure, Except.ok.injEq, Sum.inr.injEq] at h; subst h
    simp only [Tab.compMat, bind] at hm
    rw [Except.bind_eq_ok'] at hm; obtain ⟨_, -, hm⟩ := hm
    rw [Except.bind_eq_ok'] at hm; obtain ⟨⟨ka, aR, ra'⟩, hca, hm⟩ := hm; try dsimp only at hm
    rw [Except.bind_eq_ok'] at hm; obtain ⟨⟨kc, cS, rc'⟩, hcc, hm⟩ := hm; try dsimp only at hm
    split at hm; · cases hm
    rw [Except.bind_eq_ok'] at hm; obtain ⟨_, -, hm⟩ := hm
    rw [Except.bind_eq_ok'] at hm; obtain ⟨_, -, hm⟩ := hm
    rw [Except.bind_eq_ok'] at hm; obtain ⟨_, -, hm⟩ := hm
    rw [Except.bind_eq_ok'] at hm; obtain ⟨o0, hko, hm⟩ := hm
    simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hm
    obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := hm
    rw [hca, Except.ok.injEq, Prod.mk.injEq] at hca1; obtain ⟨rfl, -⟩ := hca1
    rw [hcc, Except.ok.injEq, Prod.mk.injEq] at hcc1; obtain ⟨rfl, -⟩ := hcc1
    simp only [Tab.bitsWin, Bool.and_eq_true, decide_eq_true_eq] at hwin
    have hB : ka.toNat * kc.toNat ≤ Tab.bitsMax := hwin.1.1.1.2
    have hbm : Tab.bitsMax = 2 ^ 27 := rfl
    obtain ⟨-, hgw, -, -, -, -, -, hbit⟩ := raw_kbitrows hko
    obtain ⟨-, -, hra, -⟩ := Vals.code_spec hca
    obtain ⟨-, -, hrc, -⟩ := Vals.code_spec hcc
    refine Tab.ofBits_ok hgw (by omega)
      (raw_size_of_bits hgw fun a ha j hj => let ⟨v, _, hv, _⟩ := hbit a ha j hj; ⟨v, hv⟩)
      (fun a ha j hj => by obtain ⟨v, -, hv, hv2, -⟩ := hbit a ha j hj; rw [hv]; exact hv2)
      (Vals.code_valid hca) (Vals.code_valid hcc) (Vals.code_plain hca).2.1 (Vals.code_plain hcc).2.1 (fun a ha j hj _ => ⟨?_, ?_⟩)
      (fun _ _ hv hn hr => Vals.gather_ok_of_code hca hv hn hr) (fun _ _ hv hn hr => Vals.gather_ok_of_code hcc hv hn hr)
    · obtain ⟨i, hi, -⟩ := hra a ha; rw [hi]; exact i.2
    · obtain ⟨i, hi, -⟩ := hrc j hj; rw [hi]; exact i.2
  · rw [Except.bind_eq_ok'] at h; obtain ⟨_, -, h⟩ := h; cases h

/-- **`Tab.ofBits` reads back every matrix `compTabMat` builds from a `BitsWf` one** within `Tab.bitsMax`: a set bit
    `(a, j)` of the answer is the `∨` of bits `(·, j)` of the argument, whose `rc[j]` its own read-back gathered. -/
theorem Tab.compTabMat_reads {n m M : USize} {r : Tab A B} {g w ka : USize} {o o' ra ra' rc : Enc}
    {x : Vals B n} {key : Vals A M} {y : Vals C m} (hw : BitsWf g w o x ra y rc)
    (h : Tab.compTabMat r g w o x ra = .ok (ka, o', ⟨M, key⟩, ra')) (hB : ka.toNat * w.toNat ≤ Tab.bitsMax) :
    ∀ e, Tab.ofBits ka w o' key ra' y rc ≠ .error e := by
  have hU : 2 ^ 32 ≤ USize.size := by rcases USize.size_eq with h | h <;> omega
  have hbm : Tab.bitsMax = 2 ^ 27 := rfl
  simp only [Tab.compTabMat, bind] at h
  rw [Except.bind_eq_ok'] at h; obtain ⟨_, -, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨_, -, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨_, -, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨⟨M0, sel⟩, -, h⟩ := h; try dsimp only at h
  rw [Except.bind_eq_ok'] at h; obtain ⟨key0, -, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨⟨ka0, aR, ra0⟩, hcode, h⟩ := h; try dsimp only at h
  rw [Except.bind_eq_ok'] at h; obtain ⟨_, -, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨_, -, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨o0, hko, h⟩ := h
  simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
  obtain ⟨e1, e2, hS, e3⟩ := h
  subst ka0 o0 ra0
  obtain ⟨eM, eK⟩ := Sigma.mk.inj hS
  subst M0
  have eK' := eq_of_heq eK
  subst key0
  obtain ⟨hr, hgw0, ho, -, -, -, hrcN, -⟩ := hw
  rcases hs : Tab.ofBits g w o x ra y rc with e | s
  · exact absurd hs (hr e)
  obtain ⟨-, hrc, -, ⟨My, iy, vy, hvy⟩⟩ := Tab.ofBits_reads hs
  have ho2 : ∀ a < g.toNat, ∀ j < w.toNat, (raw .i64 (g * w) o)[a * w.toNat + j]?.getD 0 < 2 :=
    fun a ha j hj => by obtain ⟨v, hv, hv2⟩ := some_lt_two (ho a ha j hj); rw [hv]; exact hv2
  obtain ⟨-, hgw, -, -, -, hseg, hidx, hbit⟩ := raw_kbitrows hko
  obtain ⟨-, -, hra, -⟩ := Vals.code_spec hcode
  refine Tab.ofBits_ok hgw (by omega)
    (raw_size_of_bits hgw fun a ha j hj => let ⟨v, _, hv, _⟩ := hbit a ha j hj; ⟨v, hv⟩)
    (fun a ha j hj => by obtain ⟨v, -, hv, hv2, -⟩ := hbit a ha j hj; rw [hv]; exact hv2)
    (Vals.code_valid hcode) hrc (Vals.code_plain hcode).2.1 hrcN (fun a ha j hj hne => ⟨?_, ?_⟩)
    (fun _ _ hv hn hr => Vals.gather_ok_of_code hcode hv hn hr)
    (fun _ _ hv hn hr => Vals.gather_ok_of_ok hv hn y hvy hr)
  · obtain ⟨i, hi, -⟩ := hra a ha; rw [hi]; exact i.2
  · obtain ⟨v, -, hv, hv2, hv1⟩ := hbit a ha j hj
    rw [hv, Option.getD_some] at hne
    have h1 : v = 1 := UInt64.toNat_inj.1 (by
      have h1 := UInt64.lt_iff_toNat_lt.1 hv2
      have h0 : v.toNat ≠ 0 := fun h0 => hne (UInt64.toNat_inj.1 h0)
      simp at h1 ⊢; omega)
    have H := hv1.1 h1
    simp only [Bool.false_eq_true, ↓reduceIte] at H
    obtain ⟨k, hk1, hk2, hon⟩ := H
    have hkM : k < M.toNat := Nat.lt_of_lt_of_le hk2 (hseg a ha).2
    refine (Tab.ofBits_in hs hgw0 ho2 (hidx k hkM) hj fun h0 => ?_).2
    rw [h0] at hon; exact absurd hon (by decide)

/-- **`Tab.ofBits` reads back every matrix `ldivTabMat` builds from a `BitsWf` one**: `ldivTabMat_spec` gives its
    words, its `none` test `Tab.bitsMax`, and `Vals.code2` the rows of each side. -/
theorem Tab.ldivTabMat_reads {n m N N' : USize} {r : Tab A B} {ub : Tab B B} {uc : Tab C C} {g w kb kc : USize}
    {o o' ra rb rc rc' : Enc} {x : Vals A n} {y : Vals C m} {zb : Vals B N} {zc : Vals C N'}
    (hw : BitsWf g w o x ra y rc)
    (h : Tab.ldivTabMat r ub uc g w o x ra y rc = .ok (some (kb, kc, o', ⟨N, zb⟩, rb, ⟨N', zc⟩, rc')))
    (hrw : r.WF) (hub : ub.WF) (huc : uc.WF) (wx : Vals.WF x) (wy : Vals.WF y) :
    ∀ e, Tab.ofBits kb kc o' zb rb zc rc' ≠ .error e := by
  have hU : 2 ^ 32 ≤ USize.size := by rcases USize.size_eq with h | h <;> omega
  obtain ⟨hr, -, ho, hx, hy, hra, hrc, -⟩ := hw
  rcases hs : Tab.ofBits g w o x ra y rc with e | s
  · exact absurd hs (hr e)
  obtain ⟨hkbc, -, PP, hw', -, -, -⟩ :=
    Tab.ldivTabMat_spec h hs (fun a ha j hj => some_lt_two (ho a ha j hj)) hx hy hra hrc hrw hub huc wx wy
  simp only [Tab.ldivTabMat, bind] at h
  rw [Except.bind_eq_ok'] at h; obtain ⟨⟨kb0, bR, bU, Nb, zb0, rb0⟩, hb2, h⟩ := h; try dsimp only at h
  rw [Except.bind_eq_ok'] at h; obtain ⟨yM, hyM, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨⟨kc0, cM, cU, Nc, zc0, rc0⟩, hc2, h⟩ := h; try dsimp only at h
  split at h
  · cases h
  rename_i hov
  repeat (rw [Except.bind_eq_ok'] at h; obtain ⟨_, -, h⟩ := h; try dsimp only at h)
  simp only [pure, Except.pure, Except.ok.injEq, Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨e1, e2, e3, hzb, e4, hzc, e5⟩ := h
  subst kb0 kc0 rb0 rc0
  obtain ⟨eN, eZ⟩ := Sigma.mk.inj hzb; subst Nb; have eZ' := eq_of_heq eZ; subst zb0
  obtain ⟨eN', eZ2⟩ := Sigma.mk.inj hzc; subst Nc; have eZ2' := eq_of_heq eZ2; subst zc0
  simp only [not_or, Nat.not_lt, Tab.bitsMax] at hov
  obtain ⟨cb, hcb⟩ := Vals.code2_code hb2
  obtain ⟨cc, hcc⟩ := Vals.code2_code hc2
  obtain ⟨-, -, hrb, -⟩ := Vals.code_spec hcb
  obtain ⟨-, -, hrc, -⟩ := Vals.code_spec hcc
  refine Tab.ofBits_ok hkbc (by omega)
    (raw_size_of_bits hkbc fun a ha j hj => let ⟨v, hv, _⟩ := hw' a ha j hj; ⟨v, hv⟩)
    (fun a ha j hj => by obtain ⟨v, hv, hv2, -⟩ := hw' a ha j hj; rw [hv]; exact hv2)
    (Vals.code_valid hcb) (Vals.code_valid hcc) (Vals.code_plain hcb).2.1 (Vals.code_plain hcc).2.1 (fun a ha j hj _ => ⟨?_, ?_⟩)
    (fun _ _ hv hn hr => Vals.gather_ok_of_code hcb hv hn hr) (fun _ _ hv hn hr => Vals.gather_ok_of_code hcc hv hn hr)
  · obtain ⟨i, hi, -⟩ := hrb a ha; rw [hi]; exact i.2
  · obtain ⟨i, hi, -⟩ := hrc j hj; rw [hi]; exact i.2

end Rel

/-! ### `comp` and `meet`: the two ops that read a bit matrix, sound on a `Rel.Wf` argument -/

namespace Rel.Lang.GenK

open Rel Rel.Rep Rel.Kernel Rel.Verify Gen
open scoped Rel.Core.Rel
open Rel.Core.Rel hiding id comp recip inter union zero le inl inr junc

variable {A B C : Obj}

theorem inter_law {R S : Rel A B} (wR : R.Wf) (wS : S.Wf) {t : Tab A B}
    (h : (do Tab.inter (← R.runE {}) (← S.runE {})) = .ok t) :
    ∃ r s, R.runE {} = .ok r ∧ S.runE {} = .ok s ∧ ∀ a c, rep t a c ↔ rep r a c ∧ rep s a c := by
  obtain ⟨r, hr, h⟩ := bind_ok h
  obtain ⟨s, hs, ht⟩ := bind_ok h
  exact ⟨r, s, hr, hs, Tab.inter_holds ht (wR.runE Known.wf_empty hr) (wS.runE Known.wf_empty hs)⟩

/-- `T ∩ M` for a `Rel.Wf` matrix `M` (`BitsWf` over `WF` sides) and a `T` that is `WF` where it runs. -/
theorem keep_law {n m : USize} {T : Except String (Tab A B)} {g w : USize} {o ra rc : Enc} {x : Vals A n}
    {y : Vals B m} {t : Tab A B} (hw : BitsWf g w o x ra y rc ∧ Vals.WF x ∧ Vals.WF y)
    (hT : ∀ u, T = .ok u → u.WF) (h : (T >>= (Tab.keepBits · g w o x ra y rc)) = .ok t) :
    ∃ u s, T = .ok u ∧ Tab.ofBits g w o x ra y rc = .ok s ∧ ∀ a c, rep t a c ↔ rep u a c ∧ rep s a c := by
  obtain ⟨u, hu, h⟩ := bind_ok h
  obtain ⟨⟨hr, hgw, ho, hx, hy, hra, hrc, hoN⟩, wx, wy⟩ := hw
  rcases hs : Tab.ofBits g w o x ra y rc with e | s
  · exact absurd hs (hr e)
  refine ⟨u, s, hu, rfl, fun a c => ?_⟩
  rw [Tab.keepBits_law h hs hgw (fun a ha j hj => some_lt_two (ho a ha j hj)) hx hy hra hrc hoN (hT u hu) wx wy]; exact Iff.rfl

/-- `meetV` of two values is the meet of the two tables they read as. -/
theorem meetV_law {R S : Rel A B} (wR : R.Wf) (wS : S.Wf) {K : Known A B} {t : Tab A B}
    (h : (meetV R S).runE K = .ok t) :
    ∃ r s, R.runE {} = .ok r ∧ S.runE {} = .ok s ∧ ∀ a c, rep t a c ↔ rep r a c ∧ rep s a c := by
  cases R <;> cases S <;> first
    | exact inter_law wR wS h
    | exact keep_law wS (fun _ h => wR.runE Known.wf_empty h) h
    | (obtain ⟨u, s, hu, hs, e⟩ := keep_law wR (fun _ h => wS.runE Known.wf_empty h) h; exact ⟨s, u, hs, hu, fun a c => (e a c).trans and_comm⟩)

/-- `K` with each unknown side filled by a `Vals.WF` value set (`meetOn` bounding `S` by a bit matrix's sides) is
    `WF`. -/
theorem _root_.Rel.Known.WF.orElse {K : Known A B} (h : K.WF) {n m : USize} {x : Vals A n} {y : Vals B m}
    (hx : Vals.WF x) (hy : Vals.WF y) :
    (⟨K.dom.orElse fun _ => some ⟨n, x⟩, K.ran.orElse fun _ => some ⟨m, y⟩, none⟩ : Known A B).WF := by
  obtain ⟨_ | _, _ | _, _⟩ := K <;> exact ⟨by first | exact hx | exact h.1, by first | exact hy | exact h.2.1, trivial⟩

/-- `meetOn K T S` agrees with `P ∩ Q` on `K`, where `T` agrees with `P`: on a pair of `T`'s table, inside the
    `bound` it hands `S` (a bit matrix's: `K`'s sides, else the matrix's row and column values), `S` agrees with `Q`;
    off it both sides are false. -/
theorem meetOn_sound {K : Known A B} {T S : Rel A B} {P Q : Core.Rel A.El B.El} (hK : K.WF) (wT : T.Wf)
    (eT : ∀ r, T.runE {} = .ok r → Agrees K (rep r) P) (wS : S.Wf) (hS : ∀ K, K.WF → S.Reps K Q) :
    ∀ t, (meetOn K T S).runE K = .ok t → Agrees K (rep t) (P ∩ Q) := by
  intro t h
  have fb : (meetV T (S.force K)).runE K = .ok t → Agrees K (rep t) (P ∩ Q) := fun h => by
    obtain ⟨r, s, hr, hs, e⟩ := meetV_law wT (wS.force hK) h
    have es := (reps_iff _ _ _).1 (hS K hK) s ((force_runE S K {}).symm.trans hs)
    exact fun x y hx hy ho => (e x y).trans (and_congr (eT r hr x y hx hy ho) (es x y hx hy ho))
  unfold meetOn at h; split at h
  · exact fb h
  · rename_i n m g w o x ra y rc
    have hK' := hK.orElse wT.2.1 wT.2.2
    obtain ⟨r, s, hr, hs, e⟩ := meetV_law wT (wS.force hK') h
    have es := (reps_iff _ _ _).1 (hS _ hK') s ((force_runE S _ {}).symm.trans hs)
    -- a row of the matrix has its key among `x` and its value among `y`, so it lies inside the bound `S` was run on
    have hin : ∀ a c, K.den.1 a a → K.den.2 c c → rep r a c →
        (⟨K.dom.orElse fun _ => some ⟨n, x⟩, K.ran.orElse fun _ => some ⟨m, y⟩, none⟩ : Known A B).den.1 a a ∧
        (⟨K.dom.orElse fun _ => some ⟨n, x⟩, K.ran.orElse fun _ => some ⟨m, y⟩, none⟩ : Known A B).den.2 c c := by
      intro a c ha hc hac
      obtain ⟨⟨_, hgw, ho, -, -, hra, hrc, -⟩, -, -⟩ := wT
      obtain ⟨_, _, _, _, _, ⟨i, -, hi⟩, j, -, hj⟩ :=
        (Tab.ofBits_set hr hra hrc hgw (fun a ha j hj => some_lt_two (ho a ha j hj)) a c).1 hac
      obtain ⟨_ | _, _ | _, _⟩ := K <;>
        exact ⟨by first | exact ha | exact (side_some rfl a).2 ⟨i, hi⟩, by first | exact hc | exact (side_some rfl c).2 ⟨j, hj⟩⟩
    have er := eT r hr
    intro a c ha hc ho
    refine (e a c).trans ⟨fun ⟨u, v⟩ => ⟨(er a c ha hc ho).1 u, (es a c (hin a c ha hc u).1 (hin a c ha hc u).2 trivial).1 v⟩,
      fun ⟨u, v⟩ => ?_⟩
    have u' := (er a c ha hc ho).2 u
    exact ⟨u', (es a c (hin a c ha hc u').1 (hin a c ha hc u').2 trivial).2 v⟩
  · split at h
    · rename_i r0 h0
      split at h
      · rename_i p hp
        have wp := bound_wf hK (wT.runE Known.wf_empty h0) hp
        obtain ⟨r, s, hr, hs, e⟩ := meetV_law (R := .tab (.ok p.1)) wp.1 (wS.force wp.2) h
        obtain rfl := Except.ok.inj hr
        obtain ⟨hu, hK⟩ := bound_spec hK (wT.runE Known.wf_empty h0) hp
        have er := eT r0 h0
        have es := (reps_iff _ _ _).1 (hS p.2 wp.2) s ((force_runE S p.2 {}).symm.trans hs)
        intro x y hx hy ho
        refine (e x y).trans ⟨fun ⟨a, b⟩ => ⟨(er x y hx hy ho).1 ((hu x y hx hy ho).1 a),
          (es x y (hK x y a).1 (hK x y a).2.1 (hK x y a).2.2).1 b⟩, fun ⟨a, b⟩ => ?_⟩
        have a' := (hu x y hx hy ho).2 ((er x y hx hy ho).2 a)
        exact ⟨a', (es x y (hK x y a').1 (hK x y a').2.1 (hK x y a').2.2).2 b⟩
      · nomatch h
    · exact fb h

theorem meetK_sound {R S : Rel A B} {X Y : Core.Rel A.El B.El} (hR : ∀ K, K.WF → R.Reps K X) (hS : ∀ K, K.WF → S.Reps K Y)
    (wR : R.Wf) (wS : S.Wf) (K : Known A B) (hK : K.WF) :
    ∀ t, (meetK K R S).runE K = .ok t → Agrees K (rep t) (X ∩ Y) := by
  intro t h
  have eF : ∀ {Z : Rel A B} {W : Core.Rel A.El B.El}, (∀ K, K.WF → Z.Reps K W) → ∀ r, (Z.force K).runE {} = .ok r →
      Agrees K (rep r) W := fun hZ r h => (reps_iff _ _ _).1 (hZ K hK) r ((force_runE _ K {}).symm.trans h)
  have sw : Agrees K (rep t) (Y ∩ X) → Agrees K (rep t) (X ∩ Y) := fun h x y hx hy ho => (h x y hx hy ho).trans and_comm
  cases R <;> cases S
  case lazy.lazy f g =>
    simp only [meetK] at h
    have e := eF hR; have w := wR.force hK
    generalize (Rel.lazy f).force K = F at e w h
    rcases F with (_ | _) | _ | _ <;> first
      | exact sw (meetOn_sound hK (wS.force hK) (eF hS) wR hR t (retried_ok h))
      | exact meetOn_sound hK w e wS hS t h
  all_goals first
    | exact sw (meetOn_sound hK (wS.force hK) (eF hS) wR hR t h)
    | exact meetOn_sound hK (wR.force hK) (eF hR) wS hS t h

theorem meet_sound {R S : Rel A B} {X Y : Core.Rel A.El B.El} (hR : ∀ K, K.WF → R.Reps K X)
    (hS : ∀ K, K.WF → S.Reps K Y) (wR : R.Wf) (wS : S.Wf) : ∀ K, K.WF → (GenK.meet A B R S).Reps K (X ∩ Y) :=
  fun K hK => by
  have eR := (reps_iff _ _ _).1 (hR K hK); have eS := (reps_iff _ _ _).1 (hS K hK)
  rw [reps_iff]
  cases R <;> cases S <;> first
    | exact meetK_sound hR hS wR wS K hK
    | exact fun t h => let ⟨r, s, hr, hs, e⟩ := meetV_law wR wS h
        fun x y hx hy ho => (e x y).trans (and_congr (eR r hr x y hx hy ho) (eS s hs x y hx hy ho))

/-- A `tab` value is `Wf` where the table it holds is `Tab.WF`. -/
theorem tab_wf {x : Except String (Tab A B)} (h : ∀ t, x = .ok t → t.WF) : (Rel.tab x).Wf := by
  cases x with
  | error => trivial
  | ok t => exact h t rfl

/-- `meetV` keeps `Tab.WF`: `Tab.inter` of two `WF` tables (`Tab.inter_wf`), or a table's rows kept by a bit
    matrix (`Tab.keepBits_wf`). -/
theorem meetV_wf {R S : Rel A B} (wR : R.Wf) (wS : S.Wf) : (meetV R S).Wf := by
  have I : ∀ x y : Rel A B, x.Wf → y.Wf → (Rel.tab do Tab.inter (← x.runE {}) (← y.runE {})).Wf := fun x y wx wy =>
    tab_wf fun t h => let ⟨r, hr, h⟩ := bind_ok h; let ⟨s, hs, h⟩ := bind_ok h
      Tab.inter_wf h (wx.runE Known.wf_empty hr) (wy.runE Known.wf_empty hs)
  have P : ∀ {n m : USize} (t : Except String (Tab A B)) (g w : USize) (o : Enc) (x : Vals A n) (ra : Enc)
      (y : Vals B m) (rc : Enc),(Rel.tab t).Wf → (Rel.tab (t >>= (Tab.keepBits · g w o x ra y rc))).Wf :=
    fun t _ _ _ _ _ _ _ wt => tab_wf fun u h => let ⟨v, hv, h⟩ := bind_ok h
      Tab.keepBits_wf h (by subst hv; exact wt)
  cases R <;> cases S <;> first | exact I _ _ wR wS | exact P _ _ _ _ _ _ _ _ wR | exact P _ _ _ _ _ _ _ _ wS

theorem meetOn_wf {K : Known A B} (hK : K.WF) {T S : Rel A B} (wT : T.Wf) (wS : S.Wf) : (meetOn K T S).Wf := by
  unfold meetOn; split
  · exact meetV_wf wT (wS.force hK)
  · exact meetV_wf wT (wS.force (hK.orElse wT.2.1 wT.2.2))
  · split
    · rename_i r0 h0
      split
      · rename_i p hp
        have wp := bound_wf hK (wT.runE Known.wf_empty h0) hp
        exact meetV_wf wp.1 (wS.force wp.2)
      · trivial
    · exact meetV_wf wT (wS.force hK)

theorem meetK_wf {K : Known A B} (hK : K.WF) {R S : Rel A B} (wR : R.Wf) (wS : S.Wf) : (meetK K R S).Wf := by
  cases R <;> cases S
  case lazy.lazy f g =>
    simp only [meetK]; have w := wR.force hK
    generalize (Rel.lazy f).force K = F at w ⊢
    rcases F with (_ | _) | _ | _ <;> first
      | exact (meetOn_wf hK (wS.force hK) wR).retried _
      | exact meetOn_wf hK w wS
  all_goals first | exact meetOn_wf hK wS wR | exact meetOn_wf hK wR wS

theorem meet_wf {R S : Rel A B} (wR : R.Wf) (wS : S.Wf) : (GenK.meet A B R S).Wf := by
  unfold GenK.meet; split <;> first | exact meetV_wf wR wS | exact fun K hK => meetK_wf hK wR wS

theorem compR_runE (r : Tab A B) (s : Tab B C) (K : Known A C) :
    (compR r s).runE K = Tab.compSel Tab.bitsMax r s := by
  unfold compR Tab.compSel
  rcases Tab.compSelM Tab.bitsMax r s with e | t | ⟨g, w, o, ra, rc⟩ <;> rfl

theorem compR_sound {r : Tab A B} {s : Tab B C} {K : Known A C} {Z : Core.Rel A.El C.El}
    (wr : r.WF) (ws : s.WF) (H : Agrees K (rep r ≫ rep s) Z) : (compR r s).Reps K Z := by
  rw [reps_iff, compR_runE]; intro t ht x z hx hz ho
  exact (Tab.compSel_holds ht wr ws x z).trans (H x z hx hz ho)

theorem compR_wf {r : Tab A B} {s : Tab B C} (wr : r.WF) (ws : s.WF) : (compR r s).Wf := by
  unfold compR; split
  next g w o ra rc h => exact ⟨Tab.compSelM_wf h (Tab.compSelM_reads h), wr.1, ws.2⟩
  next t h => exact Tab.compSelM_inl_wf h wr ws
  all_goals trivial

theorem compV_sound {r : Tab A B} {S : Rel B C} {K : Known A C} {Z : Core.Rel A.El C.El} (wr : r.WF) (wS : S.Wf)
    (H : ∀ s, S.runE {} = .ok s → Agrees K (rep r ≫ rep s) Z) : (compV r S).Reps K Z := by
  cases S with
  | bits g w o x ra y rc =>
    obtain ⟨hr, -, ho, hx, -, hra, hrc, -⟩ := wS.1
    rcases hc : Tab.compTabMat r g w o x ra with e | ⟨ka, o', ⟨M, key⟩, ra'⟩
    · simp only [compV, hc]; rw [reps_iff]; intro t ht; nomatch ht
    · simp only [compV, hc]
      rcases hs : Tab.ofBits g w o x ra y rc with e | s
      · exact absurd hs (hr e)
      split
      · rw [reps_iff]; intro t ht
        rw [Tab.compTabMat_law hc ht hs (fun a ha j hj => some_lt_two (ho a ha j hj)) hx hra hrc wr wS.2.1]; exact H s hs
      · exact compR_sound wr (Tab.ofBits_wf hs wS.2.1 wS.2.2) (H s hs)
  | tab t0 =>
    cases t0 with
    | error e => rw [reps_iff]; intro t ht; nomatch ht
    | ok s => exact compR_sound wr wS (H s rfl)
  | lazy f =>
    show (match (Rel.lazy f).runE {} with | .ok s => compR r s | .error e => .tab (.error e)).Reps K Z
    rcases hs : (Rel.lazy f).runE {} with e | s
    · rw [reps_iff]; intro t ht; nomatch ht
    · exact compR_sound wr (wS.runE Known.wf_empty hs) (H s hs)

theorem compV_wf {r : Tab A B} {S : Rel B C} (wr : r.WF) (wS : S.Wf) : (compV r S).Wf := by
  cases S with
  | bits g w o x ra y rc =>
    rcases hc : Tab.compTabMat r g w o x ra with e | ⟨ka, o', ⟨M, key⟩, ra'⟩
    · simp only [compV, hc]; trivial
    · simp only [compV, hc]
      split
      · next hle => exact ⟨Tab.compTabMat_wf hc (Tab.compTabMat_reads wS.1 hc hle) wS.1,
          Tab.compTabMat_key_wf hc wr, wS.2.2⟩
      · split
        · next s hs => exact compR_wf wr (Tab.ofBits_wf hs wS.2.1 wS.2.2)
        · trivial
  | tab t0 => cases t0 with
    | error e => trivial
    | ok s => exact compR_wf wr wS
  | lazy f =>
    show (match (Rel.lazy f).runE {} with | .ok s => compR r s | .error e => .tab (.error e)).Wf
    rcases hs : (Rel.lazy f).runE {} with e | s
    · trivial
    · exact compR_wf wr (wS.runE Known.wf_empty hs)

theorem compT_sound {r' : Except String (Tab A B)} {S : Rel B C} {K : Known A C}
    {X : Core.Rel A.El B.El} {Y : Core.Rel B.El C.El}
    (hr : ∀ r, r' = .ok r → Agrees ⟨K.dom, none, none⟩ (rep r) X) (hS : ∀ K, K.WF → S.Reps K Y) (wS : S.Wf)
    (hK : K.WF) (wr : ∀ r, r' = .ok r → r.WF) :
    (compT r' S).Reps K (X ≫ Y) := by
  rcases r' with e | r
  · rw [reps_iff]; intro t ht; nomatch ht
  have er := hr r rfl
  cases S with
  | lazy g =>
    simp only [compT]
    split
    · next hn =>
      rw [reps_iff]; intro t ht x z hx _ _
      refine (Tab.zero_holds ht x z).trans ⟨False.elim, fun ⟨b, h, _⟩ => ?_⟩
      obtain ⟨i, _, _⟩ := (er x b hx rfl trivial).2 h
      have := i.2; simp [beq_iff_eq.1 hn] at this
    · simp only [Rel.Rel.Reps]
      rcases hd : Tab.ran r with e | d
      · rw [reps_iff]; intro t ht; nomatch ht
      have kW : (⟨some ⟨d.n, d.key⟩, K.ran, none⟩ : Known B C).WF := ⟨(Tab.ran_wf hd (wr r rfl)).1, hK.2.1, trivial⟩
      refine compV_sound (wr r rfl) (wS.force kW) fun s hs a c ha hc _ => exists_congr fun b => ?_
      rw [force_runE] at hs
      have es := (reps_iff _ _ _).1 (hS _ kW) s hs
      have inRan : rep r a b → (⟨some ⟨d.n, d.key⟩, K.ran, none⟩ : Known B C).den.1 b b := fun h =>
        (side_some rfl b).2 ((keyRowRep d b).2 ⟨b, (Tab.ran_holds hd b b).2 ⟨rfl, a, h⟩⟩)
      have e1 := er a b ha rfl trivial
      exact ⟨fun ⟨h1, h2⟩ => ⟨e1.1 h1, (es b c (inRan h1) hc trivial).1 h2⟩,
        fun ⟨h1, h2⟩ => ⟨e1.2 h1, (es b c (inRan (e1.2 h1)) hc trivial).2 h2⟩⟩
  | tab t0 =>
    exact compV_sound (wr r rfl) wS fun (s : Tab B C) hs a c ha _ _ => exists_congr fun b =>
      and_congr (er a b ha rfl trivial) ((reps_iff _ _ _).1 (hS {} Known.wf_empty) s hs b c rfl rfl trivial)
  | bits g w o x ra y rc =>
    exact compV_sound (wr r rfl) wS fun (s : Tab B C) hs a c ha _ _ => exists_congr fun b =>
      and_congr (er a b ha rfl trivial) ((reps_iff _ _ _).1 (hS {} Known.wf_empty) s hs b c rfl rfl trivial)

theorem compT_wf {r' : Except String (Tab A B)} {S : Rel B C} (wr : ∀ r, r' = .ok r → r.WF) (wS : S.Wf) :
    (compT r' S).Wf := by
  rcases r' with e | r
  · trivial
  cases S with
  | lazy g =>
    simp only [compT]
    split
    · exact tab_wf fun _ h => Tab.zero_wf h
    · intro K hK; dsimp only; split
      · next d hd =>
        have kW : (⟨some ⟨d.n, d.key⟩, K.ran, none⟩ : Known B C).WF := ⟨(Tab.ran_wf hd (wr r rfl)).1, hK.2.1, trivial⟩
        exact compV_wf (wr r rfl) (wS.force kW)
      · trivial
  | tab _ => exact compV_wf (wr r rfl) wS
  | bits => exact compV_wf (wr r rfl) wS

theorem compS_sound {R : Rel A B} {s' : Except String (Tab B C)} {K : Known A C} {X : Core.Rel A.El B.El}
    {Y : Core.Rel B.El C.El} (hR : ∀ K, K.WF → R.Reps K X) (hs : ∀ s, s' = .ok s → Agrees ⟨none, K.ran, none⟩ (rep s) Y)
    (hK : K.WF) (ws : ∀ s, s' = .ok s → s.WF) (wR : R.Wf) :
    (compS R K.dom s').Reps K (X ≫ Y) := by
  rcases s' with e | s
  · rw [reps_iff]; intro t ht; nomatch ht
  have es := hs s rfl
  simp only [compS]
  rcases hr : R.runE ⟨K.dom, some ⟨s.n, s.key⟩, none⟩ with e | r
  · rw [reps_iff]; intro t ht; nomatch ht
  have kS : (⟨K.dom, some ⟨s.n, s.key⟩, none⟩ : Known A B).WF := ⟨hK.1, (ws s rfl).1, trivial⟩
  have er := (reps_iff _ R X).1 (hR _ kS) r hr
  refine compR_sound (wR.runE kS hr) (ws s rfl) fun a c ha hc _ => exists_congr fun b => ?_
  have key : ∀ {b}, rep s b c → (⟨K.dom, some ⟨s.n, s.key⟩, none⟩ : Known A B).den.2 b b := fun h =>
    (side_some rfl _).2 ((keyRowRep s _).2 ⟨c, h⟩)
  exact ⟨fun ⟨h1, h2⟩ => ⟨(er a b ha (key h2) trivial).1 h1, (es b c rfl hc trivial).1 h2⟩,
    fun ⟨h1, h2⟩ => have h2' := (es b c rfl hc trivial).2 h2; ⟨(er a b ha (key h2') trivial).2 h1, h2'⟩⟩

theorem compS_wf {R : Rel A B} {D : Option ((n : USize) × Vals A n)} {s' : Except String (Tab B C)}
    (hD : D.elim True fun c => Vals.WF c.2) (wR : R.Wf) (ws : ∀ s, s' = .ok s → s.WF) : (compS R D s').Wf := by
  rcases s' with e | s
  · trivial
  simp only [compS]; split
  · next r hr => exact compR_wf (wR.runE (K := ⟨D, some ⟨s.n, s.key⟩, none⟩) ⟨hD, (ws s rfl).1, trivial⟩ hr) (ws s rfl)
  · trivial

theorem comp_sound {R : Rel A B} {S : Rel B C} {X : Core.Rel A.El B.El}
    {Y : Core.Rel B.El C.El} (hR : ∀ K, K.WF → R.Reps K X) (hS : ∀ K, K.WF → S.Reps K Y) (wR : R.Wf) (wS : S.Wf) :
    ∀ K, K.WF → (GenK.comp A B C R S).Reps K (X ≫ Y) := fun K hK => by
  have eR := fun K hK => (reps_iff K R X).1 (hR K hK)
  have eS := fun K hK => (reps_iff K S Y).1 (hS K hK)
  have kD : (⟨K.dom, none, none⟩ : Known A B).WF := hK.dom
  have kR : (⟨none, K.ran, none⟩ : Known B C).WF := ⟨trivial, hK.2.1, trivial⟩
  have wr : ∀ r, R.runE ⟨K.dom, none, none⟩ = .ok r → r.WF := fun _ h => wR.runE kD h
  have ws : ∀ s, S.runE ⟨none, K.ran, none⟩ = .ok s → s.WF := fun _ h => wS.runE kR h
  cases R with
  | tab r => exact compT_sound (eR _ kD) hS wS hK wr
  | bits g w o x ra y rc => exact compT_sound (fun t h => eR _ kD t h) hS wS hK wr
  | lazy f =>
    simp only [GenK.comp, Rel.Rel.Reps]
    -- each leaf runs one operand on the side of `K` it touches, so its table agrees there
    split <;> (try split) <;> (try split) <;> first
      | exact compS_sound hR (eS _ kR) hK ws wR
      | exact compT_sound (eR _ kD) hS wS hK wr
      | exact retried_reps (compS_sound hR (eS _ kR) hK ws wR)
      | exact retried_reps (compT_sound (eR _ kD) hS wS hK wr)
      | (refine compS_sound hR (fun t ht => ?_) hK (fun t ht => ?_) wR <;> injection ht with h <;> subst h <;>
          first | exact eS _ kR _ ‹_› | exact ws _ ‹_›)
      | (refine compT_sound (fun t ht => ?_) hS wS hK (fun t ht => ?_) <;> injection ht with h <;> subst h <;>
          first | exact eR _ kD _ ‹_› | exact wr _ ‹_›)

theorem comp_wf {R : Rel A B} {S : Rel B C} (wR : R.Wf) (wS : S.Wf) :
    (GenK.comp A B C R S).Wf := by
  cases R with
  | tab r => exact compT_wf (fun _ h => wR.runE Known.wf_empty h) wS
  | bits => exact compT_wf (fun _ h => wR.runE Known.wf_empty h) wS
  | lazy f =>
    intro K hK; simp only [GenK.comp]
    have kD : (⟨K.dom, none, none⟩ : Known A B).WF := hK.dom
    have kR : (⟨none, K.ran, none⟩ : Known B C).WF := ⟨trivial, hK.2.1, trivial⟩
    have wr : ∀ r, (Rel.lazy f).runE ⟨K.dom, none, none⟩ = .ok r → r.WF := fun _ h => wR.runE kD h
    have ws : ∀ s, S.runE ⟨none, K.ran, none⟩ = .ok s → s.WF := fun _ h => wS.runE kR h
    split <;> (try split) <;> (try split) <;> first
      | exact compS_wf hK.1 wR ws
      | exact compT_wf wr wS
      | exact (compS_wf hK.1 wR ws).retried _
      | exact (compT_wf wr wS).retried _
      | exact compS_wf hK.1 wR fun _ h => by cases h; exact ws _ ‹_›
      | exact compT_wf (fun _ h => by cases h; exact wr _ ‹_›) wS

/-! ### `Rel.Wf` of the ops that build no `bits` value: each table step keeps `Tab.WF` -/

theorem lift1_wf {D : Obj} {f : Tab A B → Except String (Tab C D)} {k : Known C D → Known A B}
    (hk : ∀ K, K.WF → (k K).WF) (hf : ∀ t u, t.WF → f t = .ok u → u.WF) {R : Rel A B} (wR : R.Wf) :
    (lift1 f k R).Wf := by
  have L : ∀ {x : Except String (Tab A B)}, (∀ t, x = .ok t → t.WF) → (Rel.tab (x >>= f)).Wf := fun hx =>
    tab_wf fun u h => let ⟨t, ht, h⟩ := bind_ok h; hf t u (hx t ht) h
  cases R with
  | tab r => exact L fun _ h => wR.runE Known.wf_empty h
  | lazy g => exact fun K hK => L fun _ h => wR.runE (hk K hK) h
  | bits => exact fun K hK => L fun _ h => wR.runE (hk K hK) h

theorem lift2_wf {D E F : Obj} {f : Tab A B → Tab C D → Except String (Tab E F)} {kl : Known E F → Known A B}
    {kr : Known E F → Known C D} (hkl : ∀ K, K.WF → (kl K).WF) (hkr : ∀ K, K.WF → (kr K).WF)
    (hf : ∀ r s t, r.WF → s.WF → f r s = .ok t → t.WF) {R : Rel A B} {S : Rel C D} (wR : R.Wf) (wS : S.Wf) :
    (lift2 f kl kr R S).Wf := by
  have L : ∀ {x : Except String (Tab A B)} {y : Except String (Tab C D)}, (∀ t, x = .ok t → t.WF) →
      (∀ t, y = .ok t → t.WF) → (Rel.tab do f (← x) (← y)).Wf := fun hx hy =>
    tab_wf fun u h => let ⟨r, hr, h⟩ := bind_ok h; let ⟨s, hs, h⟩ := bind_ok h; hf r s u (hx r hr) (hy s hs) h
  cases R <;> cases S <;> first
    | exact L (fun _ h => wR.runE Known.wf_empty h) (fun _ h => wS.runE Known.wf_empty h)
    | exact fun K hK => L (fun _ h => wR.runE (hkl K hK) h) (fun _ h => wS.runE (hkr K hK) h)

theorem pairK_wf {D : Option ((n : USize) × Vals A n)} {R : Rel A B} {S : Rel A C} (wR : R.Wf) (wS : S.Wf)
    (hD : D.elim True fun c => Vals.WF c.2) {t : Tab A (.prod B C)} (h : pairK D R S = .ok t) : t.WF := by
  have L : ∀ p, pairOn D R S = .ok p → p.1.pair p.2 = .ok t → t.WF := fun _ hp ht =>
    let w := pairOn_wf wR wS hD hp; Tab.pair_wf ht w.1 w.2
  have M : ∀ p, pairOn D S R = .ok p → p.2.pair p.1 = .ok t → t.WF := fun _ hp ht =>
    let w := pairOn_wf wS wR hD hp; Tab.pair_wf ht w.2 w.1
  unfold pairK at h; split at h
  · split at h
    · exact L _ ‹_› h
    · obtain ⟨p, hp, ht⟩ := bind_ok (retryE_ok h); exact M p hp ht
  all_goals obtain ⟨p, hp, ht⟩ := bind_ok h
  · exact M p hp ht
  · exact L p hp ht

theorem pair_wf {R : Rel A B} {S : Rel A C} (wR : R.Wf) (wS : S.Wf) :
    (GenK.pair A B C R S).Wf := by
  unfold GenK.pair; split <;> first
    | exact fun K hK => tab_wf fun _ h => pairK_wf wR wS hK.1 h
    | exact lift2_wf (fun _ h => h.dom) (fun _ h => h.dom) (fun _ _ _ hr hs h => Tab.pair_wf h hr hs) wR wS

theorem diff_wf {R S : Rel A B} (wR : R.Wf) (wS : S.Wf) : (GenK.diff A B R S).Wf := by
  unfold GenK.diff; split
  · exact fun K hK => tab_wf fun t h => by
      obtain ⟨r, hr, h⟩ := bind_ok h
      obtain ⟨p, hp, h⟩ := bind_ok h
      obtain ⟨s, hs, ht⟩ := bind_ok h
      have wp := bound_wf hK (wR.runE hK hr) hp
      exact Tab.diff_wf ht wp.1 (wS.runE wp.2 hs)
  · exact lift2_wf (fun _ h => h) (fun _ h => h) (fun _ _ _ hr hs h => Tab.diff_wf h hr hs) wR wS

theorem ofVals_wf {f : {n : USize} → Vals A n → Except String (Tab A B)}
    (hf : ∀ (n : USize) (X : Vals A n) t, Vals.WF X → f X = .ok t → t.WF) : (ofVals A B f).Wf := by
  intro K hK; cases h : K.dom with
  | none => simp [ofVals, h, Rel.Rel.Wf]
  | some c =>
    have hX := hK.1; rw [h] at hX
    simp only [h, Option.elim]
    exact tab_wf fun t ht => hf _ _ t hX ht

theorem id_wf : (GenK.id A).Wf := by
  intro ⟨d, r, p⟩ hK
  have T : ∀ c : (n : USize) × Vals A n, Vals.WF c.2 → (Rel.tab (Tab.idU c.2)).Wf := fun _ hc =>
    tab_wf fun _ h => Tab.idU_wf h hc
  cases d with
  | some c => exact T c hK.1
  | none => cases r with
    | some c => exact T c hK.2.1
    | none => trivial

theorem top_wf {V : Rel B B} (wV : V.Wf) : (GenK.top A B V).Wf := by
  intro K hK; cases h : K.dom with
  | none => simp [GenK.top, h, Rel.Rel.Wf]
  | some c =>
    have hX := hK.1; rw [h] at hX
    have kW : (⟨none, K.ran, none⟩ : Known B B).WF := ⟨trivial, hK.2.1, trivial⟩
    simp only [GenK.top, h]
    refine tab_wf fun t ht => ?_
    obtain ⟨v, hv, ht⟩ := bind_ok ht
    obtain ⟨w, hw, ht⟩ := bind_ok ht
    exact Tab.top_wf ht hX (cut_wf kW (wV.runE kW hv) hw).2

/-- **`ldiv` is `X \ Y` within `TB`, `TC`** on a `Rel.Wf` divisor: a matrix `S` is divided on its bits
    (`Tab.ldivTabMat_law`) or read back and `Tab.ldivSel`, any other `S` through `Tab.ldivSel`. -/
theorem ldiv_sound {R : Rel A B} {S : Rel A C} {UB : Rel B B} {UC : Rel C C} {X : Core.Rel A.El B.El}
    {Y : Core.Rel A.El C.El} {TB : Core.Rel B.El B.El} {TC : Core.Rel C.El C.El} (hR : ∀ K, K.WF → R.Reps K X)
    (hS : ∀ K, K.WF → S.Reps K Y) (hB : ∀ K, K.WF → UB.Reps K TB) (hC : ∀ K, K.WF → UC.Reps K TC)
    (wR : R.Wf) (wS : S.Wf) (wB : UB.Wf) (wC : UC.Wf) : ∀ K, K.WF → (GenK.ldiv A B C R S UB UC).Reps K (ldivDen X Y TB TC) := fun K hK => by
  have eY : ∀ s, S.runE {} = .ok s → Y = rep s := fun s h =>
    agrees_empty ((reps_iff _ _ _).1 (hS {} Known.wf_empty) s h)
  have hF : ∀ K, K.WF → (S.force {}).Reps K Y := fun K _ => (reps_iff _ _ _).2 fun t ht => by
    rw [force_runE] at ht; rw [eY t ht]; exact fun _ _ _ _ _ => Iff.rfl
  have wF := wS.force Known.wf_empty
  have fF := force_runE S {} {}
  simp only [GenK.ldiv]
  generalize S.force {} = F at hF wF fF
  cases F
  case bits g w o x ra y rc =>
    rcases hr : R.runE {} with e | r <;> rcases hu : UB.runE {} with e | ub <;>
      rcases hv : UC.runE {} with e | uc <;> dsimp only
    iterate 7 (rw [reps_iff]; intro t ht; nomatch ht)
    have rX := agrees_empty ((reps_iff _ _ _).1 (hR {} Known.wf_empty) r hr)
    have rB := agrees_empty ((reps_iff _ _ _).1 (hB {} Known.wf_empty) ub hu)
    have rC := agrees_empty ((reps_iff _ _ _).1 (hC {} Known.wf_empty) uc hv)
    obtain ⟨hr0, -, ho, hx, hy, hra, hrc⟩ := wF.1
    have wr := wR.runE Known.wf_empty hr
    have wu := wB.runE Known.wf_empty hu
    have wv := wC.runE Known.wf_empty hv
    simp only [ldivM]
    rcases hm : Tab.ldivTabMat r ub uc g w o x ra y rc with e | (_ | ⟨kb, kc, o', ⟨N, zb⟩, rb, ⟨N', zc⟩, rc'⟩) <;>
      dsimp only <;> rw [reps_iff] <;> intro t ht
    · nomatch ht
    · obtain ⟨s, hs, ht⟩ := bind_ok ht
      rw [rX, eY s (fF.symm.trans hs), rB, rC]
      exact fun b c _ _ _ => Tab.ldivSel_holds ht wr (Tab.ofBits_wf hs wF.2.1 wF.2.2) wu wv b c
    · rcases hs : Tab.ofBits g w o x ra y rc with e | s
      · exact absurd hs (hr0 e)
      rw [Tab.ldivTabMat_law hm ht hs (fun a ha j hj => some_lt_two (ho a ha j hj)) hx hy hra hrc wr wu wv wF.2.1 wF.2.2, rX,
        eY s (fF.symm.trans hs), rB, rC]
      exact fun _ _ _ _ _ => Iff.rfl
  all_goals
    dsimp only
    refine lift2_sound (fun _ _ => Known.wf_empty) (fun _ _ => Known.wf_empty) hR hF wR wF (fun _ _ _ _ ht wr ws hr hs => ?_) K hK
    obtain ⟨ub, hub, ht⟩ := bind_ok ht
    obtain ⟨uc, huc, ht⟩ := bind_ok ht
    rw [agrees_empty hr, agrees_empty hs, agrees_empty ((reps_iff _ _ _).1 (hB {} Known.wf_empty) ub hub),
      agrees_empty ((reps_iff _ _ _).1 (hC {} Known.wf_empty) uc huc)]
    exact fun b c _ _ _ =>
      Tab.ldivSel_holds ht wr ws (wB.runE Known.wf_empty hub) (wC.runE Known.wf_empty huc) b c

/-- **`ldiv` keeps `Tab.WF`**: a matrix answer is `BitsWf` (`Tab.ldivTabMat_wf`) over `WF` sides
    (`Tab.ldivTabMat_sides_wf`); a table answer is `Tab.ldivSel`'s of `WF` operands (`Tab.ldivSel_wf`). -/
theorem ldiv_wf {R : Rel A B} {S : Rel A C} {UB : Rel B B} {UC : Rel C C} (wR : R.Wf) (wS : S.Wf) (wB : UB.Wf)
    (wC : UC.Wf) : (GenK.ldiv A B C R S UB UC).Wf := by
  have wF := wS.force Known.wf_empty
  simp only [GenK.ldiv]
  generalize S.force {} = F at wF
  cases F
  case bits g w o x ra y rc =>
    rcases hr : R.runE {} with e | r <;> rcases hu : UB.runE {} with e | ub <;> rcases hv : UC.runE {} with e | uc <;>
      dsimp only
    all_goals try trivial
    have wr := wR.runE Known.wf_empty hr
    have wu := wB.runE Known.wf_empty hu
    have wv := wC.runE Known.wf_empty hv
    simp only [ldivM]
    rcases hm : Tab.ldivTabMat r ub uc g w o x ra y rc with e | (_ | ⟨kb, kc, o', ⟨N, zb⟩, rb, ⟨N', zc⟩, rc'⟩) <;>
      dsimp only
    · trivial
    · exact tab_wf fun t ht => by
        obtain ⟨s, hs, ht⟩ := bind_ok ht
        have ws := Tab.ofBits_wf hs wF.2.1 wF.2.2
        exact Tab.ldivSel_wf (fun h => Tab.ldiv_wf h wr ws wu wv) ht wr ws wu wv
    · exact ⟨Tab.ldivTabMat_wf hm (Tab.ldivTabMat_reads wF.1 hm wr wu wv wF.2.1 wF.2.2) wF.1 wr wu wv wF.2.1 wF.2.2,
        Tab.ldivTabMat_sides_wf hm wr wu wv wF.2.2⟩
  all_goals exact lift2_wf (fun _ _ => Known.wf_empty) (fun _ _ => Known.wf_empty) (fun r s t hr hs h => by
    obtain ⟨ub, hub, h⟩ := bind_ok h
    obtain ⟨uc, huc, h⟩ := bind_ok h
    have wu := wB.runE Known.wf_empty hub
    have wv := wC.runE Known.wf_empty huc
    exact Tab.ldivSel_wf (fun h => Tab.ldiv_wf h hr hs wu wv) h hr hs wu wv) wR wF

end Rel.Lang.GenK
