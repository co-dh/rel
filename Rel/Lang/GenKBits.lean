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

/-- `colMap .lt` against a constant `N` below `2^63` is `1` exactly at the words below `N`. -/
theorem colMap_lt_const {n N : USize} {e c l : Enc} (hc : colConst n N.toUInt64 = .ok c)
    (hl : colMap .lt n e c = .ok l) (hN : N.toNat < 2 ^ 63) : ∀ i < n.toNat,
    ((raw .i64 n e)[i]?.getD 0).toNat ≤ N.toNat →
      (raw .i64 n l)[i]?.getD 0 = if ((raw .i64 n e)[i]?.getD 0).toNat < N.toNat then 1 else 0 := fun i hi hle => by
  have e1 := (colMap_raw hl).2.2.2 i hi
  rw [colConst_raw hc, Array.getElem?_replicate, if_pos hi, Option.getD_some,
    show (raw .i64 n e)[i]?.getD 0 = ((raw .i64 n e)[i]?.getD 0).toNat.toUInt64 from UInt64.toNat_inj.mp (by simp),
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
    (h : Tab.ofBits g w o x ra y rc = .ok X) (hgw : (g * w).toNat = g.toNat * w.toNat)
    (ho : ∀ a < g.toNat, ∀ j < w.toNat, ∃ v : UInt64, (raw .i64 (g * w) o)[a * w.toNat + j]? = some v ∧ v < 2)
    (u : A.El) (v : C.El) :
    X.Holds u v ↔ ∃ a < g.toNat, ∃ j < w.toNat, (raw .i64 (g * w) o)[a * w.toNat + j]?.getD 0 = 1 ∧
      (∃ i : Fin n.toNat, ((raw .i64 g ra)[a]?.getD 0).toNat = i.1 ∧ x.row i = u) ∧ ∃ i : Fin m.toNat,
      ((raw .i64 w rc)[j]?.getD 0).toNat = i.1 ∧ y.row i = v :=
  Tab.ofBits_holds h _ hgw (hgw ▸ Tab.ofBits_lt h) (fun a ha j hj => by
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
  have hS := Tab.ofBits_set hs hgw ho
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
  have hokw : ∀ i < t.n.toNat, (raw .i64 t.n ok)[i]?.getD 0 < 2 ∧ ((raw .i64 t.n ok)[i]?.getD 0 ≠ 0 ↔
      ((raw .i64 t.n ia)[i]?.getD 0).toNat < g.toNat ∧ ((raw .i64 t.n ic)[i]?.getD 0).toNat < w.toNat) :=
    fun i hi => by
      have e3 := (colMap_raw hok).2.2.2 i hi
      rw [colMap_lt_const hc1 hl1 hg63 i hi (Tab.index_le hia ⟨i, hi⟩),
        colMap_lt_const hc2 hl2 hw63 i hi (Tab.index_le hic ⟨i, hi⟩)] at e3
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
    have := bit_lt hA hC
    have hm : ((raw .i64 t.n ia)[i.1]?.getD 0).toNat * w.toNat < 2 ^ 64 := by omega
    rw [Nat.mod_eq_of_lt hm, Nat.mod_eq_of_lt (by omega)]
  have hbw : ∀ k < M.toNat, (raw .i64 M bw)[k]?.getD 0 = (raw .i64 (g * w) o)[((raw .i64 M ps)[k]?.getD 0).toNat]?.getD 0 :=
    fun k hk => (kgather_word hbw k hk).2
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

/-- **`Tab.compTabMat` is `R ≫ M`** for a matrix `M` as `compMat` and `compTabMat` build it: `0`/`1` words and the
    rows `x[ra[·]]` distinct (else `index` sends `R`'s value to one of two equal rows and drops the other's bits).
    `g · w` not wrapping is `kbitrows`' own law (`raw_kbitrows`). -/
theorem Tab.compTabMat_law {n m M : USize} {r : Tab A B} {g w ka : USize} {o o' ra ra' rc : Enc}
    {x : Vals B n} {key : Vals A M} {y : Vals C m} {t : Tab A C} {s : Tab B C}
    (h : Tab.compTabMat r g w o x ra = .ok (ka, o', ⟨M, key⟩, ra')) (ht : Tab.ofBits ka w o' key ra' y rc = .ok t)
    (hs : Tab.ofBits g w o x ra y rc = .ok s)
    (ho : ∀ a < g.toNat, ∀ j < w.toNat, ∃ v : UInt64, (raw .i64 (g * w) o)[a * w.toNat + j]? = some v ∧ v < 2)
    (hx : ∀ a a' : Fin g.toNat, ∀ i i' : Fin n.toNat, ((raw .i64 g ra)[a.1]?.getD 0).toNat = i.1 →
      ((raw .i64 g ra)[a'.1]?.getD 0).toNat = i'.1 → x.row i = x.row i' → a = a') :
    rep t = rep r ≫ rep s := by
  simp only [Tab.compTabMat, bind] at h
  rw [Except.bind_eq_ok'] at h; obtain ⟨X', hX', h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨ix, hix, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨c1, hc1, h⟩ := h
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
  have hT := Tab.ofBits_set ht hgw' fun a ha j hj => by
    obtain ⟨v, -, hv, hv2, -⟩ := hbit a ha j hj; exact ⟨v, hv, hv2⟩
  have hS := Tab.ofBits_set hs hgw ho
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
    colMap_lt_const hc1 hl1 hg63 q hq (Tab.index_le hix ⟨q, hq⟩)
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
  obtain ⟨π, hπ, hsurj, hgrp⟩ := csr_spec hcsr gr
    (fun q hq => ⟨UInt64.toNat_inj.mp (by simp [gr]), hcw q hq⟩) (by omega)
  have hidx : ∀ k < M.toNat, (raw .i64 M idx)[k]?.getD 0 =
      (raw .i64 r.n ix)[((raw .i64 M sel)[π k]?.getD 0).toNat]?.getD 0 := fun k hk =>
    ((hπ k hk).2).trans (kgather_word hgi (π k) (hπ k hk).1).2
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
    rcases Tab.index_spec hix q with ⟨a, ea, ra⟩ | ⟨ea, -⟩
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
      rcases Tab.index_spec hix q with ⟨a2, ea, ra2⟩ | ⟨-, hn⟩
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

/-- **A bit matrix as its producers (`compMat`, `compTabMat`) build it**: it reads back as rows (`Tab.ofBits`), `g · w`
    does not wrap, each of its `g · w` words is `0` or `1`, and each side's rows `x[ra[·]]`, `y[rc[·]]` are distinct:
    the hypotheses of `Tab.keepBits_law` and `Tab.compTabMat_law`. -/
def BitsWf {n m : USize} (g w : USize) (o : Enc) (x : Vals A n) (ra : Enc) (y : Vals C m) (rc : Enc) : Prop :=
  (∀ e, Tab.ofBits g w o x ra y rc ≠ .error e) ∧ (g * w).toNat = g.toNat * w.toNat ∧
  (∀ a < g.toNat, ∀ j < w.toNat, ((raw .i64 (g * w) o)[a * w.toNat + j]?).any (· < 2) = true) ∧
  (∀ a a' : Fin g.toNat, ∀ i i' : Fin n.toNat, ((raw .i64 g ra)[a.1]?.getD 0).toNat = i.1 →
    ((raw .i64 g ra)[a'.1]?.getD 0).toNat = i'.1 → x.row i = x.row i' → a = a') ∧
  ∀ c c' : Fin w.toNat, ∀ i i' : Fin m.toNat, ((raw .i64 w rc)[c.1]?.getD 0).toNat = i.1 →
    ((raw .i64 w rc)[c'.1]?.getD 0).toNat = i'.1 → y.row i = y.row i' → c = c'

/-- Every `bits` value `r` yields, run on any context (`force`), is `BitsWf`. -/
def Rel.Wf {A B : Obj} : Rel A B → Prop
  | .tab _ => True
  | .lazy f => ∀ K, (f K).Wf
  | .bits g w o x ra y rc => BitsWf g w o x ra y rc

theorem Rel.Wf.force {r : Rel A B} (h : r.Wf) (K : Known A B) : (r.force K).Wf := by
  induction r with
  | lazy f ih => simp only [Rel.force]; exact ih K (h K)
  | tab => exact h
  | bits => exact h

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
    refine ⟨hr, hgw, fun a ha j hj => ?_, Vals.code_rep_inj hca, Vals.code_rep_inj hcc⟩
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
  refine ⟨hr, hgw, fun a ha j hj => ?_, Vals.code_rep_inj hcode, hw.2.2.2.2⟩
  obtain ⟨v, -, hv, hv2, -⟩ := hbit a ha j hj
  rw [hv]; exact decide_eq_true hv2

/-- **`kbitrows` over a `csr` grouping**: group `G`'s bit `j` is the `∧` (`all`) or the `∨` of bit `j` of the matrix
    rows `x[q]` of the input rows `q` with `gr q = G`, stated over the input rows rather than `csr`'s order. -/
theorem csr_kbitrows {all : Bool} {n g na w : USize} {gid x ends idx m o : Enc}
    (hc : csr n g gid x = .ok (ends, idx)) (hk : kbitrows all w na n g ends idx m = .ok o) (gr : Nat → Nat)
    (hg : ∀ q < n.toNat, (raw .i64 n gid)[q]?.getD 0 = (gr q).toUInt64 ∧ gr q < g.toNat) (hg63 : g.toNat ≤ 2 ^ 63) :
    (na * w).toNat = na.toNat * w.toNat ∧ (g * w).toNat = g.toNat * w.toNat ∧
    (∀ q < n.toNat, ((raw .i64 n x)[q]?.getD 0).toNat < na.toNat) ∧
    ∀ G < g.toNat, ∀ j < w.toNat, ∃ v : UInt64, (raw .i64 (g * w) o)[G * w.toNat + j]? = some v ∧ v < 2 ∧
      (v = 1 ↔ if all then ∀ q < n.toNat, gr q = G →
          (raw .i64 (na * w) m)[((raw .i64 n x)[q]?.getD 0).toNat * w.toNat + j]?.getD 0 % 2 = 1
        else ∃ q < n.toNat, gr q = G ∧
          (raw .i64 (na * w) m)[((raw .i64 n x)[q]?.getD 0).toNat * w.toNat + j]?.getD 0 % 2 = 1) := by
  obtain ⟨π, hπ, hsurj, hseg⟩ := csr_spec hc gr hg hg63
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
    (h : Vals.code2 x y = .ok (k, bx, bY, ⟨N, z, rep⟩)) :
    ∀ a a' : Fin k.toNat, ∀ i i' : Fin N.toNat, ((raw .i64 k rep)[a.1]?.getD 0).toNat = i.1 →
      ((raw .i64 k rep)[a'.1]?.getD 0).toNat = i'.1 → z.row i = z.row i' → a = a' := fun a a' i i' hi hi' e => by
  obtain ⟨cx, cy, -, -, -, -, -, -, hrep⟩ := Vals.code2_spec h
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
      ((raw .i64 w rc)[j'.1]?.getD 0).toNat = i'.1 → y.row i = y.row i' → j = j') :
    (kb * kc).toNat = kb.toNat * kc.toNat ∧ kb.toNat * kc.toNat < 2 ^ 63 ∧ ∃ PP : Nat → Nat → Prop,
      (∀ G < kb.toNat, ∀ jj < kc.toNat, ∃ v : UInt64,
        (raw .i64 (kb * kc) o')[G * kc.toNat + jj]? = some v ∧ v < 2 ∧ (v = 1 ↔ PP G jj)) ∧
      (∀ b c, (∃ G < kb.toNat, ∃ jj < kc.toNat, PP G jj ∧
        (∃ i : Fin N.toNat, ((raw .i64 kb rb)[G]?.getD 0).toNat = i.1 ∧ zb.row i = b) ∧
        ∃ i : Fin N'.toNat, ((raw .i64 kc rc')[jj]?.getD 0).toNat = i.1 ∧ zc.row i = c) ↔
        Lang.ldivDen r.Holds s.Holds ub.Holds uc.Holds b c) ∧
      (∀ a a' : Fin kb.toNat, ∀ i i' : Fin N.toNat, ((raw .i64 kb rb)[a.1]?.getD 0).toNat = i.1 →
        ((raw .i64 kb rb)[a'.1]?.getD 0).toNat = i'.1 → zb.row i = zb.row i' → a = a') ∧
      ∀ c c' : Fin kc.toNat, ∀ i i' : Fin N'.toNat, ((raw .i64 kc rc')[c.1]?.getD 0).toNat = i.1 →
        ((raw .i64 kc rc')[c'.1]?.getD 0).toNat = i'.1 → zc.row i = zc.row i' → c = c' := by
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
  rw [Except.bind_eq_ok'] at h; obtain ⟨cg, hcg, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨on, hon, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨⟨P, sel⟩, hP, h⟩ := h; try dsimp only at h
  rw [Except.bind_eq_ok'] at h; obtain ⟨gb, hgb, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨gi, hgi, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨⟨ends, idx⟩, hcsr, h⟩ := h; try dsimp only at h
  rw [Except.bind_eq_ok'] at h; obtain ⟨o1, hk, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨one, hone, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨cnt, hcnt, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨z0, hz0, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨vac, hvac, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨cnt2, hcnt2, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨eq2, heq2, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨keep, hkeep, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨io, hio, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨cw, hcw, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨rr, hrr, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨ckc, hckc, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨rm, hrm, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨cw2, hcw2, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨im, him, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨gm, hgm, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨p1, hp1, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨gk, hgk, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨v1, hv1, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨s1, hs1, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨⟨E, eb⟩, hE, h⟩ := h; try dsimp only at h
  rw [Except.bind_eq_ok'] at h; obtain ⟨jo, hjo, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨cu1, hcu1, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨jd, hjd, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨ge, hge, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨cu2, hcu2, h⟩ := h
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
  have cst : ∀ {n : USize} {v : UInt64} {e : Enc}, colConst n v = .ok e → ∀ k < n.toNat,
      (raw .i64 n e)[k]?.getD 0 = v := fun hc k hk => by
    rw [colConst_raw hc, Array.getElem?_replicate, if_pos hk, Option.getD_some]
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
  obtain ⟨bx, bu, -, hbx, hbu, -, -, -, hrb⟩ := Vals.code2_spec hb2
  obtain ⟨cm, cu, -, hcm, hcu, hcmi, -, -, hrc⟩ := Vals.code2_spec hc2
  obtain ⟨ixN, hixN⟩ : ∃ f : Nat → Nat, ∀ i, ((raw .i64 r.n ix)[i]?.getD 0).toNat = f i := ⟨_, fun _ => rfl⟩
  obtain ⟨selN, hselN⟩ : ∃ f : Nat → Nat, ∀ q, ((raw .i64 P sel)[q]?.getD 0).toNat = f q := ⟨_, fun _ => rfl⟩
  let Vac := fun G => ∀ i < r.n.toNat, bx i ≠ G
  let Kp := fun G => ∀ i < r.n.toNat, bx i = G → ixN i < g.toNat
  let Al := fun G j => ∀ i < r.n.toNat, bx i = G → ixN i < g.toNat →
    (raw .i64 (g * w) o)[ixN i * w.toNat + j]?.getD 0 = 1
  -- `o1`: each value's `∧` over its rows whose key is a row of `M`
  obtain ⟨hgw, -, -, hbit⟩ := csr_kbitrows hcsr hk (fun q => bx (selN q)) (fun q hq => by
      obtain ⟨h1, h2⟩ := kgather_word hgb q hq; rw [h2, hselN]; rw [hselN] at h1; exact hbx _ h1) (by omega)
  have hS := Tab.ofBits_set hs hgw ho
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
    rcases Tab.index_spec hix i with ⟨a, ea, ra⟩ | ⟨ea, hn⟩
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
  have hcntw := scatter_add_count hcnt bx (fun _ => true) (fun q hq => (hbx q hq).1) (fun q hq => by
    have := (hbx q hq).2; have := kb.toNat_lt_size; omega) (fun q hq => by rw [cst hone q hq]; rfl)
  have hvacw : ∀ G < kb.toNat, (raw .i64 kb vac)[G]?.getD 0 = if Vac G then 1 else 0 := fun G hG => by
    have e := (colMap_raw hvac).2.2.2 G hG
    rw [cst hz0 G hG, hev, hcntw G hG, Except.ok.injEq] at e
    rw [← e]
    refine ifc ?_
    rw [show (0 : UInt64) = (0 : Nat).toUInt64 from rfl, u64eq _ _ (hcl _) (by omega)]
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
        have e := (colMap_raw hjd).2.2.2 k hk'
        rw [Tab.colIota_raw hjo k hk', cst hcu1 k hk', eU, eval_div_nat hk63 (by omega) hU0, Except.ok.injEq] at e
        exact e.symm
      have em : (raw .i64 (E * uc.n) jm)[k]?.getD 0 = (k % uc.n.toNat).toUInt64 := by
        have e := (colMap_raw hjm).2.2.2 k hk'
        rw [Tab.colIota_raw hjo k hk', cst hcu2 k hk', eU, eval_mod_nat hk63 (by omega) hU0, Except.ok.injEq] at e
        exact e.symm
      have hkm := Nat.mod_lt k hU0
      refine ⟨(Nat.div_lt_iff_lt_mul hU0).2 hk, hkm, ?_, ?_⟩
      · rw [(kgather_word hge k hk').2, ed, toNat_toUInt64 (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (by omega))]
      · rw [(kgather_word hgu k hk').2, em, toNat_toUInt64 (by omega), (hcu _ hkm).1]
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
    obtain ⟨hsz, -, hsw⟩ := kscatter_words hs1
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
      have := colMap_lt_const hcg hon hg63 i hi (Tab.index_le hix ⟨i, hi⟩); rwa [hixN] at this
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
        rw [(kgather_word hgi q hq).2, hselN, hqi, hixN] at this
        obtain ⟨v', hv', hv2'⟩ := ho _ hlt j hj
        rw [hv', Option.getD_some] at this ⊢; exact (odd_bit hv2').1 this
      · intro H q hq hgq
        obtain ⟨hi, hlt⟩ := (hsel _).1 ⟨q, hq, rfl⟩
        rw [(kgather_word hgi q hq).2, hselN, hixN, H _ hi hgq hlt]; decide
    have hcnt2w := scatter_add_count hcnt2 bx (fun q => decide (ixN q < g.toNat)) (fun q hq => (hbx q hq).1)
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
        have e := (colMap_raw hrr).2.2.2 k hk
        rw [Tab.colIota_raw hio k hk, cst hcw k hk, ew, eval_div_nat hk63 (by omega) hw1, Except.ok.injEq] at e
        exact e.symm
      have emd : (raw .i64 (kb * w) im)[k]?.getD 0 = (k % w.toNat).toUInt64 := by
        have e := (colMap_raw him).2.2.2 k hk
        rw [Tab.colIota_raw hio k hk, cst hcw2 k hk, ew, eval_mod_nat hk63 (by omega) hw1, Except.ok.injEq] at e
        exact e.symm
      have egm := (kgather_word hgm k hk).2
      rw [emd, toNat_toUInt64 (by omega), (hcm _ hkm).1] at egm
      have erm := (colMap_raw hrm).2.2.2 k hk
      rw [erd, cst hckc k hk] at erm
      have ep := (colMap_raw hp1).2.2.2 k hk
      simp only [Op.eval, Except.ok.injEq] at erm ep
      have hb := bit_lt hkw (hcm _ hkm).2
      refine ⟨?_, hkw, hkm, ?_⟩
      · rw [← ep, ← erm, egm, UInt64.toNat_add, UInt64.toNat_mul, toNat_toUInt64 (by omega), USize.toNat_toUInt64,
          toNat_toUInt64 (by omega), Nat.mod_eq_of_lt (show k / w.toNat * kc.toNat < 2 ^ 64 by omega)]
        exact Nat.mod_eq_of_lt (by omega : k / w.toNat * kc.toNat + cm (k % w.toNat) < 2 ^ 64)
      · have eg := (kgather_word hgk k hk).2; rw [erd, toNat_toUInt64 (by omega)] at eg; exact eg
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
  refine ⟨hkbc, hb63, PP, hout', fun b c => ?_, Vals.code2_rep_inj hb2, Vals.code2_rep_inj hc2⟩
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
      ((raw .i64 w rc)[j'.1]?.getD 0).toNat = i'.1 → y.row i = y.row i' → j = j') :
    rep t = Lang.ldivDen (rep r) (rep s) (rep ub) (rep uc) := by
  obtain ⟨hkbc, hb63, PP, hw, hden, -, -⟩ := Tab.ldivTabMat_spec h hs ho hx hy
  apply Core.Rel.ext; intro b c
  exact (Tab.ofBits_holds ht PP hkbc hb63 hw b c).trans (hden b c)

/-- **`ldivTabMat` keeps a matrix `BitsWf`** where its own reads back: its words, `kb · kc` and both sides' distinct
    rows from `Tab.ldivTabMat_spec`. -/
theorem Tab.ldivTabMat_wf {n m N N' : USize} {r : Tab A B} {ub : Tab B B} {uc : Tab C C} {g w kb kc : USize}
    {o o' ra rb rc rc' : Enc} {x : Vals A n} {y : Vals C m} {zb : Vals B N} {zc : Vals C N'}
    (h : Tab.ldivTabMat r ub uc g w o x ra y rc = .ok (some (kb, kc, o', ⟨N, zb⟩, rb, ⟨N', zc⟩, rc')))
    (hr : ∀ e, Tab.ofBits kb kc o' zb rb zc rc' ≠ .error e) (hw : BitsWf g w o x ra y rc) :
    BitsWf kb kc o' zb rb zc rc' := by
  obtain ⟨hr0, -, ho, hx, hy⟩ := hw
  rcases hs : Tab.ofBits g w o x ra y rc with e | s
  · exact absurd hs (hr0 e)
  obtain ⟨hkbc, -, PP, hw', -, hxb, hyc⟩ :=
    Tab.ldivTabMat_spec h hs (fun a ha j hj => some_lt_two (ho a ha j hj)) hx hy
  refine ⟨hr, hkbc, fun a ha j hj => ?_, hxb, hyc⟩
  obtain ⟨v, hv, hv2, -⟩ := hw' a ha j hj
  rw [hv]; exact decide_eq_true hv2

end Rel

/-! ### `comp` and `meet`: the two ops that read a bit matrix, sound on a `Rel.Wf` argument -/

namespace Rel.Lang.GenK

open Rel Rel.Rep Rel.Kernel Rel.Verify Gen
open scoped Rel.Core.Rel
open Rel.Core.Rel hiding id comp recip inter union zero le inl inr junc

variable {A B C : Obj}

/-- `Tab.ofBits` reads back every matrix `compSelM` builds, every one `compTabMat` builds from a `BitsWf` matrix
    within `Tab.bitsMax`, and every one `ldivTabMat` builds from a `BitsWf` matrix. Not proved: it needs each kernel
    `ofBits` calls to succeed on in-range indices. -/
def ReadsBack : Prop :=
  (∀ {A B C : Obj} (r : Tab A B) (s : Tab B C) (g w : USize) (o ra rc : Enc) (e : String),
    Tab.compSelM Tab.bitsMax r s = .ok (.inr (g, w, o, ra, rc)) → Tab.ofBits g w o r.key ra s.val rc ≠ .error e) ∧
  (∀ {A B C : Obj} {n m M : USize} (r : Tab A B) (g w ka : USize) (o o' ra ra' rc : Enc) (x : Vals B n)
    (key : Vals A M) (y : Vals C m) (e : String), BitsWf g w o x ra y rc →
    Tab.compTabMat r g w o x ra = .ok (ka, o', ⟨M, key⟩, ra') → ka.toNat * w.toNat ≤ Tab.bitsMax →
    Tab.ofBits ka w o' key ra' y rc ≠ .error e) ∧
  ∀ {A B C : Obj} {n m N N' : USize} (r : Tab A B) (ub : Tab B B) (uc : Tab C C) (g w kb kc : USize)
    (o o' ra rb rc rc' : Enc) (x : Vals A n) (y : Vals C m) (zb : Vals B N) (zc : Vals C N') (e : String),
    BitsWf g w o x ra y rc →
    Tab.ldivTabMat r ub uc g w o x ra y rc = .ok (some (kb, kc, o', ⟨N, zb⟩, rb, ⟨N', zc⟩, rc')) →
    Tab.ofBits kb kc o' zb rb zc rc' ≠ .error e

theorem meet_runE {d e : Bool} (R S : Rel A B) (K : Known A B) :
    (GenK.meet A B d e R S).runE K = (meetV (R.force K) (S.force K)).runE K := by
  cases R <;> cases S <;> rfl

theorem inter_case {R S : Rel A B} {K : Known A B} {X Y : Core.Rel A.El B.El} {t : Tab A B}
    (h : (do Tab.inter (← R.runE {}) (← S.runE {})) = .ok t) (eR : ∀ r, R.runE {} = .ok r → Agrees K (rep r) X)
    (eS : ∀ s, S.runE {} = .ok s → Agrees K (rep s) Y) : Agrees K (rep t) (X ∩ Y) := by
  obtain ⟨r, hr, h⟩ := bind_ok h
  obtain ⟨s, hs, ht⟩ := bind_ok h
  exact fun x y hx hy => (Tab.inter_holds ht x y).trans (and_congr (eR r hr x y hx hy) (eS s hs x y hx hy))

theorem keep_case {K : Known A B} {P Q : Core.Rel A.El B.El} {n m : USize} {T : Except String (Tab A B)}
    {g w : USize} {o ra rc : Enc} {x : Vals A n} {y : Vals B m} {t : Tab A B} (hw : BitsWf g w o x ra y rc)
    (h : (T >>= (Tab.keepBits · g w o x ra y rc)) = .ok t) (eT : ∀ u, T = .ok u → Agrees K (rep u) P)
    (eM : ∀ s, Tab.ofBits g w o x ra y rc = .ok s → Agrees K (rep s) Q) : Agrees K (rep t) (P ∩ Q) := by
  obtain ⟨u, hu, h⟩ := bind_ok h
  obtain ⟨hr, hgw, ho, hx, hy⟩ := hw
  rcases hs : Tab.ofBits g w o x ra y rc with e | s
  · exact absurd hs (hr e)
  rw [Tab.keepBits_law h hs hgw (fun a ha j hj => some_lt_two (ho a ha j hj)) hx hy]
  exact fun a c ha hc => and_congr (eT u hu a c ha hc) (eM s hs a c ha hc)

theorem meet_sound {d e : Bool} {R S : Rel A B} {X Y : Core.Rel A.El B.El} (hR : ∀ K, R.Reps K X)
    (hS : ∀ K, S.Reps K Y) (wR : R.Wf) (wS : S.Wf) : ∀ K, (GenK.meet A B d e R S).Reps K (X ∩ Y) := fun K => by
  have eR := (reps_iff _ _ _).1 (hR K); have eS := (reps_iff _ _ _).1 (hS K)
  rw [reps_iff, meet_runE]
  have fR := force_runE R K; have fS := force_runE S K
  have wR' := wR.force K; have wS' := wS.force K
  generalize R.force K = R' at fR wR'; generalize S.force K = S' at fS wS'
  have eR' : ∀ K' r, R'.runE K' = .ok r → Agrees K (rep r) X := fun K' r h => eR r ((fR K').symm.trans h)
  have eS' : ∀ K' s, S'.runE K' = .ok s → Agrees K (rep s) Y := fun K' s h => eS s ((fS K').symm.trans h)
  intro t h
  cases R' <;> cases S' <;> first
    | exact inter_case h (eR' {}) (eS' {})
    | exact keep_case wS' h (eR' K) (eS' K)
    | exact fun x y hx hy => (keep_case wR' h (eS' K) (eR' K) x y hx hy).trans and_comm

theorem meetV_wf (R S : Rel A B) : (meetV R S).Wf := by unfold meetV; split <;> trivial

theorem meet_wf {d e : Bool} (R S : Rel A B) : (GenK.meet A B d e R S).Wf := by
  unfold GenK.meet; split <;> first | exact fun _ => meetV_wf _ _ | exact meetV_wf _ _

theorem compR_runE (r : Tab A B) (s : Tab B C) (K : Known A C) :
    (compR r s).runE K = Tab.compSel Tab.bitsMax r s := by
  unfold compR Tab.compSel
  rcases Tab.compSelM Tab.bitsMax r s with e | t | ⟨g, w, o, ra, rc⟩ <;> rfl

theorem compR_sound {r : Tab A B} {s : Tab B C} {K : Known A C} {Z : Core.Rel A.El C.El}
    (H : Agrees K (rep r ≫ rep s) Z) : (compR r s).Reps K Z := by
  rw [reps_iff, compR_runE]; intro t ht x z hx hz
  exact (Tab.compSel_holds ht x z).trans (H x z hx hz)

theorem compR_wf (hb : ReadsBack) (r : Tab A B) (s : Tab B C) : (compR r s).Wf := by
  unfold compR; split
  next g w o ra rc h => exact Tab.compSelM_wf h fun e => hb.1 r s g w o ra rc e h
  all_goals trivial

theorem compV_sound {r : Tab A B} {S : Rel B C} {K : Known A C} {Z : Core.Rel A.El C.El} (wS : S.Wf)
    (H : ∀ s, S.runE {} = .ok s → Agrees K (rep r ≫ rep s) Z) : (compV r S).Reps K Z := by
  cases S with
  | bits g w o x ra y rc =>
    obtain ⟨hr, -, ho, hx, -⟩ := (wS : BitsWf g w o x ra y rc)
    rcases hc : Tab.compTabMat r g w o x ra with e | ⟨ka, o', ⟨M, key⟩, ra'⟩
    · simp only [compV, hc]; rw [reps_iff]; intro t ht; nomatch ht
    · simp only [compV, hc]
      rcases hs : Tab.ofBits g w o x ra y rc with e | s
      · exact absurd hs (hr e)
      split
      · rw [reps_iff]; intro t ht
        rw [Tab.compTabMat_law hc ht hs (fun a ha j hj => some_lt_two (ho a ha j hj)) hx]; exact H s hs
      · exact compR_sound (H s hs)
  | tab t0 =>
    cases t0 with
    | error e => rw [reps_iff]; intro t ht; nomatch ht
    | ok s => exact compR_sound (H s rfl)
  | lazy f =>
    show (match (Rel.lazy f).runE {} with | .ok s => compR r s | .error e => .tab (.error e)).Reps K Z
    rcases hs : (Rel.lazy f).runE {} with e | s
    · rw [reps_iff]; intro t ht; nomatch ht
    · exact compR_sound (H s hs)

theorem compV_wf (hb : ReadsBack) (r : Tab A B) {S : Rel B C} (wS : S.Wf) : (compV r S).Wf := by
  cases S with
  | bits g w o x ra y rc =>
    rcases hc : Tab.compTabMat r g w o x ra with e | ⟨ka, o', ⟨M, key⟩, ra'⟩
    · simp only [compV, hc]; trivial
    · simp only [compV, hc]
      split
      · next hle => exact Tab.compTabMat_wf hc (fun e => hb.2.1 r g w ka o o' ra ra' rc x key y e wS hc hle) wS
      · split
        · exact compR_wf hb r _
        · trivial
  | tab t0 => cases t0 with
    | error e => trivial
    | ok s => exact compR_wf hb r s
  | lazy f =>
    show (match (Rel.lazy f).runE {} with | .ok s => compR r s | .error e => .tab (.error e)).Wf
    rcases (Rel.lazy f).runE {} with e | s
    · trivial
    · exact compR_wf hb r s

theorem compT_sound {r' : Except String (Tab A B)} {S : Rel B C} {K : Known A C}
    {X : Core.Rel A.El B.El} {Y : Core.Rel B.El C.El}
    (hr : ∀ r, r' = .ok r → Agrees ⟨K.dom, none⟩ (rep r) X) (hS : ∀ K, S.Reps K Y) (wS : S.Wf) :
    (compT r' S).Reps K (X ≫ Y) := by
  rcases r' with e | r
  · rw [reps_iff]; intro t ht; nomatch ht
  have er := hr r rfl
  cases S with
  | lazy g =>
    simp only [compT]
    split
    · next hn =>
      rw [reps_iff]; intro t ht x z hx _
      refine (Tab.zero_holds ht x z).trans ⟨False.elim, fun ⟨b, h, _⟩ => ?_⟩
      obtain ⟨i, _, _⟩ := (er x b hx rfl).2 h
      have := i.2; simp [beq_iff_eq.1 hn] at this
    · simp only [Rel.Rel.Reps]
      rcases hd : Tab.ran r with e | d
      · rw [reps_iff]; intro t ht; nomatch ht
      refine compV_sound (wS.force _) fun s hs a c ha hc => exists_congr fun b => ?_
      rw [force_runE] at hs
      have es := (reps_iff _ _ _).1 (hS _) s hs
      have inRan : rep r a b → (⟨some ⟨d.n, d.key⟩, K.ran⟩ : Known B C).den.1 b b := fun h =>
        (side_some rfl b).2 ((keyRowRep d b).2 ⟨b, (Tab.ran_holds hd b b).2 ⟨rfl, a, h⟩⟩)
      have e1 := er a b ha rfl
      exact ⟨fun ⟨h1, h2⟩ => ⟨e1.1 h1, (es b c (inRan h1) hc).1 h2⟩,
        fun ⟨h1, h2⟩ => ⟨e1.2 h1, (es b c (inRan (e1.2 h1)) hc).2 h2⟩⟩
  | tab t0 =>
    exact compV_sound wS fun (s : Tab B C) hs a c ha _ => exists_congr fun b =>
      and_congr (er a b ha rfl) ((reps_iff _ _ _).1 (hS {}) s hs b c rfl rfl)
  | bits g w o x ra y rc =>
    exact compV_sound wS fun (s : Tab B C) hs a c ha _ => exists_congr fun b =>
      and_congr (er a b ha rfl) ((reps_iff _ _ _).1 (hS {}) s hs b c rfl rfl)

theorem compT_wf (hb : ReadsBack) (r' : Except String (Tab A B)) {S : Rel B C} (wS : S.Wf) : (compT r' S).Wf := by
  rcases r' with e | r
  · trivial
  cases S with
  | lazy g =>
    simp only [compT]
    split
    · trivial
    · intro K; dsimp only; split
      · exact compV_wf hb r (wS.force _)
      · trivial
  | tab _ => exact compV_wf hb r wS
  | bits => exact compV_wf hb r wS

theorem compS_sound {R : Rel A B} {s' : Except String (Tab B C)}
    {L : (n : USize) × Vals C n} {X : Core.Rel A.El B.El} {Y : Core.Rel B.El C.El} (hR : ∀ K, R.Reps K X)
    (hs : ∀ s, s' = .ok s → Agrees ⟨none, some L⟩ (rep s) Y) : (compS R s').Reps ⟨none, some L⟩ (X ≫ Y) := by
  rcases s' with e | s
  · rw [reps_iff]; intro t ht; nomatch ht
  have es := hs s rfl
  simp only [compS]
  rcases hr : R.runE ⟨none, some ⟨s.n, s.key⟩⟩ with e | r
  · rw [reps_iff]; intro t ht; nomatch ht
  have er := (reps_iff _ R X).1 (hR _) r hr
  refine compR_sound fun a c _ hc => exists_congr fun b => ?_
  have key : ∀ {b}, rep s b c → (⟨none, some ⟨s.n, s.key⟩⟩ : Known A B).den.2 b b := fun h =>
    (side_some rfl _).2 ((keyRowRep s _).2 ⟨c, h⟩)
  exact ⟨fun ⟨h1, h2⟩ => ⟨(er a b rfl (key h2)).1 h1, (es b c rfl hc).1 h2⟩,
    fun ⟨h1, h2⟩ => have h2' := (es b c rfl hc).2 h2; ⟨(er a b rfl (key h2')).2 h1, h2'⟩⟩

theorem compS_wf (hb : ReadsBack) (R : Rel A B) (s' : Except String (Tab B C)) : (compS R s').Wf := by
  rcases s' with e | s
  · trivial
  simp only [compS]; split
  · exact compR_wf hb _ _
  · trivial

theorem comp_sound {e : Bool} {R : Rel A B} {S : Rel B C} {X : Core.Rel A.El B.El}
    {Y : Core.Rel B.El C.El} (hR : ∀ K, R.Reps K X) (hS : ∀ K, S.Reps K Y) (wS : S.Wf) :
    ∀ K, (GenK.comp A B C e R S).Reps K (X ≫ Y) := fun K => by
  have eR := fun K => (reps_iff K R X).1 (hR K)
  cases R with
  | tab r => exact compT_sound (eR _) hS wS
  | bits g w o x ra y rc => exact compT_sound (fun t h => eR ⟨K.dom, none⟩ t h) hS wS
  | lazy f =>
    simp only [GenK.comp, Rel.Rel.Reps]
    split
    · split
      · exact compT_sound (eR _) hS wS
      · exact compS_sound (fun K => hR K) ((reps_iff _ _ _).1 (hS _))
    · exact compT_sound (eR _) hS wS

theorem comp_wf (hb : ReadsBack) {e : Bool} (R : Rel A B) {S : Rel B C} (wS : S.Wf) :
    (GenK.comp A B C e R S).Wf := by
  cases R with
  | tab r => exact compT_wf hb r wS
  | bits => exact compT_wf hb _ wS
  | lazy f =>
    intro K; simp only [GenK.comp]
    split
    · split
      · exact compT_wf hb _ wS
      · exact compS_wf hb _ _
    · exact compT_wf hb _ wS

/-! ### `Rel.Wf` of the ops that build no `bits` value -/

theorem lift1_wf {D : Obj} {f : Tab A B → Except String (Tab C D)} {k : Known C D → Known A B} (R : Rel A B) :
    (lift1 f k R).Wf := by cases R <;> first | trivial | exact fun _ => trivial

theorem lift2_wf {D E F : Obj} {f : Tab A B → Tab C D → Except String (Tab E F)} {kl : Known E F → Known A B}
    {kr : Known E F → Known C D} (R : Rel A B) (S : Rel C D) : (lift2 f kl kr R S).Wf := by
  cases R <;> cases S <;> first | trivial | exact fun _ => trivial

theorem ofVals_wf {f : {n : USize} → Vals A n → Except String (Tab A B)} : (ofVals A B f).Wf := by
  intro K; cases h : K.dom <;> simp [ofVals, h, Rel.Rel.Wf]

theorem top_wf {V : Rel B B} : (GenK.top A B V).Wf := by
  intro K; cases h : K.dom <;> simp [GenK.top, h, Rel.Rel.Wf]

/-- **`ldiv` is `X \ Y` within `TB`, `TC`** on a `Rel.Wf` divisor: a matrix `S` is divided on its bits
    (`Tab.ldivTabMat_law`) or read back and `Tab.ldivSel`, any other `S` through `Tab.ldivSel`. -/
theorem ldiv_sound {R : Rel A B} {S : Rel A C} {UB : Rel B B} {UC : Rel C C} {X : Core.Rel A.El B.El}
    {Y : Core.Rel A.El C.El} {TB : Core.Rel B.El B.El} {TC : Core.Rel C.El C.El} (hR : ∀ K, R.Reps K X)
    (hS : ∀ K, S.Reps K Y) (hB : ∀ K, UB.Reps K TB) (hC : ∀ K, UC.Reps K TC) (wS : S.Wf) :
    ∀ K, (GenK.ldiv A B C R S UB UC).Reps K (ldivDen X Y TB TC) := fun K => by
  have eY : ∀ s, S.runE {} = .ok s → Y = rep s := fun s h => agrees_empty ((reps_iff _ _ _).1 (hS {}) s h)
  have hF : ∀ K, (S.force {}).Reps K Y := fun K => (reps_iff _ _ _).2 fun t ht => by
    rw [force_runE] at ht; rw [eY t ht]; exact fun _ _ _ _ => Iff.rfl
  have wF := wS.force {}
  have fF := force_runE S {} {}
  simp only [GenK.ldiv]
  generalize S.force {} = F at hF wF fF
  cases F
  case bits g w o x ra y rc =>
    rcases hr : R.runE {} with e | r <;> rcases hu : UB.runE {} with e | ub <;>
      rcases hv : UC.runE {} with e | uc <;> dsimp only
    iterate 7 (rw [reps_iff]; intro t ht; nomatch ht)
    have rX := agrees_empty ((reps_iff _ _ _).1 (hR {}) r hr)
    have rB := agrees_empty ((reps_iff _ _ _).1 (hB {}) ub hu)
    have rC := agrees_empty ((reps_iff _ _ _).1 (hC {}) uc hv)
    obtain ⟨hr0, -, ho, hx, hy⟩ := (wF : BitsWf g w o x ra y rc)
    simp only [ldivM]
    rcases hm : Tab.ldivTabMat r ub uc g w o x ra y rc with e | (_ | ⟨kb, kc, o', ⟨N, zb⟩, rb, ⟨N', zc⟩, rc'⟩) <;>
      dsimp only <;> rw [reps_iff] <;> intro t ht
    · nomatch ht
    · obtain ⟨s, hs, ht⟩ := bind_ok ht
      rw [rX, eY s (fF.symm.trans hs), rB, rC]
      exact fun b c _ _ => Tab.ldivSel_holds ht b c
    · rcases hs : Tab.ofBits g w o x ra y rc with e | s
      · exact absurd hs (hr0 e)
      rw [Tab.ldivTabMat_law hm ht hs (fun a ha j hj => some_lt_two (ho a ha j hj)) hx hy, rX,
        eY s (fF.symm.trans hs), rB, rC]
      exact fun _ _ _ _ => Iff.rfl
  all_goals
    dsimp only
    refine lift2_sound hR hF (fun _ _ _ _ ht hr hs => ?_) K
    obtain ⟨ub, hub, ht⟩ := bind_ok ht
    obtain ⟨uc, huc, ht⟩ := bind_ok ht
    rw [agrees_empty hr, agrees_empty hs, agrees_empty ((reps_iff _ _ _).1 (hB {}) ub hub),
      agrees_empty ((reps_iff _ _ _).1 (hC {}) uc huc)]
    exact fun b c _ _ => Tab.ldivSel_holds ht b c

theorem ldiv_wf (hb : ReadsBack) (R : Rel A B) {S : Rel A C} (UB : Rel B B) (UC : Rel C C) (wS : S.Wf) :
    (GenK.ldiv A B C R S UB UC).Wf := by
  have wF := wS.force {}
  simp only [GenK.ldiv]
  generalize S.force {} = F at wF
  cases F
  case bits g w o x ra y rc =>
    rcases R.runE {} with e | r <;> rcases UB.runE {} with e | ub <;> rcases UC.runE {} with e | uc <;>
      dsimp only
    all_goals try trivial
    simp only [ldivM]
    rcases hm : Tab.ldivTabMat r ub uc g w o x ra y rc with e | (_ | ⟨kb, kc, o', ⟨N, zb⟩, rb, ⟨N', zc⟩, rc'⟩) <;>
      dsimp only
    · trivial
    · trivial
    · exact Tab.ldivTabMat_wf hm (fun e => hb.2.2 r ub uc g w kb kc o o' ra rb rc rc' x y zb zc e wF hm) wF
  all_goals exact lift2_wf _ _

end Rel.Lang.GenK
