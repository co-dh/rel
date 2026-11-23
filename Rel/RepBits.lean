module

public import Rel.Run.Bits
public import Rel.RepTabComp
public import Rel.RepSetOps
public import Rel.RepTabDiv
public import Rel.KernelSpec.BitRows

-- exposed: every def body is a spec a downstream `rfl`/`decide`/`simp` may unfold (PLAN W.8)
@[expose] public section

/-! The laws of `Tab.compBits` and `Tab.ldivBits` (`Rel/Run/Bits.lean`), from the kernels' laws and `raw_kbitrows`:
each step's words first (`Vals.code`), then the answers against `Tab.comp_holds` and `Tab.ldiv_holds`. -/

namespace Rel
open Rel.Ext Rel.Kernel Rel.Verify Ext.Enc
variable {A B C : Obj}

/-- `Vals.code`'s numbers and representatives hold no null: a scatter of `kseen`'s groups and a gather of `kasc`'s
grade. -/
theorem Vals.code_plain {n : USize} {x : Vals A n} {k : USize} {c rep : Enc} (h : Vals.code x = .ok (k, c, rep)) :
    hasNul c = false ∧ hasNul rep = false ∧ Ext.Enc.WF .i64 n c := by
  simp only [Vals.code, bind] at h
  rw [Except.bind_eq_ok'] at h; obtain ⟨es, -, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨⟨vs, p⟩, hasc, h⟩ := h; try dsimp only at h
  rw [Except.bind_eq_ok'] at h; obtain ⟨⟨k', g, f⟩, hseen, h⟩ := h; try dsimp only at h
  rw [Except.bind_eq_ok'] at h; obtain ⟨c', hc, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨rep', hrep, h⟩ := h
  simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl, rfl⟩ := h
  exact ⟨kscatter_plain hc (kseen_plain hseen).1, by rw [kgather_plain hrep (kasc_plain hasc)]; exact hasNul_wordsFoR _,
    (kscatter_closed hc).2.2 rfl (by decide)⟩

/-- `Vals.code2`'s two number columns and its representatives hold no null: gathers of `Vals.code`'s. -/
theorem Vals.code2_plain {n₁ n₂ : USize} {x : Vals A n₁} {y : Vals A n₂} {k : USize} {cx cy : Enc}
    {z : (N : USize) × Vals A N × Enc} (h : Vals.code2 x y = .ok (k, cx, cy, z)) :
    hasNul cx = false ∧ hasNul cy = false ∧ hasNul z.2.2 = false := by
  simp only [Vals.code2, bind] at h
  rw [Except.bind_eq_ok'] at h; obtain ⟨⟨N, sh⟩, -, h⟩ := h; try dsimp only at h
  rw [Except.bind_eq_ok'] at h; obtain ⟨z', -, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨⟨k', c, rep⟩, hc, h⟩ := h; try dsimp only at h
  rw [Except.bind_eq_ok'] at h; obtain ⟨cx', hx, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨cy', hy, h⟩ := h
  simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl, rfl, rfl⟩ := h
  have hcN := (Vals.code_plain hc).1
  exact ⟨by rw [kgather_plain hx hcN]; exact hasNul_wordsFoR _, by rw [kgather_plain hy hcN]; exact hasNul_wordsFoR _,
    (Vals.code_plain hc).2.1⟩

/-- **`Vals.code` numbers the rows of `x` by value**: `k ≤ n` numbers, row `i`'s number `c[i]` below `k`, two rows
numbered alike exactly when equal, and number `G`'s row `rep[G]` a row numbered `G`. -/
theorem Vals.code_spec {n : USize} {x : Vals A n} {k : USize} {c rep : Enc} (h : Vals.code x = .ok (k, c, rep))
    (hw : Vals.WF x) : k.toNat ≤ n.toNat ∧ (∀ i < n.toNat, ((raw .i64 n c)[i]?.getD 0).toNat < k.toNat) ∧
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
  obtain ⟨π, gr, fs, hkN, hp, hinj, hsur, -, hg, hf, hrow⟩ := group_rows hw hes hasc hseen
  have hU64 : USize.size ≤ 2 ^ 64 := by rcases USize.size_eq with h | h <;> omega
  have hNU := n.toNat_lt_size
  have hK : k'.toUSize.toNat = k' := USize.toNat_ofNat_of_lt' (by omega)
  have hcq : ∀ q < n.toNat, (raw .i64 n c')[π q]?.getD 0 = (gr q).toUInt64 := fun q hq => by
    rw [scatter_last_at hc (kseen_plain hseen).1 π (fun q hq => (hp q hq).1) (fun q hq => (hp q hq).2) hinj q hq, (hg q hq).1]
  have hgr : ∀ q < n.toNat, ((gr q).toUInt64).toNat = gr q := fun q hq =>
    toNat_toUInt64 (by have := (hg q hq).2; omega)
  refine ⟨by rw [hK]; exact hkN, fun i hi => ?_, fun G hG => ?_, fun i i' => ?_⟩
  · obtain ⟨q, hq, rfl⟩ := hsur i hi
    rw [hcq q hq, hgr q hq, hK]; exact (hg q hq).2
  · rw [hK] at hG
    obtain ⟨hfw, hfs, hfG⟩ := hf G hG
    have hw := (kgather_word hrep (kasc_plain hasc) G (by rw [hK]; exact hG)).2
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

/-- **`Vals.code2` numbers `x` and `y` in one order**: `x`'s row `i` gets `cx i`, `y`'s row `j` gets `cy j`, each below
`k`, and two rows (of either side) get one number exactly when they are equal. -/
theorem Vals.code2_spec {n₁ n₂ : USize} {x : Vals A n₁} {y : Vals A n₂} {k : USize} {bx bY : Enc}
    {Z : (N : USize) × Vals A N × Enc} (h : Vals.code2 x y = .ok (k, bx, bY, Z))
    (hx : Vals.WF x) (hy : Vals.WF y) :
    ∃ cx cy : Nat → Nat, k.toNat ≤ n₁.toNat + n₂.toNat ∧
      (∀ i < n₁.toNat, (raw .i64 n₁ bx)[i]?.getD 0 = (cx i).toUInt64 ∧ cx i < k.toNat) ∧
      (∀ j < n₂.toNat, (raw .i64 n₂ bY)[j]?.getD 0 = (cy j).toUInt64 ∧ cy j < k.toNat) ∧
      (∀ i i' : Fin n₁.toNat, cx i = cx i' ↔ x.row i = x.row i') ∧
      (∀ j j' : Fin n₂.toNat, cy j = cy j' ↔ y.row j = y.row j') ∧
      (∀ (i : Fin n₁.toNat) (j : Fin n₂.toNat), cx i = cy j ↔ x.row i = y.row j) ∧
      ∀ G < k.toNat, ∃ t : Fin Z.1.toNat, ((raw .i64 k Z.2.2)[G]?.getD 0).toNat = t.1 ∧
        ((∃ i : Fin n₁.toNat, cx i = G) ∨ ∃ j : Fin n₂.toNat, cy j = G) ∧
        (∀ i : Fin n₁.toNat, cx i = G ↔ x.row i = Z.2.1.row t) ∧ ∀ j : Fin n₂.toNat, cy j = G ↔ y.row j = Z.2.1.row t := by
  simp only [Vals.code2, bind] at h
  rw [Except.bind_eq_ok'] at h; obtain ⟨⟨N, sh⟩, hcat, h⟩ := h; try dsimp only at h
  rw [Except.bind_eq_ok'] at h; obtain ⟨z, hz, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨⟨k', c, rep⟩, hcode, h⟩ := h; try dsimp only at h
  rw [Except.bind_eq_ok'] at h; obtain ⟨bx', hbx, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨bY', hbY, h⟩ := h
  simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl, rfl, rfl⟩ := h
  obtain ⟨hNn, hoff⟩ := catPlan_ok hcat
  have hzr := Vals.concat_row hNn hoff x y hz hx hy
  obtain ⟨hkN, hck, hrep, hceq⟩ := Vals.code_spec hcode (Vals.concat_wf hNn hoff hz hx hy)
  have hU64 : USize.size ≤ 2 ^ 64 := by rcases USize.size_eq with h | h <;> omega
  have hNU := N.toNat_lt_size
  let cd := fun t : Nat => ((raw .i64 N c)[t]?.getD 0).toNat
  have hcd : ∀ t < N.toNat, (raw .i64 N c)[t]?.getD 0 = (cd t).toUInt64 := fun t _ =>
    UInt64.toNat_inj.mp (by simp [cd])
  have zx : ∀ i (hi : i < n₁.toNat), z.row ⟨i, by omega⟩ = x.row ⟨i, hi⟩ := fun i hi => by
    rw [hzr, dif_pos hi]
  have zy : ∀ j (hj : j < n₂.toNat), z.row ⟨n₁.toNat + j, by omega⟩ = y.row ⟨j, hj⟩ := fun j hj => by
    rw [hzr, dif_neg (Nat.not_lt.2 (Nat.le_add_right _ _))]; congr 2; simp
  have bxw : ∀ i < n₁.toNat, (raw .i64 n₁ bx')[i]?.getD 0 = (cd i).toUInt64 := fun i hi => by
    rw [(kgather_word hbx (Vals.code_plain hcode).1 i hi).2, raw_pos_word hi, toNat_toUInt64 (by omega), hcd i (by omega)]
  have byw : ∀ j < n₂.toNat, (raw .i64 n₂ bY')[j]?.getD 0 = (cd (n₁.toNat + j)).toUInt64 := fun j hj => by
    rw [(kgather_word hbY (Vals.code_plain hcode).1 j hj).2, show ((raw .i64 n₂ sh)[j]?.getD 0).toNat = n₁.toNat + j from hoff j hj,
      hcd _ (by omega)]
  have heq : ∀ t (ht : t < N.toNat) t' (ht' : t' < N.toNat), cd t = cd t' ↔ z.row ⟨t, ht⟩ = z.row ⟨t', ht'⟩ :=
    fun t ht t' ht' => by
      rw [← hceq ⟨t, ht⟩ ⟨t', ht'⟩]
      exact ⟨fun e => by rw [hcd t ht, hcd t' ht', e], fun e => by
        simp only [cd]; exact congrArg UInt64.toNat e⟩
  refine ⟨cd, fun j => cd (n₁.toNat + j), by omega, fun i hi => ⟨bxw i hi, hck i (by omega)⟩,
    fun j hj => ⟨byw j hj, hck _ (by omega)⟩, fun i i' => ?_, fun j j' => ?_, fun i j => ?_, fun G hG => ?_⟩
  · rw [heq i (by omega) i' (by omega), zx i i.2, zx i' i'.2]
  · rw [heq _ (by omega) _ (by omega), zy j j.2, zy j' j'.2]
  · rw [heq i (by omega) _ (by omega), zx i i.2, zy j j.2]
  · obtain ⟨t, ht, hct⟩ := hrep G hG
    refine ⟨t, ht, ?_, fun i => ?_, fun j => ?_⟩
    · by_cases h1 : t.1 < n₁.toNat
      · exact .inl ⟨⟨t.1, h1⟩, hct⟩
      · refine .inr ⟨⟨t.1 - n₁.toNat, by omega⟩, ?_⟩
        show cd (n₁.toNat + (t.1 - n₁.toNat)) = G
        rw [Nat.add_sub_cancel' (by omega)]; exact hct
    · show cd i = G ↔ _
      rw [← hct, heq i (by omega) t t.2, zx i i.2]
    · show cd (n₁.toNat + j) = G ↔ _
      rw [← hct, heq _ (by omega) t t.2, zy j j.2]

/-- A `P` below `N` has a last one: no later `k'` below `N` is a `P`. -/
theorem last_of_exists {P : Nat → Prop} {N : Nat} :
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
    have e1 := (colMap_post hm1).2 k hk
    have e2 := (colMap_raw hix).2.2.2 k hk
    simp only [Op.eval, Except.ok.injEq] at e1 e2; rw [UInt64.mul_comm] at e1
    have hb := Nat.mul_le_mul_right w.toNat (hr k hk)
    have hck := hc k hk
    rw [Nat.succ_mul] at hb
    rw [← e2, ← e1, UInt64.toNat_add, UInt64.toNat_mul, USize.toNat_toUInt64,
      Nat.mod_eq_of_lt (show _ < 2 ^ 64 by omega), Nat.mod_eq_of_lt (show _ < 2 ^ 64 by omega)]
  obtain ⟨hs, -, hw⟩ := kscatter_words h (kscatter_plain hone rfl)
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
    (h : Tab.ofBits g w o x ra y rc = .ok X) (hra : hasNul ra = false) (hrc : hasNul rc = false)
    (P : Nat → Nat → Prop)
    (hgw : (g * w).toNat = g.toNat * w.toNat) (hb : g.toNat * w.toNat < 2 ^ 63)
    (ho : ∀ a < g.toNat, ∀ j < w.toNat, ∃ v : UInt64, (raw .i64 (g * w) o)[a * w.toNat + j]? = some v ∧ v < 2 ∧
      (v = 1 ↔ P a j)) (u : A.El) (v : C.El) :
    X.Holds u v ↔ ∃ a < g.toNat, ∃ j < w.toNat, P a j ∧ (∃ i : Fin n.toNat,
      ((raw .i64 g ra)[a]?.getD 0).toNat = i.1 ∧ x.row i = u) ∧ ∃ i : Fin m.toNat,
      ((raw .i64 w rc)[j]?.getD 0).toNat = i.1 ∧ y.row i = v := by
  simp only [Tab.ofBits, bind] at h
  rw [Except.bind_eq_ok'] at h; obtain ⟨⟨M, sel⟩, hM, h⟩ := h; try dsimp only at h
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
    have wcw : w.toUInt64 = w.toNat.toUInt64 := UInt64.toNat_inj.mp (by simp)
    have e1 := (colMap_post hdv).2 t ht
    rw [e, wcw, eval_rdiv_nat (by omega) (by omega) hw0, Except.ok.injEq] at e1
    have e2 := (colMap_post hmd).2 t ht
    rw [e, wcw, eval_rmod_nat (by omega) (by omega) hw0, Except.ok.injEq] at e2
    have hdl : i / w.toNat < 2 ^ 64 := Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (by omega)
    have hml : i % w.toNat < 2 ^ 64 := Nat.lt_of_lt_of_le (Nat.mod_lt _ hw0) (by omega)
    have gx := (kgather_word hix hra t ht).2
    rw [← e1, toNat_toUInt64 hdl] at gx
    have gy := (kgather_word hiy hrc t ht).2
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

/-- In an ascending list the first `#{v < r}` positions are exactly the ones holding a value below `r`. -/
private theorem sorted_countP_lt : ∀ {L : List Nat}, L.Pairwise (· ≤ ·) → ∀ r t,
    t < L.countP (fun v => decide (v < r)) ↔ t < L.length ∧ L[t]?.getD 0 < r
  | [], _, r, t => by simp
  | a :: L, h, r, t => by
    rw [List.pairwise_cons] at h
    have ih := sorted_countP_lt h.2 r
    by_cases ha : a < r
    · rw [List.countP_cons_of_pos (by simpa using ha)]
      cases t with
      | zero => simp [ha]
      | succ t => simp only [List.length_cons, List.getElem?_cons_succ]; have := ih t; omega
    · rw [List.countP_cons_of_neg (by simpa using ha), List.countP_eq_zero.2 fun b hb hp => by
        have := h.1 b hb; simp only [decide_eq_true_eq] at hp; omega]
      cases t with
      | zero => simp [ha]
      | succ t =>
        simp only [List.length_cons, List.getElem?_cons_succ, Nat.not_lt_zero, false_iff, not_and]
        intro ht; rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
        have := h.1 L[t] (List.getElem_mem (show t < L.length by omega)); omega

/-- **`csr` groups the rows by `gid`**: row `t` of `idx` is row `π t` of `x`, every row of `x` is some `π t`, and
`kbitrows`' segment `r` (`[ends[r-1], ends[r])`) is the `t` with `gid (π t) = r`. -/
theorem csr_spec {n g : USize} {gid x ends idx : Enc} (h : csr n g gid x = .ok (ends, idx))
    (hgw : Ext.Enc.WF .i64 n gid) (hgN : hasNul gid = false) (hxN : hasNul x = false) (gr : Nat → Nat)
    (hg : ∀ q < n.toNat, (raw .i64 n gid)[q]?.getD 0 = (gr q).toUInt64 ∧ gr q < g.toNat) (hg63 : g.toNat ≤ 2 ^ 63) :
    ∃ π : Nat → Nat, (∀ t < n.toNat, π t < n.toNat ∧ (raw .i64 n idx)[t]?.getD 0 = (raw .i64 n x)[π t]?.getD 0) ∧
      (∀ q < n.toNat, ∃ t < n.toNat, π t = q) ∧ ∀ r < g.toNat, ∀ t,
        ((if r = 0 then 0 else ((raw .i64 g ends)[r - 1]?.getD 0).toNat) ≤ t ∧
          t < ((raw .i64 g ends)[r]?.getD 0).toNat ↔ t < n.toNat ∧ gr (π t) = r) := by
  simp only [csr, bind] at h
  rw [Except.bind_eq_ok'] at h; obtain ⟨one, hone, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨cnt, hcnt, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨ends', hends, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨⟨vs, p⟩, hasc, h⟩ := h; try dsimp only at h
  rw [Except.bind_eq_ok'] at h; obtain ⟨idx', hidx, h⟩ := h
  simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  have hU64 : USize.size ≤ 2 ^ 64 := by rcases USize.size_eq with h | h <;> omega
  have hNU := n.toNat_lt_size
  have hGU := g.toNat_lt_size
  let C := fun r => (List.range n.toNat).countP fun q => decide (gr q < r)
  have hCn : ∀ r, C r ≤ n.toNat := fun r => Nat.le_trans List.countP_le_length (by simp)
  -- `ends[G]` counts the rows with `gid ≤ G`
  have hc := scatter_add_count hcnt (kscatter_plain hone rfl) gr (fun _ => true) (fun q hq => (hg q hq).1) (fun q hq => by
    have := (hg q hq).2; omega) (fun q hq => by
      rw [colConst_raw hone, Array.getElem?_replicate, if_pos hq, Option.getD_some]; rfl)
  have hE : ∀ G < g.toNat, ((raw .i64 g ends')[G]?.getD 0).toNat = C (G + 1) := fun G hG => by
    rw [colPrefix_add_sum hends _ hc G hG, sum_countP_groups]
    simp only [Bool.and_true]; exact toNat_toUInt64 (Nat.lt_of_le_of_lt (hCn (G + 1)) (by omega))
  -- `kasc` of one `i64` column below `2^63` is the stable numeric order on `gid`
  obtain ⟨-, -, hp, -⟩ := kasc_grade hasc (by simp only [List.mem_singleton]; rintro _ rfl; exact ⟨_, hgw⟩)
  have hks : ascKeys n [(.atom .i64, gid)] = [(raw .i64 n gid).map (ordKey 8 false true)] := by
    simp only [ascKeys, ascKey, nulCodes, nulWords, hgN, Bool.false_eq_true, if_false, List.nil_append,
      List.append_nil]; rfl
  generalize hps : ascGrade n.toNat (ascKeys n [(.atom .i64, gid)]) = ps at hp
  obtain ⟨hperm, hpw⟩ := ascGrade_spec n.toNat (ascKeys n [(.atom .i64, gid)])
  rw [hps] at hperm hpw
  have hlen : ps.length = n.toNat := by rw [hperm.length_eq, List.length_range]
  have hin : ∀ i ∈ ps, i < n.toNat := fun i hi => List.mem_range.1 (hperm.mem_iff.1 hi)
  have hsz := (kscatter_words hcnt (kscatter_plain hone rfl)).1
  have hcv : ∀ q < n.toNat, (((raw .i64 n gid).map (ordKey 8 false true))[q]?.getD 0).toNat = gr q + 2 ^ 63 :=
    fun q hq => by
      have hq63 : gr q < 2 ^ 63 := by have := (hg q hq).2; omega
      rw [Array.getElem?_map, getElem?_pos (raw .i64 n gid) q (by omega), Option.map_some, Option.getD_some]
      have e := (hg q hq).1
      rw [getElem?_pos (raw .i64 n gid) q (by omega), Option.getD_some] at e
      rw [e]
      have := ordKey_signed (w := 8) (by omega) (by omega) (gr q).toUInt64
      simp only [sx, toNat_toUInt64 (show gr q < 2 ^ 64 by omega)] at this
      split at this <;> omega
  have hsorted : (ps.map gr).Pairwise (· ≤ ·) := List.pairwise_map.2 (hpw.imp_of_mem fun {i j} hi hj hij => by
    have e := hij.1
    rw [hks] at e
    simp only [lexLe, Bool.or_eq_true, decide_eq_true_eq, Bool.and_true, beq_iff_eq, UInt64.lt_iff_toNat_lt] at e
    have ci := hcv i (hin i hi); have cj := hcv j (hin j hj)
    rcases e with e | e
    · omega
    · have := congrArg UInt64.toNat e; omega)
  have hcount : ∀ r, (ps.map gr).countP (fun v => decide (v < r)) = C r := fun r => by
    rw [List.countP_map]; exact hperm.countP_eq _
  let π := fun t : Nat => ps[t]?.getD 0
  have hπ : ∀ t < n.toNat, ps[t]? = some (π t) := fun t ht => by
    simp only [π]; rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
  have hL : ∀ t < n.toNat, (ps.map gr)[t]?.getD 0 = gr (π t) := fun t ht => by
    rw [List.getElem?_map, hπ t ht]; rfl
  refine ⟨π, fun t ht => ?_, fun q hq => ?_, fun r hr t => ?_⟩
  · have hπn : π t < n.toNat := hin _ (List.mem_of_getElem? (hπ t ht))
    obtain ⟨-, e⟩ := kgather_word hidx hxN t ht
    have hpt : ((raw .i64 n p)[t]?.getD 0).toNat = π t := by
      rw [hp, List.getElem?_toArray, List.getElem?_map, hπ t ht]
      exact toNat_toUInt64 (by omega)
    rw [hpt] at e
    exact ⟨hπn, e⟩
  · obtain ⟨t, ht, e⟩ := List.mem_iff_getElem.1 (hperm.mem_iff.2 (List.mem_range.2 hq))
    refine ⟨t, by omega, ?_⟩
    simp only [π]; rw [List.getElem?_eq_getElem ht, Option.getD_some, e]
  · have hlo : (if r = 0 then 0 else ((raw .i64 g ends')[r - 1]?.getD 0).toNat) = C r := by
      split
      · subst r; simp [C]
      · rw [hE (r - 1) (by omega), Nat.sub_add_cancel (by omega)]
    rw [hlo, hE r hr]
    have h1 := sorted_countP_lt hsorted r t
    have h2 := sorted_countP_lt hsorted (r + 1) t
    rw [hcount, List.length_map, hlen] at h1 h2
    by_cases ht : t < n.toNat
    · rw [hL t ht] at h1 h2; omega
    · have := hCn (r + 1); omega

/-- **`R.compBits S` denotes `R ≫ S`** (`Tab.comp_holds`' statement). -/
theorem Tab.compBits_holds {R : Tab A B} {S : Tab B C} {X : Tab A C} (h : Tab.compBits R S = .ok X)
    (hR : R.WF) (hS : S.WF) (a : A.El) (c : C.El) : X.Holds a c ↔ ∃ b, R.Holds a b ∧ S.Holds b c := by
  simp only [Tab.compBits, bind] at h
  rw [Except.bind_eq_ok'] at h; obtain ⟨⟨ka', kc', o', ra', rc'⟩, hM, hX⟩ := h; try dsimp only at hX
  simp only [Tab.compMat, bind] at hM
  have h := hM
  rw [Except.bind_eq_ok'] at h; obtain ⟨⟨kb, bR, bS, Z⟩, hb2, h⟩ := h; try dsimp only at h
  rw [Except.bind_eq_ok'] at h; obtain ⟨⟨ka, aR, ra⟩, ha, h⟩ := h; try dsimp only at h
  rw [Except.bind_eq_ok'] at h; obtain ⟨⟨kc, cS, rc⟩, hc, h⟩ := h; try dsimp only at h
  split at h
  · cases h
  rename_i hov
  rw [Except.bind_eq_ok'] at h; obtain ⟨-, -, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨⟨ends, idx⟩, hcsr, h⟩ := h; try dsimp only at h
  rw [Except.bind_eq_ok'] at h; obtain ⟨m, hm, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨o, hk, h⟩ := h
  simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := h
  have h := hX
  obtain ⟨cx, cy, -, hcx, hcy, -, -, hxy, -⟩ := Vals.code2_spec hb2 hR.2 hS.1
  obtain ⟨-, haR, hra, haeq⟩ := Vals.code_spec ha hR.1
  obtain ⟨-, hcS, hrc, hceq⟩ := Vals.code_spec hc hS.2
  have hU64 : USize.size ≤ 2 ^ 64 := by rcases USize.size_eq with h | h <;> omega
  have hNb := kb.toNat_lt_size
  have hw : ∀ (w : UInt64), (w.toNat).toUInt64 = w := fun w => UInt64.toNat_inj.mp (by simp)
  let aN := fun i : Nat => ((raw .i64 R.n aR)[i]?.getD 0).toNat
  let cN := fun i : Nat => ((raw .i64 S.n cS)[i]?.getD 0).toNat
  -- the `a` and `c` of a set bit name rows of `R.key` and `S.val`; `b` is shared by a row of each side
  let P := fun r j => ∃ i < R.n.toNat, aN i = r ∧ ∃ k < S.n.toNat, cy k = cx i ∧ cN k = j
  have hX := Tab.ofBits_holds h (Vals.code_plain ha).2.1 (Vals.code_plain hc).2.1 P
  by_cases hkc : kc.toNat = 0
  · have hS0 : S.n.toNat = 0 := Classical.byContradiction fun e => by have := hcS 0 (by omega); omega
    have hgw : (ka * kc).toNat = ka.toNat * kc.toNat := by
      simp [USize.toNat_mul, hkc]
    rw [hX hgw (by rw [hkc, Nat.mul_zero]; decide) (fun _ _ j hj => absurd hj (by omega))]
    constructor
    · rintro ⟨-, -, j, hj, -⟩; omega
    · rintro ⟨-, -, ⟨t, -⟩⟩; exact absurd t.2 (by omega)
  have hb : ka.toNat * kc.toNat < 2 ^ 63 := by
    have := Nat.mul_le_mul_right kc.toNat (Nat.le_add_left ka.toNat kb.toNat); omega
  have hka : ka.toNat ≤ 2 ^ 63 := by
    have := Nat.mul_le_mul_left ka.toNat (show 1 ≤ kc.toNat by omega); omega
  obtain ⟨π, hπx, hπs, hseg⟩ := csr_spec hcsr (Vals.code_plain ha).2.2 (Vals.code_plain ha).1
    (Vals.code2_plain hb2).1 aN (fun q hq => ⟨(hw _).symm, haR q hq⟩) hka
  obtain ⟨hnw, hgw, -, -, -, -, -, hbit⟩ := raw_kbitrows hk
  have hM := bitMatrix_spec hm hnw (fun k hk => by
      rw [(hcy k hk).1, toNat_toUInt64 (by have := (hcy k hk).2; omega)]; exact (hcy k hk).2) hcS
  rw [hX hgw hb fun r hr j hj => ?_]
  · constructor
    · rintro ⟨r, hr, j, hj, ⟨i, hi, hir, k, hk, hki, hkj⟩, ⟨i0, h0, r0⟩, ⟨i1, h1, r1⟩⟩
      obtain ⟨i0', h0', e0⟩ := hra r hr
      obtain ⟨i1', h1', e1⟩ := hrc j hj
      obtain rfl : i0' = i0 := Fin.ext (h0'.symm.trans h0)
      obtain rfl : i1' = i1 := Fin.ext (h1'.symm.trans h1)
      refine ⟨R.val.row ⟨i, hi⟩, ⟨⟨i, hi⟩, ?_, rfl⟩, ⟨k, hk⟩, ((hxy ⟨i, hi⟩ ⟨k, hk⟩).1 hki.symm).symm, ?_⟩
      · rw [← r0]; exact (haeq ⟨i, hi⟩ i0').1 (UInt64.toNat_inj.mp (hir.trans e0.symm))
      · rw [← r1]; exact (hceq ⟨k, hk⟩ i1').1 (UInt64.toNat_inj.mp (hkj.trans e1.symm))
    · rintro ⟨b, ⟨t, ht1, ht2⟩, ⟨t', ht1', ht2'⟩⟩
      obtain ⟨i0, h0, e0⟩ := hra (aN t) (haR t t.2)
      obtain ⟨i1, h1, e1⟩ := hrc (cN t') (hcS t' t'.2)
      refine ⟨aN t, haR t t.2, cN t', hcS t' t'.2, ⟨t, t.2, rfl, t', t'.2, ?_, rfl⟩, ⟨i0, h0, ?_⟩, ⟨i1, h1, ?_⟩⟩
      · exact (hxy t t').2 (ht2.trans ht1'.symm) |>.symm
      · rw [← ht1]; exact (haeq i0 t).1 (UInt64.toNat_inj.mp e0)
      · rw [← ht2']; exact (hceq i1 t').1 (UInt64.toNat_inj.mp e1)
  -- bit `r·kc + j` is set exactly when `P r j`
  obtain ⟨v, -, hv, hv2, hv1⟩ := hbit r hr j hj
  refine ⟨v, hv, hv2, hv1.trans ?_⟩
  simp only [Bool.false_eq_true, if_false]
  constructor
  · rintro ⟨t, h1, h2, hon⟩
    obtain ⟨htn, hr'⟩ := (hseg r hr t).1 ⟨h1, h2⟩
    obtain ⟨hπn, e⟩ := hπx t htn
    rw [e, (hcx _ hπn).1, toNat_toUInt64 (by have := (hcx _ hπn).2; omega),
      hM _ (hcx _ hπn).2 j hj] at hon
    split at hon
    · rename_i hex
      obtain ⟨k, hk, hk1, hk2⟩ := hex
      rw [(hcy k hk).1, toNat_toUInt64 (by have := (hcy k hk).2; omega)] at hk1
      exact ⟨π t, hπn, hr', k, hk, hk1, hk2⟩
    · simp at hon
  · rintro ⟨i, hi, hir, k, hk, hki, hkj⟩
    obtain ⟨t, ht, rfl⟩ := hπs i hi
    obtain ⟨h1, h2⟩ := (hseg r hr t).2 ⟨ht, hir⟩
    refine ⟨t, h1, h2, ?_⟩
    obtain ⟨hπn, e⟩ := hπx t ht
    rw [e, (hcx _ hπn).1, toNat_toUInt64 (by have := (hcx _ hπn).2; omega),
      hM _ (hcx _ hπn).2 j hj, if_pos ⟨k, hk, by
        rw [(hcy k hk).1, toNat_toUInt64 (by have := (hcy k hk).2; omega)]; exact hki, hkj⟩]
    rfl

/-- **`compBits` is `comp`** on the pairs it holds: the fused kernel answers what the composition of primitives does. -/
theorem Tab.compBits_comp {R : Tab A B} {S : Tab B C} {X Y : Tab A C} (h : Tab.compBits R S = .ok X)
    (h' : R.comp S = .ok Y) (hR : R.WF) (hS : S.WF) : X.Holds = Y.Holds :=
  funext fun a => funext fun c => propext ((Tab.compBits_holds h hR hS a c).trans (Tab.comp_holds h' hR hS a c).symm)

/-- **`colCat` is the words of `a`, then those of `b`**. -/
theorem colCat_raw {n₁ n₂ N : USize} {a b o : Enc} (h : colCat n₁ n₂ a b = .ok (N, o))
    (ha : hasNul a = false) (hb : hasNul b = false) :
    N.toNat = n₁.toNat + n₂.toNat ∧ ∀ q < N.toNat, (raw .i64 N o)[q]?.getD 0 =
      if q < n₁.toNat then (raw .i64 n₁ a)[q]?.getD 0 else (raw .i64 n₂ b)[q - n₁.toNat]?.getD 0 := by
  simp only [colCat, bind] at h
  rw [Except.bind_eq_ok'] at h; obtain ⟨⟨N', sh⟩, hcat, h⟩ := h; try dsimp only at h
  rw [Except.bind_eq_ok'] at h; obtain ⟨s1, hs1, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨s2, hs2, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨o', ho, h⟩ := h
  simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  obtain ⟨hNn, hoff⟩ := catPlan_ok hcat
  have hU64 : USize.size ≤ 2 ^ 64 := by rcases USize.size_eq with h | h <;> omega
  have hNU := N'.toNat_lt_size
  -- each side lands at `d + k`, and every other word is the fill `0`
  have side : ∀ {m : USize} {ix e s : Enc}, kscatter .last m ix e N' 0 = .ok s → hasNul e = false → ∀ d,
      (∀ k < m.toNat, ((raw .i64 m ix)[k]?.getD 0).toNat = d + k) → d + m.toNat ≤ N'.toNat →
      ∀ q < N'.toNat, (raw .i64 N' s)[q]?.getD 0 =
        if d ≤ q ∧ q < d + m.toNat then (raw .i64 m e)[q - d]?.getD 0 else 0 := by
    intro m ix e s hs he d hix hd q hq
    split
    · rename_i hq'
      have := scatter_last_at hs he (fun k => d + k) (fun k hk => UInt64.toNat_inj.mp (by
        dsimp only; rw [hix k hk, toNat_toUInt64 (by omega)])) (fun k hk => by dsimp only; omega)
        (fun k _ kk _ e => by dsimp only at e; omega) (q - d) (by omega)
      dsimp only at this; rwa [Nat.add_sub_cancel' hq'.1] at this
    · rename_i hq'
      obtain ⟨hsz, -, hw⟩ := kscatter_words hs he
      obtain ⟨-, hfill, -⟩ := (scatterWords_spec _ _ _ _).2 _ hw
      rw [hfill q hq fun k hk e => by
        have e' : ((raw .i64 m ix)[k]?.getD 0).toNat = q := e
        rw [hsz] at hk; rw [hix k hk] at e'; omega, Option.getD_some]
  have h1 := side hs1 ha 0 (fun k hk => by rw [raw_pos_word hk, toNat_toUInt64 (by omega), Nat.zero_add]) (by omega)
  have h2 := side hs2 hb n₁.toNat hoff (by omega)
  refine ⟨hNn, fun q hq => ?_⟩
  have e := (colMap_raw ho).2.2.2 q hq
  simp only [Op.eval, Except.ok.injEq] at e
  rw [← e, h1 q hq, h2 q hq]
  by_cases hq1 : q < n₁.toNat
  · rw [if_pos ⟨Nat.zero_le _, by omega⟩, if_neg (by omega), if_pos hq1, Nat.sub_zero, UInt64.add_zero]
  · rw [if_neg (by omega), if_pos ⟨by omega, by omega⟩, if_neg hq1, UInt64.zero_add]

/-- `colCat`'s answer is a plain `i64` column: a `colMap` (`colMap_plain`, `colMap_closed`). -/
theorem colCat_plain {n₁ n₂ N : USize} {a b o : Enc} (h : colCat n₁ n₂ a b = .ok (N, o)) :
    hasNul o = false ∧ Ext.Enc.WF .i64 N o := by
  simp only [colCat, bind] at h
  rw [Except.bind_eq_ok'] at h; obtain ⟨⟨N', sh⟩, -, h⟩ := h; try dsimp only at h
  rw [Except.bind_eq_ok'] at h; obtain ⟨s1, -, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨s2, -, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨o', ho, h⟩ := h
  simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  exact ⟨colMap_plain (by lockstep) ho, (colMap_closed (by lockstep) ho).2⟩

/-- **`R.ldivBits S UB UC` denotes `R\S` within `UB`, `UC`** (`Tab.ldiv_holds`' statement). -/
theorem Tab.ldivBits_holds {R : Tab A B} {S : Tab A C} {UB : Tab B B} {UC : Tab C C} {T : Tab B C}
    (h : Tab.ldivBits R S UB UC = .ok T) (hR : R.WF) (hS : S.WF) (hUB : UB.WF) (hUC : UC.WF) (b : B.El) (c : C.El) :
    T.Holds b c ↔ Lang.ldivDen R.Holds S.Holds UB.Holds UC.Holds b c := by
  simp only [Tab.ldivBits, bind] at h
  rw [Except.bind_eq_ok'] at h; obtain ⟨⟨ka, aR, aS, Za⟩, ha2, h⟩ := h; try dsimp only at h
  rw [Except.bind_eq_ok'] at h; obtain ⟨⟨kb, bR, bU, Nb, zb, rb⟩, hb2, h⟩ := h; try dsimp only at h
  rw [Except.bind_eq_ok'] at h; obtain ⟨⟨kc, cS, cU, Nc, zc, rc⟩, hc2, h⟩ := h; try dsimp only at h
  split at h
  · cases h
  rename_i hov
  rw [Except.bind_eq_ok'] at h; obtain ⟨-, -, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨one, hone, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨cnt, hcnt, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨eqc, heqc, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨⟨E, eb⟩, hE, h⟩ := h; try dsimp only at h
  rw [Except.bind_eq_ok'] at h; obtain ⟨⟨N, gid⟩, hgid, h⟩ := h; try dsimp only at h
  rw [Except.bind_eq_ok'] at h; obtain ⟨kE, hkE, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨⟨N2, ix⟩, hix, h⟩ := h; try dsimp only at h
  rw [Except.bind_eq_ok'] at h; obtain ⟨⟨ends, idx⟩, hcsr, h⟩ := h; try dsimp only at h
  rw [Except.bind_eq_ok'] at h; obtain ⟨kU, hkU, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨⟨NS, rr⟩, hrr, h⟩ := h; try dsimp only at h
  rw [Except.bind_eq_ok'] at h; obtain ⟨⟨NS2, cc⟩, hcc, h⟩ := h; try dsimp only at h
  rw [Except.bind_eq_ok'] at h; obtain ⟨m, hm, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨o, hk, h⟩ := h
  obtain ⟨ax, as, -, hax, has, -, -, haxs, -⟩ := Vals.code2_spec ha2  hR.1 hS.1
  obtain ⟨bx, bu, -, hbx, hbu, -, -, -, hrb⟩ := Vals.code2_spec hb2 hR.2 hUB.2
  obtain ⟨cs, cu, -, hcs, hcu, -, -, -, hrc⟩ := Vals.code2_spec hc2 hS.2 hUC.2
  have hU64 : USize.size ≤ 2 ^ 64 := by rcases USize.size_eq with h | h <;> omega
  have hw : ∀ (w : UInt64), (w.toNat).toUInt64 = w := fun w => UInt64.toNat_inj.mp (by simp)
  have hNka := ka.toNat_lt_size; have hNkb := kb.toNat_lt_size; have hNkc := kc.toNat_lt_size
  have hX := Tab.ofBits_holds h (Vals.code2_plain hb2).2.2 (Vals.code2_plain hc2).2.2
  -- no `b` number or no `c` number: both sides are empty
  by_cases h0 : kb.toNat = 0 ∨ kc.toNat = 0
  · have hgw : (kb * kc).toNat = kb.toNat * kc.toNat := by
      rcases h0 with h0 | h0 <;> simp [USize.toNat_mul, h0]
    rw [hX (fun _ _ => False) hgw (by rcases h0 with h0 | h0 <;> simp [h0])
      (fun G hG j hj => (by rcases h0 with h0 | h0 <;> omega : False).elim)]
    refine ⟨fun ⟨_, _, _, _, hP, _⟩ => hP.elim, fun ⟨h1, h2⟩ => ?_⟩
    rcases h2 with ⟨a, t, ht1, ht2⟩ | ⟨⟨b', u, hu1, hu2⟩, c', u', hu1', hu2'⟩
    · obtain ⟨s, -, -⟩ := h1 a ⟨t, ht1, ht2⟩
      have := (hbx t t.2).2; have := (hcs s s.2).2; omega
    · have := (hbu u u.2).2; have := (hcu u' u'.2).2; omega
  have hkb1 : 0 < kb.toNat := by omega
  have hkc1 : 0 < kc.toNat := by omega
  have hb63 : kb.toNat * kc.toNat < 2 ^ 63 := by
    have := Nat.mul_le_mul_right kc.toNat (show kb.toNat ≤ ka.toNat + 1 + kb.toNat by omega); omega
  have hka63 : ka.toNat + 1 < 2 ^ 63 := by
    have := Nat.mul_le_mul_left (ka.toNat + 1 + kb.toNat) (show 1 ≤ kc.toNat by omega); omega
  -- `cnt[G]` is `0` exactly when no row of `R` has value number `G`
  have hcntw := scatter_add_count hcnt (kscatter_plain hone rfl) bx (fun _ => true) (fun q hq => (hbx q hq).1) (fun q hq => by
    have := (hbx q hq).2; have := kb.toNat_lt_size; omega) (fun q hq => by
      rw [colConst_raw hone, Array.getElem?_replicate, if_pos hq, Option.getD_some]; rfl)
  have hz : ∀ G < kb.toNat, ((raw .i64 kb eqc)[G]?.getD 0 = 1 ↔ ∀ i < R.n.toNat, bx i ≠ G) ∧
      (raw .i64 kb eqc)[G]?.getD 0 < 2 := fun G hG => by
    have e := (colMap_post heqc).2 G hG
    have hev : ∀ x : UInt64, Op.eval .eq 0 x = .ok (if x = 0 then 1 else 0) := fun x => by
      show Except.ok (if ((0 : UInt64) == x) = true then 1 else 0) = _
      by_cases h : x = 0
      · simp [h]
      · simp [h, Ne.symm h]
    rw [hev, hcntw G hG,
      Except.ok.injEq] at e
    rw [← e]
    have hcl : ((List.range R.n.toNat).countP fun q => bx q == G && true) ≤ R.n.toNat :=
      Nat.le_trans List.countP_le_length (by simp)
    have hNU := R.n.toNat_lt_size
    by_cases hc0 : ((List.range R.n.toNat).countP fun q => bx q == G && true) = 0
    · rw [hc0, if_pos (show Nat.toUInt64 0 = 0 from rfl)]
      refine ⟨⟨fun _ i hi e => ?_, fun _ => rfl⟩, by decide⟩
      rw [List.countP_eq_zero] at hc0
      exact hc0 i (List.mem_range.2 hi) (by simp [e])
    · have hne : ((List.range R.n.toNat).countP fun q => bx q == G && true).toUInt64 ≠ 0 := fun e => by
        have := congrArg UInt64.toNat e; rw [toNat_toUInt64 (by omega)] at this; exact hc0 (by simpa using this)
      rw [if_neg hne]
      refine ⟨⟨fun e => absurd e (by decide), fun H => absurd ?_ hc0⟩, by decide⟩
      rw [List.countP_eq_zero]; intro i hi e; simp at e; exact H i (List.mem_range.1 hi) e
  have hwc := whereCol_spec hE fun G hG => (hz G hG).2
  have hEs := whereCol_size hE
  let ebN := fun e : Nat => ((raw .i64 E eb)[e]?.getD 0).toNat
  have heb1 : ∀ e < E.toNat, ebN e < kb.toNat ∧ ∀ i < R.n.toNat, bx i ≠ ebN e := fun e he => by
    have e1 := congrArg (·[e]?) hwc
    simp only [List.getElem?_map, Array.getElem?_toList, getElem?_pos (raw .i64 E eb) e (by omega),
      Option.map_some] at e1
    have hm := List.mem_of_getElem? e1.symm
    rw [List.mem_filter, List.mem_range] at hm
    have hv : ebN e = ((raw .i64 E eb)[e]'(by omega)).toNat := by
      simp only [ebN]; rw [getElem?_pos (raw .i64 E eb) e (by omega), Option.getD_some]
    rw [hv]
    refine ⟨hm.1, (hz _ hm.1).1.1 ?_⟩
    have h2 := (hz _ hm.1).2
    have h3 : (raw .i64 kb eqc)[((raw .i64 E eb)[e]'(by omega)).toNat]?.getD 0 ≠ 0 := by simpa using hm.2
    have b01 : ∀ v : UInt64, v < 2 → v ≠ 0 → v = 1 := fun v h2 h3 => by
      have := UInt64.lt_iff_toNat_lt.1 h2
      have h4 : v.toNat ≠ 0 := fun e => h3 (UInt64.toNat_inj.mp (by simpa using e))
      apply UInt64.toNat_inj.mp; simp at this ⊢; omega
    exact b01 _ h2 h3
  have heb2 : ∀ G < kb.toNat, (∀ i < R.n.toNat, bx i ≠ G) → ∃ e < E.toNat, ebN e = G := fun G hG H => by
    have hm : G ∈ (List.range kb.toNat).filter fun i => (raw .i64 kb eqc)[i]?.getD 0 ≠ 0 :=
      List.mem_filter.2 ⟨List.mem_range.2 hG, by simp [(hz G hG).1.2 H]⟩
    rw [← hwc, List.mem_iff_getElem?] at hm
    obtain ⟨e, he⟩ := hm
    simp only [List.getElem?_map, Array.getElem?_toList] at he
    obtain ⟨wd, hwd, hwi⟩ := Option.map_eq_some_iff.1 he
    have heE : e < E.toNat := by
      rw [← hEs]; exact Classical.byContradiction fun hc => by
        rw [Array.getElem?_eq_none_iff.2 (Nat.le_of_not_lt hc)] at hwd; cases hwd
    exact ⟨e, heE, by simp only [ebN]; rw [hwd, Option.getD_some, hwi]⟩
  -- the grouping column `gid` (values of `R`, then the numbers of no row) and the matrix rows `ix` it groups
  obtain ⟨hN, hgw'⟩ := colCat_raw hgid (Vals.code2_plain hb2).1 (whereCol_plain hE)
  obtain ⟨hN2, hixw⟩ := colCat_raw hix (Vals.code2_plain ha2).1 (kscatter_plain hkE rfl)
  obtain rfl : N = N2 := USize.toNat_inj.mp (by omega)
  let gr := fun q => if q < R.n.toNat then bx q else ebN (q - R.n.toNat)
  have hg : ∀ q < N.toNat, (raw .i64 N gid)[q]?.getD 0 = (gr q).toUInt64 ∧ gr q < kb.toNat := fun q hq => by
    rw [hgw' q hq]; simp only [gr]
    split
    · exact hbx q (by assumption)
    · exact ⟨(hw _).symm, (heb1 _ (by omega)).1⟩
  obtain ⟨π, hπx, hπs, hseg⟩ := csr_spec hcsr (colCat_plain hgid).2 (colCat_plain hgid).1 (colCat_plain hix).1
    gr hg (by omega)
  obtain ⟨hnw, hgw, -, -, -, -, hidxb, hbit⟩ := raw_kbitrows hk
  have hN1 : 0 < N.toNat := by
    by_cases hR : ∃ i < R.n.toNat, bx i = 0
    · obtain ⟨i, hi, -⟩ := hR; omega
    · obtain ⟨e, he, -⟩ := heb2 0 hkb1 fun i hi e => hR ⟨i, hi, e⟩; omega
  have hka1 : (ka + 1).toNat = ka.toNat + 1 := by
    have h1 := hidxb 0 hN1
    rw [USize.toNat_add, USize.toNat_one] at h1 ⊢
    rcases Nat.lt_or_ge (ka.toNat + 1) USize.size with h2 | h2
    · exact Nat.mod_eq_of_lt h2
    · rw [show ka.toNat + 1 = USize.size by have := ka.toNat_lt_size; omega, Nat.mod_self] at h1; omega
  have hkaw : ((ka.toUInt64 : UInt64)).toNat = ka.toNat := USize.toNat_toUInt64 ka
  let ixN := fun q => if q < R.n.toNat then ax q else ka.toNat
  have hixN : ∀ q < N.toNat, ((raw .i64 N ix)[q]?.getD 0).toNat = ixN q := fun q hq => by
    rw [hixw q hq]; simp only [ixN]
    split
    · rw [(hax q (by assumption)).1, toNat_toUInt64 (by have := (hax q (by assumption)).2; omega)]
    · rw [colConst_raw hkE, Array.getElem?_replicate, if_pos (by omega), Option.getD_some, hkaw]
  -- the matrix: row `as s` holds `cs s` for each row `s` of `S`, row `ka` holds `ran UC`
  obtain ⟨hNS, hrrw⟩ := colCat_raw hrr (Vals.code2_plain ha2).2.1 (kscatter_plain hkU rfl)
  obtain ⟨hNS2, hccw⟩ := colCat_raw hcc (Vals.code2_plain hc2).1 (Vals.code2_plain hc2).2.1
  obtain rfl : NS = NS2 := USize.toNat_inj.mp (by omega)
  let rN := fun k => if k < S.n.toNat then as k else ka.toNat
  let cN := fun k => if k < S.n.toNat then cs k else cu (k - S.n.toNat)
  have hrN : ∀ k < NS.toNat, ((raw .i64 NS rr)[k]?.getD 0).toNat = rN k := fun k hk => by
    rw [hrrw k hk]; simp only [rN]
    split
    · rw [(has k (by assumption)).1, toNat_toUInt64 (by have := (has k (by assumption)).2; omega)]
    · rw [colConst_raw hkU, Array.getElem?_replicate, if_pos (by omega), Option.getD_some, hkaw]
  have hcN : ∀ k < NS.toNat, ((raw .i64 NS cc)[k]?.getD 0).toNat = cN k := fun k hk => by
    rw [hccw k hk]; simp only [cN]
    split
    · rw [(hcs k (by assumption)).1, toNat_toUInt64 (by have := (hcs k (by assumption)).2; omega)]
    · rw [(hcu _ (by omega)).1, toNat_toUInt64 (by have := (hcu (k - S.n.toNat) (by omega)).2; omega)]
  have hM := bitMatrix_spec hm hnw (fun k hk => by
      rw [hrN k hk, hka1]; simp only [rN]; split
      · have := (has k (by assumption)).2; omega
      · omega)
    (fun k hk => by
      rw [hcN k hk]; simp only [cN]; split
      · exact (hcs k (by assumption)).2
      · exact (hcu _ (by omega)).2)
  -- bit `G·kc + j` holds exactly when every row of `R` valued `G` has its key's row of `S` at `c`-number `j`,
  -- and, where no row of `R` is valued `G`, some row of `UC` is numbered `j`
  let P := fun G j => (∀ i < R.n.toNat, bx i = G → ∃ s < S.n.toNat, as s = ax i ∧ cs s = j) ∧
    ((∀ i < R.n.toNat, bx i ≠ G) → ∃ u < UC.n.toNat, cu u = j)
  have hon : ∀ j < kc.toNat, ∀ t < N.toNat,
      ((raw .i64 ((ka + 1) * kc) m)[((raw .i64 N idx)[t]?.getD 0).toNat * kc.toNat + j]?.getD 0) % 2 = 1 ↔
        if π t < R.n.toNat then ∃ s < S.n.toNat, as s = ax (π t) ∧ cs s = j else ∃ u < UC.n.toNat, cu u = j :=
    fun j hj t ht => by
      obtain ⟨hπn, e⟩ := hπx t ht
      have hix := hixN _ hπn
      have hlt : ixN (π t) < (ka + 1).toNat := by
        rw [hka1]; simp only [ixN]; split
        · have := (hax (π t) (by assumption)).2; omega
        · omega
      rw [e, hix, hM _ hlt j hj]
      have key : (∃ k < NS.toNat, ((raw .i64 NS rr)[k]?.getD 0).toNat = ixN (π t) ∧
          ((raw .i64 NS cc)[k]?.getD 0).toNat = j) ↔ (if π t < R.n.toNat then
            ∃ s < S.n.toNat, as s = ax (π t) ∧ cs s = j else ∃ u < UC.n.toNat, cu u = j) := by
        simp only [ixN]
        by_cases hp : π t < R.n.toNat
        · simp only [if_pos hp]
          have hax' := (hax (π t) hp).2
          constructor
          · rintro ⟨k, hk, h1, h2⟩
            rw [hrN k hk] at h1; rw [hcN k hk] at h2; simp only [rN, cN] at h1 h2
            by_cases hks : k < S.n.toNat
            · rw [if_pos hks] at h1 h2; exact ⟨k, hks, h1, h2⟩
            · rw [if_neg hks] at h1; omega
          · rintro ⟨s, hs, h1, h2⟩
            refine ⟨s, by omega, ?_, ?_⟩
            · rw [hrN s (by omega)]; simp only [rN, if_pos hs]; exact h1
            · rw [hcN s (by omega)]; simp only [cN, if_pos hs]; exact h2
        · simp only [if_neg hp]
          constructor
          · rintro ⟨k, hk, h1, h2⟩
            rw [hrN k hk] at h1; rw [hcN k hk] at h2; simp only [rN, cN] at h1 h2
            by_cases hks : k < S.n.toNat
            · rw [if_pos hks] at h1; have := (has k hks).2; omega
            · rw [if_neg hks] at h2; exact ⟨k - S.n.toNat, by omega, h2⟩
          · rintro ⟨u, hu, h2⟩
            refine ⟨S.n.toNat + u, by omega, ?_, ?_⟩
            · rw [hrN _ (by omega)]; simp only [rN, if_neg (show ¬ S.n.toNat + u < S.n.toNat by omega)]
            · rw [hcN _ (by omega)]; simp only [cN, if_neg (show ¬ S.n.toNat + u < S.n.toNat by omega),
                Nat.add_sub_cancel_left]; exact h2
      rw [← key]
      split <;> rename_i hh <;> simp [hh]
  have ho : ∀ G < kb.toNat, ∀ j < kc.toNat, ∃ v : UInt64, (raw .i64 (kb * kc) o)[G * kc.toNat + j]? = some v ∧
      v < 2 ∧ (v = 1 ↔ P G j) := fun G hG j hj => by
    obtain ⟨v, -, hv, hv2, hv1⟩ := hbit G hG j hj
    refine ⟨v, hv, hv2, hv1.trans ?_⟩
    simp only [if_true]
    constructor
    · intro H
      refine ⟨fun i hi hiG => ?_, fun Hn => ?_⟩
      · obtain ⟨t, ht, rfl⟩ := hπs i (by omega)
        have := (hon j hj t ht).1 (H t ((hseg G hG t).2 ⟨ht, by simp only [gr, if_pos hi]; exact hiG⟩).1
          ((hseg G hG t).2 ⟨ht, by simp only [gr, if_pos hi]; exact hiG⟩).2)
        rwa [if_pos hi] at this
      · obtain ⟨e, he, heG⟩ := heb2 G hG Hn
        obtain ⟨t, ht, hπt⟩ := hπs (R.n.toNat + e) (by omega)
        have hs := (hseg G hG t).2 ⟨ht, by
          simp only [gr]; rw [hπt, if_neg (by omega), Nat.add_sub_cancel_left]; exact heG⟩
        have := (hon j hj t ht).1 (H t hs.1 hs.2)
        rwa [hπt, if_neg (by omega)] at this
    · rintro ⟨P1, P2⟩ t h1 h2
      obtain ⟨ht, hgt⟩ := (hseg G hG t).1 ⟨h1, h2⟩
      have hπn := (hπx t ht).1
      rw [hon j hj t ht]
      simp only [gr] at hgt
      split
      · rename_i hh; rw [if_pos hh] at hgt; exact P1 _ hh hgt
      · rename_i hh; rw [if_neg hh] at hgt
        exact P2 fun i hi e => (heb1 _ (by omega)).2 i hi (e.trans hgt.symm)
  rw [hX P hgw hb63 ho]
  show _ ↔ (∀ a, R.Holds a b → S.Holds a c) ∧ ((∃ a, R.Holds a b) ∨ ((∃ b', UB.Holds b' b) ∧ ∃ c', UC.Holds c' c))
  constructor
  · rintro ⟨G, hG, j, hj, ⟨P1, P2⟩, ⟨i0, h0, r0⟩, ⟨i1, h1, r1⟩⟩
    obtain ⟨t, ht, hexb, hxb, hub⟩ := hrb G hG
    obtain ⟨t', ht', -, hxc, huc⟩ := hrc j hj
    obtain rfl : t = i0 := Fin.ext (ht.symm.trans h0)
    obtain rfl : t' = i1 := Fin.ext (ht'.symm.trans h1)
    refine ⟨fun a ⟨i, hi1, hi2⟩ => ?_, ?_⟩
    · obtain ⟨s, hs, hs1, hs2⟩ := P1 i i.2 ((hxb i).2 (hi2.trans r0.symm))
      exact ⟨⟨s, hs⟩, ((haxs i ⟨s, hs⟩).1 hs1.symm).symm.trans hi1, ((hxc ⟨s, hs⟩).1 hs2).trans r1⟩
    · by_cases hR : ∃ i : Fin R.n.toNat, bx i = G
      · obtain ⟨i, hi⟩ := hR
        exact .inl ⟨R.key.row i, i, rfl, ((hxb i).1 hi).trans r0⟩
      · obtain ⟨u, hu, hcu'⟩ := P2 fun i hi e => hR ⟨⟨i, hi⟩, e⟩
        obtain ⟨u', hu'⟩ := hexb.resolve_left hR
        exact .inr ⟨⟨UB.key.row u', u', rfl, ((hub u').1 hu').trans r0⟩, UC.key.row ⟨u, hu⟩, ⟨u, hu⟩, rfl,
          ((huc ⟨u, hu⟩).1 hcu').trans r1⟩
  · rintro ⟨H1, H2⟩
    -- `b` has a number `G` (a row of `R` or `UB` valued `b`), `c` a number `j` (a row of `S` or `UC`)
    have hB : ∃ G < kb.toNat, (∃ i : Fin R.n.toNat, bx i = G ∧ R.val.row i = b) ∨
        ∃ u : Fin UB.n.toNat, bu u = G ∧ UB.val.row u = b := by
      rcases H2 with ⟨a, i, -, hi⟩ | ⟨⟨b', u, -, hu⟩, -⟩
      · exact ⟨bx i, (hbx i i.2).2, .inl ⟨i, rfl, hi⟩⟩
      · exact ⟨bu u, (hbu u u.2).2, .inr ⟨u, rfl, hu⟩⟩
    have hC : ∃ j < kc.toNat, (∃ s : Fin S.n.toNat, cs s = j ∧ S.val.row s = c) ∨
        ∃ u : Fin UC.n.toNat, cu u = j ∧ UC.val.row u = c := by
      rcases H2 with ⟨a, i, hi1, hi2⟩ | ⟨-, c', u, -, hu⟩
      · obtain ⟨s, -, hs⟩ := H1 a ⟨i, hi1, hi2⟩
        exact ⟨cs s, (hcs s s.2).2, .inl ⟨s, rfl, hs⟩⟩
      · exact ⟨cu u, (hcu u u.2).2, .inr ⟨u, rfl, hu⟩⟩
    obtain ⟨G, hG, hGb⟩ := hB
    obtain ⟨j, hj, hjc⟩ := hC
    obtain ⟨t, ht, -, hxb, hub⟩ := hrb G hG
    obtain ⟨t', ht', -, hxc, huc⟩ := hrc j hj
    have zb_b : zb.row t = b := by
      rcases hGb with ⟨i, hi, e⟩ | ⟨u, hu, e⟩
      · exact ((hxb i).1 hi).symm.trans e
      · exact ((hub u).1 hu).symm.trans e
    have zc_c : zc.row t' = c := by
      rcases hjc with ⟨s, hs, e⟩ | ⟨u, hu, e⟩
      · exact ((hxc s).1 hs).symm.trans e
      · exact ((huc u).1 hu).symm.trans e
    refine ⟨G, hG, j, hj, ⟨fun i hi hiG => ?_, fun Hn => ?_⟩, ⟨t, ht, zb_b⟩, ⟨t', ht', zc_c⟩⟩
    · obtain ⟨s, hs1, hs2⟩ := H1 (R.key.row ⟨i, hi⟩) ⟨⟨i, hi⟩, rfl, ((hxb ⟨i, hi⟩).1 hiG).trans zb_b⟩
      exact ⟨s, s.2, ((haxs ⟨i, hi⟩ s).2 hs1.symm).symm, (hxc s).2 (hs2.trans zc_c.symm)⟩
    · rcases H2 with ⟨a, i, -, hi⟩ | ⟨-, c', u, -, hu⟩
      · exact absurd ((hxb i).2 (hi.trans zb_b.symm)) (Hn i i.2)
      · exact ⟨u, u.2, (huc u).2 (hu.trans zc_c.symm)⟩

/-- **`ldivBits` is `ldiv`** on the pairs it holds: the fused kernel answers what the composition of primitives does. -/
theorem Tab.ldivBits_ldiv {R : Tab A B} {S : Tab A C} {UB : Tab B B} {UC : Tab C C} {T T' : Tab B C}
    (h : Tab.ldivBits R S UB UC = .ok T) (h' : Tab.ldiv R S UB UC = .ok T')
    (hR : R.WF) (hS : S.WF) (hUB : UB.WF) (hUC : UC.WF) : T.Holds = T'.Holds :=
  funext fun b => funext fun c => propext ((Tab.ldivBits_holds h hR hS hUB hUC b c).trans (Tab.ldiv_holds h' hR hS hUB hUC b c).symm)

/-- **`R.compSel bits S` denotes `R ≫ S`** at every `bits`: its bit branch by `Tab.compBits_holds`, its other by
`Tab.compFrom_canon`. -/
theorem Tab.compSel_holds {bits : Nat} {R : Tab A B} {S : Tab B C} {X : Tab A C} (h : Tab.compSel bits R S = .ok X)
    (hR : R.WF) (hS : S.WF) (a : A.El) (c : C.El) : X.Holds a c ↔ ∃ b, R.Holds a b ∧ S.Holds b c := by
  simp only [Tab.compSel, bind] at h
  rw [Except.bind_eq_ok'] at h; obtain ⟨e, he, h⟩ := h
  simp only [Tab.compSelM, bind] at he
  rw [Except.bind_eq_ok'] at he; obtain ⟨x, hx, he⟩ := he
  rw [Except.bind_eq_ok'] at he; obtain ⟨T, -, he⟩ := he
  have hF : ∀ {Y : Tab A C}, Tab.compFrom Tab.blockRows R S x = .ok Y → e = .inl Y →
      (X.Holds a c ↔ ∃ b, R.Holds a b ∧ S.Holds b c) := fun hY hp => by
    subst hp; simp only [pure, Except.pure, Except.ok.injEq] at h; subst h
    obtain ⟨U, hU, hUw, hH⟩ := Tab.compFrom_canon hx hY hR hS; rw [Tab.canon_holds hU hUw]; exact hH a c
  have hP : ∀ {Y : Tab A C}, (pure (Sum.inl Y) : Except String _) = .ok e → e = .inl Y := fun he => by
    simp only [pure, Except.pure, Except.ok.injEq] at he; exact he.symm
  split at he
  · rw [Except.bind_eq_ok'] at he; obtain ⟨Y, hY, he⟩ := he; exact hF hY (hP he)
  · rw [Except.bind_eq_ok'] at he; obtain ⟨_, -, he⟩ := he
    rw [Except.bind_eq_ok'] at he; obtain ⟨_, -, he⟩ := he
    split at he
    · rw [Except.bind_eq_ok'] at he; obtain ⟨m, hm, he⟩ := he
      cases he
      refine Tab.compBits_holds ?_ hR hS a c
      simp only [Tab.compBits, bind]; rw [hm]; exact h
    · rw [Except.bind_eq_ok'] at he; obtain ⟨Y, hY, he⟩ := he; exact hF hY (hP he)

/-- **`R.ldivSel d bits S UB UC` denotes `R\S` within `UB`, `UC`** at every `bits`, where the division `d` does on
`R`, `S`: its bit branch by `Tab.ldivBits_holds`, its other by `hd`. -/
theorem Tab.ldivSel_holdsBy {d : Tab A B → Tab A C → Tab B B → Tab C C → Except String (Tab B C)} {bits : Nat}
    {R : Tab A B} {S : Tab A C} {UB : Tab B B} {UC : Tab C C} {T : Tab B C}
    (hd : ∀ {T}, d R S UB UC = .ok T → ∀ b c, T.Holds b c ↔ Lang.ldivDen R.Holds S.Holds UB.Holds UC.Holds b c)
    (h : Tab.ldivSel d bits R S UB UC = .ok T) (hR : R.WF) (hS : S.WF) (hUB : UB.WF) (hUC : UC.WF)
    (b : B.El) (c : C.El) :
    T.Holds b c ↔ Lang.ldivDen R.Holds S.Holds UB.Holds UC.Holds b c := by
  simp only [Tab.ldivSel, bind] at h
  rw [Except.bind_eq_ok'] at h; obtain ⟨x, -, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨_, -, h⟩ := h
  split at h
  · exact hd h b c
  · rw [Except.bind_eq_ok'] at h; obtain ⟨_, -, h⟩ := h
    rw [Except.bind_eq_ok'] at h; obtain ⟨_, -, h⟩ := h
    split at h
    · exact Tab.ldivBits_holds h hR hS hUB hUC b c
    · exact hd h b c

/-- **`R.ldivSel ldiv bits S UB UC` denotes `R\S` within `UB`, `UC`**: `ldivSel_holdsBy` with `Tab.ldiv_holds`. -/
theorem Tab.ldivSel_holds {bits : Nat} {R : Tab A B} {S : Tab A C} {UB : Tab B B} {UC : Tab C C} {T : Tab B C}
    (h : Tab.ldivSel Tab.ldiv bits R S UB UC = .ok T) (hR : R.WF) (hS : S.WF) (hUB : UB.WF) (hUC : UC.WF)
    (b : B.El) (c : C.El) :
    T.Holds b c ↔ Lang.ldivDen R.Holds S.Holds UB.Holds UC.Holds b c :=
  Tab.ldivSel_holdsBy (fun h => Tab.ldiv_holds h hR hS hUB hUC) h hR hS hUB hUC b c

end Rel
