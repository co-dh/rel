import Rel.RepTabDiv
import Rel.Lang.GenKFold

/-! The law of `Tab.positions` (`Rel/Run/Where.lean`): each array to `positionsL` of its elements' test. -/

namespace Rel
open Rel.Ext Rel.Kernel Rel.Verify Ext.Enc Rel.Rep

/-- The rows below `Σ_{<i} w`, filtered, are the runs before `i` filtered one after another. -/
theorem filter_runs (wN : Nat → Nat) (keep : Nat → Bool) : ∀ i,
    (List.range ((List.range i).map wN).sum).filter keep =
      ((List.range i).map fun g => (List.range' ((List.range g).map wN).sum (wN g)).filter keep).flatten
  | 0 => by simp
  | i + 1 => by
    rw [sum_range_succ', List.range_succ, List.map_append, List.flatten_append, ← filter_runs wN keep i,
      List.range_eq_range', List.range_eq_range', ← List.range'_append_1, List.filter_append]
    simp only [List.range_eq_range', Nat.zero_add, List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil,
      List.append_nil]

/-- Element `d` of run `i` sits at `Σ_{<i} |F g| + d` of the runs laid one after another. -/
theorem getElem?_flatten_runs {α : Type} (F : Nat → List α) : ∀ n i d, i < n → d < (F i).length →
    ((List.range n).map F).flatten[((List.range i).map fun g => (F g).length).sum + d]? = (F i)[d]?
  | 0, _, _, h, _ => absurd h (Nat.not_lt_zero _)
  | n + 1, i, d, hi, hd => by
    have hlen : (((List.range n).map F).flatten).length = ((List.range n).map fun g => (F g).length).sum := by
      simp [List.length_flatten, List.map_map, Function.comp_def]
    rw [List.range_succ, List.map_append, List.flatten_append]
    by_cases c : i < n
    · have := sum_range_mono (fun g => (F g).length) (show i + 1 ≤ n by omega)
      rw [sum_range_succ'] at this; simp only at this
      rw [List.getElem?_append_left (by rw [hlen]; omega), getElem?_flatten_runs F n i d c hd]
    · obtain rfl : i = n := by omega
      rw [List.getElem?_append_right (by rw [hlen]; omega), hlen]; simp

namespace Tab

open Classical in
/-- **`positions P X` denotes `positionsL`** of the test `∃ y, P x y` on each array of `X`: the kept element rows
(`whereCol_spec`) are the runs of the cells (`expand_spec`) filtered one after another (`filter_runs`), each cell's
count of them (`kscatter .add`) its width, so cell `i` reads its own run's kept rows, as offsets `u`. The counts sum
to the `K` kept rows, so the new cells lie inside the payload: `positions` keeps `Tab.WF` (`Vals.cells_wf`). -/
theorem positions_spec {B : Obj} {n : USize} {P : Tab B B} {X : Vals (.arr B) n} {res : Tab (.arr B) (.arr .long)}
    (h : Tab.positions P X = .ok res) (wP : P.WF) (wX : Vals.WF X) : (∀ xs ys, res.Holds xs ys ↔
      (∃ i, X.row i = xs) ∧ ys = positionsL (fun x => decide (∃ y, P.Holds x y)) xs) ∧ res.WF := by
  obtain ⟨m, lo, up, f⟩ := X
  dsimp only [Tab.positions] at h
  split at h; · cases h
  rename_i hb
  simp only [bind] at h
  rw [Except.bind_eq_ok'] at h; obtain ⟨_, -, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨w, hw, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨⟨T, G, u⟩, hex, h⟩ := h; try dsimp only at h
  rw [Except.bind_eq_ok'] at h; obtain ⟨sg, hsg, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨ix, hix, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨v, hv, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨D, hD, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨ia, hia, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨cD, hcD, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨b, hbm, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨⟨K, sel⟩, hwh, h⟩ := h; try dsimp only at h
  rw [Except.bind_eq_ok'] at h; obtain ⟨gs, hgs, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨z, hz, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨pay, hpay, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨cnt, hcnt, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨Y, hY, h⟩ := h
  have hm63 : m.toNat < 2 ^ 63 := by omega
  have hn63 : n.toNat < 2 ^ 63 := by omega
  have hnm : n.toNat * m.toNat < 2 ^ 63 := by omega
  have hU64 : USize.size ≤ 2 ^ 64 := by rcases USize.size_eq with h | h <;> omega
  obtain ⟨SN, EN, hse', hb1, hrow⟩ := cellSpan_spec wX.1 hm63 f
  obtain ⟨wN, hwN⟩ : ∃ F : Nat → Nat, ∀ i, F i = EN i - SN i := ⟨_, fun _ => rfl⟩
  have hww : ∀ i < n.toNat, (raw .i64 n w)[i]?.getD 0 = (wN i).toUInt64 := by
    intro i hi
    have es := (colMap_raw hw).2.2.2 i hi
    rw [(hse' i hi).2, (hse' i hi).1] at es; simp only [Op.eval, Except.ok.injEq] at es
    rw [← es, hwN, toUInt64_sub (hb1 i).1]
  have hwm : ∀ i, wN i ≤ m.toNat := fun i => by have := hb1 i; rw [hwN]; omega
  have hsum : ∀ k, ((List.range k).map wN).sum ≤ k * m.toNat := fun k => by
    induction k with
    | zero => simp
    | succ k ih => rw [sum_range_succ', Nat.succ_mul]; have := hwm k; omega
  have hsn : ((List.range n.toNat).map wN).sum < 2 ^ 63 := by have := hsum n.toNat; omega
  obtain ⟨hTn, hrun⟩ := expand_spec hex wN hww hsn hn63
  -- the element at row `Σ_{<g} w + d` is cell `g`'s element `d`
  have hvt : ∀ g < n.toNat, ∀ d < wN g, ∀ (ht : ((List.range g).map wN).sum + d < T.toNat)
      (hd : SN g + d < m.toNat), Vals.row v ⟨_, ht⟩ = Vals.row f ⟨_, hd⟩ := by
    intro g hg d hdw ht hd
    obtain ⟨j, hj, hvj⟩ := Vals.gather_row f hv ⟨_, ht⟩
    rw [hvj]; congr 1; apply Fin.ext; rw [← hj]
    have hgS : ((List.range g).map wN).sum + wN g ≤ ((List.range n.toNat).map wN).sum := by
      rw [← sum_range_succ']; exact sum_range_mono wN hg
    obtain ⟨hG, hu⟩ := hrun g hg (((List.range g).map wN).sum + d) (by omega) (by omega)
    have es := (colMap_raw hix).2.2.2 _ ht
    rw [(kgather_word hsg _ ht).2, hG, toNat_toUInt64 (by omega), (hse' g hg).1, hu] at es
    simp only [Op.eval, Except.ok.injEq] at es
    rw [← es, ← UInt64.ofNat_add, Nat.add_sub_cancel_left, toNat_toUInt64 (by omega)]
  -- the test word of row `t`: `1` where its element is a key of `D = dom P`
  have hbt : ∀ t (ht : t < T.toNat), (raw .i64 T b)[t]?.getD 0 =
      if ∃ y, P.Holds (Vals.row v ⟨t, ht⟩) y then 1 else 0 := by
    intro t ht
    have es : (Except.ok (if ((raw .i64 T ia)[t]?.getD 0 != D.n.toUInt64) = true then (1 : UInt64) else 0) :
        Except String UInt64) = .ok ((raw .i64 T b)[t]?.getD 0) := by
      have := (colMap_raw hbm).2.2.2 t ht
      rwa [colConst_raw hcD, Array.getElem?_replicate, if_pos ht, Option.getD_some] at this
    rw [← Except.ok.inj es]
    have hDn := D.n.toNat_lt_size
    rcases Tab.index_spec hia (Tab.dom_wf hD wP).1 (Vals.gather_wf hv wX.2) ⟨t, ht⟩ with ⟨a, ea, hra⟩ | ⟨ea, hno⟩
    · have hk : ∃ y, P.Holds (Vals.row v ⟨t, ht⟩) y := ((Tab.dom_holds hD _ _).1 ⟨a, hra, rfl⟩).2
      have hne : (raw .i64 T ia)[t]?.getD 0 ≠ D.n.toUInt64 := fun c => by
        have := congrArg UInt64.toNat c; rw [ea, USize.toNat_toUInt64] at this; omega
      simp [hk, hne]
    · have hk : ¬∃ y, P.Holds (Vals.row v ⟨t, ht⟩) y := fun c => by
        obtain ⟨a, ha, -⟩ := (Tab.dom_holds hD _ _).2 ⟨rfl, c⟩; exact hno a ha
      have heq : (raw .i64 T ia)[t]?.getD 0 = D.n.toUInt64 := by
        apply UInt64.toNat_inj.mp; rw [ea, USize.toNat_toUInt64]
      simp [hk, heq]
  obtain ⟨keep, hkeep⟩ : ∃ F : Nat → Bool, ∀ t, F t = decide ((raw .i64 T b)[t]?.getD 0 ≠ 0) := ⟨_, fun _ => rfl⟩
  have hb2 : ∀ t < T.toNat, (raw .i64 T b)[t]?.getD 0 < 2 := fun t ht => by rw [hbt t ht]; split <;> decide
  have hb01 : ∀ t < T.toNat, (raw .i64 T b)[t]?.getD 0 = if keep t then 1 else 0 := fun t ht => by
    have e := hbt t ht; rw [hkeep]; split at e <;> simp [e]
  -- the kept rows, ascending
  have hL := whereCol_spec hwh hb2
  have hsz := whereCol_size hwh
  have hKT := whereCol_le hwh hb2
  have hruns := filter_runs wN keep n.toNat
  rw [← hTn] at hruns
  obtain ⟨off, hoff⟩ : ∃ F : Nat → Nat, ∀ g, F g = ((List.range g).map wN).sum := ⟨_, fun _ => rfl⟩
  obtain ⟨cN, hcN⟩ : ∃ F : Nat → Nat, ∀ g, F g = ((List.range' (off g) (wN g)).filter keep).length :=
    ⟨_, fun _ => rfl⟩
  simp only [← hoff] at hrun hTn hruns hvt
  -- the rows naming cell `g` are its run
  have hfilt : ∀ g < n.toNat, (List.range T.toNat).filter (fun k => ((raw .i64 T G)[k]?.getD 0).toNat = g) =
      List.range' (off g) (wN g) := fun g hg => by
    rw [hoff]; exact expand_group_run hex wN hww hsn hn63 g hg
  -- each cell's width is its count of kept rows
  obtain ⟨hGs, -, hcw⟩ := kscatter_words hcnt
  obtain ⟨-, hcf⟩ := scatterWords_fold (f := (· + ·)) (fun _ _ => rfl) hcw
  rw [hGs] at hcf
  have hcn : ∀ g < n.toNat, (raw .i64 n cnt)[g]?.getD 0 = (cN g).toUInt64 := fun g hg => by
    rw [hcf g hg, hfilt g hg]
    have e : (List.range' (off g) (wN g)).map ((raw .i64 T b)[·]?.getD 0) =
        (List.range' (off g) (wN g)).map fun t => if keep t then (1 : UInt64) else 0 := by
      apply List.map_congr_left; intro t ht; rw [List.mem_range'_1] at ht
      have : off g + wN g ≤ T.toNat := by rw [hTn, hoff, hoff, ← sum_range_succ']; exact sum_range_mono wN hg
      exact hb01 t (by omega)
    rw [e, foldl_add_count, UInt64.zero_add, List.countP_eq_length_filter, hcN]
  -- the kept rows are the runs' kept rows one after another, `Σ_{<n} cN` of them
  have hLk : (raw .i64 K sel).toList.map UInt64.toNat =
      ((List.range n.toNat).map fun g => (List.range' (off g) (wN g)).filter keep).flatten := by
    rw [hL, hTn, ← hruns, hTn]; exact List.filter_congr fun t _ => (hkeep t).symm
  have hK : K.toNat = ((List.range n.toNat).map cN).sum := by
    have := congrArg List.length hLk
    rw [List.length_map, Array.length_toList, hsz, List.length_flatten, List.map_map] at this
    rw [this]; congr 1; apply List.map_congr_left; intro g _; exact (hcN g).symm
  have hsel : ∀ j (hj : j < K.toNat), ((raw .i64 K sel).toList.map UInt64.toNat)[j]? =
      some (((raw .i64 K sel)[j]?.getD 0).toNat) := fun j hj => by
    rw [List.getElem?_map, Array.getElem?_toList, Array.getElem?_eq_getElem (by omega)]; rfl
  have hpj : ∀ j (hj : j < K.toNat), Vals.row (A := .long) pay ⟨j, hj⟩ =
      ((raw .i64 T u)[((raw .i64 K sel)[j]?.getD 0).toNat]?.getD 0).toInt64 := fun j hj => by
    have es := (colMap_raw (colArr_ok hpay)).2.2.2 j hj
    rw [colConst_raw hz, Array.getElem?_replicate, if_pos hj, Option.getD_some, (kgather_word hgs j hj).2] at es
    simp only [Op.eval, Except.ok.injEq, UInt64.add_zero] at es
    rw [Vals.row_atom, Arr.get_i64, ← es]
  have hTo : T.toNat < 2 ^ 63 := by rw [hTn, hoff]; exact hsn
  suffices hY' : ∀ i : Fin n.toNat, Vals.row Y i =
      positionsL (fun x => decide (∃ y, P.Holds x y)) (Vals.row (A := .arr B) ⟨m, lo, up, f⟩ i) by
    refine ⟨fun xs ys => ?_,
      canon_wf h ⟨wX, Vals.cells_wf hY cN hcn (by rw [hK]; exact Nat.le_refl _) (by omega) trivial⟩⟩
    rw [canon_holds h]
    simp only [Tab.Holds]
    constructor
    · rintro ⟨i, rfl, rfl⟩; exact ⟨⟨i, rfl⟩, hY' i⟩
    · rintro ⟨⟨i, rfl⟩, rfl⟩; exact ⟨i, rfl, hY' i⟩
  intro i
  have hiS : off i.1 + wN i.1 ≤ T.toNat := by rw [hTn, hoff, hoff, ← sum_range_succ']; exact sum_range_mono wN i.2
  have hpos : ∀ d < wN i.1, keep (off i.1 + d) =
      (Vals.row (A := .arr B) ⟨m, lo, up, f⟩ i)[d]?.any (fun x => decide (∃ y, P.Holds x y)) := fun d hd => by
    have hd' : SN i.1 + d < m.toNat := by have := hb1 i.1; rw [hwN] at hd; omega
    have ht : off i.1 + d < T.toNat := by omega
    have hdl : d < (Vals.row (A := .arr B) ⟨m, lo, up, f⟩ i).length := by
      rw [hrow i, List.length_map, List.length_range', ← hwN]; exact hd
    have hx : (Vals.row (A := .arr B) ⟨m, lo, up, f⟩ i)[d] = Vals.row f ⟨SN i.1 + d, hd'⟩ := by
      simp only [hrow i, List.getElem_map, List.getElem_range', Nat.one_mul, dif_pos hd']
    rw [List.getElem?_eq_getElem hdl, Option.any_some, hx, ← hvt i.1 i.2 d hd ht hd', hkeep, hbt _ ht]
    by_cases c : ∃ y, P.Holds (Vals.row v ⟨off i.1 + d, ht⟩) y <;> simp [c]
  have hxl : (Vals.row (A := .arr B) ⟨m, lo, up, f⟩ i).length = wN i.1 := by
    rw [hrow i, List.length_map, List.length_range', hwN]
  have hF : ((List.range' (off i.1) (wN i.1)).filter keep).map (· - off i.1) =
      (List.range (wN i.1)).filter fun d => keep (off i.1 + d) := by
    rw [List.range'_eq_map_range, List.filter_map, List.map_map]
    conv => rhs; rw [← List.map_id ((List.range (wN i.1)).filter fun d => keep (off i.1 + d))]
    apply List.map_congr_left; intro d _; simp
  rw [Vals.cells_row hY cN hcn (by rw [hK]; exact Nat.le_refl _) (by omega) i, positionsL, hxl,
    List.filter_congr (fun d hd => (hpos d (List.mem_range.1 hd)).symm), ← hF, List.map_map]
  apply List.ext_getElem (by simp [hcN])
  intro d h1 h2
  have hdc : d < cN i.1 := by simpa using h1
  have hlt : ((List.range i.1).map cN).sum + d < K.toNat := by
    rw [hK]; have := sum_range_mono cN (show i.1 + 1 ≤ n.toNat from i.2); rw [sum_range_succ'] at this; omega
  have hd2 : d < ((List.range' (off i.1) (wN i.1)).filter keep).length := by rw [← hcN]; exact hdc
  have hFd := getElem?_flatten_runs (fun g => (List.range' (off g) (wN g)).filter keep) n.toNat i.1 d i.2 hd2
  simp only [← hcN] at hFd
  rw [← hLk, hsel _ hlt, List.getElem?_eq_getElem hd2, Option.some.injEq] at hFd
  have hmem := List.getElem_mem hd2
  rw [List.mem_filter, List.mem_range'_1] at hmem
  simp only [List.getElem_map, List.getElem_range', Nat.one_mul, dif_pos hlt, hpj _ hlt, hFd, Function.comp_apply]
  rw [(hrun i.1 i.2 _ hmem.1.1 hmem.1.2).2]; rfl

end Tab

namespace Lang.GenK

open Classical in
/-- `positions(p)`, `Expand.primE`'s fit of the row (`elems`, `Tab.positions`): each array in demand to the positions
of its elements in `dom T` (`elemsTest_sound`). -/
theorem positions_sound {B : Obj} {R : Rel B B} {T : Den B B} (hR : ∀ K, K.WF → R.Reps K T) (wR : R.Wf) :
    ∀ K, K.WF → (GenK.elems B B (.arr .long) R fun P X => Tab.positions P X).Reps K
      (fun xs ys => ys = positionsL (fun x => decide (∃ y, T x y)) xs) :=
  elemsTest_sound (C := .arr .long) (F := fun p (xs : List B.El) => positionsL p xs)
    (fun h wP wX xs ys => (Tab.positions_spec h wP wX).1 xs ys)
    (fun p q xs h => by
      simp only [positionsL]; congr 1; exact List.filter_congr fun t _ => by
        cases e : xs[t]? with
        | none => rfl
        | some x => simp only [Option.any_some]; exact h x (List.mem_of_getElem? e)) hR wR

end Lang.GenK

end Rel
