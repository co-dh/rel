import Rel.Run.Div
import Rel.RepCanon
import Rel.RepSetOps
import Rel.RepTabComp
import Rel.Run.Alg
import Rel.Lang.Den

/-! The laws of the operators of `Rel/Run/Div.lean` (`ldiv`, `rdiv`, `lam`, `E`, `nil`, `lt`, `leq`), and their
checks against the old layer (`Alg.leftDivC`, `rightDivC`, `lamOnC`, `memC`, `EC`, `nil`, `ltC`, `leqC`) on the same
`foR` tables, as sets. -/

namespace Rel
open Rel.Ext Rel.Kernel Rel.Verify Ext.Enc

namespace Tab
variable {A B C : Obj}

/-- **`nil D` denotes `nilDen` on `D`**: each key of `D` to the empty array. -/
theorem nil_holds {n : USize} {D : Vals A n} {T : Tab A (.arr B)} (h : Tab.nil D = .ok T) (a : A.El)
    (ys : List B.El) : T.Holds a ys ↔ (∃ i, D.row i = a) ∧ ys = [] := by
  unfold Tab.nil at h; simp only [bind, Except.bind] at h
  split at h; · cases h
  split at h; · cases h
  rw [canon_holds h]
  simp only [Tab.Holds, Vals.row]
  exact ⟨fun ⟨i, h1, h2⟩ => ⟨⟨i, h1⟩, h2.symm⟩, fun ⟨⟨i, h1⟩, h2⟩ => ⟨i, h1, h2.symm⟩⟩

/-- **`cross X Y` denotes `X × Y`**: every pair of a row of `X` and a row of `Y`. Output row `t` reads `X` at
`t div m` and `Y` at `t mod m` (`eval_div_nat`, `eval_mod_nat`); the pair `(i, j)` is row `j + i·m`. -/
theorem cross_holds {n m : USize} {X : Vals A n} {Y : Vals B m} {T : Tab A B} (h : cross X Y = .ok T) (a : A.El)
    (b : B.El) : T.Holds a b ↔ (∃ i, X.row i = a) ∧ ∃ j, Y.row j = b := by
  unfold cross at h
  split at h; · cases h
  rename_i hb
  simp only [bind, Except.bind] at h
  split at h; · cases h
  split at h; · cases h
  rename_i mc hmc
  split at h; · cases h
  rename_i dv hdv
  split at h; · cases h
  rename_i x hx
  split at h; · cases h
  rename_i mv hmv
  split at h; · cases h
  rename_i y hy
  rw [canon_holds h]
  have hU : USize.size ≤ 2 ^ 64 := by rcases USize.size_eq with h | h <;> omega
  have hT : (n.toNat * m.toNat).toUSize.toNat = n.toNat * m.toNat := by
    rw [Nat.toUSize]; exact USize.toNat_ofNat_of_lt (by omega)
  constructor
  · rintro ⟨t, rfl, rfl⟩
    obtain ⟨i, -, hi⟩ := Vals.gather_row X hx t
    obtain ⟨j, -, hj⟩ := Vals.gather_row Y hy t
    exact ⟨⟨i, hi.symm⟩, ⟨j, hj.symm⟩⟩
  · rintro ⟨⟨i, rfl⟩, ⟨j, rfl⟩⟩
    have hm : 0 < m.toNat := by have := j.2; omega
    have hn : 0 < n.toNat := by have := i.2; omega
    have hmn := Nat.le_mul_of_pos_left m.toNat hn
    have hlt : j.1 + i.1 * m.toNat < n.toNat * m.toNat := by
      have := Nat.mul_le_mul_right m.toNat (show i.1 + 1 ≤ n.toNat from i.2); rw [Nat.succ_mul] at this; omega
    have ht : j.1 + i.1 * m.toNat < (n.toNat * m.toNat).toUSize.toNat := by rw [hT]; exact hlt
    have hw : ∀ (op : Op) (e : Enc) (r : Nat), colMap op (n.toNat * m.toNat).toUSize .pos mc = .ok e →
        Op.eval op (j.1 + i.1 * m.toNat).toUInt64 m.toNat.toUInt64 = .ok r.toUInt64 → r < 2 ^ 64 →
        ((raw .i64 (n.toNat * m.toNat).toUSize e)[j.1 + i.1 * m.toNat]?.getD 0).toNat = r := by
      intro op e r he hr hr64
      obtain ⟨-, -, -, hev⟩ := colMap_raw he
      have := hev _ ht
      rw [raw_pos_word ht, colConst_raw hmc, Array.getElem?_replicate, if_pos ht, Option.getD_some, hr] at this
      rw [← Except.ok.inj this, toNat_toUInt64 hr64]
    have hd := hw .div dv i.1 hdv (by
      rw [eval_div_nat (by omega) (by omega) hm, Nat.add_mul_div_right _ _ hm, Nat.div_eq_of_lt j.2, Nat.zero_add])
      (by have := n.toNat_lt_size; omega)
    have hmo := hw .mod mv j.1 hmv (by
      rw [eval_mod_nat (by omega) (by omega) hm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt j.2])
      (by have := m.toNat_lt_size; omega)
    obtain ⟨i', hi', hxi⟩ := Vals.gather_row X hx ⟨_, ht⟩
    obtain ⟨j', hj', hyj⟩ := Vals.gather_row Y hy ⟨_, ht⟩
    have e1 : i' = i := Fin.ext (by rw [← hi', hd])
    have e2 : j' = j := Fin.ext (by rw [← hj', hmo])
    subst e1 e2
    exact ⟨⟨_, ht⟩, hxi, hyj⟩

end Tab

/-- **`whereCol` answers `K` words** (to move beside `whereCol_spec`, `Rel/RepSetOps.lean`): its last step is a
`kgather` of `K` rows. -/
theorem whereCol_size {m K : USize} {b o : Enc} (h : whereCol m b = .ok (K, o)) : (raw .i64 K o).size = K.toNat := by
  unfold whereCol at h
  have hB : m.toNat < min (USize.size - 1) (2 ^ 63) := by
    refine Classical.byContradiction fun hn => ?_; simp only [hn, if_false] at h; cases h
  simp only [hB, if_true, bind, Except.bind, Functor.map, Except.map] at h
  repeat (split at h; · cases h)
  rename_i o' ho'
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj h).symm
  obtain ⟨his, -, -, hoe⟩ := raw_kgather _ _ _ _ _ ho'
  rw [hoe, (wordsFoR_closed _ (by rw [Array.size_map, his])).2.1, Array.size_map, his]

/-- The signed reading of a word: itself below `2^63`, itself less `2^64` from there (to move beside `toInt64_toInt`,
`Rel/RepTabComp.lean`). -/
theorem toInt64_toInt_cond (x : UInt64) :
    x.toInt64.toInt = if x.toNat < 2 ^ 63 then (x.toNat : Int) else (x.toNat : Int) - 2 ^ 64 := by
  split
  · exact toInt64_toInt (by assumption)
  · rename_i hx
    have := x.toNat_lt
    simp only [UInt64.toInt64, Int64.toInt, Int64.toBitVec, BitVec.toInt_eq_toNat_cond, UInt64.toNat] at *
    rw [if_neg (by omega)]; simp

/-- **EXPAND places each group's run** (to move with `expand`): where word `g` of the `K` widths is `wN g`, below
`2^63` in total, there are `T = Σ wN` rows, and row `t` of group `g`'s run `[Σ_{<g} wN, Σ_{≤g} wN)` has group `g`
and offset `t - Σ_{<g} wN`. -/
theorem expand_spec {K T : USize} {w G u : Enc} (h : expand K w = .ok (T, G, u)) (wN : Nat → Nat)
    (hw : ∀ g < K.toNat, (raw .i64 K w)[g]?.getD 0 = (wN g).toUInt64)
    (hs : ((List.range K.toNat).map wN).sum < 2 ^ 63) (hK : K.toNat < 2 ^ 63) :
    T.toNat = ((List.range K.toNat).map wN).sum ∧ ∀ g < K.toNat, ∀ t, ((List.range g).map wN).sum ≤ t →
      t < ((List.range g).map wN).sum + wN g → (raw .i64 T G)[t]?.getD 0 = g.toUInt64 ∧
        (raw .i64 T u)[t]?.getD 0 = (t - ((List.range g).map wN).sum).toUInt64 := by
  unfold expand at h
  split at h; · cases h
  rename_i P hP
  dsimp only at h
  split at h; · cases h
  rename_i hTU
  have hPf : ∃ md pk, P = .foR md pk := by
    unfold colPrefix at hP; simp only [bind, Except.bind] at hP; split at hP; · cases hP
    exact kscan_foR hP
  generalize hT : lastCount _ P _ = Tn at h hTU
  simp only [bind] at h
  rw [Except.bind_eq_ok'] at h; obtain ⟨_, -, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨o, ho, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨sc, hsc, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨pm, hpm, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨Gc, hGc, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨og, hog, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨u', hu, h⟩ := h
  simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl, rfl⟩ := h
  have hPw := colPrefix_add_sum hP wN hw
  have hSwm : ∀ g g', g < g' → ((List.range g).map wN).sum + wN g ≤ ((List.range g').map wN).sum :=
    fun g g' hg => by rw [← sum_range_succ']; exact sum_range_mono wN hg
  have hSwk : ∀ g ≤ K.toNat, ((List.range g).map wN).sum ≤ ((List.range K.toNat).map wN).sum :=
    fun g hg => sum_range_mono wN hg
  have hTn : Tn = ((List.range K.toNat).map wN).sum := hT.symm.trans (lastCount_eq _ hPf hs
    (fun hk0 => by rw [hPw (K.toNat - 1) (by omega), Nat.sub_add_cancel hk0])
    (fun hk0 => by rw [hk0]; rfl))
  have how : ∀ g < K.toNat, (raw .i64 K o)[g]?.getD 0 = ((List.range g).map wN).sum.toUInt64 := fun g hg => by
    have e := (colMap_raw ho).2.2.2 g hg
    rw [hPw g hg, hw g hg, sum_range_succ'] at e; simp only [Op.eval, Except.ok.injEq] at e
    rw [← e, ← toUInt64_sub (by omega), Nat.add_sub_cancel]
  have hTT : Tn.toUSize.toNat = Tn := USize.toNat_ofNat_of_lt' (by omega)
  have hT1 : (Tn.toUSize + 1).toNat = Tn + 1 := by
    rw [USize.toNat_add, hTT]; simp only [USize.toNat_one]
    exact Nat.mod_eq_of_lt (by have : USize.size = 2 ^ System.Platform.numBits := rfl; omega)
  refine ⟨by rw [hTT, hTn], fun g hg t h1 h2 => ?_⟩
  have := hSwm g K.toNat hg
  have htT : t < Tn.toUSize.toNat := by omega
  have hGw : (raw .i64 Tn.toUSize Gc)[t]?.getD 0 = g.toUInt64 := by
    obtain ⟨-, e⟩ := kgather_word hGc t htT
    rw [raw_pos_word htT, toNat_toUInt64 (by omega)] at e
    rw [e]
    obtain ⟨-, lo, alt⟩ := expand_groups hsc hpm (fun g => ((List.range g).map wN).sum) how
      (fun g hg => by dsimp only; have := hSwk g (by omega); omega) hK t (by omega)
    have lo' := lo g hg h1
    have hx : ((raw .i64 (Tn.toUSize + 1) pm)[t]?.getD 0).toNat = g := by
      rcases alt with e0 | ⟨G', hG', h3, e3⟩
      · omega
      · rcases Nat.lt_or_ge g G' with hl | hl
        · have := hSwm g G' hl; omega
        · omega
    rw [← hx]; simp
  refine ⟨hGw, ?_⟩
  have e := (colMap_raw hu).2.2.2 t htT
  rw [raw_pos_word htT, (kgather_word hog t htT).2, hGw, toNat_toUInt64 (by omega), how g hg] at e
  simp only [Op.eval, Except.ok.injEq] at e
  rw [← e, toUInt64_sub h1]

/-- A word whose signed reading is not negative is below `2^63` and reads as itself (to move with `toInt64_toInt_cond`). -/
theorem toInt64_nonneg {x : UInt64} (h : 0 ≤ x.toInt64.toInt) : x.toNat < 2 ^ 63 ∧ x.toInt64.toInt = x.toNat := by
  rw [toInt64_toInt_cond] at h ⊢
  have := x.toNat_lt
  split at h <;> rename_i hx
  · rw [if_pos hx]; exact ⟨hx, rfl⟩
  · omega

namespace Tab
variable {A B : Obj}

/-- **`keep T b` holds the rows of `T` whose word of `b` is `1`**, `b` holding `0`/`1` words: answer row `j` is input
row `sel[j]`, and `sel` lists every position of a `1` (`whereCol_spec`, `whereCol_size`). -/
theorem keep_holds {T U : Tab A B} {b : Enc} (h : T.keep b = .ok U)
    (hb : ∀ i < T.n.toNat, (raw .i64 T.n b)[i]?.getD 0 < 2) (a : A.El) (c : B.El) :
    U.Holds a c ↔ ∃ i : Fin T.n.toNat, (raw .i64 T.n b)[i.1]?.getD 0 ≠ 0 ∧ T.key.row i = a ∧ T.val.row i = c := by
  unfold keep at h; simp only [bind, Except.bind] at h
  split at h; · cases h
  rename_i Ms hMs; obtain ⟨M, sel⟩ := Ms
  split at h; · cases h
  rename_i x hx
  split at h; · cases h
  rename_i y hy
  cases h
  have hsel := whereCol_spec hMs hb
  have hsz := whereCol_size hMs
  simp only [Tab.Holds]
  constructor
  · rintro ⟨j, rfl, rfl⟩
    obtain ⟨i, hi, hxi⟩ := Vals.gather_row _ hx j
    obtain ⟨i', hi', hyi⟩ := Vals.gather_row _ hy j
    have e : i' = i := Fin.ext (by rw [← hi', hi])
    subst e
    have hj : j.1 < (raw .i64 M sel).size := by rw [hsz]; exact j.2
    have hGm := List.mem_map_of_mem (f := UInt64.toNat) (Array.getElem_mem_toList hj)
    rw [hsel, List.mem_filter, decide_eq_true_eq] at hGm
    rw [Array.getElem?_eq_getElem hj, Option.getD_some] at hi
    rw [hi] at hGm
    exact ⟨i', hGm.2, hxi.symm, hyi.symm⟩
  · rintro ⟨i, hbi, rfl, rfl⟩
    have hm : i.1 ∈ (raw .i64 M sel).toList.map UInt64.toNat := by
      rw [hsel, List.mem_filter, List.mem_range, decide_eq_true_eq]; exact ⟨i.2, hbi⟩
    obtain ⟨w, hw, hwi⟩ := List.mem_map.1 hm
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hw
    have hj' : j < (raw .i64 M sel).size := by simpa using hj
    have hjM : j < M.toNat := by rw [← hsz]; exact hj'
    simp only [Array.getElem_toList] at hwi
    have hsj : ((raw .i64 M sel)[j]?.getD 0).toNat = i.1 := by
      rw [Array.getElem?_eq_getElem hj', Option.getD_some, hwi]
    obtain ⟨i1, hi1, hx1⟩ := Vals.gather_row _ hx ⟨j, hjM⟩
    obtain ⟨i2, hi2, hy2⟩ := Vals.gather_row _ hy ⟨j, hjM⟩
    have e1 : i1 = i := Fin.ext (by rw [← hi1, hsj])
    have e2 : i2 = i := Fin.ext (by rw [← hi2, hsj])
    subst e1 e2
    exact ⟨⟨j, hjM⟩, hx1, hy2⟩

/-- **`cmpOn op U` is the pairs of `dom U` that `r` relates**, `op` testing `r` on the signed words: `keep` of
`cross` of the domain with itself, row `i` kept where `op` answers `1`. -/
theorem cmpOn_holds {op : Op} {r : Int64 → Int64 → Bool}
    (hop : ∀ x y : UInt64, op.eval x y = .ok (if r x.toInt64 y.toInt64 then 1 else 0))
    {U T : Tab .long .long} (h : cmpOn op U = .ok T) (a c : Int64) :
    T.Holds a c ↔ (∃ v, U.Holds a v) ∧ (∃ v, U.Holds c v) ∧ r a c = true := by
  unfold cmpOn at h; simp only [bind, Except.bind] at h
  split at h; · cases h
  rename_i d hd
  split at h; · cases h
  rename_i X hX
  split at h; · cases h
  rename_i w hw
  obtain ⟨-, -, -, hev⟩ := colMap_raw hw
  have hwv : ∀ i : Fin X.n.toNat, (raw .i64 X.n w)[i.1]?.getD 0 =
      if r (X.key.row i) (X.val.row i) then 1 else 0 := by
    intro i
    have := hev i.1 i.2
    rw [hop] at this
    rw [← Except.ok.inj this, Vals.row_atom, Vals.row_atom, Arr.get_i64, Arr.get_i64]
  have hdom : ∀ x : Int64, (∃ i, d.key.row i = x) ↔ ∃ v, U.Holds x v := fun x => by
    constructor
    · rintro ⟨i, rfl⟩; exact ((dom_holds hd _ _).1 ⟨i, rfl, rfl⟩).2
    · intro hv; obtain ⟨i, hi, -⟩ := (dom_holds hd x x).2 ⟨rfl, hv⟩; exact ⟨i, hi⟩
  rw [keep_holds h (fun i hi => by rw [hwv ⟨i, hi⟩]; split <;> decide), ← hdom a, ← hdom c, ← and_assoc,
    ← cross_holds hX a c]
  simp only [Tab.Holds]
  constructor
  · rintro ⟨i, hi, rfl, rfl⟩
    rw [hwv i] at hi
    exact ⟨⟨i, rfl, rfl⟩, by cases hr : r (X.key.row i) (X.val.row i) <;> simp_all⟩
  · rintro ⟨⟨i, rfl, rfl⟩, hr⟩
    exact ⟨i, by rw [hwv i, if_pos hr]; decide, rfl, rfl⟩

/-- **`lt U` denotes `ltDen`**: `<` on `dom U`. -/
theorem lt_holds {U T : Tab .long .long} (h : Tab.lt U = .ok T) (a c : Int64) :
    T.Holds a c ↔ Lang.ltDen U.Holds a c := by
  rw [cmpOn_holds (r := fun x y => decide (x < y)) (fun _ _ => rfl) h, decide_eq_true_eq]

/-- **`leq U` denotes `leqDen`**: `≤` on `dom U`. -/
theorem leq_holds {U T : Tab .long .long} (h : Tab.leq U = .ok T) (a c : Int64) :
    T.Holds a c ↔ Lang.leqDen U.Holds a c := by
  rw [cmpOn_holds (r := fun x y => decide (x ≤ y)) (fun _ _ => rfl) h, decide_eq_true_eq]

/-- **`mem X` denotes `∋` on the arrays `X`**: each cell of `X` to each of its elements. Cell `i` is `[s, e)` with
`s = max lo 0`, `e = max (min hi m) s` (`Vals.row` of an `arr` side reads `lo ≤ j < hi` over `j < m`, the same
`j`); EXPAND of the widths `e - s` (`expand_spec`) puts output row `Σ_{<i} w + (j - s)` at cell `i`, element `j`. -/
theorem mem_holds {n : USize} {X : Vals (.arr B) n} {T : Tab (.arr B) B} (h : Tab.mem X = .ok T)
    (xs : List B.El) (b : B.El) : T.Holds xs b ↔ (∃ i, X.row i = xs) ∧ b ∈ xs := by
  obtain ⟨m, lo, up, f⟩ := X
  dsimp only [Tab.mem] at h
  split at h; · cases h
  rename_i hb
  simp only [bind] at h
  rw [Except.bind_eq_ok'] at h; obtain ⟨_, -, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨c0, hc0, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨s, hs, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨cm, hcm, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨mn, hmn, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨e, he, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨wd, hwd, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨⟨Tn, G, u⟩, hex, h⟩ := h; try dsimp only at h
  rw [Except.bind_eq_ok'] at h; obtain ⟨sg, hsg, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨ix, hix, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨x, hx, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨y, hy, h⟩ := h
  rw [canon_holds h]
  have hU : USize.size ≤ 2 ^ 64 := by rcases USize.size_eq with h | h <;> omega
  have hm63 : m.toNat < 2 ^ 63 := by omega
  have hn63 : n.toNat < 2 ^ 63 := by omega
  have hmU : m.toUInt64 = m.toNat.toUInt64 := UInt64.toNat_inj.mp (by simp <;> omega)
  -- each cell's bounds as integers, `SN ≤ EN`
  obtain ⟨Lf, hLf⟩ : ∃ F : Nat → Int, ∀ i, F i = ((raw .i64 n lo.enc)[i]?.getD 0).toInt64.toInt := ⟨_, fun _ => rfl⟩
  obtain ⟨Hf, hHf⟩ : ∃ F : Nat → Int, ∀ i, F i = ((raw .i64 n up.enc)[i]?.getD 0).toInt64.toInt := ⟨_, fun _ => rfl⟩
  obtain ⟨SN, hSN⟩ : ∃ F : Nat → Nat, ∀ i, F i = (Lf i).toNat := ⟨_, fun _ => rfl⟩
  obtain ⟨EN, hEN⟩ : ∃ F : Nat → Nat, ∀ i, F i = max (min (Hf i).toNat m.toNat) (SN i) := ⟨_, fun _ => rfl⟩
  obtain ⟨wN, hwN⟩ : ∃ F : Nat → Nat, ∀ i, F i = EN i - SN i := ⟨_, fun _ => rfl⟩
  have hL63 : ∀ i, Lf i < 2 ^ 63 := fun i => by
    rw [hLf, toInt64_toInt_cond]; have := ((raw .i64 n lo.enc)[i]?.getD 0).toNat_lt; split <;> omega
  have hH63 : ∀ i, Hf i < 2 ^ 63 := fun i => by
    rw [hHf, toInt64_toInt_cond]; have := ((raw .i64 n up.enc)[i]?.getD 0).toNat_lt; split <;> omega
  have hcell : ∀ (i : Fin n.toNat) (j : Nat), j < m.toNat →
      (((lo.get i).toInt ≤ (j : Int) ∧ (j : Int) < (up.get i).toInt) ↔ SN i ≤ j ∧ j < EN i) := by
    intro i j hj
    rw [Arr.get_i64, Arr.get_i64, ← hLf, ← hHf, hEN, hSN]; omega
  -- the words `s`, `e - s`
  have hsw : ∀ i < n.toNat, (raw .i64 n s)[i]?.getD 0 = (SN i).toUInt64 := by
    intro i hi
    have es : (Except.ok (if ((raw .i64 n lo.enc)[i]?.getD 0).toInt64 < (0 : UInt64).toInt64 then (0 : UInt64)
        else (raw .i64 n lo.enc)[i]?.getD 0) : Except String UInt64) = .ok ((raw .i64 n s)[i]?.getD 0) := by
      have := (colMap_raw hs).2.2.2 i hi
      rwa [colConst_raw hc0, Array.getElem?_replicate, if_pos hi, Option.getD_some] at this
    rw [← Except.ok.inj es, hSN]
    have z : (0 : UInt64).toInt64.toInt = 0 := rfl
    split <;> rename_i hl <;> rw [Int64.lt_iff_toInt_lt, z, ← hLf] at hl
    · rw [show (Lf i).toNat = 0 by omega]; rfl
    · obtain ⟨h63, hv⟩ := toInt64_nonneg (x := (raw .i64 n lo.enc)[i]?.getD 0) (by rw [← hLf]; omega)
      rw [← hLf] at hv; rw [hv, Int.toNat_natCast]; simp
  have hmw : ∀ i < n.toNat, ((raw .i64 n mn)[i]?.getD 0).toInt64.toInt = min (Hf i) m.toNat := by
    intro i hi
    have es : (Except.ok (if (m.toNat.toUInt64).toInt64 < ((raw .i64 n up.enc)[i]?.getD 0).toInt64
        then m.toNat.toUInt64 else (raw .i64 n up.enc)[i]?.getD 0) : Except String UInt64) = .ok ((raw .i64 n mn)[i]?.getD 0) := by
      have := (colMap_raw hmn).2.2.2 i hi
      rwa [colConst_raw hcm, Array.getElem?_replicate, if_pos hi, Option.getD_some, hmU] at this
    rw [← Except.ok.inj es]
    have zm := toInt64_toInt_nat hm63
    split <;> rename_i hl <;> rw [Int64.lt_iff_toInt_lt, zm, ← hHf] at hl
    · rw [zm]; omega
    · rw [← hHf]; omega
  have hew : ∀ i < n.toNat, (raw .i64 n e)[i]?.getD 0 = (EN i).toUInt64 := by
    intro i hi
    have es : (Except.ok (if ((raw .i64 n mn)[i]?.getD 0).toInt64 < ((raw .i64 n s)[i]?.getD 0).toInt64
        then (raw .i64 n s)[i]?.getD 0 else (raw .i64 n mn)[i]?.getD 0) : Except String UInt64) = .ok ((raw .i64 n e)[i]?.getD 0) :=
      (colMap_raw he).2.2.2 i hi
    have hS63 : SN i < 2 ^ 63 := by rw [hSN]; have := hL63 i; omega
    have zs : ((raw .i64 n s)[i]?.getD 0).toInt64.toInt = SN i := by rw [hsw i hi]; exact toInt64_toInt_nat hS63
    rw [← Except.ok.inj es]
    split <;> rename_i hl <;> rw [Int64.lt_iff_toInt_lt, zs, hmw i hi] at hl
    · rw [hsw i hi, hEN]; congr 1; omega
    · obtain ⟨h63, hv⟩ := toInt64_nonneg (x := (raw .i64 n mn)[i]?.getD 0) (by rw [hmw i hi]; omega)
      rw [hmw i hi] at hv
      rw [← UInt64.ofNat_toNat (x := (raw .i64 n mn)[i]?.getD 0), hEN]; congr 1; omega
  have hww : ∀ i < n.toNat, (raw .i64 n wd)[i]?.getD 0 = (wN i).toUInt64 := by
    intro i hi
    have es := (colMap_raw hwd).2.2.2 i hi
    rw [hew i hi, hsw i hi] at es; simp only [Op.eval, Except.ok.injEq] at es
    rw [← es, hwN, toUInt64_sub (by rw [hEN]; omega)]
  have hwm : ∀ i, wN i ≤ m.toNat := fun i => by rw [hwN, hEN]; omega
  have hsum : ∀ k, ((List.range k).map wN).sum ≤ k * m.toNat := fun k => by
    induction k with
    | zero => simp
    | succ k ih => rw [sum_range_succ', Nat.succ_mul]; have := hwm k; omega
  have hsn : ((List.range n.toNat).map wN).sum < 2 ^ 63 := by have := hsum n.toNat; omega
  obtain ⟨hTn, hrun⟩ := expand_spec hex wN hww hsn hn63
  -- row `t` of cell `g`'s run reads cell `g` and element `SN g + (t - Σ_{<g} w)`
  have hrow : ∀ g < n.toNat, ∀ t, ((List.range g).map wN).sum ≤ t → t < ((List.range g).map wN).sum + wN g →
      ((raw .i64 Tn G)[t]?.getD 0).toNat = g ∧
        ((raw .i64 Tn ix)[t]?.getD 0).toNat = SN g + (t - ((List.range g).map wN).sum) := by
    intro g hg t h1 h2
    obtain ⟨hG, hu⟩ := hrun g hg t h1 h2
    have hgS : ((List.range g).map wN).sum + wN g ≤ ((List.range n.toNat).map wN).sum := by
      rw [← sum_range_succ']; exact sum_range_mono wN hg
    have htT : t < Tn.toNat := by omega
    have hEm : EN g ≤ m.toNat ∨ wN g = 0 := by rw [hwN, hEN]; omega
    refine ⟨by rw [hG, toNat_toUInt64 (by omega)], ?_⟩
    have es := (colMap_raw hix).2.2.2 t htT
    rw [(kgather_word hsg t htT).2, hG, toNat_toUInt64 (by omega), hsw g hg, hu] at es
    simp only [Op.eval, Except.ok.injEq] at es
    rw [← es, ← UInt64.ofNat_add, toNat_toUInt64 (by rw [hSN]; have := hL63 g; omega)]
  simp only [Tab.Holds]
  constructor
  · rintro ⟨t, rfl, rfl⟩
    obtain ⟨g, hg, h1, h2⟩ := exists_group wN n.toNat t (by rw [← hTn]; exact t.2)
    obtain ⟨hG, hI⟩ := hrow g hg t h1 h2
    obtain ⟨i, hi, hxi⟩ := Vals.gather_row _ hx t
    obtain ⟨j, hj, hyj⟩ := Vals.gather_row _ hy t
    have ei : i = ⟨g, hg⟩ := Fin.ext (by rw [← hi, hG])
    subst ei
    refine ⟨⟨_, hxi.symm⟩, ?_⟩
    rw [hxi, hyj]
    simp only [Vals.row, List.mem_filterMap, List.mem_finRange, true_and]
    refine ⟨j, ?_⟩
    rw [if_pos ((hcell _ j.1 j.2).2 (by have := hwN g; rw [hI] at hj; simp only [Fin.val_mk]; omega))]
  · rintro ⟨⟨i, rfl⟩, hb⟩
    simp only [Vals.row, List.mem_filterMap, List.mem_finRange, true_and] at hb
    obtain ⟨j, hj⟩ := hb
    split at hj
    case isFalse => cases hj
    rename_i hc
    cases hj
    obtain ⟨h1, h2⟩ := (hcell i j.1 j.2).1 hc
    have hgS : ((List.range i.1).map wN).sum + wN i.1 ≤ ((List.range n.toNat).map wN).sum := by
      rw [← sum_range_succ']; exact sum_range_mono wN i.2
    have ht : ((List.range i.1).map wN).sum + (j.1 - SN i.1) < Tn.toNat := by rw [hwN] at hgS; omega
    obtain ⟨hG, hI⟩ := hrow i.1 i.2 (((List.range i.1).map wN).sum + (j.1 - SN i.1)) (by omega)
      (by rw [hwN]; omega)
    obtain ⟨i', hi', hxi⟩ := Vals.gather_row _ hx ⟨_, ht⟩
    obtain ⟨j', hj', hyj⟩ := Vals.gather_row _ hy ⟨_, ht⟩
    have ei : i' = i := Fin.ext (by rw [← hi', hG])
    have ej : j' = j := Fin.ext (by rw [← hj', hI]; omega)
    subst ei ej
    exact ⟨⟨_, ht⟩, hxi, hyj⟩

end Tab

/-- **A duplicate-free list inside another is no longer**: each element of `l₁` erased from `l₂` in turn. -/
theorem nodup_length_le {α : Type} [DecidableEq α] : ∀ {l₁ l₂ : List α}, l₁.Nodup → l₁ ⊆ l₂ →
    l₁.length ≤ l₂.length
  | [], _, _, _ => Nat.zero_le _
  | a :: l, l₂, d, h => by
    obtain ⟨ha, d⟩ := List.nodup_cons.1 d
    have hm : a ∈ l₂ := h (List.mem_cons.2 (Or.inl rfl))
    have := nodup_length_le (l₂ := l₂.erase a) d fun x hx =>
      (List.mem_erase_of_ne fun e => ha (by rw [← e]; exact hx)).2 (h (List.mem_cons_of_mem _ hx))
    rw [List.length_erase_of_mem hm] at this
    have := List.length_pos_of_mem hm
    simp only [List.length_cons]; omega

/-- **A duplicate-free list inside another is as long as it exactly when it holds all of it**: an element of `l₂`
missing from `l₁` leaves `l₁` inside `l₂` less that element (`nodup_length_le`). -/
theorem nodup_length_eq_iff {α : Type} [DecidableEq α] {l₁ l₂ : List α} (d₁ : l₁.Nodup) (d₂ : l₂.Nodup)
    (h : l₁ ⊆ l₂) : l₁.length = l₂.length ↔ l₂ ⊆ l₁ :=
  ⟨fun e y hy => Classical.byContradiction fun hn => by
      have := nodup_length_le d₁ fun x hx => (List.mem_erase_of_ne (a := x) (b := y) fun e' => hn (by rw [← e']; exact hx)).2 (h hx)
      rw [List.length_erase_of_mem hy] at this
      have := List.length_pos_of_mem hy; omega,
   fun h' => Nat.le_antisymm (nodup_length_le d₁ h) (nodup_length_le d₂ h')⟩

/-- **`kscatter (.last)` at distinct indices** writes word `q` of `e` at index `π q`: no later row writes there. -/
theorem scatter_last_at {N K : USize} {ix e o : Enc} (h : kscatter .last N ix e K 0 = .ok o) (π : Nat → Nat)
    (hix : ∀ q < N.toNat, (raw .i64 N ix)[q]?.getD 0 = (π q).toUInt64) (hπ : ∀ q < N.toNat, π q < K.toNat)
    (hinj : ∀ q < N.toNat, ∀ q' < N.toNat, π q = π q' → q = q') :
    ∀ q < N.toNat, (raw .i64 K o)[π q]?.getD 0 = (raw .i64 N e)[q]?.getD 0 := by
  obtain ⟨hs, -, hw⟩ := kscatter_words h
  have hK := K.toNat_lt_size
  have hU : USize.size ≤ 2 ^ 64 := by rcases USize.size_eq with h | h <;> omega
  have hat : ∀ q < N.toNat, ((raw .i64 N ix)[q]?.getD 0).toNat = π q := fun q hq => by
    rw [hix q hq, toNat_toUInt64 (by have := hπ q hq; omega)]
  intro q hq
  have := ((scatterWords_spec _ _ _ _).2 _ hw).2.2 q (by omega) fun q' h1 h2 e => by
    have e' : ((raw .i64 N ix)[q']?.getD 0).toNat = ((raw .i64 N ix)[q]?.getD 0).toNat := e
    rw [hat q' (by omega), hat q hq] at e'; have := hinj _ (by omega) _ hq e'; omega
  have h' : (raw .i64 K o)[π q]? = some ((raw .i64 N e)[q]?.getD 0) := by rw [← hat q hq]; exact this
  rw [h']; rfl

/-- **GROUP over the rows of `x`** (`Vals.cols`, `kasc`, `kseen` over the sorted columns): sorted row `q` is input
row `π q`, `π` a permutation of the rows; sorted row `q` is in group `gr q`, whose first sorted row is `fs G`; two
sorted rows share a group exactly when their input rows are equal. -/
theorem group_rows {A : Obj} {N : USize} {x : Vals A N} {es : List (AscKey × Enc)} {vs : List Enc} {p g f : Enc}
    {k : Nat} (hes : Vals.cols x = .ok es) (hasc : kasc N es = .ok (vs, p))
    (hseen : kseen N ((es.map (·.1)).zip vs) = .ok (k, g, f)) :
    ∃ π gr fs : Nat → Nat, k ≤ N.toNat ∧
      (∀ q < N.toNat, (raw .i64 N p)[q]?.getD 0 = (π q).toUInt64 ∧ π q < N.toNat) ∧
      (∀ q < N.toNat, ∀ q' < N.toNat, π q = π q' → q = q') ∧
      (∀ i < N.toNat, ∃ q < N.toNat, π q = i) ∧
      (∀ P : Nat → Bool, (List.range N.toNat).countP (fun q => P (π q)) = (List.range N.toNat).countP P) ∧
      (∀ q < N.toNat, (raw .i64 N g)[q]?.getD 0 = (gr q).toUInt64 ∧ gr q < k) ∧
      (∀ G < k, (raw .i64 k.toUSize f)[G]?.getD 0 = (fs G).toUInt64 ∧ fs G < N.toNat ∧ gr (fs G) = G) ∧
      ∀ q < N.toNat, ∀ q' < N.toNat, gr q = gr q' ↔
        ∀ (h : π q < N.toNat) (h' : π q' < N.toNat), x.row ⟨π q, h⟩ = x.row ⟨π q', h'⟩ := by
  obtain ⟨cs, hcs, hp, hkq⟩ := kasc_grade hasc
  obtain ⟨hperm, -⟩ := ascGrade_spec N.toNat (ascKeys N es)
  obtain ⟨hk, hg, hf⟩ := kseen_ok hseen
  generalize ascGrade N.toNat (ascKeys N es) = ps at hp hkq hperm
  generalize seenKey N ((es.map (·.1)).zip vs) = Kk at hk hg hf hkq
  have hU : USize.size ≤ 2 ^ 64 := by rcases USize.size_eq with h | h <;> omega
  have hNU := N.toNat_lt_size
  have hlen : ps.length = N.toNat := by simpa using hperm.length_eq
  have hpsN : ∀ q < N.toNat, ps[q]?.getD 0 < N.toNat := fun q hq => by
    rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
    exact List.mem_range.1 (hperm.mem_iff.1 (List.getElem_mem _))
  have hkN : k ≤ N.toNat := by rw [hk]; unfold firstsOf; exact Nat.le_trans (List.length_filter_le _ _) (by simp)
  have hK : k.toUSize.toNat = k := USize.toNat_ofNat_of_lt' (by omega)
  have hpsN' : ∀ q (hq : q < ps.length), ps[q] < N.toNat := fun q _ => List.mem_range.1 (hperm.mem_iff.1 (List.getElem_mem _))
  have hnd := hperm.nodup_iff.2 List.nodup_range
  obtain ⟨-, -, hgg, hfg, -⟩ := firsts_spec Kk N.toNat
  refine ⟨fun q => ps[q]?.getD 0, Verify.groupOf Kk N.toNat, fun G => (firstsOf Kk N.toNat)[G]?.getD 0, hkN,
    fun q hq => ⟨by rw [hp]; simp [List.getElem?_eq_getElem (show q < ps.length by omega)], hpsN q hq⟩,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro q hq q' hq' e
    simp only [List.getElem?_eq_getElem (show q < ps.length by omega),
      List.getElem?_eq_getElem (show q' < ps.length by omega), Option.getD_some] at e
    rcases Nat.lt_trichotomy q q' with hl | hl | hl
    · exact absurd e (List.pairwise_iff_getElem.1 hnd _ _ _ _ hl)
    · exact hl
    · exact absurd e.symm (List.pairwise_iff_getElem.1 hnd _ _ _ _ hl)
  · intro i hi
    obtain ⟨q, hq, e⟩ := List.getElem_of_mem (hperm.mem_iff.2 (List.mem_range.2 hi))
    exact ⟨q, by omega, by simp [List.getElem?_eq_getElem hq, e]⟩
  · intro P
    have hmap : (List.range N.toNat).map (fun q => ps[q]?.getD 0) = ps :=
      List.ext_getElem (by simp [hlen]) fun i h1 h2 => by simp [List.getElem?_eq_getElem h2]
    rw [show (fun q => P (ps[q]?.getD 0)) = P ∘ (fun q => ps[q]?.getD 0) from rfl, ← List.countP_map, hmap,
      hperm.countP_eq]
  · intro q hq
    exact ⟨by rw [hg, (wordsFoR_closed _ (by simp)).2.1]; simp [hq],
      by have := groupOf_lt (g := Kk) (m := N.toNat) hq; omega⟩
  · intro G hG
    have hG' : G < (firstsOf Kk N.toNat).length := by omega
    refine ⟨by rw [hf, (wordsFoR_closed _ (by rw [hK, hk]; simp)).2.1]; simp [List.getElem?_eq_getElem hG'], ?_, ?_⟩
    · simp only [List.getElem?_eq_getElem hG', Option.getD_some]; exact firsts_lt Kk N.toNat (List.getElem_mem _)
    · simp only [List.getElem?_eq_getElem hG', Option.getD_some]; exact hfg G hG'
  · intro q hq q' hq'
    simp only [List.getElem?_eq_getElem (show q < ps.length by omega),
      List.getElem?_eq_getElem (show q' < ps.length by omega), Option.getD_some]
    rw [hgg q hq q' hq', hkq q (by omega), hkq q' (by omega)]
    exact ⟨fun e h h' => Vals.row_of_codes x hes hcs ⟨ps[q], h⟩ ⟨ps[q'], h'⟩ e,
      fun e => Vals.codes_of_row x hes hcs ⟨_, hpsN' q (by omega)⟩ ⟨_, hpsN' q' (by omega)⟩
        (e (hpsN' q (by omega)) (hpsN' q' (by omega)))⟩

/-- **`R.canon`'s rows are distinct** (`Vals.nub_distinct` of its pair side). -/
theorem Tab.canon_distinct {k v : Obj} {R U : Tab k v} (h : R.canon = .ok U) {j j' : Fin U.n.toNat} (hjj : j ≠ j') :
    (U.key.row j, U.val.row j) ≠ (U.key.row j', U.val.row j') := by
  unfold Tab.canon at h
  cases hn : Vals.nub (A := .prod k v) (R.key, R.val) with
  | error s => simp [hn, Functor.map, Except.map] at h
  | ok r =>
    simp only [hn, Functor.map, Except.map, Except.ok.injEq] at h
    subst h
    exact Vals.nub_distinct hn hjj

/-! ## Checks on `foR` tables -/

section Checks

/-- Two lists hold the same elements: the old layer orders a float NaN first, `kasc` by `ordCode`, and the old `memC`,
`ltC` keep repeats (that the new answer has none is `canonOk`). -/
private def sameSet {α : Type} [BEq α] : Option (List α) → Option (List α) → Bool
  | some a, some b => a.all b.contains && b.all a.contains
  | _, _ => false

/-- A new operator's answer as a list, `none` on `.error`. -/
private def newL {k v : Obj} (r : Except String (Tab k v)) : Option (List (k.El × v.El)) := r.toOption.map Tab.toList

/-- An old operator's answer as a list, `none` where it ran past its capacity. -/
private def oldL {k v : Obj} (c : Tab k v × Bool) : Option (List (k.El × v.El)) := if c.2 then some c.1.toList else none

/-- The answer is `.ok` and canonical: `canon` of it lists the same rows in the same order. -/
private def canonOk {k v : Obj} [BEq k.El] [BEq v.El] (r : Except String (Tab k v)) : Bool :=
  match r with
  | .ok T => (T.canon.toOption.map Tab.toList) == some T.toList
  | .error _ => false

/-- `𝟙` on `U`, the universe a `Tm` passes as a coreflexive. -/
private def idT {A : Obj} {n : USize} (U : Vals A n) : Tab A A := ⟨n, U, U⟩

/-- Tables with duplicate rows, negatives, keys of one value each, a value shared by every key, and no rows. -/
private def ts : List (List (Int64 × Int64)) :=
  [[(3, 1), (1, 2), (3, 1), (-1, 2), (1, 2), (2, 7), (-5, -5), (0, 0)],
   [(2, 5), (1, -3), (2, 6), (7, 7), (9, 0), (2, 5), (-5, 4), (0, 0)],
   [(1, 2), (1, 5), (2, 2), (2, 5), (3, 2), (3, 2)], []]

/-- The universe `1 2 5 7 9 -3 2`, a value twice. -/
private def U := Alg.col [1, 2, 5, 7, 9, -3, 2]

-- `\` and `/` against `leftDivC`, `rightDivC` on every pair of tables, within `U`; each answer canonical
#guard ts.all fun ps => ts.all fun qs =>
  let R := tab ps; let S := tab qs
  canonOk (R.ldiv S (idT U) (idT U)) && canonOk (R.rdiv S (idT U) (idT U)) &&
  sameSet (newL (R.ldiv S (idT U) (idT U))) (oldL (Alg.leftDivC R S U U)) &&
  sameSet (newL (R.rdiv S (idT U) (idT U))) (oldL (Alg.rightDivC R S U U))

#guard newL ((tab [(1, 2), (1, 5), (2, 2), (2, 5), (3, 2)]).ldiv (tab [(1, 7), (2, 7), (2, 8), (3, 7)])
  (idT (Alg.col [2, 5, 6])) (idT (Alg.col [7, 9]))) == some [(2, 7), (5, 7), (6, 7), (6, 9)]

-- `<`, `≤` against `ltC`, `leqC`, on `U` and on no values
#guard canonOk (Tab.lt (idT U)) && canonOk (Tab.leq (idT U)) &&
  sameSet (newL (Tab.lt (idT U))) (oldL (Alg.ltC U)) && sameSet (newL (Tab.leq (idT U))) (oldL (Alg.leqC U)) &&
  newL (Tab.lt (tab [])) == some [] && newL (Tab.leq (tab [(4, 0), (2, 0)])) == some [(2, 2), (2, 4), (4, 4)]

/-- The keys `3 1 4 -1 3`: `3` twice, `4` the key of no row. -/
private def D := Alg.col [3, 1, 4, -1, 3]

/-- The old answer's rows whose key is a row of `D`: `lamOnC` runs on `dom R ∪ D`, the new `lam` on the keys in
demand `D` (`Tm.lam`), the denotation `lamDen` on every key. -/
private def onD {v : Obj} (o : Option (List (Int64 × v.El))) : Option (List (Int64 × v.El)) :=
  o.map (·.filter fun r => [3, 1, 4, -1].contains r.1)

/-- Each key has one cell in each answer, holding the same elements: the cells' order is `kasc`'s in the new answer and
the old layer's (a float NaN first) in the old one. -/
private def sameCells {k v : Type} [BEq k] [BEq v] (a b : Option (List (k × List v))) : Bool :=
  let sub (x y : List (k × List v)) := x.all fun (a, ys) => y.any fun (a', ys') =>
    a == a' && ys.length == ys'.length && ys.all ys'.contains && ys'.all ys.contains
  match a, b with
  | some x, some y => sub x y && sub y x
  | _, _ => false

-- `Λ` on `D` against `lamOnC` on `D`, and `nil`
#guard ts.all fun ps => canonOk (Tab.lam D (tab ps)) &&
  sameSet (newL (Tab.lam D (tab ps))) (onD (oldL (Alg.lamOnC (tab ps) D)))
#guard newL (Tab.lam D (tab [(3, 1), (1, 2), (3, 1), (-1, 2), (1, 2), (3, -7)])) ==
  some [(-1, [2]), (1, [2]), (3, [-7, 1]), (4, [])]
#guard canonOk (Tab.nil (A := .long) (B := .long) D) &&
  newL (Tab.nil (A := .long) (B := .long) D) == some [(-1, []), (1, []), (3, []), (4, [])]

/-- `-0.0`, `+0.0`, NaN with payloads `1` and `2`, `+inf`, `-inf`, `1.5`, `-0.0` again, as `f64` bits. -/
private def f64s : List UInt64 := [0x8000000000000000, 0, 0x7ff8000000000001, 0x7ff8000000000002, 0x7ff0000000000000,
  0xfff0000000000000, 0x3ff8000000000000, 0x8000000000000000]

-- `E` against `EC` on `arrCells` (empty cells, `[5]` from three ranges, `[5,1]` twice), on no cells, and with a
-- relation of no rows
#guard [(arrCells, arrPay), ([], arrPay)].all fun (cs, ps) =>
  let X := (arrTab cs ps).key
  [tab [(5, 1), (9, 2), (1, 3), (5, 4)], tab [(9, 0)], tab []].all fun R =>
    canonOk (Tab.E X R) && sameCells (newL (Tab.E X R)) (oldL (Alg.EC R X))

-- `E` on float and tuple elements: cells over `f64s` (`[-0.0]` from `[0,1)` and `[7,8)`, the empty cell, both NaNs)
-- and over pairs (`[(1,5)]` from two ranges)
#guard
  let x := Arr.ofFn .f64 8 (f64s.getD · 0) ⟨by decide, by decide⟩
  let X := (arrOn [(0, 1, 0), (7, 8, 0), (2, 4, 0), (3, 3, 0), (0, 8, 0), (5, 7, 0)] x).key
  let R : Tab (.atom .f64) .long := ⟨8, x, Alg.col [1, 1, 2, 3, 4, 4, 5, 6]⟩
  let Y := (arrOn [(0, 1, 0), (2, 3, 0), (0, 4, 0), (1, 1, 0)] ((Alg.col [1, 2, 1, 3], Alg.col [5, 5, 5, 6]) :
    Vals (.prod .long .long) 4)).key
  let S : Tab (.prod .long .long) .long := ⟨3, (Alg.col [1, 1, 3], Alg.col [5, 5, 6]), Alg.col [7, 8, 9]⟩
  canonOk (Tab.E X R) && sameCells (newL (Tab.E X R)) (oldL (Alg.EC R X)) &&
  canonOk (Tab.E Y S) && sameCells (newL (Tab.E Y S)) (oldL (Alg.EC S Y))

-- `∋` on cells (empty ones, clamped ones, one cell twice) against `memC`, and on no cells
#guard [(arrCells, arrPay), (arrCells.take 3, arrPay), ([], arrPay), ([(0, 0, 1), (0, 0, 1)], [])].all fun (cs, ps) =>
  let X := (arrTab cs ps).key
  canonOk (Tab.mem X) && sameSet (newL (Tab.mem X)) (oldL (Alg.memC X))

-- a float value column (stored-bit equality) and a tuple value column, through `\`, `/` and `Λ`
#guard
  let x := Arr.ofFn .f64 8 (f64s.getD · 0) ⟨by decide, by decide⟩
  let R : Tab .long (.atom .f64) := ⟨8, Alg.col [3, 1, 2, 1, 4, 4, 0, 1], x⟩
  let S : Tab .long .long := tab [(3, 5), (1, 6), (2, 5), (1, 5), (4, 5), (0, 5), (0, 6)]
  let Ux := Arr.ofFn .f64 3 (f64s.getD · 0) ⟨by decide, by decide⟩
  canonOk (R.ldiv S (idT Ux) (idT U)) && sameSet (newL (R.ldiv S (idT Ux) (idT U))) (oldL (Alg.leftDivC R S Ux U)) &&
  sameCells (newL (Tab.lam D R)) (onD (oldL (Alg.lamOnC R D)))
#guard
  let R : Tab .long (.prod .long .long) := ⟨5, Alg.col [3, 1, 3, 1, 2], (Alg.col [1, 1, 2, 1, 2], Alg.col [5, 6, 5, 6, 5])⟩
  let S : Tab .long .long := tab [(3, 5), (1, 6), (1, 5), (2, 5)]
  let Up : Vals (.prod .long .long) 2 := (Alg.col [9, 9], Alg.col [9, 8])
  canonOk (R.ldiv S (idT Up) (idT U)) && sameSet (newL (R.ldiv S (idT Up) (idT U))) (oldL (Alg.leftDivC R S Up U)) &&
  sameSet (newL (Tab.lam D R)) (onD (oldL (Alg.lamOnC R D)))

end Checks

end Rel
