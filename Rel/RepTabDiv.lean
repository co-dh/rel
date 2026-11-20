import Rel.Run.Div
import Rel.Run.Fix
import Rel.Run.Power
import Rel.Run.List
import Rel.RepStruct
import Rel.RepCanon
import Rel.RepSetOps
import Rel.RepTabComp
import Rel.Lang.Den

/-! The laws of the operators of `Rel/Run/Div.lean` (`ldiv`, `rdiv`, `lam`, `E`, `nil`, `lt`, `leq`), and the checks
of those, `Rel/Run/Fix.lean`'s, `Rel/Run/Power.lean`'s and `Rel/Run/List.lean`'s operators on `foR` tables against their
denotations (`Rel/Lang/Den.lean`) on lists, as sets. -/

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

/-- **`cmpOn op K L` is `K ≫ r ≫ L`**, `op` testing `r` on the signed words: `keep` of `cross K L`, row `i` kept
where `op` answers `1`. -/
theorem cmpOn_holds {op : Op} {r : Int64 → Int64 → Bool}
    (hop : ∀ x y : UInt64, op.eval x y = .ok (if r x.toInt64 y.toInt64 then 1 else 0))
    {n m : USize} {K : Vals .long n} {L : Vals .long m} {T : Tab .long .long} (h : cmpOn op K L = .ok T)
    (a c : Int64) : T.Holds a c ↔ (∃ i, K.row i = a) ∧ (∃ j, L.row j = c) ∧ r a c = true := by
  unfold cmpOn at h; simp only [bind, Except.bind] at h
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
  rw [keep_holds h (fun i hi => by rw [hwv ⟨i, hi⟩]; split <;> decide), ← and_assoc, ← cross_holds hX a c]
  simp only [Tab.Holds]
  constructor
  · rintro ⟨i, hi, rfl, rfl⟩
    rw [hwv i] at hi
    exact ⟨⟨i, rfl, rfl⟩, by cases hr : r (X.key.row i) (X.val.row i) <;> simp_all⟩
  · rintro ⟨⟨i, rfl, rfl⟩, hr⟩
    exact ⟨i, by rw [hwv i, if_pos hr]; decide, rfl, rfl⟩

/-- **`lt K L` denotes `K ≫ < ≫ L`**. -/
theorem lt_holds {n m : USize} {K : Vals .long n} {L : Vals .long m} {T : Tab .long .long} (h : Tab.lt K L = .ok T)
    (a c : Int64) : T.Holds a c ↔ (∃ i, K.row i = a) ∧ (∃ j, L.row j = c) ∧ a < c := by
  rw [cmpOn_holds (r := fun x y => decide (x < y)) (fun _ _ => rfl) h, decide_eq_true_eq]

/-- **`leq K L` denotes `K ≫ ≤ ≫ L`**. -/
theorem leq_holds {n m : USize} {K : Vals .long n} {L : Vals .long m} {T : Tab .long .long}
    (h : Tab.leq K L = .ok T) (a c : Int64) : T.Holds a c ↔ (∃ i, K.row i = a) ∧ (∃ j, L.row j = c) ∧ a ≤ c := by
  rw [cmpOn_holds (r := fun x y => decide (x ≤ y)) (fun _ _ => rfl) h, decide_eq_true_eq]

/-- The keys of `dom U` are the keys of `U`. -/
private theorem dom_key {k v : Obj} {U : Tab k v} {d : Tab k k} (hd : U.dom = .ok d) (x : k.El) :
    (∃ i, d.key.row i = x) ↔ ∃ y, U.Holds x y := by
  constructor
  · rintro ⟨i, rfl⟩; exact ((dom_holds hd _ _).1 ⟨i, rfl, rfl⟩).2
  · intro hv; obtain ⟨i, hi, -⟩ := (dom_holds hd x x).2 ⟨rfl, hv⟩; exact ⟨i, hi⟩

/-- **`lt` on both sides `dom U` denotes `ltDen`**: `lt_holds` at `K = L = dom U`. -/
theorem lt_dom_holds {U d T : Tab .long .long} (hd : U.dom = .ok d) (h : Tab.lt d.key d.key = .ok T)
    (a c : Int64) : T.Holds a c ↔ Lang.ltDen U.Holds a c := by
  rw [lt_holds h, dom_key hd, dom_key hd]

/-- **`leq` on both sides `dom U` denotes `leqDen`**: `leq_holds` at `K = L = dom U`. -/
theorem leq_dom_holds {U d T : Tab .long .long} (hd : U.dom = .ok d) (h : Tab.leq d.key d.key = .ok T)
    (a c : Int64) : T.Holds a c ↔ Lang.leqDen U.Holds a c := by
  rw [leq_holds h, dom_key hd, dom_key hd]

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

/-- **An `arr` row whose words are in range**: `lo = a`, `hi = b` with `a ≤ b ≤ m < 2^63` read the payload rows
`[a, b)`. -/
theorem Vals.row_cell {B : Obj} {n m : USize} (lo hi : Arr .i64 n) (f : Vals B m) (i : Fin n.toNat) {a b : Nat}
    (ha : (raw .i64 n lo.enc)[i.1]?.getD 0 = a.toUInt64) (hb : (raw .i64 n hi.enc)[i.1]?.getD 0 = b.toUInt64)
    (hab : a ≤ b) (hbm : b ≤ m.toNat) (hm : m.toNat < 2 ^ 63) :
    Vals.row (A := .arr B) ⟨m, lo, hi, f⟩ i =
      (List.range' a (b - a)).map fun k => if h : k < m.toNat then Vals.row f ⟨k, h⟩ else B.dflt := by
  have hi : (i.1.toUInt64).toNat = i.1 := by
    have := i.2; have := n.toNat_lt_size; have := USize.size_le; simp; omega
  rw [Vals.row_arr]
  simp only [cellStart, cellLen, hi, ha, hb, toInt64_toInt_nat (show a < 2 ^ 63 by omega),
    toInt64_toInt_nat (show b < 2 ^ 63 by omega)]
  congr 2 <;> omega

/-- **`cellSpan` reads each cell as `[SN, EN)`**: `s = SN = max lo 0`, `e = EN = max (min hi m) SN`, and the row is
the payload rows `[SN, EN)`, so `SN ≤ EN`, and `EN ≤ m` or the cell is empty. -/
theorem cellSpan_spec {B : Obj} {n m : USize} {lo up s e : Arr .i64 n} (h : cellSpan m lo up = .ok (s, e))
    (hm63 : m.toNat < 2 ^ 63) (f : Vals B m) :
    ∃ SN EN : Nat → Nat, (∀ i < n.toNat, (raw .i64 n s.enc)[i]?.getD 0 = (SN i).toUInt64 ∧
      (raw .i64 n e.enc)[i]?.getD 0 = (EN i).toUInt64) ∧
      (∀ i, SN i ≤ EN i ∧ SN i < 2 ^ 63 ∧ (EN i ≤ m.toNat ∨ EN i = SN i)) ∧
      ∀ i : Fin n.toNat, Vals.row (A := .arr B) ⟨m, lo, up, f⟩ i =
        (List.range' (SN i) (EN i - SN i)).map fun k => if h : k < m.toNat then Vals.row f ⟨k, h⟩ else B.dflt := by
  simp only [cellSpan, bind] at h
  rw [Except.bind_eq_ok'] at h; obtain ⟨c0, hc0, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨s', hs, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨cm, hcm, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨mn, hmn, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨e', he, h⟩ := h
  cases h
  replace hs := colArr_ok hs; replace he := colArr_ok he
  have hmU : m.toUInt64 = m.toNat.toUInt64 := UInt64.toNat_inj.mp (by simp <;> omega)
  obtain ⟨Lf, hLf⟩ : ∃ F : Nat → Int, ∀ i, F i = ((raw .i64 n lo.enc)[i]?.getD 0).toInt64.toInt := ⟨_, fun _ => rfl⟩
  obtain ⟨Hf, hHf⟩ : ∃ F : Nat → Int, ∀ i, F i = ((raw .i64 n up.enc)[i]?.getD 0).toInt64.toInt := ⟨_, fun _ => rfl⟩
  obtain ⟨SN, hSN⟩ : ∃ F : Nat → Nat, ∀ i, F i = (Lf i).toNat := ⟨_, fun _ => rfl⟩
  obtain ⟨EN, hEN⟩ : ∃ F : Nat → Nat, ∀ i, F i = max (min (Hf i).toNat m.toNat) (SN i) := ⟨_, fun _ => rfl⟩
  have hL63 : ∀ i, Lf i < 2 ^ 63 := fun i => by
    rw [hLf, toInt64_toInt_cond]; have := ((raw .i64 n lo.enc)[i]?.getD 0).toNat_lt; split <;> omega
  have hsw : ∀ i < n.toNat, (raw .i64 n s.enc)[i]?.getD 0 = (SN i).toUInt64 := by
    intro i hi
    have es : (Except.ok (if ((raw .i64 n lo.enc)[i]?.getD 0).toInt64 < (0 : UInt64).toInt64 then (0 : UInt64)
        else (raw .i64 n lo.enc)[i]?.getD 0) : Except String UInt64) = .ok ((raw .i64 n s.enc)[i]?.getD 0) := by
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
        then m.toNat.toUInt64 else (raw .i64 n up.enc)[i]?.getD 0) : Except String UInt64) =
          .ok ((raw .i64 n mn)[i]?.getD 0) := by
      have := (colMap_raw hmn).2.2.2 i hi
      rwa [colConst_raw hcm, Array.getElem?_replicate, if_pos hi, Option.getD_some, hmU] at this
    rw [← Except.ok.inj es]
    have zm := toInt64_toInt_nat hm63
    split <;> rename_i hl <;> rw [Int64.lt_iff_toInt_lt, zm, ← hHf] at hl
    · rw [zm]; omega
    · rw [← hHf]; omega
  have hew : ∀ i < n.toNat, (raw .i64 n e.enc)[i]?.getD 0 = (EN i).toUInt64 := by
    intro i hi
    have es : (Except.ok (if ((raw .i64 n mn)[i]?.getD 0).toInt64 < ((raw .i64 n s.enc)[i]?.getD 0).toInt64
        then (raw .i64 n s.enc)[i]?.getD 0 else (raw .i64 n mn)[i]?.getD 0) : Except String UInt64) =
          .ok ((raw .i64 n e.enc)[i]?.getD 0) :=
      (colMap_raw he).2.2.2 i hi
    have hS63 : SN i < 2 ^ 63 := by rw [hSN]; have := hL63 i; omega
    have zs : ((raw .i64 n s.enc)[i]?.getD 0).toInt64.toInt = SN i := by rw [hsw i hi]; exact toInt64_toInt_nat hS63
    rw [← Except.ok.inj es]
    split <;> rename_i hl <;> rw [Int64.lt_iff_toInt_lt, zs, hmw i hi] at hl
    · rw [hsw i hi, hEN]; congr 1; omega
    · obtain ⟨h63, hv⟩ := toInt64_nonneg (x := (raw .i64 n mn)[i]?.getD 0) (by rw [hmw i hi]; omega)
      rw [hmw i hi] at hv
      rw [← UInt64.ofNat_toNat (x := (raw .i64 n mn)[i]?.getD 0), hEN]; congr 1; omega
  refine ⟨SN, EN, fun i hi => ⟨hsw i hi, hew i hi⟩, fun i => ⟨by rw [hEN]; omega,
    by rw [hSN]; have := hL63 i; omega, by rw [hEN]; omega⟩, fun i => ?_⟩
  have hi : (i.1.toUInt64).toNat = i.1 := by
    have := i.2; have := n.toNat_lt_size; have := USize.size_le; simp; omega
  rw [Vals.row_arr]
  simp only [cellStart, cellLen, hi, ← hLf, ← hHf]
  by_cases hs : SN i ≤ m.toNat
  · rw [hSN] at hs
    rw [show min (max (Lf i) 0).toNat m.toNat = SN i by rw [hSN]; omega,
      show (min (Hf i) (m.toNat : Int)).toNat - SN i = EN i - SN i by rw [hEN, hSN]; omega]
  · rw [hSN] at hs
    rw [show (min (Hf i) (m.toNat : Int)).toNat - min (max (Lf i) 0).toNat m.toNat = 0 by omega,
      show EN i - SN i = 0 by rw [hEN, hSN]; omega]; rfl

/-- **The non-empty cells** (`uncons`, `unsnoc`): `whereCol` of `s < e` after `cellSpan` lists exactly the cells
`[SN, EN)` with `SN < EN`. -/
theorem cellSpan_where {B : Obj} {n m M : USize} {lo up s e : Arr .i64 n} {lt sel : Enc}
    (h : cellSpan m lo up = .ok (s, e)) (hlt : colMap .lt n s.enc e.enc = .ok lt) (hw : whereCol n lt = .ok (M, sel))
    (hm63 : m.toNat < 2 ^ 63) (f : Vals B m) :
    ∃ SN EN : Nat → Nat, (∀ i < n.toNat, (raw .i64 n s.enc)[i]?.getD 0 = (SN i).toUInt64 ∧
      (raw .i64 n e.enc)[i]?.getD 0 = (EN i).toUInt64) ∧
      (∀ i, SN i ≤ EN i ∧ SN i < 2 ^ 63 ∧ (EN i ≤ m.toNat ∨ EN i = SN i)) ∧
      (∀ i : Fin n.toNat, Vals.row (A := .arr B) ⟨m, lo, up, f⟩ i =
        (List.range' (SN i) (EN i - SN i)).map fun k => if h : k < m.toNat then Vals.row f ⟨k, h⟩ else B.dflt) ∧
      (∀ k < M.toNat, ((raw .i64 M sel)[k]?.getD 0).toNat < n.toNat ∧
        SN ((raw .i64 M sel)[k]?.getD 0).toNat < EN ((raw .i64 M sel)[k]?.getD 0).toNat) ∧
      ∀ i < n.toNat, SN i < EN i → ∃ k < M.toNat, ((raw .i64 M sel)[k]?.getD 0).toNat = i := by
  obtain ⟨SN, EN, hse, hb, hrow⟩ := cellSpan_spec h hm63 f
  have ltw : ∀ i < n.toNat, (raw .i64 n lt)[i]?.getD 0 = if SN i < EN i then 1 else 0 := by
    intro i hi
    have es : (Except.ok (if decide ((SN i).toUInt64.toInt64 < (EN i).toUInt64.toInt64) then (1 : UInt64) else 0) :
        Except String UInt64) = .ok ((raw .i64 n lt)[i]?.getD 0) := by
      have := (colMap_raw hlt).2.2.2 i hi
      rwa [(hse i hi).1, (hse i hi).2] at this
    rw [← Except.ok.inj es]
    have h1 := toInt64_toInt_nat (hb i).2.1
    have h2 := toInt64_toInt_nat (show EN i < 2 ^ 63 by have := hb i; omega)
    by_cases c : SN i < EN i <;> simp only [Int64.lt_iff_toInt_lt, h1, h2, Int.ofNat_lt, c, decide_true,
      decide_false, if_true, if_false, Bool.false_eq_true]
  have h2 : ∀ i < n.toNat, (raw .i64 n lt)[i]?.getD 0 < 2 := fun i hi => by rw [ltw i hi]; split <;> decide
  have hsz := whereCol_size hw
  have hmem : ∀ x, (∃ k < M.toNat, ((raw .i64 M sel)[k]?.getD 0).toNat = x) ↔
      x < n.toNat ∧ (raw .i64 n lt)[x]?.getD 0 ≠ 0 := fun x => by
    have hs : x ∈ ((raw .i64 M sel).toList.map UInt64.toNat) ↔
        x ∈ (List.range n.toNat).filter fun i => (raw .i64 n lt)[i]?.getD 0 ≠ 0 := by rw [whereCol_spec hw h2]
    rw [List.mem_iff_getElem] at hs
    simp only [List.mem_filter, List.mem_range, decide_eq_true_eq, List.length_map,
      Array.length_toList, hsz, List.getElem_map, Array.getElem_toList] at hs
    rw [← hs]
    constructor
    · rintro ⟨k, hk, rfl⟩; exact ⟨k, hk, by rw [Array.getElem?_eq_getElem (by omega)]; rfl⟩
    · rintro ⟨k, hk, rfl⟩; exact ⟨k, hk, by rw [Array.getElem?_eq_getElem (by omega)]; rfl⟩
  refine ⟨SN, EN, hse, hb, hrow, fun k hk => ?_, fun i hi c => ?_⟩
  · obtain ⟨hn, hne⟩ := (hmem _).1 ⟨k, hk, rfl⟩
    rw [ltw _ hn] at hne
    exact ⟨hn, by split at hne <;> first | assumption | exact absurd rfl hne⟩
  · obtain ⟨k, hk, e⟩ := (hmem i).2 ⟨hi, by rw [ltw i hi, if_pos c]; decide⟩
    exact ⟨k, hk, e⟩

/-- **`Vals.pack` keeps every row**: where a payload is cut, cell `i` (`[SN, EN)`, `cellSpan_spec`) is laid out at
`[Σ_{<i} w, Σ_{≤i} w)` (`Vals.cells`), whose row `Σ_{<i} w + d` is gathered from payload row `SN + d` (`expand_spec`). -/
theorem Vals.pack_row : {A : Obj} → {n : USize} → (x : Vals A n) → {y : Vals A n} → Vals.pack x = .ok y →
    ∀ i, Vals.row y i = Vals.row x i
  | .atom _, _, x, _, h, i => by
    simp only [Vals.pack, pure, Except.pure, Except.ok.injEq] at h; cases h; rfl
  | .prod _ _, _, x, _, h, i => by
    simp only [Vals.pack, bind, Except.bind, pure, Except.pure] at h
    split at h; · cases h
    rename_i y1 h1
    split at h; · cases h
    rename_i y2 h2
    cases h
    simp only [Vals.row, Vals.pack_row x.1 h1, Vals.pack_row x.2 h2]
  | .sum _ _, _, ⟨l, r, tag, idx, x, y⟩, _, h, i => by
    simp only [Vals.pack, bind, Except.bind, pure, Except.pure] at h
    split at h; · cases h
    rename_i x' h1
    split at h; · cases h
    rename_i y' h2
    cases h
    simp only [Vals.row, Vals.pack_row x h1, Vals.pack_row y h2]
  | .arr B, n, ⟨m, lo, up, f⟩, y, h, i => by
    simp only [Vals.pack] at h
    split at h; · cases h
    rename_i hb
    simp only [bind] at h
    rw [Except.bind_eq_ok'] at h; obtain ⟨_, -, h⟩ := h
    rw [Except.bind_eq_ok'] at h; obtain ⟨⟨s, e⟩, hse, h⟩ := h; try dsimp only at h
    rw [Except.bind_eq_ok'] at h; obtain ⟨w, hw, h⟩ := h
    split at h; · cases h
    rename_i P hP
    split at h
    case isFalse =>
      rw [Except.bind_eq_ok'] at h; obtain ⟨f', hf', h⟩ := h
      cases h
      simp only [Vals.row, Vals.pack_row f hf']
    rw [Except.bind_eq_ok'] at h; obtain ⟨⟨T, G, u⟩, hex, h⟩ := h; try dsimp only at h
    rw [Except.bind_eq_ok'] at h; obtain ⟨sg, hsg, h⟩ := h
    rw [Except.bind_eq_ok'] at h; obtain ⟨ix, hix, h⟩ := h
    rw [Except.bind_eq_ok'] at h; obtain ⟨g', hg', h⟩ := h
    rw [Except.bind_eq_ok'] at h; obtain ⟨p, hp, h⟩ := h
    simp only [Vals.cells, bind] at h
    rw [Except.bind_eq_ok'] at h; obtain ⟨P', hP', h⟩ := h
    rw [Except.bind_eq_ok'] at h; obtain ⟨lo', hlo', h⟩ := h
    rw [Except.bind_eq_ok'] at h; obtain ⟨c0, hc0, h⟩ := h
    rw [Except.bind_eq_ok'] at h; obtain ⟨hi', hhi', h⟩ := h
    cases h
    have hm63 : m.toNat < 2 ^ 63 := by omega
    have hn63 : n.toNat < 2 ^ 63 := by omega
    have hnm : n.toNat * m.toNat < 2 ^ 63 := by omega
    obtain ⟨SN, EN, hse', hb1, hrow⟩ := cellSpan_spec hse hm63 f
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
    have hP'w := colPrefix_add_sum hP' wN hww
    have hgS : ((List.range i.1).map wN).sum + wN i.1 ≤ ((List.range n.toNat).map wN).sum := by
      rw [← sum_range_succ']; exact sum_range_mono wN i.2
    have hlo : (raw .i64 n lo'.enc)[i.1]?.getD 0 = ((List.range i.1).map wN).sum.toUInt64 := by
      have es := (colMap_raw (colArr_ok hlo')).2.2.2 i.1 i.2
      rw [hP'w i.1 i.2, hww i.1 i.2, sum_range_succ'] at es; simp only [Op.eval, Except.ok.injEq] at es
      rw [← es, ← toUInt64_sub (by omega), Nat.add_sub_cancel]
    have hhi : (raw .i64 n hi'.enc)[i.1]?.getD 0 = (((List.range i.1).map wN).sum + wN i.1).toUInt64 := by
      have es := (colMap_raw (colArr_ok hhi')).2.2.2 i.1 i.2
      rw [hP'w i.1 i.2, colConst_raw hc0, Array.getElem?_replicate, if_pos i.2, Option.getD_some,
        sum_range_succ'] at es
      simp only [Op.eval, Except.ok.injEq, UInt64.add_zero] at es
      rw [← es]
    rw [Vals.row_cell lo' hi' p i hlo hhi (by omega) (by omega) (by omega), hrow i, Nat.add_sub_cancel_left,
      ← hwN, List.range'_eq_map_range, List.range'_eq_map_range, List.map_map, List.map_map]
    refine List.map_congr_left fun d hd => ?_
    have hd' : d < wN i.1 := List.mem_range.mp hd
    have ht : ((List.range i.1).map wN).sum + d < T.toNat := by omega
    have hEm : SN i.1 + d < m.toNat := by have := hb1 i.1; rw [hwN] at hd'; omega
    simp only [Function.comp_apply, dif_pos ht, dif_pos hEm]
    rw [Vals.pack_row g' hp]
    obtain ⟨j, hj, hgj⟩ := Vals.gather_row f hg' ⟨_, ht⟩
    rw [hgj]; congr 1; apply Fin.ext; rw [← hj]; dsimp only
    obtain ⟨hG, hu⟩ := hrun i.1 i.2 (((List.range i.1).map wN).sum + d) (by omega) (by omega)
    have es := (colMap_raw hix).2.2.2 _ ht
    rw [(kgather_word hsg _ ht).2, hG, toNat_toUInt64 (by omega), (hse' i.1 i.2).1, hu] at es
    simp only [Op.eval, Except.ok.injEq] at es
    rw [← es, ← UInt64.ofNat_add, Nat.add_sub_cancel_left,
      toNat_toUInt64 (by have := (hb1 i.1).2.1; have := hwm i.1; omega)]

/-- An `i64` column gathered (`Arr.gather`) reads at `j` the word of `x` at `ix[j]`. -/
theorem Arr.gather_raw {m n : USize} {ix : Enc} (x : Arr .i64 n) {y : Arr .i64 m} (h : Arr.gather m ix x = .ok y)
    (j : Fin m.toNat) : ∃ i : Fin n.toNat, ((raw .i64 m ix)[j.1]?.getD 0).toNat = i.1 ∧
      (raw .i64 m y.enc)[j.1]?.getD 0 = (raw .i64 n x.enc)[i.1]?.getD 0 := by
  obtain ⟨i, hi, e⟩ := Arr.gather_row x h j
  rw [Arr.get_i64, Arr.get_i64] at e
  exact ⟨i, hi, by simpa using congrArg Int64.toUInt64 e⟩

namespace Tab
variable {B : Obj}

/-- **`uncons X` denotes `cons°` on the arrays `X`**: each non-empty cell of `X` to its head and its tail. -/
theorem uncons_holds {n : USize} {X : Vals (.arr B) n} {T : Tab (.arr B) (.prod B (.arr B))}
    (h : Tab.uncons X = .ok T) (xs : List B.El) (p : (Obj.prod B (.arr B)).El) :
    T.Holds xs p ↔ (∃ i, X.row i = xs) ∧ xs = p.1 :: p.2 := by
  obtain ⟨m, lo, up, f⟩ := X
  dsimp only [Tab.uncons] at h
  split at h; · cases h
  rename_i hb
  simp only [bind] at h
  rw [Except.bind_eq_ok'] at h; obtain ⟨_, -, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨⟨s, e⟩, hse, h⟩ := h; try dsimp only at h
  rw [Except.bind_eq_ok'] at h; obtain ⟨lt, hlt, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨⟨M, sel⟩, hw, h⟩ := h; try dsimp only at h
  rw [Except.bind_eq_ok'] at h; obtain ⟨sM, hsM, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨K, hK, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨hd, hhd, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨c1, hc1, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨lo', hlo', h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨eM, heM, h⟩ := h
  rw [canon_holds h]
  have hm63 : m.toNat < 2 ^ 63 := by omega
  obtain ⟨SN, EN, hw1, hb1, hrow, hsel, hall⟩ := cellSpan_where hse hlt hw hm63 f
  let g : Nat → B.El := fun k => if h : k < m.toNat then Vals.row f ⟨k, h⟩ else B.dflt
  have hcons : ∀ i : Fin n.toNat, SN i < EN i →
      Vals.row (A := .arr B) ⟨m, lo, up, f⟩ i = g (SN i) :: (List.range' (SN i + 1) (EN i - SN i - 1)).map g := by
    intro i c; rw [hrow i, show EN i - SN i = (EN i - SN i - 1) + 1 by omega, List.range'_succ]; rfl
  have hJ : ∀ j : Fin M.toNat, ∃ i : Fin n.toNat, SN i < EN i ∧ ((raw .i64 M sel)[j.1]?.getD 0).toNat = i ∧
      K.row j = Vals.row (A := .arr B) ⟨m, lo, up, f⟩ i ∧
      Vals.row (A := .prod B (.arr B)) (hd, ⟨m, lo', eM, f⟩) j =
        (g (SN i), (List.range' (SN i + 1) (EN i - SN i - 1)).map g) := by
    intro j
    obtain ⟨i, hi, hKi⟩ := Vals.gather_row _ hK j
    obtain ⟨hin, c⟩ := hsel j.1 j.2
    rw [hi] at c
    obtain ⟨i2, hi2, hs2⟩ := Arr.gather_raw s hsM j
    obtain ⟨i3, hi3, he3⟩ := Arr.gather_raw e heM j
    have e2 : i = i2 := Fin.ext (hi.symm.trans hi2)
    have e3 : i = i3 := Fin.ext (hi.symm.trans hi3)
    subst e2 e3
    rw [(hw1 _ i.2).1] at hs2
    rw [(hw1 _ i.2).2] at he3
    have hEm : EN i ≤ m.toNat := by have := hb1 i; omega
    obtain ⟨i4, hi4, hd4⟩ := Vals.gather_row _ hhd j
    have e4 : i4.1 = SN i := by rw [← hi4, hs2, toNat_toUInt64 (by have := hb1 i; omega)]
    have hlo : (raw .i64 M lo'.enc)[j.1]?.getD 0 = (SN i + 1).toUInt64 := by
      have es := (colMap_raw (colArr_ok hlo')).2.2.2 j.1 j.2
      rw [colConst_raw hc1, Array.getElem?_replicate, if_pos j.2, Option.getD_some, hs2] at es
      simp only [Op.eval, Except.ok.injEq] at es
      have := (hb1 i).2.1; rw [← es]; apply UInt64.toNat_inj.mp; simp <;> omega
    refine ⟨i, c, hi, hKi, ?_⟩
    show (hd.row j, Vals.row (A := .arr B) ⟨m, lo', eM, f⟩ j) = _
    rw [hd4, Vals.row_cell lo' eM f j hlo he3 (by omega) hEm hm63,
      show EN i - (SN i + 1) = EN i - SN i - 1 by omega]
    simp only [g]; rw [dif_pos (by omega)]
    congr 2; exact Fin.ext e4
  simp only [Tab.Holds]
  constructor
  · rintro ⟨j, rfl, rfl⟩
    obtain ⟨i, c, -, hKi, hv⟩ := hJ j
    rw [hv, hKi]; exact ⟨⟨i, rfl⟩, hcons i c⟩
  · rintro ⟨⟨i, rfl⟩, hx⟩
    have c : SN i < EN i := by
      have := congrArg List.length hx; rw [hrow i] at this; simp at this; omega
    obtain ⟨k, hk, hki⟩ := hall i i.2 c
    obtain ⟨i', -, hi', hKi, hv⟩ := hJ ⟨k, hk⟩
    have e' : i' = i := Fin.ext (by rw [← hi', hki])
    subst e'
    rw [hcons i' c, List.cons.injEq] at hx
    exact ⟨⟨k, hk⟩, hKi, by rw [hv, hx.1, hx.2]⟩

/-- **`unsnoc X` denotes `snoc°` on the arrays `X`**: each non-empty cell of `X` to its front and its last element. -/
theorem unsnoc_holds {n : USize} {X : Vals (.arr B) n} {T : Tab (.arr B) (.prod (.arr B) B)}
    (h : Tab.unsnoc X = .ok T) (xs : List B.El) (p : (Obj.prod (.arr B) B).El) :
    T.Holds xs p ↔ (∃ i, X.row i = xs) ∧ xs = p.1 ++ [p.2] := by
  obtain ⟨m, lo, up, f⟩ := X
  dsimp only [Tab.unsnoc] at h
  split at h; · cases h
  rename_i hb
  simp only [bind] at h
  rw [Except.bind_eq_ok'] at h; obtain ⟨_, -, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨⟨s, e⟩, hse, h⟩ := h; try dsimp only at h
  rw [Except.bind_eq_ok'] at h; obtain ⟨lt, hlt, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨⟨M, sel⟩, hw, h⟩ := h; try dsimp only at h
  rw [Except.bind_eq_ok'] at h; obtain ⟨eM, heM, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨c1, hc1, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨l, hl, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨K, hK, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨sM, hsM, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨tl, htl, h⟩ := h
  rw [canon_holds h]
  have hm63 : m.toNat < 2 ^ 63 := by omega
  obtain ⟨SN, EN, hw1, hb1, hrow, hsel, hall⟩ := cellSpan_where hse hlt hw hm63 f
  let g : Nat → B.El := fun k => if h : k < m.toNat then Vals.row f ⟨k, h⟩ else B.dflt
  have hsnoc : ∀ i : Fin n.toNat, SN i < EN i →
      Vals.row (A := .arr B) ⟨m, lo, up, f⟩ i = (List.range' (SN i) (EN i - SN i - 1)).map g ++ [g (EN i - 1)] := by
    intro i c
    obtain ⟨L, hL⟩ : ∃ L, EN i - SN i = L + 1 := ⟨EN i - SN i - 1, by omega⟩
    rw [hrow i, hL, List.range'_concat, List.map_append, Nat.add_sub_cancel, Nat.one_mul,
      show SN i + L = EN i - 1 by omega]
    rfl
  have hJ : ∀ j : Fin M.toNat, ∃ i : Fin n.toNat, SN i < EN i ∧ ((raw .i64 M sel)[j.1]?.getD 0).toNat = i ∧
      K.row j = Vals.row (A := .arr B) ⟨m, lo, up, f⟩ i ∧
      Vals.row (A := .prod (.arr B) B) (⟨m, sM, l, f⟩, tl) j =
        ((List.range' (SN i) (EN i - SN i - 1)).map g, g (EN i - 1)) := by
    intro j
    obtain ⟨i, hi, hKi⟩ := Vals.gather_row _ hK j
    obtain ⟨hin, c⟩ := hsel j.1 j.2
    rw [hi] at c
    obtain ⟨i2, hi2, hs2⟩ := Arr.gather_raw s hsM j
    obtain ⟨i3, hi3, he3⟩ := Arr.gather_raw e heM j
    have e2 : i = i2 := Fin.ext (hi.symm.trans hi2)
    have e3 : i = i3 := Fin.ext (hi.symm.trans hi3)
    subst e2 e3
    rw [(hw1 _ i.2).1] at hs2
    rw [(hw1 _ i.2).2] at he3
    have hEm : EN i ≤ m.toNat := by have := hb1 i; omega
    have hlw : (raw .i64 M l.enc)[j.1]?.getD 0 = (EN i - 1).toUInt64 := by
      have es := (colMap_raw (colArr_ok hl)).2.2.2 j.1 j.2
      rw [colConst_raw hc1, Array.getElem?_replicate, if_pos j.2, Option.getD_some, he3] at es
      simp only [Op.eval, Except.ok.injEq] at es
      rw [← es, toUInt64_sub (by omega)]; rfl
    obtain ⟨i4, hi4, ht4⟩ := Vals.gather_row _ htl j
    have e4 : i4.1 = EN i - 1 := by rw [← hi4, hlw, toNat_toUInt64 (by have := hb1 i; omega)]
    refine ⟨i, c, hi, hKi, ?_⟩
    show (Vals.row (A := .arr B) ⟨m, sM, l, f⟩ j, tl.row j) = _
    rw [ht4, Vals.row_cell sM l f j hs2 hlw (by omega) (by omega) hm63, show EN i - 1 - SN i = EN i - SN i - 1 by omega]
    simp only [g]; rw [dif_pos (by omega)]
    exact congrArg (fun r => (_, f.row r)) (Fin.ext e4)
  simp only [Tab.Holds]
  constructor
  · rintro ⟨j, rfl, rfl⟩
    obtain ⟨i, c, -, hKi, hv⟩ := hJ j
    rw [hv, hKi]; exact ⟨⟨i, rfl⟩, hsnoc i c⟩
  · rintro ⟨⟨i, rfl⟩, hx⟩
    have c : SN i < EN i := by
      have := congrArg List.length hx; rw [hrow i] at this; simp at this; omega
    obtain ⟨k, hk, hki⟩ := hall i i.2 c
    obtain ⟨i', -, hi', hKi, hv⟩ := hJ ⟨k, hk⟩
    have e' : i' = i := Fin.ext (by rw [← hi', hki])
    subst e'
    rw [hsnoc i' c] at hx
    obtain ⟨h1, h2⟩ := List.append_inj' hx rfl
    exact ⟨⟨k, hk⟩, hKi, by rw [hv, h1, (List.cons.inj h2).1]⟩

/-- A round's split of what is left at each key (`peelL` by `uncons`, `peelR` by `unsnoc`), given the law of its
converse `u`: the element read now and the rest, each the pairs `rest ≫ u` projected (`foldRounds_holds`' `hpeel`). -/
theorem peel_holds {K E C : Obj} {rest : Tab K (.arr E)} {u : Tab (.arr E) C} {c : Tab K C}
    {o₁ : Tab C E} {o₂ : Tab C (.arr E)} {el : Tab K E} {rest' : Tab K (.arr E)} (Pe : (Obj.arr E).El → C.El → Prop)
    (fst : C.El → E.El) (snd : C.El → (Obj.arr E).El)
    (hu : ∀ r q, u.Holds r q ↔ (∃ i, rest.val.row i = r) ∧ Pe r q) (hc : rest.comp u = .ok c)
    (h₁ : ∀ q x, o₁.Holds q x ↔ (∃ i, c.val.row i = q) ∧ x = fst q)
    (h₂ : ∀ q r', o₂.Holds q r' ↔ (∃ i, c.val.row i = q) ∧ r' = snd q)
    (he : c.comp o₁ = .ok el) (hr : c.comp o₂ = .ok rest') :
    (∀ k x, el.Holds k x ↔ ∃ r q, rest.Holds k r ∧ Pe r q ∧ fst q = x) ∧
    ∀ k r', rest'.Holds k r' ↔ ∃ r q, rest.Holds k r ∧ Pe r q ∧ snd q = r' := by
  have hc' : ∀ k q, c.Holds k q ↔ ∃ r, rest.Holds k r ∧ Pe r q := fun k q => by
    rw [comp_holds hc]
    exact exists_congr fun r => and_congr_right fun ⟨i, _, hi⟩ => (hu r q).trans (and_iff_right ⟨i, hi⟩)
  have side {D : Obj} {o : Tab C D} (p : C.El → D.El) (ho : ∀ q y, o.Holds q y ↔ (∃ i, c.val.row i = q) ∧ y = p q)
      {t : Tab K D} (ht : c.comp o = .ok t) (k : K.El) (y : D.El) :
      t.Holds k y ↔ ∃ r q, rest.Holds k r ∧ Pe r q ∧ p q = y := by
    rw [comp_holds ht]
    constructor
    · rintro ⟨q, hq, hy⟩
      obtain ⟨r, hr, hp⟩ := (hc' k q).1 hq
      exact ⟨r, q, hr, hp, ((ho q y).1 hy).2.symm⟩
    · rintro ⟨r, q, hr, hp, rfl⟩
      obtain ⟨i, -, hi⟩ := (hc' k q).2 ⟨r, hr, hp⟩
      exact ⟨q, (hc' k q).2 ⟨r, hr, hp⟩, (ho q _).2 ⟨⟨i, hi⟩, rfl⟩⟩
  exact ⟨side fst h₁ he, side snd h₂ hr⟩

/-- **`peelL` is `cons°` on what is left** (`uncons_holds`): `x` the head of a key's array, the rest its tail. -/
theorem peelL_holds {K E : Obj} {rest : Tab K (.arr E)} {el : Tab K E} {rest' : Tab K (.arr E)}
    (h : peelL rest = .ok (el, rest')) :
    (∀ k x, el.Holds k x ↔ ∃ r r', rest.Holds k r ∧ r = x :: r') ∧
    ∀ k r', rest'.Holds k r' ↔ ∃ r x, rest.Holds k r ∧ r = x :: r' := by
  unfold peelL at h; simp only [bind, Except.bind_eq_ok'] at h
  obtain ⟨u, hu, c, hc, o₁, ho₁, a, ha, o₂, ho₂, b, hb, h⟩ := h
  cases h
  obtain ⟨h1, h2⟩ := peel_holds (C := .prod E (.arr E)) (fun r q => r = q.1 :: q.2) Prod.fst Prod.snd
    (uncons_holds hu) hc (outl_holds ho₁) (outr_holds ho₂) ha hb
  exact ⟨fun k x => (h1 k x).trans ⟨fun ⟨r, q, hr, hp, hx⟩ => ⟨r, q.2, hr, hx ▸ hp⟩,
      fun ⟨r, r', hr, hp⟩ => ⟨r, (x, r'), hr, hp, rfl⟩⟩,
    fun k r' => (h2 k r').trans ⟨fun ⟨r, q, hr, hp, hx⟩ => ⟨r, q.1, hr, hx ▸ hp⟩,
      fun ⟨r, x, hr, hp⟩ => ⟨r, (x, r'), hr, hp, rfl⟩⟩⟩

/-- **`peelR` is `snoc°` on what is left** (`unsnoc_holds`): `x` the last element of a key's array, the rest its
front. -/
theorem peelR_holds {K E : Obj} {rest : Tab K (.arr E)} {el : Tab K E} {rest' : Tab K (.arr E)}
    (h : peelR rest = .ok (el, rest')) :
    (∀ k x, el.Holds k x ↔ ∃ r r', rest.Holds k r ∧ r = r' ++ [x]) ∧
    ∀ k r', rest'.Holds k r' ↔ ∃ r x, rest.Holds k r ∧ r = r' ++ [x] := by
  unfold peelR at h; simp only [bind, Except.bind_eq_ok'] at h
  obtain ⟨u, hu, c, hc, o₂, ho₂, a, ha, o₁, ho₁, b, hb, h⟩ := h
  cases h
  obtain ⟨h1, h2⟩ := peel_holds (C := .prod (.arr E) E) (fun r q => r = q.1 ++ [q.2]) Prod.snd Prod.fst
    (unsnoc_holds hu) hc (outr_holds ho₂) (outl_holds ho₁) ha hb
  exact ⟨fun k x => (h1 k x).trans ⟨fun ⟨r, q, hr, hp, hx⟩ => ⟨r, q.1, hr, hx ▸ hp⟩,
      fun ⟨r, r', hr, hp⟩ => ⟨r, (r', x), hr, hp, rfl⟩⟩,
    fun k r' => (h2 k r').trans ⟨fun ⟨r, q, hr, hp, hx⟩ => ⟨r, q.2, hr, hx ▸ hp⟩,
      fun ⟨r, x, hr, hp⟩ => ⟨r, (r', x), hr, hp, rfl⟩⟩⟩

/-- **`R.pack` denotes `R`** (`Vals.pack_row` on both sides): `foldRounds_holds`' `hpack`. -/
theorem pack_holds {k v : Obj} {R R' : Tab k v} (h : R.pack = .ok R') (a : k.El) (b : v.El) :
    R'.Holds a b ↔ R.Holds a b := by
  unfold Tab.pack at h; simp only [bind, Except.bind_eq_ok'] at h
  obtain ⟨key, hk, val, hv, h⟩ := h
  cases h
  simp only [Tab.Holds, Vals.pack_row _ hk, Vals.pack_row _ hv]

end Tab


/-- **`ldiv` holds as `ldivDen`**: a pair `(b, c)` of the counting stage has as many `R`-witnesses `a` of `b` with
`S a c` as `R`-witnesses of `b` at all, so (rows being distinct) every one; the vacuous `b`s come from the `CROSS`. -/
theorem Tab.ldiv_holds {A B C : Obj} {R : Tab A B} {S : Tab A C} {UB : Tab B B} {UC : Tab C C} {T : Tab B C}
    (h : Tab.ldiv R S UB UC = .ok T) (b : B.El) (c : C.El) :
    T.Holds b c ↔ Lang.ldivDen R.Holds S.Holds UB.Holds UC.Holds b c := by
  classical
  unfold Tab.ldiv at h
  simp only [bind] at h
  rw [Except.bind_eq_ok'] at h; obtain ⟨r, hr, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨s, hs, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨Q, hQ, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨es, hes, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨⟨vs, p⟩, hasc, h⟩ := h; try dsimp only at h
  rw [Except.bind_eq_ok'] at h; obtain ⟨⟨k, g, f⟩, hseen, h⟩ := h; try dsimp only at h
  rw [Except.bind_eq_ok'] at h; obtain ⟨c1, hc1, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨cnt, hcnt, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨⟨N, sh⟩, hcat, h⟩ := h; try dsimp only at h
  split at h
  · rw [Except.bind_eq_ok'] at h; obtain ⟨_, h', -⟩ := h; cases h'
  rename_i hN63
  rw [Except.bind_eq_ok'] at h; obtain ⟨_, -, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨z, hz, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨bs, hbs, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨⟨bv, bp⟩, hbasc, h⟩ := h; try dsimp only at h
  rw [Except.bind_eq_ok'] at h; obtain ⟨⟨bk, bg, bf⟩, hbseen, h⟩ := h; try dsimp only at h
  rw [Except.bind_eq_ok'] at h; obtain ⟨cn, hcn, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨lt, hlt, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨cR, hcR, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨code, hcode, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨q, hq, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨ck, hck, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨qa, hqa, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨cq, hcq, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨d, hd, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨eqc, heqc, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨⟨M, sel⟩, hM, h⟩ := h; try dsimp only at h
  rw [Except.bind_eq_ok'] at h; obtain ⟨ix, hix, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨X1, hX1, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨Y1, hY1, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨ub, hub, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨rr, hrr, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨df, hdf, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨uc, huc, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨cr, hcr, h⟩ := h
  rw [union_holds h, cross_holds hcr]
  have hP : (∃ j, X1.row j = b ∧ Y1.row j = c) ↔
      (∃ a, R.Holds a b ∧ S.Holds a c) ∧ ∀ a, R.Holds a b → S.Holds a c := by
    have hU64 : USize.size ≤ 2 ^ 64 := by rcases USize.size_eq with h | h <;> omega
    obtain ⟨hNn, hoff⟩ := catPlan_ok hcat
    have hzr := Vals.concat_row hNn hoff r.val Q.key hz
    have hNU := N.toNat_lt_size
    obtain ⟨π1, gr1, fs1, hkN, hp1, -, hsur1, hcnt1, hg1, hf1, hrow1⟩ := group_rows hes hasc hseen
    obtain ⟨π2, gr2, fs2, hbkN, hp2, hinj2, hsur2, hcnt2, hg2, -, hrow2⟩ := group_rows hbs hbasc hbseen
    have hK : k.toUSize.toNat = k := USize.toNat_ofNat_of_lt' (by omega)
    have hbK : bk.toUSize.toNat = bk := USize.toNat_ofNat_of_lt' (by omega)
    have hnU : r.n.toUInt64 = r.n.toNat.toUInt64 := UInt64.toNat_inj.mp (by simp <;> omega)
    ------------------------------------------------------------------ `Q`'s rows, `r`'s rows
    have hQh : ∀ a, Q.Holds b (a, c) ↔ R.Holds a b ∧ S.Holds a c := fun a => by
      obtain ⟨U₀, hU₀, hH₀⟩ := compOne_canon hQ; rw [canon_holds hU₀, hH₀]
      constructor
      · rintro ⟨a', ⟨i, h1, h2⟩, ⟨j, h3, h4⟩⟩
        obtain ⟨e1, e2⟩ := Prod.mk.inj (show (s.key.row j, s.val.row j) = (a, c) from h4)
        exact ⟨(canon_holds hr a b).1 ⟨i, h2.trans (h3.symm.trans e1), h1⟩, (canon_holds hs a c).1 ⟨j, e1, e2⟩⟩
      · rintro ⟨hab, hac⟩
        obtain ⟨i, h1, h2⟩ := (canon_holds hr a b).2 hab
        obtain ⟨j, h3, h4⟩ := (canon_holds hs a c).2 hac
        exact ⟨a, ⟨i, h2, h1⟩, ⟨j, h3, show (s.key.row j, s.val.row j) = (a, c) by rw [h3, h4]⟩⟩
    obtain ⟨U, hUc, -⟩ := compOne_canon hQ
    have hQd : ∀ i i' : Fin Q.n.toNat, Q.key.row i = Q.key.row i' → Q.val.row i = Q.val.row i' → i = i' :=
      fun i i' e1 e2 => Classical.byContradiction fun hne => Tab.canon_distinct hUc hne (by rw [e1, e2])
    have hrd : ∀ i i' : Fin r.n.toNat, r.key.row i = r.key.row i' → r.val.row i = r.val.row i' → i = i' :=
      fun i i' e1 e2 => Classical.byContradiction fun hne => Tab.canon_distinct hr hne (by rw [e1, e2])
    ------------------------------------------------------------------ the finite count
    obtain ⟨P1, hP1⟩ : ∃ P : Nat → Bool, ∀ i, P i =
        decide (∃ h : i < Q.n.toNat, Q.key.row ⟨i, h⟩ = b ∧ Q.val.2.row ⟨i, h⟩ = c) := ⟨_, fun _ => rfl⟩
    obtain ⟨P2, hP2⟩ : ∃ P : Nat → Bool, ∀ i, P i = decide (∃ h : i < r.n.toNat, r.val.row ⟨i, h⟩ = b) :=
      ⟨_, fun _ => rfl⟩
    have hfin : (List.range Q.n.toNat).countP P1 = (List.range N.toNat).countP P2 ↔
        ∀ a, R.Holds a b → S.Holds a c := by
      obtain ⟨f1, hf1'⟩ : ∃ F : Nat → Option A.El, ∀ i,
          F i = if h : i < Q.n.toNat then some (Q.val.1.row ⟨i, h⟩) else none := ⟨_, fun _ => rfl⟩
      obtain ⟨f2, hf2'⟩ : ∃ F : Nat → Option A.El, ∀ i,
          F i = if h : i < r.n.toNat then some (r.key.row ⟨i, h⟩) else none := ⟨_, fun _ => rfl⟩
      have m1 : ∀ y, y ∈ ((List.range Q.n.toNat).filter P1).map f1 ↔ ∃ a, y = some a ∧ Q.Holds b (a, c) := by
        intro y; simp only [List.mem_map, List.mem_filter, List.mem_range, hP1, decide_eq_true_eq]
        constructor
        · rintro ⟨i, ⟨hi, hi', h1, h2⟩, rfl⟩
          rw [hf1', dif_pos hi]
          exact ⟨_, rfl, ⟨i, hi⟩, h1, show (Q.val.1.row ⟨i, hi⟩, Q.val.2.row ⟨i, hi⟩) = _ by rw [h2]⟩
        · rintro ⟨a, rfl, ⟨i, h1, h2⟩⟩
          obtain ⟨e1, e2⟩ := Prod.mk.inj (show (Q.val.1.row i, Q.val.2.row i) = (a, c) from h2)
          exact ⟨i.1, ⟨i.2, i.2, h1, e2⟩, by rw [hf1', dif_pos i.2]; exact congrArg some e1⟩
      have m2 : ∀ y, y ∈ ((List.range N.toNat).filter P2).map f2 ↔ ∃ a, y = some a ∧ R.Holds a b := by
        intro y; simp only [List.mem_map, List.mem_filter, List.mem_range, hP2, decide_eq_true_eq]
        constructor
        · rintro ⟨i, ⟨-, hi, h1⟩, rfl⟩
          rw [hf2', dif_pos hi]; exact ⟨_, rfl, (canon_holds hr _ _).1 ⟨⟨i, hi⟩, rfl, h1⟩⟩
        · rintro ⟨a, rfl, hab⟩
          obtain ⟨i, h1, h2⟩ := (canon_holds hr a b).2 hab
          exact ⟨i.1, ⟨by have := i.2; omega, i.2, h2⟩, by rw [hf2', dif_pos i.2]; exact congrArg some h1⟩
      have d1 : (((List.range Q.n.toNat).filter P1).map f1).Nodup := by
        refine List.pairwise_map.2 (List.Pairwise.imp_of_mem (fun {i i'} hi hi' hne e => hne ?_)
          (List.Pairwise.filter P1 List.nodup_range))
        simp only [List.mem_filter, List.mem_range, hP1, decide_eq_true_eq] at hi hi'
        obtain ⟨-, hi, h1, h2⟩ := hi
        obtain ⟨-, hi', h1', h2'⟩ := hi'
        rw [hf1', hf1', dif_pos hi, dif_pos hi'] at e
        have := hQd ⟨i, hi⟩ ⟨i', hi'⟩ (h1.trans h1'.symm)
          (show (Q.val.1.row _, Q.val.2.row _) = (Q.val.1.row _, Q.val.2.row _) by rw [Option.some.inj e, h2, h2'])
        exact congrArg Fin.val this
      have d2 : (((List.range N.toNat).filter P2).map f2).Nodup := by
        refine List.pairwise_map.2 (List.Pairwise.imp_of_mem (fun {i i'} hi hi' hne e => hne ?_)
          (List.Pairwise.filter P2 List.nodup_range))
        simp only [List.mem_filter, List.mem_range, hP2, decide_eq_true_eq] at hi hi'
        obtain ⟨-, hi, h1⟩ := hi
        obtain ⟨-, hi', h1'⟩ := hi'
        rw [hf2', hf2', dif_pos hi, dif_pos hi'] at e
        exact congrArg Fin.val (hrd ⟨i, hi⟩ ⟨i', hi'⟩ (Option.some.inj e) (h1.trans h1'.symm))
      have sub : ((List.range Q.n.toNat).filter P1).map f1 ⊆ ((List.range N.toNat).filter P2).map f2 :=
        fun y hy => by obtain ⟨a, rfl, hq⟩ := (m1 y).1 hy; exact (m2 _).2 ⟨a, rfl, ((hQh a).1 hq).1⟩
      have := nodup_length_eq_iff d1 d2 sub
      simp only [List.length_map] at this
      rw [List.countP_eq_length_filter, List.countP_eq_length_filter, this]
      constructor
      · intro hs a hab
        obtain ⟨a', e, hq⟩ := (m1 _).1 (hs ((m2 _).2 ⟨a, rfl, hab⟩))
        cases e; exact ((hQh a).1 hq).2
      · intro hall y hy
        obtain ⟨a, rfl, hab⟩ := (m2 y).1 hy
        exact (m1 _).2 ⟨a, rfl, (hQh a).2 ⟨hab, hall a hab⟩⟩
    ------------------------------------------------------------------ the words of `cnt`, `d`, `eqc`
    have hcntw : ∀ G < k, (raw .i64 k.toUSize cnt)[G]?.getD 0 =
        ((List.range Q.n.toNat).countP fun q => gr1 q == G && true).toUInt64 :=
      fun G hG => fold_add_count (Tab.groupFold_ok (fn := (· + ·)) (fun _ _ => rfl) hseen hcnt).1
        (Tab.groupFold_ok (fn := (· + ·)) (fun _ _ => rfl) hseen hcnt).2.2 gr1 (fun _ => true) (fun q hq => (hg1 q hq).1)
        (fun q hq => by have := (hg1 q hq).2; omega) (fun q hq => by rw [colConst_raw hc1]; simp [hq]) G (by omega)
    have hcntG : ∀ G < k, ∀ h : π1 (fs1 G) < Q.n.toNat, Q.key.row ⟨_, h⟩ = b → Q.val.2.row ⟨_, h⟩ = c →
        ((List.range Q.n.toNat).countP fun q => gr1 q == G && true) = (List.range Q.n.toNat).countP P1 := by
      intro G hG h hb hc
      rw [← hcnt1 P1]
      refine List.countP_congr fun q hq => ?_
      have hq := List.mem_range.1 hq
      obtain ⟨-, hfn, hfg⟩ := hf1 G hG
      have e := hrow1 q hq (fs1 G) hfn
      rw [hfg] at e
      simp only [Bool.and_true, beq_iff_eq, hP1, decide_eq_true_eq]
      rw [e]
      constructor
      · intro hr'
        obtain ⟨e1, e2⟩ := Prod.mk.inj (show (Q.key.row _, Q.val.2.row _) = (Q.key.row _, Q.val.2.row _) from
          hr' (hp1 q hq).2 h)
        exact ⟨(hp1 q hq).2, e1.trans hb, e2.trans hc⟩
      · rintro ⟨h', e1, e2⟩ h1 h2
        show (Q.key.row _, Q.val.2.row _) = (Q.key.row _, Q.val.2.row _)
        rw [e1, e2, hb, hc]
    have hltw : ∀ q < N.toNat, (raw .i64 N lt)[q]?.getD 0 = if decide (π2 q < r.n.toNat) then 1 else 0 :=
      fun q hq => by
        have e := (colMap_raw hlt).2.2.2 q hq
        rw [(hp2 q hq).1, colConst_raw hcn, Array.getElem?_replicate, if_pos hq, Option.getD_some, hnU,
          eval_lt_nat (by have := (hp2 q hq).2; omega) (by omega), Except.ok.injEq] at e
        rw [← e]; simp
    have hqw : ∀ G < k, (raw .i64 k.toUSize q)[G]?.getD 0 = (π1 (fs1 G)).toUInt64 := fun G hG => by
      obtain ⟨hfw, hfn, -⟩ := hf1 G hG
      rw [(kgather_word hq G (by omega)).2, hfw, toNat_toUInt64 (by omega), (hp1 _ hfn).1]
    have hdG : ∀ G < k, ∀ h : π1 (fs1 G) < Q.n.toNat, Q.key.row ⟨_, h⟩ = b →
        (raw .i64 k.toUSize d)[G]?.getD 0 = ((List.range N.toNat).countP P2).toUInt64 := by
      intro G hG h hb
      have hqaw : (raw .i64 k.toUSize qa)[G]?.getD 0 = (r.n.toNat + π1 (fs1 G)).toUInt64 := by
        have e := (colMap_raw hqa).2.2.2 G (by omega)
        rw [hqw G hG, colConst_raw hck, Array.getElem?_replicate, if_pos (by omega), Option.getD_some] at e
        simp only [Op.eval, Except.ok.injEq] at e
        rw [← e, hnU, ← UInt64.ofNat_add, Nat.add_comm]
      obtain ⟨q2, hq2, hpq2⟩ := hsur2 (r.n.toNat + π1 (fs1 G)) (by omega)
      have hcqw : (raw .i64 k.toUSize cq)[G]?.getD 0 = (gr2 q2).toUInt64 := by
        rw [(kgather_word hcq G (by omega)).2, hqaw, toNat_toUInt64 (by omega), ← hpq2,
          scatter_last_at hcode π2 (fun q hq => (hp2 q hq).1) (fun q hq => (hp2 q hq).2) hinj2 q2 hq2,
          (hg2 q2 hq2).1]
      have hgq := (hg2 q2 hq2).2
      rw [(kgather_word hd G (by omega)).2, hcqw, toNat_toUInt64 (by omega),
        fold_add_count (Tab.groupFold_ok (fn := (· + ·)) (fun _ _ => rfl) hbseen hcR).1
          (Tab.groupFold_ok (fn := (· + ·)) (fun _ _ => rfl) hbseen hcR).2.2 gr2 (fun q => decide (π2 q < r.n.toNat))
          (fun q hq => (hg2 q hq).1)
          (fun q hq => by have := (hg2 q hq).2; omega) hltw (gr2 q2) (by omega), ← hcnt2 P2]
      have hz2 : ∀ h2 : π2 q2 < N.toNat, z.row ⟨_, h2⟩ = b := fun h2 => by
        rw [hzr, dif_neg (show ¬ π2 q2 < r.n.toNat by omega)]
        have : (⟨π2 q2 - r.n.toNat, by omega⟩ : Fin Q.n.toNat) = ⟨π1 (fs1 G), h⟩ := Fin.ext (by simp only; omega)
        rw [this]; exact hb
      congr 1
      refine List.countP_congr fun q' hq' => ?_
      have hq' := List.mem_range.1 hq'
      have e := hrow2 q' hq' q2 hq2
      rw [hP2]
      rw [Bool.eq_iff_iff]
      simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, e, iff_true]
      constructor
      · rintro ⟨hr', hl⟩
        have hzq : z.row ⟨π2 q', (hp2 q' hq').2⟩ = r.val.row ⟨π2 q', hl⟩ := by rw [hzr, dif_pos hl]
        exact ⟨hl, hzq.symm.trans ((hr' (hp2 q' hq').2 (hp2 q2 hq2).2).trans (hz2 _))⟩
      · rintro ⟨hl, hv⟩
        have hzq : z.row ⟨π2 q', (hp2 q' hq').2⟩ = r.val.row ⟨π2 q', hl⟩ := by rw [hzr, dif_pos hl]
        exact ⟨fun h1 h2 => by rw [hz2 h2]; exact hzq.trans hv, hl⟩
    -- `Op.eval .eq` is `if a == x then 1 else 0` by definition (its `w` is private to `Rel.Kernel.Op`)
    have heqe : ∀ G < k, Except.ok (if (raw .i64 k.toUSize cnt)[G]?.getD 0 == (raw .i64 k.toUSize d)[G]?.getD 0
        then (1 : UInt64) else 0) = (.ok ((raw .i64 k.toUSize eqc)[G]?.getD 0) : Except String UInt64) :=
      fun G hG => (colMap_raw heqc).2.2.2 G (by omega)
    have hb2 : ∀ G < k, (raw .i64 k.toUSize eqc)[G]?.getD 0 < 2 := fun G hG => by
      rw [← Except.ok.inj (heqe G hG)]; split <;> decide
    have heqw : ∀ G < k, (raw .i64 k.toUSize eqc)[G]?.getD 0 ≠ 0 ↔
        (raw .i64 k.toUSize cnt)[G]?.getD 0 = (raw .i64 k.toUSize d)[G]?.getD 0 := fun G hG => by
      rw [← Except.ok.inj (heqe G hG)]
      split
      · exact ⟨fun _ => beq_iff_eq.1 ‹_›, fun _ => by decide⟩
      · exact ⟨fun h' => absurd rfl h', fun e => absurd (beq_iff_eq.2 e) ‹_›⟩
    have hsel := whereCol_spec hM (fun G hG => hb2 G (by omega))
    have hsz := whereCol_size hM
    have hcl : ∀ G < k, ((List.range Q.n.toNat).countP P1 : Nat).toUInt64 =
        ((List.range N.toNat).countP P2 : Nat).toUInt64 ↔
        (List.range Q.n.toNat).countP P1 = (List.range N.toNat).countP P2 := fun G _ => by
      have := List.countP_le_length (p := P1) (l := List.range Q.n.toNat)
      have := List.countP_le_length (p := P2) (l := List.range N.toNat)
      simp only [List.length_range] at *
      constructor
      · intro e; have := congrArg UInt64.toNat e
        rwa [toNat_toUInt64 (by omega), toNat_toUInt64 (by omega)] at this
      · intro e; rw [e]
    ------------------------------------------------------------------ the kept groups
    constructor
    · rintro ⟨j, hj1, hj2⟩
      obtain ⟨i, hi, hxi⟩ := Vals.gather_row _ hX1 j
      obtain ⟨i', hi', hyi⟩ := Vals.gather_row _ hY1 j
      have e : i = i' := Fin.ext (by rw [← hi, hi'])
      subst e
      have hjM : j.1 < (raw .i64 M sel).size := by rw [hsz]; exact j.2
      have hG := List.mem_map_of_mem (f := UInt64.toNat) (Array.getElem_mem_toList hjM)
      rw [hsel, List.mem_filter, List.mem_range, decide_eq_true_eq] at hG
      obtain ⟨hGk, hGne⟩ := hG
      rw [hK] at hGk
      have hixw := (kgather_word hix j.1 j.2).2
      rw [Array.getElem?_eq_getElem hjM, Option.getD_some, hqw _ hGk] at hixw
      generalize ((raw .i64 M sel)[j.1]'hjM).toNat = G at hGk hGne hixw
      obtain ⟨-, hfn, -⟩ := hf1 G hGk
      have hπ := (hp1 _ hfn).2
      have ei : i = ⟨π1 (fs1 G), hπ⟩ := Fin.ext (by rw [← hi, hixw, toNat_toUInt64 (by omega)])
      subst ei
      have hb' : Q.key.row ⟨_, hπ⟩ = b := hxi.symm.trans hj1
      have hc' : Q.val.2.row ⟨_, hπ⟩ = c := hyi.symm.trans hj2
      have hall := hfin.1 ((hcl G hGk).1 (by
        rw [← hcntG G hGk hπ hb' hc', ← hcntw G hGk, ← hdG G hGk hπ hb']; exact (heqw G hGk).1 hGne))
      exact ⟨⟨_, ((hQh _).1 ⟨_, hb', show (Q.val.1.row _, Q.val.2.row _) = _ by rw [hc']⟩)⟩, hall⟩
    · rintro ⟨⟨a0, hab, hac⟩, hall⟩
      obtain ⟨i, h1, h2⟩ := (hQh a0).2 ⟨hab, hac⟩
      obtain ⟨-, e2⟩ := Prod.mk.inj (show (Q.val.1.row i, Q.val.2.row i) = (a0, c) from h2)
      obtain ⟨q0, hq0, hπq⟩ := hsur1 i.1 i.2
      have hG := (hg1 q0 hq0).2
      obtain ⟨-, hfn, hfg⟩ := hf1 (gr1 q0) hG
      have hπ := (hp1 _ hfn).2
      have hrr := (hrow1 (fs1 (gr1 q0)) hfn q0 hq0).1 hfg hπ (hp1 _ hq0).2
      obtain ⟨eb, ec⟩ := Prod.mk.inj (show (Q.key.row _, Q.val.2.row _) = (Q.key.row _, Q.val.2.row _) from hrr)
      have hfi : (⟨π1 q0, (hp1 _ hq0).2⟩ : Fin Q.n.toNat) = i := Fin.ext hπq
      rw [hfi] at eb ec
      have hb' : Q.key.row ⟨_, hπ⟩ = b := eb.trans h1
      have hc' : Q.val.2.row ⟨_, hπ⟩ = c := ec.trans e2
      have hne : (raw .i64 k.toUSize eqc)[gr1 q0]?.getD 0 ≠ 0 := (heqw _ hG).2 (by
        rw [hcntw _ hG, hcntG _ hG hπ hb' hc', hdG _ hG hπ hb']; exact (hcl _ hG).2 (hfin.2 hall))
      have hm : gr1 q0 ∈ (raw .i64 M sel).toList.map UInt64.toNat := by
        rw [hsel, List.mem_filter, List.mem_range, decide_eq_true_eq, hK]; exact ⟨hG, hne⟩
      obtain ⟨w, hw, hwi⟩ := List.mem_map.1 hm
      obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hw
      have hj' : j < (raw .i64 M sel).size := by simpa using hj
      have hjM : j < M.toNat := by rw [← hsz]; exact hj'
      simp only [Array.getElem_toList] at hwi
      have hixw := (kgather_word hix j hjM).2
      rw [Array.getElem?_eq_getElem hj', Option.getD_some, hwi, hqw _ hG] at hixw
      obtain ⟨i1, hi1, hx1⟩ := Vals.gather_row _ hX1 ⟨j, hjM⟩
      obtain ⟨i2, hi2, hy2⟩ := Vals.gather_row _ hY1 ⟨j, hjM⟩
      have e1 : i1 = ⟨_, hπ⟩ := Fin.ext (by rw [← hi1, hixw, toNat_toUInt64 (by omega)])
      have e2 : i2 = ⟨_, hπ⟩ := Fin.ext (by rw [← hi2, hixw, toNat_toUInt64 (by omega)])
      subst e1 e2
      exact ⟨⟨j, hjM⟩, hx1.trans hb', hy2.trans hc'⟩
  have hD : (∃ i, df.key.row i = b) ↔ (∃ b', UB.Holds b' b) ∧ ¬∃ a, R.Holds a b := by
    constructor
    · rintro ⟨i, rfl⟩
      have h1 := (diff_holds hdf _ _).1 ⟨i, rfl, rfl⟩
      obtain ⟨e, hb⟩ := (ran_holds hub _ _).1 h1.1
      rw [← e] at h1
      exact ⟨hb, fun ha => h1.2 ((ran_holds hrr _ _).2 ⟨rfl, ha⟩)⟩
    · rintro ⟨hb, hn⟩
      obtain ⟨i, h1, -⟩ := (diff_holds hdf b b).2
        ⟨(ran_holds hub b b).2 ⟨rfl, hb⟩, fun h' => hn ((ran_holds hrr b b).1 h').2⟩
      exact ⟨i, h1⟩
  have hU : (∃ j, uc.key.row j = c) ↔ ∃ c', UC.Holds c' c := by
    constructor
    · rintro ⟨j, rfl⟩
      obtain ⟨e, hc⟩ := (ran_holds huc _ _).1 ⟨j, rfl, rfl⟩
      exact hc
    · intro hc
      obtain ⟨j, h1, -⟩ := (ran_holds huc c c).2 ⟨rfl, hc⟩
      exact ⟨j, h1⟩
  show _ ↔ (∀ a, R.Holds a b → S.Holds a c) ∧ ((∃ a, R.Holds a b) ∨ ((∃ b', UB.Holds b' b) ∧ ∃ c', UC.Holds c' c))
  rw [show (⟨M, X1, Y1⟩ : Tab B C).Holds b c ↔ _ from hP, hD, hU]
  by_cases hb : ∃ a, R.Holds a b
  · constructor
    · rintro (⟨-, hall⟩ | ⟨⟨-, hn⟩, -⟩)
      · exact ⟨hall, Or.inl hb⟩
      · exact absurd hb hn
    · rintro ⟨hall, -⟩
      obtain ⟨a, ha⟩ := hb
      exact Or.inl ⟨⟨a, ha, hall a ha⟩, hall⟩
  · constructor
    · rintro (⟨⟨a, ha, -⟩, -⟩ | ⟨⟨hb', -⟩, hc'⟩)
      · exact absurd ⟨a, ha⟩ hb
      · exact ⟨fun a ha => absurd ⟨a, ha⟩ hb, Or.inr ⟨hb', hc'⟩⟩
    · rintro ⟨-, (ha | ⟨hb', hc'⟩)⟩
      · exact absurd ha hb
      · exact Or.inr ⟨⟨hb', hb⟩, hc'⟩

/-- **`rdiv` holds as `rdivDen`**: it is `ldiv` of the two converses, conversed (`R / S = (S° \ R°)°`). -/
theorem Tab.rdiv_holds {A B C : Obj} {R : Tab A C} {S : Tab B C} {UA : Tab A A} {UB : Tab B B} {T : Tab A B}
    (h : Tab.rdiv R S UA UB = .ok T) (a : A.El) (b : B.El) :
    T.Holds a b ↔ Lang.rdivDen R.Holds S.Holds UA.Holds UB.Holds a b := by
  unfold Tab.rdiv at h
  simp only [bind] at h
  rw [Except.bind_eq_ok'] at h; obtain ⟨S', hS, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨R', hR, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨L, hL, h⟩ := h
  rw [conv_holds h, ldiv_holds hL]
  simp only [Lang.ldivDen, Lang.rdivDen, conv_holds hS, conv_holds hR, and_comm (a := ∃ b', UB.Holds b' b)]

/-! ## Checks on `foR` tables -/

section Checks

/-- An operator's answer as a list, `none` on `.error`. -/
private def newL {k v : Obj} (r : Except String (Tab k v)) : Option (List (k.El × v.El)) := r.toOption.map Tab.toList

/-- The answer `r` runs and holds one row per key of `sp`, its cell the elements of `sp`'s cell as a set: an answer's
cell is in `kasc`'s order (`ordCode`), a spec's in its own. -/
private def cellsOk {k v : Obj} [BEq k.El] [BEq v.El] (r : Except String (Tab k (.arr v)))
    (sp : List (k.El × List v.El)) : Bool :=
  let sub (x y : List (k.El × List v.El)) := x.all fun (a, ys) => y.any fun (a', ys') =>
    a == a' && ys.length == ys'.length && ys.all ys'.contains && ys'.all ys.contains
  match r with
  | .ok T => let b := sp.eraseDups; T.toList.length == b.length && sub T.toList b && sub b T.toList
  | .error _ => false

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
private def us : List Int64 := [1, 2, 5, 7, 9, -3, 2]
private def U := Alg.col us

/-- `R\S` within the universes `UB`, `UC` (`ldivDen`): `(b, c)` when every `a` with `R a b` has `S a c`, and `b` is a
target of `R` or `b`, `c` lie in the universes. -/
private def ldivSp {A B C : Obj} [BEq A.El] [BEq B.El] [BEq C.El] (R : Tab A B) (S : Tab A C) (UB : Tab B B)
    (UC : Tab C C) : List (B.El × C.El) :=
  let r := R.toList; let s := S.toList; let ub := UB.toList.map (·.1); let uc := UC.toList.map (·.1)
  ((r.map (·.2) ++ ub).flatMap fun b => (s.map (·.2) ++ uc).map (b, ·)).filter fun (b, c) =>
    r.all (fun (a, b') => b' != b || s.contains (a, c)) && (r.any (·.2 == b) || ub.contains b && uc.contains c)

/-- `R/S` within the universes `UA`, `UB` (`rdivDen`): `(x, y)` when every `c` with `S y c` has `R x c`, and `y` is a
source of `S` or `x`, `y` lie in the universes. -/
private def rdivSp {A B C : Obj} [BEq A.El] [BEq B.El] [BEq C.El] (R : Tab A C) (S : Tab B C) (UA : Tab A A)
    (UB : Tab B B) : List (A.El × B.El) :=
  let r := R.toList; let s := S.toList; let ua := UA.toList.map (·.1); let ub := UB.toList.map (·.1)
  ((r.map (·.1) ++ ua).flatMap fun x => (s.map (·.1) ++ ub).map (x, ·)).filter fun (x, y) =>
    s.all (fun (y', c) => y' != y || r.contains (x, c)) && (s.any (·.1 == y) || ua.contains x && ub.contains y)

-- `\` and `/` against `ldivDen`, `rdivDen` on every pair of tables, within `U`; each answer canonical
#guard ts.all fun ps => ts.all fun qs =>
  let R := tab ps; let S := tab qs
  canonOk (R.ldiv S (idT U) (idT U)) && canonOk (R.rdiv S (idT U) (idT U)) &&
  specOk (R.ldiv S (idT U) (idT U)) (ldivSp R S (idT U) (idT U)) &&
  specOk (R.rdiv S (idT U) (idT U)) (rdivSp R S (idT U) (idT U))

#guard newL ((tab [(1, 2), (1, 5), (2, 2), (2, 5), (3, 2)]).ldiv (tab [(1, 7), (2, 7), (2, 8), (3, 7)])
  (idT (Alg.col [2, 5, 6])) (idT (Alg.col [7, 9]))) == some [(2, 7), (5, 7), (6, 7), (6, 9)]

/-- A two-sided operator `f` (`lt`, `leq`, `top`) on the whole universe `U`: both sides `dom U`. -/
private def whole {A : Obj} (f : ∀ {n m : USize}, Vals A n → Vals A m → Except String (Tab A A)) (U : Tab A A) :
    Except String (Tab A A) := do let d ← U.dom; f d.key d.key

/-- `f K L` is canonical and holds the rows of `K ≫ whole f U ≫ L` (`Tab.comp`), as a set. -/
private def sidesOk {A : Obj} [BEq A.El] (f : ∀ {n m : USize}, Vals A n → Vals A m → Except String (Tab A A))
    (U : Tab A A) {n m : USize} (K : Vals A n) (L : Vals A m) : Bool :=
  canonOk (f K L) && ((do (← (idT K).comp (← whole f U)).comp (idT L) : Except String (Tab A A))).toOption.any
    fun T => specOk (f K L) T.toList

-- `<`, `≤` on both sides `dom U` against `ltDen`, `leqDen`, on `U` and on no values
#guard canonOk (whole Tab.lt (idT U)) && canonOk (whole Tab.leq (idT U)) &&
  specOk (whole Tab.lt (idT U)) (us.flatMap fun a => (us.filter (a < ·)).map (a, ·)) &&
  specOk (whole Tab.leq (idT U)) (us.flatMap fun a => (us.filter (a ≤ ·)).map (a, ·)) &&
  newL (whole Tab.lt (tab [])) == some [] &&
  newL (whole Tab.leq (tab [(4, 0), (2, 0)])) == some [(2, 2), (2, 4), (4, 4)]

/-- Known sides inside `U`: none, a value twice, and two that differ. -/
private def sides : List ((n : USize) × Vals .long n) :=
  [⟨_, Alg.col []⟩, ⟨_, Alg.col [2, 9, -3, 2]⟩, ⟨_, Alg.col [5, 1, 7]⟩, ⟨_, Alg.col [1, 2, 5, 7, 9, -3]⟩]

/-- An `f64` column of the bits `ws`. -/
private def fcol (ws : List UInt64) : Vals (.atom .f64) ws.length.toUSize := Arr.ofFn .f64 _ (ws.getD · 0)

/-- The `f64` universe `-0.0`, `+0.0`, a NaN, `1.5`, `+inf`. -/
private def FU := fcol [0x8000000000000000, 0, 0x7ff8000000000001, 0x3ff8000000000000, 0x7ff0000000000000]

/-- Known `f64` sides inside `FU`: none, a value twice, two that differ, all of `FU`. -/
private def fsides : List ((n : USize) × Vals (.atom .f64) n) :=
  [⟨_, fcol []⟩, ⟨_, fcol [0x3ff8000000000000, 0x8000000000000000, 0x3ff8000000000000]⟩,
   ⟨_, fcol [0, 0x7ff8000000000001, 0x7ff0000000000000]⟩, ⟨_, FU⟩]

-- `<`, `≤`, `⊤` on the known sides `K`, `L` against `K ≫ (both sides dom U) ≫ L`, every pair of sides; `⊤` on `f64`
#guard sides.all fun ⟨_, K⟩ => sides.all fun ⟨_, L⟩ =>
  sidesOk Tab.lt (idT U) K L && sidesOk Tab.leq (idT U) K L && sidesOk Tab.top (idT U) K L
#guard fsides.all fun ⟨_, K⟩ => fsides.all fun ⟨_, L⟩ => sidesOk Tab.top (idT FU) K L

/-- The keys `3 1 4 -1 3`: `3` twice, `4` the key of no row. -/
private def ds : List Int64 := [3, 1, 4, -1, 3]
private def D := Alg.col ds

/-- `Λ(R)` (`lamDen`) on the keys `ks` in demand (`Tm.lam`): each key to the image of `R` at it, each element once. -/
private def lamSp {A B : Obj} [BEq A.El] [BEq B.El] (ks : List A.El) (R : Tab A B) : List (A.El × List B.El) :=
  ks.map fun a => (a, ((R.toList.filter (·.1 == a)).map (·.2)).eraseDups)

/-- `E(R) = Λ(∋ ≫ R)` (`EDen`) on the arrays `xs`: each to the images of its elements, each once. -/
private def ESp {A B : Obj} [BEq A.El] [BEq B.El] (xs : List (List A.El)) (R : Tab A B) :
    List (List A.El × List B.El) :=
  xs.map fun x => (x, ((R.toList.filter fun r => x.contains r.1).map (·.2)).eraseDups)

-- `Λ` on `D` against `lamDen` on `D`, and `nil`
#guard ts.all fun ps => canonOk (Tab.lam D (tab ps)) && cellsOk (Tab.lam D (tab ps)) (lamSp ds (tab ps))
#guard newL (Tab.lam D (tab [(3, 1), (1, 2), (3, 1), (-1, 2), (1, 2), (3, -7)])) ==
  some [(-1, [2]), (1, [2]), (3, [-7, 1]), (4, [])]
#guard canonOk (Tab.nil (A := .long) (B := .long) D) &&
  newL (Tab.nil (A := .long) (B := .long) D) == some [(-1, []), (1, []), (3, []), (4, [])]

/-- `-0.0`, `+0.0`, NaN with payloads `1` and `2`, `+inf`, `-inf`, `1.5`, `-0.0` again, as `f64` bits. -/
private def f64s : List UInt64 := [0x8000000000000000, 0, 0x7ff8000000000001, 0x7ff8000000000002, 0x7ff0000000000000,
  0xfff0000000000000, 0x3ff8000000000000, 0x8000000000000000]

-- `E` against `EDen` on `arrCells` (empty cells, `[5]` from three ranges, `[5,1]` twice), on no cells, and with a
-- relation of no rows
#guard [(arrCells, arrPay), ([], arrPay)].all fun (cs, ps) =>
  let X := (arrTab cs ps).key
  [tab [(5, 1), (9, 2), (1, 3), (5, 4)], tab [(9, 0)], tab []].all fun R =>
    canonOk (Tab.E X R) && cellsOk (Tab.E X R) (ESp (Vals.rows X) R)

-- `E` on float and tuple elements: cells over `f64s` (`[-0.0]` from `[0,1)` and `[7,8)`, the empty cell, both NaNs)
-- and over pairs (`[(1,5)]` from two ranges)
#guard
  let x := Arr.ofFn .f64 8 (f64s.getD · 0) ⟨by decide, by decide⟩
  let X := (arrOn [(0, 1, 0), (7, 8, 0), (2, 4, 0), (3, 3, 0), (0, 8, 0), (5, 7, 0)] x).key
  let R : Tab (.atom .f64) .long := ⟨8, x, Alg.col [1, 1, 2, 3, 4, 4, 5, 6]⟩
  let Y := (arrOn [(0, 1, 0), (2, 3, 0), (0, 4, 0), (1, 1, 0)] ((Alg.col [1, 2, 1, 3], Alg.col [5, 5, 5, 6]) :
    Vals (.prod .long .long) 4)).key
  let S : Tab (.prod .long .long) .long := ⟨3, (Alg.col [1, 1, 3], Alg.col [5, 5, 6]), Alg.col [7, 8, 9]⟩
  canonOk (Tab.E X R) && cellsOk (Tab.E X R) (ESp (Vals.rows X) R) &&
  canonOk (Tab.E Y S) && cellsOk (Tab.E Y S) (ESp (Vals.rows Y) S)

-- `∋` on cells (empty ones, clamped ones, one cell twice) against `x ∋ a`, and on no cells
#guard [(arrCells, arrPay), (arrCells.take 3, arrPay), ([], arrPay), ([(0, 0, 1), (0, 0, 1)], [])].all fun (cs, ps) =>
  let X := (arrTab cs ps).key
  canonOk (Tab.mem X) && specOk (Tab.mem X) ((Vals.rows X).flatMap fun (x : List Int64) => x.map (x, ·))

-- a float value column (stored-bit equality) and a tuple value column, through `\`, `/` and `Λ`
#guard
  let x := Arr.ofFn .f64 8 (f64s.getD · 0) ⟨by decide, by decide⟩
  let R : Tab .long (.atom .f64) := ⟨8, Alg.col [3, 1, 2, 1, 4, 4, 0, 1], x⟩
  let S : Tab .long .long := tab [(3, 5), (1, 6), (2, 5), (1, 5), (4, 5), (0, 5), (0, 6)]
  let Ux := Arr.ofFn .f64 3 (f64s.getD · 0) ⟨by decide, by decide⟩
  canonOk (R.ldiv S (idT Ux) (idT U)) && specOk (R.ldiv S (idT Ux) (idT U)) (ldivSp R S (idT Ux) (idT U)) &&
  cellsOk (Tab.lam D R) (lamSp ds R)
#guard
  let R : Tab .long (.prod .long .long) := ⟨5, Alg.col [3, 1, 3, 1, 2], (Alg.col [1, 1, 2, 1, 2], Alg.col [5, 6, 5, 6, 5])⟩
  let S : Tab .long .long := tab [(3, 5), (1, 6), (1, 5), (2, 5)]
  let Up : Vals (.prod .long .long) 2 := (Alg.col [9, 9], Alg.col [9, 8])
  canonOk (R.ldiv S (idT Up) (idT U)) && specOk (R.ldiv S (idT Up) (idT U)) (ldivSp R S (idT Up) (idT U)) &&
  cellsOk (Tab.lam D R) (lamSp ds R)

/-! `Tab.nu`, `Tab.mu` (`Rel/Run/Fix.lean`) against fixed points worked by hand. -/

/-- `TestArcs`' body `t ∩ A\(X e)` on `V = {0,1}`, `D = {0,1,2}`: `A = {(1,0)}`, `e = 𝟙(D)`, `t` missing `(1,1)`. -/
private def arcT := tab [(0, 0), (0, 1), (0, 2), (1, 0), (1, 2)]
private def arcA := tab [(1, 0)]
private def arcE := tab [(0, 0), (1, 1), (2, 2)]
private def arcNew (X : Tab .long .long) : Except String (Tab .long .long) := do
  arcT.inter (← arcA.ldiv (← X.comp arcE) (idT (Alg.col [0, 1])) (idT (Alg.col [0, 1, 2])))
/-- `TestArcs`' answer: `(0,1)` drops, since `(1,1)` is not in `t`. -/
private def arcZ : List (Int64 × Int64) := [(0, 0), (0, 2), (1, 0), (1, 2)]

-- ν from `⊤(V,D)`, from its own fixed point, and from no rows
#guard specOk (Tab.nu arcNew (tab [(0, 0), (0, 1), (0, 2), (1, 0), (1, 1), (1, 2)])) arcZ &&
  specOk (Tab.nu arcNew (tab arcZ)) arcZ && specOk (Tab.nu arcNew (tab [])) []

/-- Transitive closure `μX : E ∪ X E` of the edges `E`. -/
private def tcNew (E X : Tab .long .long) : Except String (Tab .long .long) := do E.union (← X.comp E)

-- the cycle `2 → 3 → 4 → 2` entered from `1`, closed to `{1,2,3,4} × {2,3,4}`: 12 pairs at round 3, seen fixed at
-- round 4, so `cap = 4` fails and `cap = 5` passes
#guard let E := tab [(1, 2), (2, 3), (3, 4), (4, 2)]
  (newL (Tab.mu "tc" 4 (tcNew E))).isNone &&
    [5, 9].all fun cap => specOk (Tab.mu "tc" cap (tcNew E)) ([1, 2, 3, 4].flatMap fun a => [2, 3, 4].map (a, ·))
-- the cap reached is reported with the μ's text and its cap
#guard let E := tab [(1, 2), (2, 3), (3, 4), (4, 2)]
  match Tab.mu "tc" 4 (tcNew E) with | .error e => e == Tab.capMsg "tc" 4 | .ok _ => false
-- an already-closed `E` and no edges
#guard [tab [(1, 2), (2, 2), (1, 1)], tab []].all fun E => specOk (Tab.mu "tc" 3 (tcNew E)) E.toList
-- an error of the body is the loop's error
#guard match Tab.nu (fun _ => throw "body") (tab arcZ) with | .error e => e == "body" | .ok _ => false
#guard match Tab.mu "tc" 9 (fun (_ : Tab .long .long) => throw "body") with | .error e => e == "body" | .ok _ => false

/-! ### `Rel/Run/Power.lean` against the old layer -/

/-- Arrays of longs: `arrCells` (empty cells, clamped ones, one cell twice, unsorted), a prefix of it, no cells, and
empty cells over no payload. -/
private def arrXs : List (Tab (.arr .long) .long) :=
  [arrTab arrCells arrPay, arrTab (arrCells.take 3) arrPay, arrTab [] arrPay, arrTab [(0, 0, 1), (0, 0, 1)] []]

/-- Arrays of pairs over the payload `(1,5) (2,5) (1,5) (3,6)`: `[(1,5)]` from two ranges, the empty cell, a cell
clamped, one cell twice. -/
private def pairXs : Vals (.arr (.prod .long .long)) 6 :=
  (arrOn [(0, 1, 0), (2, 3, 0), (0, 4, 0), (1, 1, 0), (2, 9, 0), (0, 4, 0)]
    ((Alg.col [1, 2, 1, 3], Alg.col [5, 5, 5, 6]) : Vals (.prod .long .long) 4)).key

/-- The test of pairs of `Q`: the pairs `D` composed with `𝟙` on `Q`'s rows, so `(b, c)` to itself iff `Q b c`. -/
private def pairsIn {B : Obj} (Q : Tab B B) (D : Tab (.prod B B) (.prod B B)) :
    Except String (Tab (.prod B B) (.prod B B)) := do D.comp (← Tab.idU (Q.key, Q.val))

/-- `est(Q)` (`estDen`, `Q` read through `pairsIn`) on the arrays `xs`: `b` of `x` when every other `c` of `x` has
`Q b c`. -/
private def estSp {B : Obj} [BEq B.El] (Q : Tab B B) (xs : List (List B.El)) : List (List B.El × B.El) :=
  xs.flatMap fun x => (x.filter fun b => x.all fun c => c == b || Q.toList.contains (b, c)).map (x, ·)

/-- `thin(Q)` (`thinDen`): each `x` to its `c` that no `b` of `x` beats strictly, each once. -/
private def thinSp {B : Obj} [BEq B.El] (Q : Tab B B) (xs : List (List B.El)) : List (List B.El × List B.El) :=
  xs.map fun x =>
    (x, (x.filter fun c => !x.any fun b => Q.toList.contains (b, c) && !Q.toList.contains (c, b)).eraseDups)

/-- Orders on longs: `≤` on `1 5 9`, a relation that is not one (`5` before `1`, `9` only to itself), and none. -/
private def ordLs : List (Tab .long .long) :=
  [tab [(1, 1), (1, 5), (1, 9), (5, 5), (5, 9), (9, 9), (1, 5)], tab [(5, 1), (9, 9)], tab []]

/-- Lexicographic `≤` on the pairs `(1,5) (2,5) (3,6)`. -/
private def ordPs : Tab (.prod .long .long) (.prod .long .long) :=
  ⟨6, (Alg.col [1, 1, 1, 2, 2, 3], Alg.col [5, 5, 5, 5, 5, 6]), (Alg.col [1, 2, 3, 2, 3, 3], Alg.col [5, 5, 6, 5, 6, 6])⟩

-- `setify`, `length`, `at(k)` against `Λ(∋)`, the length and `atDen` on arrays of longs and of pairs
#guard arrXs.all fun T => let X := T.key; let xs : List (List Int64) := Vals.rows X
  canonOk (Tab.setify X) && cellsOk (Tab.setify X) (xs.map fun x => (x, x.eraseDups)) &&
  canonOk (Tab.length X) && specOk (Tab.length X) (xs.map fun x => (x, Int64.ofNat x.length)) &&
  [0, 1, 2, 5].all fun k => canonOk (Tab.atPos k X) && specOk (Tab.atPos k X) (xs.filterMap fun x => x[k]?.map (x, ·))
#guard let xs : List (List (Int64 × Int64)) := Vals.rows pairXs
  canonOk (Tab.setify pairXs) && cellsOk (Tab.setify pairXs) (xs.map fun x => (x, x.eraseDups)) &&
  canonOk (Tab.length pairXs) && specOk (Tab.length pairXs) (xs.map fun x => (x, Int64.ofNat x.length)) &&
  [0, 1, 3].all fun k => canonOk (Tab.atPos k pairXs) &&
    specOk (Tab.atPos k pairXs) (xs.filterMap fun x => x[k]?.map (x, ·))

-- `τ` against `a ↦ [a]` on longs (a value twice), on no values, and on pairs
#guard [tab [(3, 0), (1, 0), (3, 0), (-2, 0)], tab []].all fun T => let X := T.key
  canonOk (Tab.tau X) && specOk (Tab.tau X) ((Vals.rows X).map fun a => (a, [a]))
#guard let X : Vals (.prod .long .long) 4 := (Alg.col [1, 2, 1, 3], Alg.col [5, 5, 5, 6])
  canonOk (Tab.tau X) && specOk (Tab.tau X) ((Vals.rows X).map fun a => (a, [a]))

-- `est`, `thin` against `estDen`, `thinDen`, each order, on arrays of longs and of pairs
#guard arrXs.all fun T => let X := T.key; ordLs.all fun Q =>
  canonOk (Tab.est (pairsIn Q) X) && specOk (Tab.est (pairsIn Q) X) (estSp Q (Vals.rows X)) &&
  canonOk (Tab.thin (pairsIn Q) X) && cellsOk (Tab.thin (pairsIn Q) X) (thinSp Q (Vals.rows X))
#guard canonOk (Tab.est (pairsIn ordPs) pairXs) &&
  specOk (Tab.est (pairsIn ordPs) pairXs) (estSp ordPs (Vals.rows pairXs)) &&
  canonOk (Tab.thin (pairsIn ordPs) pairXs) &&
  cellsOk (Tab.thin (pairsIn ordPs) pairXs) (thinSp ordPs (Vals.rows pairXs))

/-- `arrCells`-style fixtures for the list rows (`Rel/Run/List.lean`): `arrCells` (empty, clamped and repeated cells,
so repeated rows), a prefix of it, no cells, empty cells over no payload, and cells over `2^63 - 1` and the null whose
sums overflow or meet the null. -/
private def listFix : List (List (Int64 × Int64 × Int64) × List Int64) :=
  [(arrCells, arrPay), (arrCells.take 3, arrPay), ([], arrPay), ([(0, 0, 1), (0, 0, 1)], []),
   ([(0, 2, 0), (1, 3, 0), (2, 3, 0), (0, 3, 0), (3, 4, 1)], [9223372036854775807, 1, -1, -9223372036854775807 - 1])]

/-- The `rowDens` rows `snoc`, `cat`, `cons`, `zip` after `P`; `uncons`, `unsnoc`, `uncat` and `sum` on the arrays
`xs`, each array to every decomposition of it. -/
private def snocSp {K B : Obj} (P : Tab K (.prod (.arr B) B)) : List (K.El × List B.El) :=
  P.toList.map fun (k, p) => (k, (p.1 : List B.El) ++ [p.2])
private def catSp {K B : Obj} (P : Tab K (.prod (.arr B) (.arr B))) : List (K.El × List B.El) :=
  P.toList.map fun (k, p) => (k, (p.1 : List B.El) ++ p.2)
private def consSp {K B : Obj} (P : Tab K (.prod B (.arr B))) : List (K.El × List B.El) :=
  P.toList.map fun (k, p) => (k, p.1 :: (p.2 : List B.El))
private def zipSp {K A B : Obj} (P : Tab K (.prod (.arr A) (.arr B))) : List (K.El × List (A.El × B.El)) :=
  P.toList.map fun (k, p) => (k, (p.1 : List A.El).zip p.2)
private def unconsSp {B : Obj} (xs : List (List B.El)) : List (List B.El × B.El × List B.El) :=
  xs.filterMap fun x => match x with | b :: r => some (x, b, r) | [] => none
private def unsnocSp {B : Obj} (xs : List (List B.El)) : List (List B.El × List B.El × B.El) :=
  xs.filterMap fun x => x.getLast?.map fun b => (x, x.dropLast, b)
private def uncatSp {B : Obj} (xs : List (List B.El)) : List (List B.El × List B.El × List B.El) :=
  xs.flatMap fun x => (List.range (x.length + 1)).map fun k => (x, x.take k, x.drop k)
private def sumSp (xs : List (List Int64)) : List (List Int64 × Int64) :=
  xs.filterMap fun x => if x.all (· != Alg.nul) && (List.range (x.length + 1)).all (fun t =>
    let s := ((x.drop t).map Int64.toInt).sum; decide (-2 ^ 63 < s ∧ s < 2 ^ 63)) then some (x, x.foldr (· + ·) 0)
    else none

-- `snoc cat cons zip sum uncons unsnoc uncat` against their `rowDens`, on long and pair elements, as sets (`canon` of
-- the answer)
#guard listFix.all fun (cs, ps) =>
  let A := arrTab cs ps
  let X := A.key; let x := A.val
  let Y := (arrOn cs (Alg.col (ps.map (· * 10 + 3)))).key
  let Z := (arrOn cs ((Alg.col ps, List.length_map _ ▸ Alg.col (ps.map (· - 1))) :
    Vals (.prod .long .long) ps.length.toUSize)).key
  let P₁ : Tab .long (.prod (.arr .long) .long) := ⟨_, x, (X, x)⟩
  let P₂ : Tab .long (.prod (.arr .long) (.arr .long)) := ⟨_, x, (X, Y)⟩
  let P₃ : Tab .long (.prod .long (.arr .long)) := ⟨_, x, (x, Y)⟩
  let P₄ : Tab .long (.prod (.arr .long) (.arr (.prod .long .long))) := ⟨_, x, (Y, Z)⟩
  let Q₁ : Tab .long (.prod (.arr (.prod .long .long)) (.prod .long .long)) := ⟨_, x, (Z, (x, x))⟩
  let Q₂ : Tab .long (.prod (.arr (.prod .long .long)) (.arr (.prod .long .long))) := ⟨_, x, (Z, Z)⟩
  let Q₃ : Tab .long (.prod (.prod .long .long) (.arr (.prod .long .long))) := ⟨_, x, ((x, x), Z)⟩
  let ok {A B : Obj} [BEq A.El] [BEq B.El] (r : Except String (Tab A B)) (sp : List (A.El × B.El)) :=
    specOk (r >>= Tab.canon) sp
  canonOk (Tab.snoc P₁) && canonOk (Tab.uncat X) &&
  ok (Tab.snoc P₁) (snocSp P₁) && ok (Tab.cat P₂) (catSp P₂) && ok (Tab.cons P₃) (consSp P₃) &&
  ok (Tab.zip P₄) (zipSp P₄) && ok (Tab.sum X) (sumSp (Vals.rows X)) &&
  ok (Tab.uncons X) (unconsSp (Vals.rows X)) && ok (Tab.unsnoc X) (unsnocSp (Vals.rows X)) &&
  ok (Tab.uncat X) (uncatSp (Vals.rows X)) &&
  ok (Tab.snoc Q₁) (snocSp Q₁) && ok (Tab.cat Q₂) (catSp Q₂) && ok (Tab.cons Q₃) (consSp Q₃) &&
  ok (Tab.uncons Z) (unconsSp (Vals.rows Z)) && ok (Tab.unsnoc Z) (unsnocSp (Vals.rows Z)) &&
  ok (Tab.uncat Z) (uncatSp (Vals.rows Z))

-- `sum` drops `[2^63 - 1, 1]` (a suffix sum past `2^63`) and `[null]`, keeps `[2^63 - 1, 1, -1]` (every suffix sum
-- inside), as `rowDens` states
#guard specOk (Tab.sum (arrTab (listFix.getD 4 ([], [])).1 (listFix.getD 4 ([], [])).2).key)
  [([1, -1], 0), ([-1], -1), ([9223372036854775807, 1, -1], 9223372036854775807)]

/-- One cell `[0, 1)` over `2^63` positions (`pos`, nothing stored): its row is `[0]`. -/
private def bigCell : Except String (Vals (.arr .long) 1) := do
  pure ⟨9223372036854775808, ← colArr .add 1 (← colConst 1 0) (← colConst 1 0),
    ← colArr .add 1 (← colConst 1 1) (← colConst 1 0),
    (⟨.vector .i64 9223372036854775808 .pos none, by simp [Ext.QValue.WFAt, Ext.Enc.WF]⟩ : Arr .i64 9223372036854775808)⟩

-- `Vals.pack` past `2^63` elements is the error: `cellSpan` would read the size as the signed word `-2^63`, every
-- width `0`, and answer a payload of no rows
#guard match bigCell, bigCell >>= Vals.pack with
  | .ok _, .error e => e == "pack: 1 cells over 9223372036854775808 elements past 2^63"
  | _, _ => false

end Checks

/-! ## `Λ` and `E`: `lam_holds`, `E_holds` -/

namespace Tab
variable {A B : Obj}

/-- **`lam D R` is `canon` of one row per key `a` of `D`, its cell the rows of `r = canon R` with key `a`, in
`r`'s order**: `L` lists those rows' positions ascending. GROUP over `D ++ r.key` (`sorted_groups`): group `G` holds
the sorted positions `[Fs, Fs + cnt)`, its `D` rows first (`[Fs, Fs + cD)`, `kasc` stable) and then its `r` rows,
ascending in `r` (`hmono`); the cell `[Fs + cD, Fs + cnt)` of the payload reads `r` at `p - n`. -/
theorem lam_canon {n : USize} {D : Vals A n} {R : Tab A B} {T : Tab A (.arr B)} (h : Tab.lam D R = .ok T) :
    ∃ (r : Tab A B) (U : Tab A (.arr B)), R.canon = .ok r ∧ U.canon = .ok T ∧ ∀ a ys,
      U.Holds a ys ↔ (∃ i, D.row i = a) ∧
      ∃ L : List Nat, L.Pairwise (· < ·) ∧ (∀ j, j ∈ L ↔ ∃ hj : j < r.n.toNat, r.key.row ⟨j, hj⟩ = a) ∧
        ys = L.map fun j => if hj : j < r.n.toNat then r.val.row ⟨j, hj⟩ else B.dflt := by
  dsimp only [Tab.lam] at h
  simp only [bind] at h
  rw [Except.bind_eq_ok'] at h; obtain ⟨r, hr, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨⟨N, sh⟩, hcat, h⟩ := h; try dsimp only at h
  split at h; · cases h
  rename_i hN
  rw [Except.bind_eq_ok'] at h; obtain ⟨_, -, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨z, hz, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨es, hes, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨⟨vs, p⟩, hasc, h⟩ := h; try dsimp only at h
  rw [Except.bind_eq_ok'] at h; obtain ⟨⟨k, g, f⟩, hseen, h⟩ := h; try dsimp only at h
  rw [Except.bind_eq_ok'] at h; obtain ⟨nc, hnc, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨lt, hlt, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨cD, hcD, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨lo, hlo, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨c1, hc1, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨cnt, hcnt, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨hi, hhi, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨c0, hc0, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨b, hb, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨⟨M, sel⟩, hwh, h⟩ := h; try dsimp only at h
  rw [Except.bind_eq_ok'] at h; obtain ⟨fs, hfs, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨iD, hiD, h⟩ := h
  refine ⟨r, ?_⟩
  ------------------------------------------------------------------ the sorted rows and their groups
  obtain ⟨hNn, hoff⟩ := catPlan_ok hcat
  have hU : USize.size ≤ 2 ^ 64 := by rcases USize.size_eq with h | h <;> omega
  have hNU := N.toNat_lt_size
  obtain ⟨cs, hcs, hp, hkq⟩ := kasc_grade hasc
  obtain ⟨hperm, hsort⟩ := ascGrade_spec N.toNat (ascKeys N es)
  obtain ⟨hk, hg, hf⟩ := kseen_ok hseen
  generalize ascGrade N.toNat (ascKeys N es) = ps at hp hkq hperm hsort
  generalize seenKey N ((es.map (·.1)).zip vs) = Kk at hk hg hf hkq
  have hlen : ps.length = N.toNat := by simpa using hperm.length_eq
  have hpsN : ∀ q < N.toNat, ps[q]?.getD 0 < N.toNat := fun q hq => by
    rw [List.getElem?_eq_getElem (by omega), Option.getD_some]
    exact List.mem_range.1 (hperm.mem_iff.1 (List.getElem_mem _))
  have hkN : k ≤ N.toNat := by rw [hk]; unfold firstsOf; exact Nat.le_trans (List.length_filter_le _ _) (by simp)
  have hK : k.toUSize.toNat = k := USize.toNat_ofNat_of_lt' (by omega)
  have hpw : ∀ q < N.toNat, (raw .i64 N p)[q]?.getD 0 = (ps[q]?.getD 0).toUInt64 := fun q hq => by
    rw [hp]; simp [List.getElem?_eq_getElem (show q < ps.length by omega)]
  have hgw : ∀ q < N.toNat, (raw .i64 N g)[q]?.getD 0 = (Verify.groupOf Kk N.toNat q).toUInt64 := fun q hq => by
    rw [hg, (wordsFoR_closed _ (by simp)).2.1]; simp [hq]
  have hfw : ∀ G < k, (raw .i64 k.toUSize f)[G]?.getD 0 = ((firstsOf Kk N.toNat)[G]?.getD 0).toUInt64 :=
    fun G hG => by
      rw [hf, (wordsFoR_closed _ (by rw [hK, hk]; simp)).2.1]
      simp [List.getElem?_eq_getElem (show G < (firstsOf Kk N.toNat).length by omega)]
  have hgr : ∀ q < N.toNat, Verify.groupOf Kk N.toNat q < k := fun q hq => by
    have := groupOf_lt (g := Kk) (m := N.toNat) hq; omega
  have fs' := firsts_spec Kk N.toNat
  have hn63 : N.toNat < 2 ^ 63 := by omega
  have hnN : n.toNat ≤ N.toNat := by omega
  have hps : ∀ q (hq : q < N.toNat), ps[q]?.getD 0 = ps[q]'(by omega) := fun q hq => by
    rw [List.getElem?_eq_getElem (by omega)]; rfl
  have hnU : n.toUInt64 = n.toNat.toUInt64 := UInt64.toNat_inj.mp (by simp <;> omega)
  have hltw : ∀ q < N.toNat, (raw .i64 N lt)[q]?.getD 0 =
      if decide (ps[q]?.getD 0 < n.toNat) then 1 else 0 := fun q hq => by
    have e := (colMap_raw hlt).2.2.2 q hq
    rw [hpw q hq, colConst_raw hnc, Array.getElem?_replicate, if_pos hq, Option.getD_some, hnU,
      eval_lt_nat (by have := hpsN q hq; omega) (by omega), Except.ok.injEq] at e
    rw [← e]; simp
  obtain ⟨cDN, hcDN⟩ : ∃ F : Nat → Nat, F = fun G => (List.range N.toNat).countP
      fun q => Verify.groupOf Kk N.toNat q == G && decide (ps[q]?.getD 0 < n.toNat) := ⟨_, rfl⟩
  obtain ⟨cntN, hcntN⟩ : ∃ F : Nat → Nat, F = fun G => (List.range N.toNat).countP
      fun q => Verify.groupOf Kk N.toNat q == G && true := ⟨_, rfl⟩
  have hcDw : ∀ G < k, (raw .i64 k.toUSize cD)[G]?.getD 0 = (cDN G).toUInt64 := fun G hG => by
    rw [scatter_add_count hcD (Verify.groupOf Kk N.toNat) (fun q => decide (ps[q]?.getD 0 < n.toNat)) hgw
      (fun q hq => by have := hgr q hq; omega) hltw G (by omega), hcDN]
  have hcntw : ∀ G < k, (raw .i64 k.toUSize cnt)[G]?.getD 0 = (cntN G).toUInt64 := fun G hG => by
    rw [scatter_add_count hcnt (Verify.groupOf Kk N.toNat) (fun _ => true) hgw
      (fun q hq => by have := hgr q hq; omega) (fun q hq => by rw [colConst_raw hc1]; simp [hq]) G (by omega), hcntN]
  have hle : ∀ G, cDN G ≤ cntN G := fun G => by
    rw [hcDN, hcntN]; exact List.countP_mono_left fun x _ hx => by simp at hx ⊢; exact hx.1
  obtain ⟨Fs, hFs⟩ : ∃ F : Nat → Nat, ∀ G, F G = (firstsOf Kk N.toNat)[G]?.getD 0 := ⟨_, fun _ => rfl⟩
  have hKks : ∀ q (hq : q < ps.length), Kk q = (ascKeys N es).map (·[ps[q]]?.getD 0) := fun q hq => by
    rw [hkq q hq]; simp [seenKey]
  have sg : ∀ G < k, (∀ q, (q < N.toNat ∧ Verify.groupOf Kk N.toNat q = G) ↔ Fs G ≤ q ∧ q < Fs G + cntN G) ∧
      (∀ q, (q < N.toNat ∧ Verify.groupOf Kk N.toNat q = G ∧ ps[q]?.getD 0 < n.toNat) ↔
        Fs G ≤ q ∧ q < Fs G + cDN G) := by
    intro G hG
    have hG' : G < (firstsOf Kk N.toNat).length := by omega
    have := sorted_groups (n := n.toNat) hlen hsort (fun q hq => hKks q hq) hG'
    rw [hFs, List.getElem?_eq_getElem hG', Option.getD_some, hcntN, hcDN]; exact this
  have hFsG : ∀ G < k, Fs G < N.toNat ∧ Verify.groupOf Kk N.toNat (Fs G) = G := fun G hG => by
    have hG' : G < (firstsOf Kk N.toNat).length := by omega
    rw [hFs, List.getElem?_eq_getElem hG', Option.getD_some]
    exact ⟨(fs'.2.1 _).1 (List.getElem_mem _) |>.1, fs'.2.2.2.1 G hG'⟩
  have hcN : ∀ G < k, Fs G < Fs G + cntN G ∧ Fs G + cntN G ≤ N.toNat := fun G hG => by
    obtain ⟨sgA, -⟩ := sg G hG
    have h1 := ((sgA (Fs G)).1 (hFsG G hG)).2
    have h2 := ((sgA (Fs G + cntN G - 1)).2 ⟨by omega, by omega⟩).1
    omega
  have hgD : ∀ G < k, 0 < cDN G → ps[Fs G]?.getD 0 < n.toNat := fun G hG hc =>
    ((sg G hG).2 (Fs G)).2 ⟨Nat.le_refl _, by omega⟩ |>.2.2
  -- rows of the same group are equal rows of `z`, and back
  have grp_row : ∀ q (hq : q < N.toNat) q' (hq' : q' < N.toNat),
      Verify.groupOf Kk N.toNat q = Verify.groupOf Kk N.toNat q' →
      z.row ⟨_, hpsN q hq⟩ = z.row ⟨_, hpsN q' hq'⟩ := fun q hq q' hq' e => by
    have eK := (fs'.2.2.1 q hq q' hq').1 e
    rw [hkq q (by omega), hkq q' (by omega), ← hps q hq, ← hps q' hq'] at eK
    exact Vals.row_of_codes z hes hcs _ _ eK
  have row_grp : ∀ q (hq : q < N.toNat) q' (hq' : q' < N.toNat),
      z.row ⟨_, hpsN q hq⟩ = z.row ⟨_, hpsN q' hq'⟩ →
      Verify.groupOf Kk N.toNat q = Verify.groupOf Kk N.toNat q' := fun q hq q' hq' e => by
    have eK := Vals.codes_of_row z hes hcs _ _ e
    have eK2 : Kk q = Kk q' := by rw [hkq q (by omega), hkq q' (by omega), ← hps q hq, ← hps q' hq']; exact eK
    exact (fs'.2.2.1 q hq q' hq').2 eK2
  have hinv : ∀ i < N.toNat, ∃ q, ∃ hq : q < N.toNat, ps[q]?.getD 0 = i := fun i hi => by
    obtain ⟨q, hq, e⟩ := List.mem_iff_getElem.1 (hperm.mem_iff.2 (List.mem_range.2 hi))
    exact ⟨q, by omega, by rw [hps q (by omega)]; exact e⟩
  have zD : ∀ i (hi : i < n.toNat), z.row ⟨i, by omega⟩ = D.row ⟨i, hi⟩ := fun i hi => by
    rw [Vals.concat_row hNn hoff D r.key hz, dif_pos hi]
  have zR : ∀ j (hj : j < r.n.toNat), z.row ⟨n.toNat + j, by omega⟩ = r.key.row ⟨j, hj⟩ := fun j hj => by
    rw [Vals.concat_row hNn hoff D r.key hz, dif_neg (by simp)]; simp only [Nat.add_sub_cancel_left]
  -- within a group, sorted positions read ascending input rows (`kasc` is stable)
  have hmono : ∀ q q', q < q' → q' < N.toNat →
      Verify.groupOf Kk N.toNat q = Verify.groupOf Kk N.toNat q' → ps[q]?.getD 0 < ps[q']?.getD 0 := by
    intro q q' hlt' hq' e
    have eK := (fs'.2.2.1 q (by omega) q' hq').1 e
    rw [hKks q (by omega), hKks q' (by omega)] at eK
    have := (List.pairwise_iff_getElem.1 hsort) q q' (by omega) (by omega) hlt'
    rw [hps q (by omega), hps q' hq']
    exact this.2 (lexLe_of_keys _ eK.symm)
  -- the cell of group `G`: the input rows of its sorted positions `[Fs + cD, Fs + cnt)`, less `n`
  obtain ⟨Ln, hLn⟩ : ∃ F : Nat → List Nat, ∀ G, F G =
      (List.range' (Fs G + cDN G) (cntN G - cDN G)).map (fun q => ps[q]?.getD 0 - n.toNat) := ⟨_, fun _ => rfl⟩
  have hLin : ∀ G < k, ∀ q, Fs G + cDN G ≤ q → q < Fs G + cntN G →
      q < N.toNat ∧ Verify.groupOf Kk N.toNat q = G ∧ n.toNat ≤ ps[q]?.getD 0 := fun G hG q h1 h2 => by
    obtain ⟨sgA, sgR⟩ := sg G hG
    obtain ⟨hq, hqG⟩ := (sgA q).2 ⟨by omega, h2⟩
    exact ⟨hq, hqG, Nat.le_of_not_lt fun hc => by have := (sgR q).1 ⟨hq, hqG, hc⟩; omega⟩
  have hLp : ∀ G < k, (Ln G).Pairwise (· < ·) := fun G hG => by
    rw [hLn, List.pairwise_map, List.range'_eq_map_range, List.pairwise_map]
    refine List.Pairwise.imp_of_mem (fun {x y} hx hy hxy => ?_) (pairwise_range (cntN G - cDN G))
    rw [List.mem_range] at hx hy
    obtain ⟨-, gx, nx⟩ := hLin G hG (Fs G + cDN G + x) (by omega) (by omega)
    obtain ⟨hy', gy, ny⟩ := hLin G hG (Fs G + cDN G + y) (by omega) (by omega)
    have := hmono (Fs G + cDN G + x) (Fs G + cDN G + y) (by omega) hy' (gx.trans gy.symm)
    omega
  have hLm : ∀ G (hG : G < k) (hi0 : ps[Fs G]?.getD 0 < n.toNat) j,
      j ∈ Ln G ↔ ∃ hj : j < r.n.toNat, r.key.row ⟨j, hj⟩ = D.row ⟨_, hi0⟩ := by
    intro G hG hi0 j
    obtain ⟨hF, hFg⟩ := hFsG G hG
    rw [hLn, List.mem_map]
    constructor
    · rintro ⟨q, hq, rfl⟩
      rw [List.mem_range'_1] at hq
      obtain ⟨hqN, hqG, hnq⟩ := hLin G hG q hq.1 (by omega)
      have hj : ps[q]?.getD 0 - n.toNat < r.n.toNat := by have := hpsN q hqN; omega
      refine ⟨hj, ?_⟩
      rw [← zR _ hj, ← zD _ hi0]
      have := grp_row q hqN (Fs G) hF (hqG.trans hFg.symm)
      simp only [Nat.add_sub_cancel' hnq]; exact this
    · rintro ⟨hj, e⟩
      obtain ⟨q, hq, eq⟩ := hinv (n.toNat + j) (by omega)
      have e' : z.row ⟨_, hpsN q hq⟩ = z.row ⟨_, hpsN (Fs G) hF⟩ := by
        have h1 : z.row ⟨_, hpsN q hq⟩ = z.row ⟨n.toNat + j, by omega⟩ := by simp only [eq]
        rw [h1, zR j hj, e, ← zD _ hi0]
      have hqG := (row_grp q hq (Fs G) hF e').trans hFg
      obtain ⟨sgA, sgR⟩ := sg G hG
      have h1 := (sgA q).1 ⟨hq, hqG⟩
      have h2 : Fs G + cDN G ≤ q := Nat.le_of_not_lt fun hc => by
        have := ((sgR q).2 ⟨h1.1, hc⟩).2.2; omega
      exact ⟨q, List.mem_range'_1.2 ⟨h2, by omega⟩, by omega⟩
  ------------------------------------------------------------------ the words `lo`, `hi`, the kept groups
  have hlow : ∀ G < k, (raw .i64 k.toUSize lo.enc)[G]?.getD 0 = (Fs G + cDN G).toUInt64 := fun G hG => by
    have e := (colMap_raw (colArr_ok hlo)).2.2.2 G (by omega)
    rw [hfw G hG, hcDw G hG] at e; simp only [Op.eval, Except.ok.injEq] at e
    rw [← e, hFs]; exact (UInt64.ofNat_add _ _).symm
  have hhiw : ∀ G < k, (raw .i64 k.toUSize hi.enc)[G]?.getD 0 = (Fs G + cntN G).toUInt64 := fun G hG => by
    have e := (colMap_raw (colArr_ok hhi)).2.2.2 G (by omega)
    rw [hfw G hG, hcntw G hG] at e; simp only [Op.eval, Except.ok.injEq] at e
    rw [← e, hFs]; exact (UInt64.ofNat_add _ _).symm
  have hbw : ∀ G < k, (raw .i64 k.toUSize b)[G]?.getD 0 = if 0 < cDN G then 1 else 0 := fun G hG => by
    have e := (colMap_raw hb).2.2.2 G (by omega)
    have := hle G; have := hcN G hG
    rw [colConst_raw hc0, Array.getElem?_replicate, if_pos (by omega), Option.getD_some, hcDw G hG,
      show Op.eval .lt 0 (cDN G).toUInt64 = .ok (if 0 < cDN G then 1 else 0) from
        eval_lt_nat (x := 0) (by omega) (by omega), Except.ok.injEq] at e
    rw [← e]
  have hsel := whereCol_spec hwh (fun G hG => by rw [hbw G (by omega)]; split <;> decide)
  have hsz := whereCol_size hwh
  have hselj : ∀ j < M.toNat, ((raw .i64 M sel)[j]?.getD 0).toNat < k ∧
      0 < cDN ((raw .i64 M sel)[j]?.getD 0).toNat := fun j hj => by
    have hj' : j < (raw .i64 M sel).size := by rw [hsz]; exact hj
    have hGm := List.mem_map_of_mem (f := UInt64.toNat) (Array.getElem_mem_toList hj')
    rw [hsel, List.mem_filter, decide_eq_true_eq, List.mem_range] at hGm
    rw [Array.getElem?_eq_getElem hj', Option.getD_some]
    refine ⟨by omega, ?_⟩
    have := hGm.2; rw [hbw _ (by omega)] at this
    exact Classical.byContradiction fun hc => this (if_neg hc)
  have hselG : ∀ G < k, 0 < cDN G → ∃ j, ∃ hj : j < M.toNat, ((raw .i64 M sel)[j]?.getD 0).toNat = G :=
    fun G hG hc => by
      have hm : G ∈ (raw .i64 M sel).toList.map UInt64.toNat := by
        rw [hsel, List.mem_filter, List.mem_range, decide_eq_true_eq, hbw G (by omega), if_pos hc]
        exact ⟨by omega, by decide⟩
      obtain ⟨w, hw, hwi⟩ := List.mem_map.1 hm
      obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hw
      have hj' : j < (raw .i64 M sel).size := by simpa using hj
      refine ⟨j, by rw [← hsz]; exact hj', ?_⟩
      simp only [Array.getElem_toList] at hwi
      rw [Array.getElem?_eq_getElem hj', Option.getD_some, hwi]
  have hiDj : ∀ j < M.toNat, (raw .i64 M iD)[j]?.getD 0 =
      (ps[Fs ((raw .i64 M sel)[j]?.getD 0).toNat]?.getD 0).toUInt64 := fun j hj => by
    obtain ⟨hG, -⟩ := hselj j hj
    obtain ⟨hF, -⟩ := hFsG _ hG
    rw [(kgather_word hiD j hj).2, (kgather_word hfs j hj).2, hfw _ hG, ← hFs, toNat_toUInt64 (by omega), hpw _ hF]
  have hgat : ∀ {x : Arr .i64 k.toUSize} {y : Arr .i64 M} {w : Nat → Nat}, Arr.gather M sel x = .ok y →
      (∀ G < k, (raw .i64 k.toUSize x.enc)[G]?.getD 0 = (w G).toUInt64) →
      ∀ j < M.toNat, (raw .i64 M y.enc)[j]?.getD 0 = (w ((raw .i64 M sel)[j]?.getD 0).toNat).toUInt64 := by
    intro x y w hxy hw j hj
    obtain ⟨i, hi, e⟩ := Arr.gather_row x hxy ⟨j, hj⟩
    rw [Arr.get_i64, Arr.get_i64] at e
    have e' := congrArg Int64.toUInt64 e; simp only [UInt64.toUInt64_toInt64] at e'
    rw [e', hw i.1 (by omega)]; rw [hi]
  ------------------------------------------------------------------ the rows of the table before `canon`
  have key : ∀ {m : USize} (y : Vals B m), (∀ q (hq : q < N.toNat), n.toNat ≤ ps[q]?.getD 0 →
        ∃ hm : q < m.toNat, ∃ hj : ps[q]?.getD 0 - n.toNat < r.n.toNat, y.row ⟨q, hm⟩ = r.val.row ⟨_, hj⟩) →
      ∀ {xk : Vals A M} {alo ahi : Arr .i64 M}, Vals.gather M iD D = .ok xk → Arr.gather M sel lo = .ok alo →
        Arr.gather M sel hi = .ok ahi → ∀ a ys,
        (Tab.mk M xk ⟨m, alo, ahi, y⟩ : Tab A (.arr B)).Holds a ys ↔ (∃ i, D.row i = a) ∧
          ∃ L : List Nat, L.Pairwise (· < ·) ∧ (∀ j, j ∈ L ↔ ∃ hj : j < r.n.toNat, r.key.row ⟨j, hj⟩ = a) ∧
            ys = L.map fun j => if hj : j < r.n.toNat then r.val.row ⟨j, hj⟩ else B.dflt := by
    intro m y hy xk alo ahi hxk halo hahi a ys
    have walo := hgat halo hlow
    have wahi := hgat hahi hhiw
    have hcell : ∀ j (hj : j < M.toNat), Vals.row (A := .arr B) ⟨m, alo, ahi, y⟩ ⟨j, hj⟩ =
        (Ln ((raw .i64 M sel)[j]?.getD 0).toNat).map
          fun j => if hj : j < r.n.toNat then r.val.row ⟨j, hj⟩ else B.dflt := by
      intro j hj
      obtain ⟨hG, hc⟩ := hselj j hj
      have wl := walo j hj; have wh := wahi j hj
      generalize ((raw .i64 M sel)[j]?.getD 0).toNat = G at hG hc wl wh ⊢
      have hjU : (j.toUInt64).toNat = j := toNat_toUInt64 (by have := M.toNat_lt_size; omega)
      have hcN' := hcN G hG; have hle' := hle G
      have e1 : cellStart m.toNat (raw .i64 M alo.enc) j.toUInt64 = min (Fs G + cDN G) m.toNat := by
        unfold cellStart; rw [hjU, wl, toInt64_toInt_nat (by omega)]; omega
      have e2 : cellLen m.toNat (raw .i64 M alo.enc) (raw .i64 M ahi.enc) j.toUInt64 =
          min (Fs G + cntN G) m.toNat - min (Fs G + cDN G) m.toNat := by
        unfold cellLen; rw [e1, hjU, wh, toInt64_toInt_nat (by omega)]; omega
      rw [Vals.row_arr]; rw [e1, e2]
      by_cases hne : cDN G < cntN G
      · obtain ⟨hqN, -, hnq⟩ := hLin G hG (Fs G + cntN G - 1) (by omega) (by omega)
        obtain ⟨hm, -, -⟩ := hy _ hqN hnq
        rw [show min (Fs G + cDN G) m.toNat = Fs G + cDN G by omega,
          show min (Fs G + cntN G) m.toNat = Fs G + cntN G by omega,
          show Fs G + cntN G - (Fs G + cDN G) = cntN G - cDN G by omega, hLn, List.map_map]
        refine List.map_congr_left fun q hq => ?_
        rw [List.mem_range'_1] at hq
        obtain ⟨hqN, -, hnq⟩ := hLin G hG q hq.1 (by omega)
        obtain ⟨hm, hj', e⟩ := hy q hqN hnq
        simp only [Function.comp, dif_pos hm, dif_pos hj', e]
      · rw [show min (Fs G + cntN G) m.toNat - min (Fs G + cDN G) m.toNat = 0 by omega, hLn,
          show cntN G - cDN G = 0 by omega]
        rfl
    have hxj : ∀ j (hj : j < M.toNat), ∃ hi0 : ps[Fs ((raw .i64 M sel)[j]?.getD 0).toNat]?.getD 0 < n.toNat,
        xk.row ⟨j, hj⟩ = D.row ⟨_, hi0⟩ := by
      intro j hj
      obtain ⟨hG, hc⟩ := hselj j hj
      have hi0 := hgD _ hG hc
      obtain ⟨i, hi, e⟩ := Vals.gather_row D hxk ⟨j, hj⟩
      simp only [Fin.val_mk] at hi
      rw [hiDj j hj, toNat_toUInt64 (by omega)] at hi
      exact ⟨hi0, by rw [e]; congr 1; exact Fin.ext hi.symm⟩
    simp only [Tab.Holds]
    constructor
    · rintro ⟨⟨j, hj⟩, hxa, hys⟩
      obtain ⟨hG, -⟩ := hselj j hj
      obtain ⟨hi0, hx⟩ := hxj j hj
      refine ⟨⟨_, hx.symm.trans hxa⟩, Ln _, hLp _ hG, fun j' => ?_, ?_⟩
      · rw [hLm _ hG hi0, ← hxa, hx]
      · rw [← hys, hcell j hj]
    · rintro ⟨⟨i, rfl⟩, L, hLp', hLm', rfl⟩
      obtain ⟨q, hq, hqi⟩ := hinv i.1 (by omega)
      have hG := hgr q hq
      generalize hGq : Verify.groupOf Kk N.toNat q = G at hG
      have hqD := ((sg G hG).2 q).1 ⟨hq, hGq, by omega⟩
      obtain ⟨j, hj, hjG⟩ := hselG G hG (by omega)
      obtain ⟨hi0, hx⟩ := hxj j hj
      have hcj := hcell j hj
      rw [hjG] at hcj
      simp only [hjG] at hi0 hx
      have hDi : D.row ⟨_, hi0⟩ = D.row i := by
        show D.row ⟨_, hi0⟩ = D.row ⟨i.1, i.2⟩
        rw [← zD _ hi0, ← zD i.1 i.2]
        have := grp_row (Fs G) (hFsG G hG).1 q hq ((hFsG G hG).2.trans hGq.symm)
        simp only [hqi] at this; exact this
      refine ⟨⟨j, hj⟩, hx.trans hDi, ?_⟩
      rw [hcj]
      congr 1
      exact pairwise_eq_of_mem Nat.lt_irrefl (fun _ _ => Nat.lt_asymm) (hLp G hG) hLp' fun j' => by
        rw [hLm G hG hi0, hLm' j', hDi]
  ------------------------------------------------------------------ the payload: `r.val` at `p - n`, or no rows
  split at h
  · rename_i hr0
    rw [Except.bind_eq_ok'] at h; obtain ⟨pay, hpay, h⟩ := h
    cases hpay
    rw [Except.bind_eq_ok'] at h; obtain ⟨xk, hxk, h⟩ := h
    rw [Except.bind_eq_ok'] at h; obtain ⟨alo, halo, h⟩ := h
    rw [Except.bind_eq_ok'] at h; obtain ⟨ahi, hahi, h⟩ := h
    exact ⟨_, hr, h, key r.val (fun q hq hnq => absurd (hpsN q hq) (by omega)) hxk halo hahi⟩
  · rename_i hr0
    rw [Except.bind_eq_ok'] at h; obtain ⟨pm, hpm, h⟩ := h
    rw [Except.bind_eq_ok'] at h; obtain ⟨z0, hz0, h⟩ := h
    rw [Except.bind_eq_ok'] at h; obtain ⟨mx, hmx, h⟩ := h
    rw [Except.bind_eq_ok'] at h; obtain ⟨pay, hpay, h⟩ := h
    simp only [Functor.map, Except.map] at hpay
    split at hpay; · cases hpay
    rename_i y hy
    cases hpay
    rw [Except.bind_eq_ok'] at h; obtain ⟨xk, hxk, h⟩ := h
    rw [Except.bind_eq_ok'] at h; obtain ⟨alo, halo, h⟩ := h
    rw [Except.bind_eq_ok'] at h; obtain ⟨ahi, hahi, h⟩ := h
    refine ⟨_, hr, h, key y (fun q hq hnq => ?_) hxk halo hahi⟩
    have hs63 : ps[q]?.getD 0 - n.toNat < 2 ^ 63 := by have := hpsN q hq; omega
    have hmxw : (raw .i64 N mx)[q]?.getD 0 = (ps[q]?.getD 0 - n.toNat).toUInt64 := by
      have e1 := (colMap_raw hpm).2.2.2 q hq
      rw [hpw q hq, colConst_raw hnc, Array.getElem?_replicate, if_pos hq, Option.getD_some, hnU] at e1
      simp only [Op.eval, Except.ok.injEq] at e1
      have e2 := (colMap_raw hmx).2.2.2 q hq
      rw [← e1, ← toUInt64_sub hnq, colConst_raw hz0, Array.getElem?_replicate, if_pos hq, Option.getD_some,
        show Op.eval .max (ps[q]?.getD 0 - n.toNat).toUInt64 0 = .ok (ps[q]?.getD 0 - n.toNat).toUInt64 by
          rw [eval_max (by rw [toNat_toUInt64 (by omega)]; omega) (by decide)]; simp] at e2
      exact (Except.ok.inj e2).symm
    obtain ⟨i, hi, e⟩ := Vals.gather_row r.val hy ⟨q, hq⟩
    simp only [Fin.val_mk] at hi
    rw [hmxw, toNat_toUInt64 (by omega)] at hi
    exact ⟨hq, by omega, by rw [e]; congr 1; exact Fin.ext hi.symm⟩


/-- **`lam D R` denotes `Λ(R)` on the keys `D`, each cell in `R`'s order codes**: `a` of `D` to the list `ys` of its
images under `R`, each once and ascending by the codes `kasc` gives the rows `(a, b)` of `R` (strictly: no two
equal by stored bits). The codes order the images strictly (`keys_of_lexLe`, `Vals.codes_of_row`), so two such
lists are one (`pairwise_eq_of_mem`), and `lam_canon`'s cell is one (`canon_sorted`). -/
theorem lam_holds {n : USize} {D : Vals A n} {R : Tab A B} {T : Tab A (.arr B)} (h : Tab.lam D R = .ok T)
    (a : A.El) (ys : List B.El) :
    T.Holds a ys ↔ (∃ i, D.row i = a) ∧ (∀ b, b ∈ ys ↔ R.Holds a b) ∧
      ∀ es, Vals.cols (A := .prod A B) (R.key, R.val) = .ok es →
        ∃ s : Fin ys.length → Fin R.n.toNat, (∀ u, R.key.row (s u) = a ∧ R.val.row (s u) = ys[u]) ∧
          ∀ u u' : Fin ys.length, u.1 < u'.1 → lexLe (ascKeys R.n es) (s u) (s u') = true ∧
            seenKey R.n es (s u) ≠ seenKey R.n es (s u') := by
  obtain ⟨r, U, hr, hU, hH⟩ := lam_canon h
  obtain ⟨es0, cs, hes0, hcs⟩ := canon_codes hr
  rw [canon_holds hU, hH]
  -- the strict order the codes put on the images of `a`
  have hsk : ∀ i j : Fin R.n.toNat, R.key.row i = R.key.row j → R.val.row i = R.val.row j →
      seenKey R.n es0 i = seenKey R.n es0 j := fun i j e1 e2 =>
    Vals.codes_of_row (A := .prod A B) (R.key, R.val) hes0 hcs i j (Prod.ext e1 e2)
  have hks : ∀ i : Nat, seenKey R.n es0 i = (ascKeys R.n es0).map (·[i]?.getD 0) := fun i => by simp [seenKey]
  obtain ⟨lc, hlc⟩ : ∃ F : B.El → B.El → Prop, ∀ x y, F x y ↔ ∃ i j : Fin R.n.toNat, R.key.row i = a ∧
      R.val.row i = x ∧ R.key.row j = a ∧ R.val.row j = y ∧ lexLe (ascKeys R.n es0) i j = true ∧
      seenKey R.n es0 i ≠ seenKey R.n es0 j := ⟨_, fun _ _ => Iff.rfl⟩
  have lirr : ∀ x, ¬lc x x := fun x hx => by
    obtain ⟨i, j, h1, h2, h3, h4, -, hne⟩ := (hlc x x).1 hx
    exact hne (hsk i j (h1.trans h3.symm) (h2.trans h4.symm))
  have lasym : ∀ x y, lc x y → ¬lc y x := fun x y hxy hyx => by
    obtain ⟨i, j, h1, h2, h3, h4, hl, hne⟩ := (hlc x y).1 hxy
    obtain ⟨j', i', h1', h2', h3', h4', hl', -⟩ := (hlc y x).1 hyx
    have ei := hsk i i' (h1.trans h3'.symm) (h2.trans h4'.symm)
    have ej := hsk j' j (h1'.trans h3.symm) (h2'.trans h4.symm)
    rw [hks, hks] at ei ej
    have hji : lexLe (ascKeys R.n es0) j i = true :=
      lexLe_trans _ _ _ _ (lexLe_trans _ _ _ _ (lexLe_of_keys _ ej.symm) hl') (lexLe_of_keys _ ei.symm)
    exact hne (by rw [hks, hks]; exact keys_of_lexLe _ hl hji)
  -- a cell in canonical order satisfies the right-hand side, and every such list is ascending in `lc`
  have fwd : ∀ L : List Nat, L.Pairwise (· < ·) → (∀ j, j ∈ L ↔ ∃ hj : j < r.n.toNat, r.key.row ⟨j, hj⟩ = a) →
      let ys := L.map fun j => if hj : j < r.n.toNat then r.val.row ⟨j, hj⟩ else B.dflt
      (∀ b, b ∈ ys ↔ R.Holds a b) ∧ ∀ es, Vals.cols (A := .prod A B) (R.key, R.val) = .ok es →
        ∃ s : Fin ys.length → Fin R.n.toNat, (∀ u, R.key.row (s u) = a ∧ R.val.row (s u) = ys[u]) ∧
          ∀ u u' : Fin ys.length, u.1 < u'.1 → lexLe (ascKeys R.n es) (s u) (s u') = true ∧
            seenKey R.n es (s u) ≠ seenKey R.n es (s u') := by
    intro L hLp hLm ys
    refine ⟨fun b => ?_, fun es hes => ?_⟩
    · rw [← canon_holds hr, List.mem_map]
      constructor
      · rintro ⟨j, hj, rfl⟩
        obtain ⟨hj', e⟩ := (hLm j).1 hj
        exact ⟨⟨j, hj'⟩, e, by simp only [dif_pos hj']⟩
      · rintro ⟨j, e1, rfl⟩
        exact ⟨j.1, (hLm j.1).2 ⟨j.2, e1⟩, by simp only [dif_pos j.2]⟩
    · obtain ⟨sel, hrow, hord⟩ := canon_sorted hr hes
      have hLr : ∀ u (hu : u < L.length), L[u] < r.n.toNat := fun u hu => ((hLm _).1 (List.getElem_mem hu)).1
      have hlen : ys.length = L.length := List.length_map _
      refine ⟨fun u => sel ⟨L[u.1]'(by omega), hLr u.1 (by omega)⟩, fun u => ?_, fun u u' hu => ?_⟩
      · obtain ⟨e1, e2⟩ := Prod.mk.inj (hrow ⟨L[u.1]'(by omega), hLr u.1 (by omega)⟩)
        refine ⟨e1 ▸ ((hLm _).1 (List.getElem_mem _)).2, ?_⟩
        rw [← e2]; simp only [ys, Fin.getElem_fin, List.getElem_map, dif_pos (hLr u.1 (by omega))]
      · exact hord _ _ (List.pairwise_iff_getElem.1 hLp _ _ (by omega) (by omega) hu)
  have pw : ∀ ys : List B.El, (∀ es, Vals.cols (A := .prod A B) (R.key, R.val) = .ok es →
      ∃ s : Fin ys.length → Fin R.n.toNat, (∀ u, R.key.row (s u) = a ∧ R.val.row (s u) = ys[u]) ∧
        ∀ u u' : Fin ys.length, u.1 < u'.1 → lexLe (ascKeys R.n es) (s u) (s u') = true ∧
          seenKey R.n es (s u) ≠ seenKey R.n es (s u')) → ys.Pairwise lc := fun ys hy => by
    obtain ⟨s, hs, hord⟩ := hy es0 hes0
    refine List.pairwise_iff_getElem.2 fun u u' hu hu' hlt => (hlc _ _).2 ?_
    obtain ⟨h1, h2⟩ := hs ⟨u, hu⟩; obtain ⟨h3, h4⟩ := hs ⟨u', hu'⟩
    exact ⟨_, _, h1, h2, h3, h4, hord ⟨u, hu⟩ ⟨u', hu'⟩ hlt⟩
  constructor
  · rintro ⟨hD, L, hLp, hLm, rfl⟩
    exact ⟨hD, fwd L hLp hLm⟩
  · rintro ⟨hD, hm, ho⟩
    obtain ⟨L, hLp, hLm⟩ := exists_range_filter r.n.toNat fun j hj => r.key.row ⟨j, hj⟩ = a
    obtain ⟨hm0, ho0⟩ := fwd L hLp hLm
    exact ⟨hD, L, hLp, hLm, pairwise_eq_of_mem lirr lasym (pw ys ho) (pw _ ho0) fun b => by rw [hm, hm0]⟩

/-- **`lam D R` denotes `lamDen R` on the keys `D`** (`Tm.lam`), where `B`'s order codes agree with `B.lt`: `hB` says
that on any table of pairs, two rows of one key whose codes ascend strictly (`lexLe`, distinct `seenKey`) hold
values ascending in `B.lt` (`Obj.key`). `lam_holds`'s cell is then `B.lt`-ascending, and `lamDen`'s list is that
cell (`pairwise_eq_of_mem`). `hB` fails at a float atom: `ordCode` is IEEE totalOrder on stored bits, `Obj.key`
puts every NaN lowest and `-0.0 = +0.0`. -/
theorem lam_den {n : USize} {D : Vals A n} {R : Tab A B} {T : Tab A (.arr B)} (h : Tab.lam D R = .ok T)
    (hB : ∀ (m : USize) (x : Vals (.prod A B) m) es, Vals.cols x = .ok es → ∀ i i' : Fin m.toNat,
      (x.row i).1 = (x.row i').1 → lexLe (ascKeys m es) i i' = true → seenKey m es i ≠ seenKey m es i' →
        B.lt (x.row i).2 (x.row i').2)
    (a : A.El) (ys : List B.El) : T.Holds a ys ↔ (∃ i, D.row i = a) ∧ Lang.lamDen R.Holds a ys := by
  obtain ⟨r, U, hr, hU, hH⟩ := lam_canon h
  obtain ⟨es0, -, hes0, -⟩ := canon_codes hr
  have lirr : ∀ x, ¬B.lt x x := fun x => List.lt_irrefl _
  have lasym : ∀ x y, B.lt x y → ¬B.lt y x := fun _ _ => List.lt_asymm
  have up : ∀ ys : List B.El, (∀ es, Vals.cols (A := .prod A B) (R.key, R.val) = .ok es →
      ∃ s : Fin ys.length → Fin R.n.toNat, (∀ u, R.key.row (s u) = a ∧ R.val.row (s u) = ys[u]) ∧
        ∀ u u' : Fin ys.length, u.1 < u'.1 → lexLe (ascKeys R.n es) (s u) (s u') = true ∧
          seenKey R.n es (s u) ≠ seenKey R.n es (s u')) → ys.Pairwise B.lt := fun ys ho => by
    obtain ⟨s, hs, hord⟩ := ho es0 hes0
    refine List.pairwise_iff_getElem.2 fun u u' hu hu' hlt => ?_
    obtain ⟨h1, h2⟩ := hs ⟨u, hu⟩; obtain ⟨h3, h4⟩ := hs ⟨u', hu'⟩
    obtain ⟨hl, hne⟩ := hord ⟨u, hu⟩ ⟨u', hu'⟩ hlt
    have := hB R.n (R.key, R.val) es0 hes0 (s ⟨u, hu⟩) (s ⟨u', hu'⟩) (h1.trans h3.symm) hl hne
    simp only [Fin.getElem_fin] at h2 h4
    rw [← h2, ← h4]; exact this
  rw [lam_holds h]
  constructor
  · rintro ⟨hD, hm, ho⟩; exact ⟨hD, up ys ho, hm⟩
  · rintro ⟨hD, hp, hm⟩
    obtain ⟨L, hLp, hLm⟩ := exists_range_filter r.n.toNat fun j hj => r.key.row ⟨j, hj⟩ = a
    have hT0 := (canon_holds hU _ _).2 ((hH _ _).2 ⟨hD, L, hLp, hLm, rfl⟩)
    obtain ⟨-, hm0, ho0⟩ := (lam_holds h a _).1 hT0
    rw [pairwise_eq_of_mem lirr lasym hp (up _ ho0) fun b => by rw [hm, hm0]]
    exact (lam_holds h a _).1 hT0

/-- **`E X R` is `lam X Q`, `Q` the pairs `(xs, b)` of `X` with `b` an image of an element of `xs`** (`mem_holds`,
`comp_holds`): `E`'s laws are `lam`'s at `Q`. -/
theorem E_lam {n : USize} {X : Vals (.arr A) n} {R : Tab A B} {T : Tab (.arr A) (.arr B)} (h : Tab.E X R = .ok T) :
    ∃ Q : Tab (.arr A) B, Tab.lam X Q = .ok T ∧
      ∀ xs b, Q.Holds xs b ↔ (∃ i, X.row i = xs) ∧ ∃ a, a ∈ xs ∧ R.Holds a b := by
  simp only [Tab.E, bind] at h
  rw [Except.bind_eq_ok'] at h; obtain ⟨M0, hM0, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨Q, hQ, h⟩ := h
  refine ⟨Q, h, fun xs b => ?_⟩
  rw [comp_holds hQ]
  simp only [mem_holds hM0]
  exact ⟨fun ⟨a, ⟨hX, ha⟩, hr⟩ => ⟨hX, a, ha, hr⟩, fun ⟨hX, a, ha, hr⟩ => ⟨a, ⟨hX, ha⟩, hr⟩⟩

/-- **`E X R` denotes `E(R)` on the arrays `X`, each cell in the order codes of `Q`** (`E_lam`, `lam_holds`): `xs`
of `X` to the images of its elements under `R`, each once, ascending by the codes of the rows `(xs, b)` of `Q`. -/
theorem E_holds {n : USize} {X : Vals (.arr A) n} {R : Tab A B} {T : Tab (.arr A) (.arr B)} (h : Tab.E X R = .ok T) :
    ∃ Q : Tab (.arr A) B, (∀ xs b, Q.Holds xs b ↔ (∃ i, X.row i = xs) ∧ ∃ a, a ∈ xs ∧ R.Holds a b) ∧
      ∀ xs ys, T.Holds xs ys ↔ (∃ i, X.row i = xs) ∧ (∀ b, b ∈ ys ↔ ∃ a, a ∈ xs ∧ R.Holds a b) ∧
        ∀ es, Vals.cols (A := .prod (.arr A) B) (Q.key, Q.val) = .ok es →
          ∃ s : Fin ys.length → Fin Q.n.toNat, (∀ u, Q.key.row (s u) = xs ∧ Q.val.row (s u) = ys[u]) ∧
            ∀ u u' : Fin ys.length, u.1 < u'.1 → lexLe (ascKeys Q.n es) (s u) (s u') = true ∧
              seenKey Q.n es (s u) ≠ seenKey Q.n es (s u') := by
  obtain ⟨Q, hl, hQ⟩ := E_lam h
  refine ⟨Q, hQ, fun xs ys => ?_⟩
  rw [lam_holds hl]
  constructor
  · rintro ⟨hX, hm, ho⟩
    exact ⟨hX, fun b => (hm b).trans ((hQ xs b).trans ⟨fun h => h.2, fun h => ⟨hX, h⟩⟩), ho⟩
  · rintro ⟨hX, hm, ho⟩
    exact ⟨hX, fun b => (hm b).trans ((hQ xs b).trans ⟨fun h => h.2, fun h => ⟨hX, h⟩⟩).symm, ho⟩

/-- **`E X R` denotes `EDen R` on the arrays `X`** (`Tm.E`), where `B`'s order codes agree with `B.lt` on tables of
pairs keyed by arrays of `A` (`lam_den`'s `hB` at `.arr A`). -/
theorem E_den {n : USize} {X : Vals (.arr A) n} {R : Tab A B} {T : Tab (.arr A) (.arr B)} (h : Tab.E X R = .ok T)
    (hB : ∀ (m : USize) (x : Vals (.prod (.arr A) B) m) es, Vals.cols x = .ok es → ∀ i i' : Fin m.toNat,
      (x.row i).1 = (x.row i').1 → lexLe (ascKeys m es) i i' = true → seenKey m es i ≠ seenKey m es i' →
        B.lt (x.row i).2 (x.row i').2)
    (xs : List A.El) (ys : List B.El) : T.Holds xs ys ↔ (∃ i, X.row i = xs) ∧ Lang.EDen R.Holds xs ys := by
  obtain ⟨Q, hl, hQ⟩ := E_lam h
  rw [lam_den hl hB]
  simp only [Lang.EDen, Lang.lamDen, Core.Rel.comp, hQ]
  constructor
  · rintro ⟨hX, hp, hm⟩
    exact ⟨hX, hp, fun b => (hm b).trans ⟨fun ⟨_, a, ha, hr⟩ => ⟨a, ha, hr⟩, fun ⟨a, ha, hr⟩ => ⟨hX, a, ha, hr⟩⟩⟩
  · rintro ⟨hX, hp, hm⟩
    exact ⟨hX, hp, fun b => (hm b).trans ⟨fun ⟨a, ha, hr⟩ => ⟨hX, a, ha, hr⟩, fun ⟨_, a, ha, hr⟩ => ⟨a, ha, hr⟩⟩⟩

/-- **`setify X` denotes `Λ(∋)` on the arrays `X`** (`rowDens`'s `setify`), where `B`'s order codes agree with
`B.lt` (`lam_den`'s `hB`): `lam_den` of `mem_holds`. -/
theorem setify_den {n : USize} {X : Vals (.arr B) n} {T : Tab (.arr B) (.arr B)} (h : Tab.setify X = .ok T)
    (hB : ∀ (m : USize) (x : Vals (.prod (.arr B) B) m) es, Vals.cols x = .ok es → ∀ i i' : Fin m.toNat,
      (x.row i).1 = (x.row i').1 → lexLe (ascKeys m es) i i' = true → seenKey m es i ≠ seenKey m es i' →
        B.lt (x.row i).2 (x.row i').2)
    (xs : List B.El) (ys : List B.El) :
    T.Holds xs ys ↔ (∃ i, X.row i = xs) ∧ Lang.lamDen (fun xs b => b ∈ xs : Lang.Den (.arr B) B) xs ys := by
  unfold Tab.setify at h; simp only [bind] at h
  rw [Except.bind_eq_ok'] at h; obtain ⟨G, hG, h⟩ := h
  rw [lam_den h hB]
  constructor
  · rintro ⟨hX, hp, hm⟩
    exact ⟨hX, hp, fun b => (hm b).trans ((mem_holds hG xs b).trans (and_iff_right hX))⟩
  · rintro ⟨hX, hp, hm⟩
    exact ⟨hX, hp, fun b => (hm b).trans ((mem_holds hG xs b).trans (and_iff_right hX)).symm⟩

/-- **`tau X` denotes `τ` on `X`** (`rowDens`: `Y = [a]`), where `A`'s order codes agree with `A.lt`: `lam_den` of
`idU_holds`, the one list of `A.lt`-ascending elements `{a}` being `[a]` (`pairwise_eq_of_mem`). -/
theorem tau_den {A : Obj} {n : USize} {X : Vals A n} {T : Tab A (.arr A)} (h : Tab.tau X = .ok T)
    (hB : ∀ (m : USize) (x : Vals (.prod A A) m) es, Vals.cols x = .ok es → ∀ i i' : Fin m.toNat,
      (x.row i).1 = (x.row i').1 → lexLe (ascKeys m es) i i' = true → seenKey m es i ≠ seenKey m es i' →
        A.lt (x.row i).2 (x.row i').2)
    (a : A.El) (ys : List A.El) : T.Holds a ys ↔ (∃ i, X.row i = a) ∧ ys = [a] := by
  unfold Tab.tau at h; simp only [bind] at h
  rw [Except.bind_eq_ok'] at h; obtain ⟨I, hI, h⟩ := h
  rw [lam_den h hB]
  have lirr : ∀ x, ¬A.lt x x := fun x => List.lt_irrefl _
  have lasym : ∀ x y, A.lt x y → ¬A.lt y x := fun _ _ => List.lt_asymm
  constructor
  · rintro ⟨hX, hp, hm⟩
    refine ⟨hX, pairwise_eq_of_mem lirr lasym hp (List.pairwise_singleton _ _) fun b => (hm b).trans ?_⟩
    rw [idU_holds hI, List.mem_singleton]; exact ⟨fun h => h.1.symm, fun h => ⟨h.symm, hX⟩⟩
  · rintro ⟨hX, rfl⟩
    refine ⟨hX, List.pairwise_singleton _ _, fun b => ?_⟩
    rw [idU_holds hI, List.mem_singleton]; exact ⟨fun h => ⟨h.symm, hX⟩, fun h => h.1.symm⟩

end Tab

end Rel
