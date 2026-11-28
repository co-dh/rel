module

public import Rel.Run.Div
public import Rel.Run.Fix
public import Rel.Run.Power
public import Rel.Run.List
public import Rel.Run.Bits
public import Rel.Run.Asc
public import Rel.RepCols
public import Rel.RepCanon
public import Rel.RepSetOps
public import Rel.RepTabCompBase

-- exposed: every def body is a spec a downstream `rfl`/`decide`/`simp` may unfold (PLAN W.8)
@[expose] public section

/-! `pack` keeps the rows and `Tab.WF` (`ValsB.pack_row`, `ValsB.pack_wf`, `Tab.pack_holds`), before `Tab.comp`'s
blocks (`Rel/RepTabComp.lean`) pack their accumulator. -/

namespace Rel
open  Rel.Kernel Rel.Verify Enc

variable {A B : Obj}

theorem Opt.filler_ne {t : QAtomicType} (hg : t ≠ .general) : Opt.filler t = none := by
  cases t <;> first | exact absurd rfl hg | rfl

/-- **An `arr` row whose words are in range**: `lo = a`, `hi = b` with `a ≤ b ≤ m < 2^63` read the payload rows
`[a, b)`. -/
theorem Vals.row_cell {B : Obj} {n m : USize} (lo hi : ColB false .i64 n) (f : Vals B m) (i : Fin n.toNat) {a b : Nat}
    (ha : (raw .i64 n lo.enc)[i.1]?.getD 0 = a.toUInt64) (hb : (raw .i64 n hi.enc)[i.1]?.getD 0 = b.toUInt64)
    (hab : a ≤ b) (hbm : b ≤ m.toNat) (hm : m.toNat < 2 ^ 63) :
    ValsB.row (o := false) (A := .arr B) ⟨m, lo, hi, f⟩ i =
      (List.range' a (b - a)).map fun k => if h : k < m.toNat then ValsB.row f ⟨k, h⟩ else B.dflt := by
  have hc : 0 ≤ (lo.get i).toInt ∧ (lo.get i).toInt ≤ (hi.get i).toInt ∧ (hi.get i).toInt ≤ (m.toNat : Int) := by
    simp only [ColB.get_i64 lo (Arr.flat lo _), ColB.get_i64 hi (Arr.flat hi _), ha, hb, toInt64_toInt_nat (show a < 2 ^ 63 by omega),
      toInt64_toInt_nat (show b < 2 ^ 63 by omega)]; omega
  have hu : (i.1.toUInt64).toNat = i.1 := by
    have := i.2; have := n.toNat_lt_size; have := USize.size_le; simp; omega
  rw [ValsB.row_arr i (Arr.flat lo i) (Arr.flat hi i) hc]
  simp only [cellStart, cellLen, hu, ha, hb, toInt64_toInt_nat (show a < 2 ^ 63 by omega),
    toInt64_toInt_nat (show b < 2 ^ 63 by omega)]
  congr 2 <;> omega

/-- **`Vals.row_cell` for a cell that may lie past the payload**: `a ≤ b` with `b ≤ m` or `a = b`, the empty cell
being read empty wherever it lies (`uncat`'s split of a cell `cellSpan` clamped). -/
theorem Vals.row_span {B : Obj} {n m : USize} (lo hi : ColB false .i64 n) (f : Vals B m) (i : Fin n.toNat) {a b : Nat}
    (ha : (raw .i64 n lo.enc)[i.1]?.getD 0 = a.toUInt64) (hb : (raw .i64 n hi.enc)[i.1]?.getD 0 = b.toUInt64)
    (hab : a ≤ b) (hbm : b ≤ m.toNat ∨ a = b) (h63 : a < 2 ^ 63) (hm : m.toNat < 2 ^ 63) :
    ValsB.row (o := false) (A := .arr B) ⟨m, lo, hi, f⟩ i =
      (List.range' a (b - a)).map fun k => if h : k < m.toNat then ValsB.row f ⟨k, h⟩ else B.dflt := by
  rcases hbm with hbm | rfl
  · exact Vals.row_cell lo hi f i ha hb hab hbm hm
  rw [Vals.row_empty i (by rw [ColB.get_i64 lo (Arr.flat lo _), ColB.get_i64 hi (Arr.flat hi _)]; rw [ha, hb]), Nat.sub_self, List.range'_zero, List.map_nil]

/-- **A cell `Vals.WF` admits reads as `[SN, EN)`** (`0 ≤ lo ≤ hi ≤ m`, so no clamp): `lo = SN`, `hi = EN` as
words, and the row is the payload rows `[SN, EN)`, so `SN ≤ EN`, and `EN ≤ m` or the cell is empty. -/
theorem cellSpan_spec {B : Obj} {n m : USize} {lo up : ColB false .i64 n}
    (hc : ∀ i : Fin n.toNat, 0 ≤ (lo.get i).toInt ∧ (lo.get i).toInt ≤ (up.get i).toInt ∧
      (up.get i).toInt ≤ (m.toNat : Int))
    (hm63 : m.toNat < 2 ^ 63) (f : Vals B m) :
    ∃ SN EN : Nat → Nat, (∀ i < n.toNat, (raw .i64 n lo.enc)[i]?.getD 0 = (SN i).toUInt64 ∧
      (raw .i64 n up.enc)[i]?.getD 0 = (EN i).toUInt64) ∧
      (∀ i, SN i ≤ EN i ∧ SN i < 2 ^ 63 ∧ (EN i ≤ m.toNat ∨ EN i = SN i)) ∧
      ∀ i : Fin n.toNat, ValsB.row (o := false) (A := .arr B) ⟨m, lo, up, f⟩ i =
        (List.range' (SN i) (EN i - SN i)).map fun k => if h : k < m.toNat then ValsB.row f ⟨k, h⟩ else B.dflt := by
  obtain ⟨Lf, hLf⟩ : ∃ F : Nat → Int, ∀ i, F i = ((raw .i64 n lo.enc)[i]?.getD 0).toInt64.toInt := ⟨_, fun _ => rfl⟩
  obtain ⟨Hf, hHf⟩ : ∃ F : Nat → Int, ∀ i, F i = ((raw .i64 n up.enc)[i]?.getD 0).toInt64.toInt := ⟨_, fun _ => rfl⟩
  obtain ⟨SN, hSN⟩ : ∃ F : Nat → Nat, ∀ i, F i = (Lf i).toNat := ⟨_, fun _ => rfl⟩
  obtain ⟨EN, hEN⟩ : ∃ F : Nat → Nat, ∀ i, F i = max (min (Hf i).toNat m.toNat) (SN i) := ⟨_, fun _ => rfl⟩
  have hL63 : ∀ i, Lf i < 2 ^ 63 := fun i => by
    rw [hLf, toInt64_toInt_cond]; have := ((raw .i64 n lo.enc)[i]?.getD 0).toNat_lt; split <;> omega
  have hcw : ∀ i < n.toNat, 0 ≤ Lf i ∧ Lf i ≤ Hf i ∧ Hf i ≤ m.toNat := fun i hi => by
    have := hc ⟨i, hi⟩; rw [ColB.get_i64 lo (Arr.flat lo _), ColB.get_i64 up (Arr.flat up _)] at this; rw [hLf, hHf]; exact this
  have hsw : ∀ i < n.toNat, (raw .i64 n lo.enc)[i]?.getD 0 = (SN i).toUInt64 := fun i hi => by
    obtain ⟨-, hv⟩ := toInt64_nonneg (x := (raw .i64 n lo.enc)[i]?.getD 0) (by rw [← hLf]; exact (hcw i hi).1)
    rw [← hLf] at hv; rw [hSN, hv, Int.toNat_natCast]; exact UInt64.ofNat_toNat.symm
  have hew : ∀ i < n.toNat, (raw .i64 n up.enc)[i]?.getD 0 = (EN i).toUInt64 := fun i hi => by
    obtain ⟨-, hv⟩ := toInt64_nonneg (x := (raw .i64 n up.enc)[i]?.getD 0) (by rw [← hHf]; have := hcw i hi; omega)
    rw [← hHf] at hv; have := hcw i hi
    rw [show EN i = ((raw .i64 n up.enc)[i]?.getD 0).toNat by rw [hEN, hSN]; omega]; exact UInt64.ofNat_toNat.symm
  refine ⟨SN, EN, fun i hi => ⟨hsw i hi, hew i hi⟩, fun i => ⟨by rw [hEN]; omega,
    by rw [hSN]; have := hL63 i; omega, by rw [hEN]; omega⟩, fun i => ?_⟩
  have hi : (i.1.toUInt64).toNat = i.1 := by
    have := i.2; have := n.toNat_lt_size; have := USize.size_le; simp; omega
  rw [ValsB.row_arr i (Arr.flat lo i) (Arr.flat up i) (hc i)]
  simp only [cellStart, cellLen, hi, ← hLf, ← hHf]
  have := hcw i i.2
  rw [show (Lf i).toNat = SN i by rw [hSN], show (Hf i).toNat - SN i = EN i - SN i by rw [hEN, hSN]; omega]

/-- **The start of a cell `Vals.WF` admits is at most `m`**: `0 ≤ lo ≤ hi ≤ m`. -/
theorem cellSpan_start_le {n m : USize} {lo up : ColB false .i64 n}
    (hc : ∀ i : Fin n.toNat, 0 ≤ (lo.get i).toInt ∧ (lo.get i).toInt ≤ (up.get i).toInt ∧
      (up.get i).toInt ≤ (m.toNat : Int)) (i : Fin n.toNat) : ((raw .i64 n lo.enc)[i.1]?.getD 0).toNat ≤ m.toNat := by
  have hl := hc i
  rw [ColB.get_i64 lo (Arr.flat lo _), ColB.get_i64 up (Arr.flat up _)] at hl
  obtain ⟨-, hv⟩ := toInt64_nonneg (x := (raw .i64 n lo.enc)[i.1]?.getD 0) hl.1
  omega

/-- **The non-empty cells** (`uncons`, `unsnoc`): `whereCol` of `lo < hi` on cells `Vals.WF` admits lists exactly
the cells `[SN, EN)` with `SN < EN`. -/
theorem cellSpan_where {B : Obj} {n m M : USize} {lo up : ColB false .i64 n} {lt sel : Enc}
    (h : ∀ i : Fin n.toNat, 0 ≤ (lo.get i).toInt ∧ (lo.get i).toInt ≤ (up.get i).toInt ∧
      (up.get i).toInt ≤ (m.toNat : Int))
    (hlt : colMap .lt n lo.enc up.enc = .ok lt) (hw : whereCol n lt = .ok (M, sel))
    (hm63 : m.toNat < 2 ^ 63) (f : Vals B m) :
    ∃ SN EN : Nat → Nat, (∀ i < n.toNat, (raw .i64 n lo.enc)[i]?.getD 0 = (SN i).toUInt64 ∧
      (raw .i64 n up.enc)[i]?.getD 0 = (EN i).toUInt64) ∧
      (∀ i, SN i ≤ EN i ∧ SN i < 2 ^ 63 ∧ (EN i ≤ m.toNat ∨ EN i = SN i)) ∧
      (∀ i : Fin n.toNat, ValsB.row (o := false) (A := .arr B) ⟨m, lo, up, f⟩ i =
        (List.range' (SN i) (EN i - SN i)).map fun k => if h : k < m.toNat then ValsB.row f ⟨k, h⟩ else B.dflt) ∧
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

/-- **A cell `[a, b)` with `a ≤ b ≤ m`**, its bounds the words of the naturals `a` and `b`, `m` below `2^63`: the cell
clause of `Vals.WF`. -/
theorem cell_wf_nat {n m : USize} {lo hi : Arr .i64 n} {i : Fin n.toNat} {a b : Nat}
    (hlo : (raw .i64 n lo.enc)[i.1]?.getD 0 = a.toUInt64) (hhi : (raw .i64 n hi.enc)[i.1]?.getD 0 = b.toUInt64)
    (hab : a ≤ b) (hbm : b ≤ m.toNat) (hm : m.toNat < 2 ^ 63) :
    0 ≤ (lo.get i).toInt ∧ (lo.get i).toInt ≤ (hi.get i).toInt ∧ (hi.get i).toInt ≤ (m.toNat : Int) := by
  rw [Arr.get_i64, Arr.get_i64, hlo, hhi, toInt64_toInt_nat (by omega), toInt64_toInt_nat (by omega)]; omega

/-- **A one-source `scanArr .first` with no chains copies its source**: row `i` of the answer is row `i` of `P`. -/
theorem scanArr_first_word {n : USize} {P : Enc} {hs : kscanStream .first [(n, P)] [] [] = false} {y : Arr .i64 n}
    (h : scanArr .first false .i64 .i64 n none [(n, P)] [] [] hs = .ok y) (i : Nat) (hi : i < n.toNat) :
    (raw .i64 n y.enc)[i]? = some ((raw .i64 n P)[i]?.getD 0) := by
  unfold scanArr at h
  split at h
  · rename_i r hr
    cases h
    obtain ⟨-, -, hrow⟩ := kscan_first_chain hs hr
    obtain ⟨v, hc, ho⟩ := hrow i hi
    simp only [chain, List.foldlM_nil, pure, Except.pure, Except.ok.injEq] at hc
    subst hc
    simpa only [if_neg (by decide : QAtomicType.i64 ≠ .u1), Arr.enc] using ho
  · cases h

/-- **`Vals.cells` lays cell `i` out at `[Σ_{<i} w, Σ_{≤i} w)`** of its payload, as the words of `lo` and `hi`. -/
theorem Vals.cells_spec {B : Obj} {n T : USize} {w : Enc} {pay : Vals B T} {Y : Vals (.arr B) n}
    (hY : Vals.cells n w pay = .ok Y) (wN : Nat → Nat) (hw : ∀ i < n.toNat, (raw .i64 n w)[i]?.getD 0 = (wN i).toUInt64)
    (hT : ((List.range n.toNat).map wN).sum ≤ T.toNat) (_hT63 : T.toNat < 2 ^ 63) :
    ∃ lo hi : Arr .i64 n, Y = ⟨T, lo, hi, pay⟩ ∧ ∀ i : Fin n.toNat,
      ((List.range i.1).map wN).sum + wN i.1 ≤ T.toNat ∧
      (raw .i64 n lo.enc)[i.1]?.getD 0 = ((List.range i.1).map wN).sum.toUInt64 ∧
      (raw .i64 n hi.enc)[i.1]?.getD 0 = (((List.range i.1).map wN).sum + wN i.1).toUInt64 := by
  simp only [Vals.cells, bind] at hY
  rw [Except.bind_eq_ok'] at hY; obtain ⟨P', hP', hY⟩ := hY
  rw [Except.bind_eq_ok'] at hY; obtain ⟨lo', hlo', hY⟩ := hY
  rw [Except.bind_eq_ok'] at hY; obtain ⟨hi', hhi', hY⟩ := hY
  cases hY
  have hP'w := colPrefix_add_sum hP' wN hw
  refine ⟨lo', hi', rfl, fun i => ?_⟩
  have hgS : ((List.range i.1).map wN).sum + wN i.1 ≤ ((List.range n.toNat).map wN).sum := by
    rw [← sum_range_succ']; exact sum_range_mono wN i.2
  refine ⟨by omega, ?_, ?_⟩
  · have es := (colMap_raw (colArr_ok hlo')).2.2.2 i.1 i.2
    rw [hP'w i.1 i.2, hw i.1 i.2, sum_range_succ'] at es; simp only [Op.eval, Except.ok.injEq] at es
    rw [← es, ← toUInt64_sub (by omega), Nat.add_sub_cancel]
  · rw [scanArr_first_word hhi' i.1 i.2, Option.getD_some, hP'w i.1 i.2]
    simp [List.range_succ]

/-- **`Vals.cells` reads cell `i` as the payload rows `[Σ_{<i} w, Σ_{≤i} w)`** (`Vals.cells_spec`). -/
theorem Vals.cells_row {B : Obj} {n T : USize} {w : Enc} {pay : Vals B T} {Y : Vals (.arr B) n}
    (hY : Vals.cells n w pay = .ok Y) (wN : Nat → Nat) (hw : ∀ i < n.toNat, (raw .i64 n w)[i]?.getD 0 = (wN i).toUInt64)
    (hT : ((List.range n.toNat).map wN).sum ≤ T.toNat) (hT63 : T.toNat < 2 ^ 63) (i : Fin n.toNat) :
    ValsB.row Y i = (List.range' ((List.range i.1).map wN).sum (wN i.1)).map
      fun k => if h : k < T.toNat then ValsB.row pay ⟨k, h⟩ else B.dflt := by
  obtain ⟨lo', hi', rfl, hb⟩ := Vals.cells_spec hY wN hw hT hT63
  obtain ⟨hgT, hlo, hhi⟩ := hb i
  rw [Vals.row_cell lo' hi' pay i hlo hhi (by omega) hgT hT63, Nat.add_sub_cancel_left]

/-- **`Vals.cells` keeps `Vals.WF`**: cell `i` is `[Σ_{<i} w, Σ_{≤i} w)`, inside the `T` payload rows the widths sum
to at most (`Vals.cells_spec`). -/
theorem Vals.cells_wf {B : Obj} {n T : USize} {w : Enc} {pay : Vals B T} {Y : Vals (.arr B) n}
    (hY : Vals.cells n w pay = .ok Y) (wN : Nat → Nat) (hw : ∀ i < n.toNat, (raw .i64 n w)[i]?.getD 0 = (wN i).toUInt64)
    (hT : ((List.range n.toNat).map wN).sum ≤ T.toNat) (hT63 : T.toNat < 2 ^ 63) (hp : Vals.WF pay) : Vals.WF Y := by
  obtain ⟨lo', hi', rfl, hb⟩ := Vals.cells_spec hY wN hw hT hT63
  refine ⟨trivial, trivial, fun i _ => ?_, hp⟩
  obtain ⟨hgT, hlo, hhi⟩ := hb i
  exact cell_wf_nat hlo hhi (by omega) hgT hT63

/-- `Σ_{<k} wN ≤ k · c` where each `wN i` below `k` is at most `c`. -/
theorem sum_range_le_mul {wN : Nat → Nat} {c : Nat} : ∀ {k : Nat}, (∀ i < k, wN i ≤ c) →
    ((List.range k).map wN).sum ≤ k * c
  | 0, _ => by simp
  | k + 1, h => by
    have := h k (by omega); have := sum_range_le_mul (k := k) fun i hi => h i (by omega)
    rw [sum_range_succ', Nat.succ_mul]; omega

/-- **`cellSpan`'s widths**: word `i` of `e - s` is `EN i - SN i` (`cellSpan_spec`'s words), at most `m`. -/
theorem cellSpan_width {n m : USize} {s e : ColB false .i64 n} {w : Enc} {SN EN : Nat → Nat}
    (hse : ∀ i < n.toNat, (raw .i64 n s.enc)[i]?.getD 0 = (SN i).toUInt64 ∧
      (raw .i64 n e.enc)[i]?.getD 0 = (EN i).toUInt64)
    (hb : ∀ i, SN i ≤ EN i ∧ SN i < 2 ^ 63 ∧ (EN i ≤ m.toNat ∨ EN i = SN i)) (hw : colMap .sub n e.enc s.enc = .ok w) :
    ∀ i < n.toNat, (raw .i64 n w)[i]?.getD 0 = (EN i - SN i).toUInt64 ∧ EN i - SN i ≤ m.toNat := fun i hi => by
  have es := (colMap_raw hw).2.2.2 i hi
  rw [(hse i hi).2, (hse i hi).1] at es; simp only [Op.eval, Except.ok.injEq] at es
  exact ⟨by rw [← es, toUInt64_sub (hb i).1], by have := hb i; omega⟩

/-- **`Vals.cells` over the EXPAND of its own widths keeps `Vals.WF`** (`Vals.cells_wf`): each width at most `c` and
`n · c` below `2^63`, so the `T = Σ w` payload rows (`expand_spec`) hold every cell. -/
theorem Vals.cells_expand_wf {B : Obj} {n T : USize} {w G u : Enc} {pay : Vals B T} {Y : Vals (.arr B) n}
    (hex : expand n w = .ok (T, G, u)) (hY : Vals.cells n w pay = .ok Y) (c : Nat)
    (hc : ∀ i < n.toNat, ((raw .i64 n w)[i]?.getD 0).toNat ≤ c) (hnc : n.toNat * c < 2 ^ 63) (hn : n.toNat < 2 ^ 63)
    (hp : Vals.WF pay) : Vals.WF Y := by
  have hw : ∀ i < n.toNat, (raw .i64 n w)[i]?.getD 0 = ((raw .i64 n w)[i]?.getD 0).toNat.toUInt64 :=
    fun _ _ => UInt64.ofNat_toNat.symm
  have hs := sum_range_le_mul hc
  have hT := (expand_spec hex _ hw (by omega) hn).1
  exact Vals.cells_wf hY _ hw (by omega) (by omega) hp

/-- **A payload laid out by the EXPANDed widths of `X`'s cells** (`ValsB.pack`, `Tab.map`): the cells `n w pay` over a
payload whose row `t` is `g` of `X`'s payload row at the gathered position `ix[t]` are `X`'s cells mapped by `g`; the
output element `d` of cell `i` is payload row `Σ_{<i} w + d` (`expand_spec`, `colPrefix_add_sum`), there `SN i + d`. -/
theorem Vals.cells_expand_row {A B : Obj} {n m : USize} {lo up : ColB false .i64 n} {f : Vals A m}
    {w G u sg ix : Enc} {T : USize} (hb : ¬2 ^ 63 ≤ n.toNat * m.toNat + n.toNat + m.toNat)
    (hse : ∀ i : Fin n.toNat, 0 ≤ (lo.get i).toInt ∧ (lo.get i).toInt ≤ (up.get i).toInt ∧
      (up.get i).toInt ≤ (m.toNat : Int))
    (hw : colMap .sub n up.enc lo.enc = .ok w) (hex : expand n w = .ok (T, G, u))
    (hsg : kgather T G n lo.enc = .ok sg) (hix : colMap .add T sg u = .ok ix) (g : A.El → B.El) {pay : Vals B T}
    (hp : ∀ t : Fin T.toNat, ∃ j : Fin m.toNat, ((raw .i64 T ix)[t.1]?.getD 0).toNat = j.1 ∧
      ValsB.row pay t = g (ValsB.row f j))
    {Y : Vals (.arr B) n} (hY : Vals.cells n w pay = .ok Y) (i : Fin n.toNat) :
    ValsB.row Y i = (ValsB.row (o := false) (A := .arr A) ⟨m, lo, up, f⟩ i).map g := by
  have hm63 : m.toNat < 2 ^ 63 := by omega
  have hn63 : n.toNat < 2 ^ 63 := by omega
  have hnm : n.toNat * m.toNat < 2 ^ 63 := by omega
  obtain ⟨SN, EN, hse', hb1, hrow⟩ := cellSpan_spec hse hm63 f
  obtain ⟨wN, hwN⟩ : ∃ F : Nat → Nat, ∀ i, F i = EN i - SN i := ⟨_, fun _ => rfl⟩
  have hww : ∀ i < n.toNat, (raw .i64 n w)[i]?.getD 0 = (wN i).toUInt64 := fun i hi => by
    rw [hwN]; exact (cellSpan_width hse' hb1 hw i hi).1
  have hwm : ∀ i, wN i ≤ m.toNat := fun i => by have := hb1 i; rw [hwN]; omega
  have hsn : ((List.range n.toNat).map wN).sum < 2 ^ 63 := by
    have := sum_range_le_mul (k := n.toNat) fun i _ => hwm i; omega
  obtain ⟨hTn, hrun⟩ := expand_spec hex wN hww hsn hn63
  have hgS : ((List.range i.1).map wN).sum + wN i.1 ≤ ((List.range n.toNat).map wN).sum := by
    rw [← sum_range_succ']; exact sum_range_mono wN i.2
  rw [Vals.cells_row hY wN hww (by omega) (by omega) i, hrow i, ← hwN, List.range'_eq_map_range, List.range'_eq_map_range, List.map_map, List.map_map, List.map_map]
  refine List.map_congr_left fun d hd => ?_
  have hd' : d < wN i.1 := List.mem_range.mp hd
  have ht : ((List.range i.1).map wN).sum + d < T.toNat := by omega
  have hEm : SN i.1 + d < m.toNat := by have := hb1 i.1; rw [hwN] at hd'; omega
  simp only [Function.comp_apply, dif_pos ht, dif_pos hEm]
  obtain ⟨j, hj, hgj⟩ := hp ⟨_, ht⟩
  rw [hgj]; congr 2; apply Fin.ext; rw [← hj]; dsimp only
  obtain ⟨hG, hu⟩ := hrun i.1 i.2 (((List.range i.1).map wN).sum + d) (by omega) (by omega)
  have es := (colMap_raw hix).2.2.2 _ ht
  rw [(kgather_word hsg lo.plain _ ht).2, hG, toNat_toUInt64 (by omega), (hse' i.1 i.2).1, hu] at es
  simp only [Op.eval, Except.ok.injEq] at es
  rw [← es, ← UInt64.ofNat_add, Nat.add_sub_cancel_left,
    toNat_toUInt64 (by have := (hb1 i.1).2.1; have := hwm i.1; omega)]

/-- **`colConst n w` is a plain column** (`kscatter_closed`, `kscatter_plain`): `Enc.WF` at `i64`, no null. -/
theorem colConst_plain {n : USize} {w : UInt64} {e : Enc} (h : colConst n w = .ok e) :
    Enc.WF .i64 n e ∧ hasNul e = false :=
  ⟨(kscatter_closed h).2.2 (by decide) (by decide), kscatter_plain h rfl⟩

/-- **`colMap` of two columns under an op that orders null** (`Op.nulFold = some (b, fill)`), nulls included: the answer
is `Enc.WF` and row `i` has the flag `b` folds of the sources' flags (`kscan_nul_row`; `0` and `0` where neither holds a
null, `colMap_closed`) and, where that flag is `0`, the word `chain post (op (rdFill a) (rdFill c))`. -/
theorem colMap_nul_row {op b : Op} {fill : UInt64} (hnf : op.nulFold = some (b, fill)) (hb : b.eval 0 0 = .ok 0)
    {n : USize} {a c o : Enc} {post : List (Op × UInt64)} (hWa : Enc.WF .i64 n a) (hWc : Enc.WF .i64 n c)
    (hs : kscanStream op [(n, a), (n, c)] [] post = false) (h : colMap op n a c .i64 .i64 [] post = .ok o) :
    Enc.WF .i64 n o ∧ ∀ i < n.toNat, ∃ nl, b.eval (rdNul n a i) (rdNul n c i) = .ok nl ∧
      (foRNuls n o)[i]? = some (if nl != 0 then 1 else 0) ∧ (nl = 0 → ∃ w, (raw .i64 n o)[i]? = some w ∧
        (op.eval (rdFill fill .i64 n a i) (rdFill fill .i64 n c i) >>= chain post) = .ok w) := by
  have hWs : ∀ p ∈ [(n, a), (n, c)], Enc.WF .i64 p.1 p.2 := fun p hp => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> assumption
  by_cases hN : hasNul a = true ∨ hasNul c = true
  · have hex : ∃ p ∈ [(n, a), (n, c)], hasNul p.2 = true := by
      rcases hN with hN | hN
      · exact ⟨(n, a), by simp, hN⟩
      · exact ⟨(n, c), by simp, hN⟩
    unfold colMap at h; simp only [bind, Except.bind] at h
    split at h; · cases h
    rename_i r hr; simp only [pure, Except.pure, Except.ok.injEq] at h; subst h
    obtain ⟨out, nl, hos, hnl, hr1, hV, hF, p, ps, hes, hrow⟩ :=
      kscan_nul_row hnf (by decide : (QAtomicType.i64).width = some 8) (by decide) hs hWs hex hr
    simp only [List.cons.injEq] at hes; obtain ⟨rfl, rfl, -⟩ := hes
    refine ⟨hF, fun i hi => ?_⟩
    obtain ⟨hv, hn1, hn2⟩ := hrow i hi
    simp only [List.map_cons, List.map_nil, List.foldlM_cons, List.foldlM_nil, bind_pure] at hn1 hv
    refine ⟨nl[i]?.getD 0, hn1, hn2, fun h0 => ?_⟩
    have hsz : n.toNat = (out.map (cutBit .i64)).size := by simp [hos]
    have hb : Column.bitAt (nulMap nl) i = false := by
      have h1 := foRNuls_wordsFoR (out.map (cutBit .i64)) (nulMap nl) hsz i (by simpa [hos] using hi)
      rw [← hr1, hn2, h0] at h1
      cases hb : Column.bitAt (nulMap nl) i <;> simp_all
    have h2 := raw_wordsFoR_of_bit (out.map (cutBit .i64)) (nulMap nl) (m := n) (by simp [hos]) i
      (by simpa [hos] using hi) hb
    rw [← hr1] at h2
    refine ⟨out[i]?.getD 0, ?_, hv⟩
    rw [h2]; simp only [Array.getElem_map, cutBit, if_neg (by decide : QAtomicType.i64 ≠ .u1),
      Array.getElem?_eq_getElem (show i < out.size by omega), Option.getD_some]
  · have hNa : hasNul a = false := by simp_all
    have hNc : hasNul c = false := by simp_all
    have hF : op.nulFold = none ∨ ∀ p ∈ [(n, a), (n, c)], hasNul p.2 = false := Or.inr fun p hp => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp; rcases hp with rfl | rfl <;> assumption
    have hn : op ≠ .null := by rintro rfl; simp [Op.nulFold] at hnf
    have hC := colMap_closed hs h hF
    obtain ⟨-, -, -, hrow⟩ := colMap_chain h hs hn hF
    refine ⟨hC.2.1, fun i hi => ?_⟩
    have hra : rdNul n a i = 0 := by simp [rdNul, Verify.foRNuls_plain hWa hNa hi]
    have hrc : rdNul n c i = 0 := by simp [rdNul, Verify.foRNuls_plain hWc hNc hi]
    refine ⟨0, by rw [hra, hrc]; exact hb, by rw [Verify.foRNuls_plain hC.2.1 hC.2.2 hi]; rfl, fun _ => ?_⟩
    obtain ⟨x', y', v, w, hx, hy, hv, hw, ho⟩ := hrow i hi
    simp only [chain, List.foldlM_nil, pure, Except.pure, Except.ok.injEq] at hx hy
    subst hx hy
    refine ⟨w, by rw [ho, if_neg (by decide : QAtomicType.i64 ≠ .u1)], ?_⟩
    simp only [rdFill, hra, hrc, bne_self_eq_false, Bool.false_eq_true, if_false, hv]
    exact hw

/-- A null row of an `i64` column reads `default`, `i64` min (`Dep.Carrier.null`). -/
theorem ColB.get_null {n : USize} {x : Opt .i64 n} {i : Fin n.toNat} (h : x.get i = none) :
    (ColB.get (o := true) x i).toInt = -2 ^ 63 := by
  simp only [ColB.get, h]; decide

/-- Row `i` of `x` where it is not owned is the null, read as `i64` min. -/
theorem ColB.get_unowned {n : USize} {P : Fin n.toNat → Prop} {x : Opt .i64 n} (hx : ColB.OwnedOn (o := true) x P)
    {i : Fin n.toNat} (hp : ¬P i) : (ColB.get (o := true) x i).toInt = -2 ^ 63 :=
  ColB.get_null (by rw [(hx i).2 hp]; exact Opt.filler_ne (by decide))

/-- **`max x 0` of a nullable `i64` column is a plain column** (`colMap_nul_row`: a null reads `i64` min, which `max`
lifts to `0`): `ColB.get x` clamped below at `0`. -/
theorem Opt.maxZero {n : USize} (x : Opt .i64 n) {z s : Enc} (hz : colConst n 0 = .ok z)
    (h : colMap .max n x.enc z = .ok s) : ∃ a : Arr .i64 n, a.enc = s ∧
      ∀ i : Fin n.toNat, (a.get i).toInt = max (ColB.get (o := true) x i).toInt 0 := by
  obtain ⟨hzW, hzN⟩ := colConst_plain hz
  have hs : kscanStream .max [(n, x.enc), (n, z)] [] [] = false := by simp [kscanStream]
  obtain ⟨hW, hrow⟩ := colMap_nul_row (b := .and) (fill := 0x8000000000000000) rfl (by simp [Op.eval]) x.wf hzW hs h
  have hz0 : ∀ i < n.toNat, rdNul n z i = 0 := fun i hi => by simp [rdNul, Verify.foRNuls_plain hzW hzN hi]
  have hnl : ∀ i < n.toNat, ∀ nl, (Op.and).eval (rdNul n x.enc i) (rdNul n z i) = .ok nl → nl = 0 := fun i hi nl h1 => by
    rw [hz0 i hi] at h1; simp only [Op.eval, UInt64.and_zero, Except.ok.injEq] at h1; exact h1.symm
  have hfl : ∀ i < n.toNat, (foRNuls n s)[i]? = some 0 := fun i hi => by
    obtain ⟨nl, h1, h2, -⟩ := hrow i hi
    rw [h2, hnl i hi nl h1]; rfl
  have hN : hasNul s = false := by
    refine Classical.byContradiction fun hc => ?_
    have hc' : hasNul s = true := by simpa using hc
    rw [Verify.hasNul_flags hW] at hc'
    simp only [Array.any_eq_true] at hc'
    obtain ⟨j, hj, hne⟩ := hc'
    have hj' : j < n.toNat := by rwa [Verify.foRNuls_size] at hj
    have := hfl j hj'
    rw [Array.getElem?_eq_getElem hj] at this
    simp only [Option.some.injEq] at this
    simp [this] at hne
  refine ⟨Arr.mk s hW hN, rfl, fun i => ?_⟩
  obtain ⟨nl, h1, h2, h3⟩ := hrow i.1 i.2
  obtain ⟨w, hw, hv⟩ := h3 (hnl i.1 i.2 nl h1)
  rw [Arr.get_i64]
  show ((raw .i64 n s)[i.1]?.getD 0).toInt64.toInt = _
  rw [hw, Option.getD_some]
  have hzr : rdFill 0x8000000000000000 .i64 n z i.1 = 0 := by
    simp [rdFill, hz0 i.1 i.2, colConst_raw hz, Array.getElem?_replicate, i.2]
  rw [hzr] at hv
  simp only [Op.eval, chain, List.foldlM_nil, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at hv
  have h0 : ((0 : UInt64).toInt64).toInt = 0 := by decide
  have hi : ∀ x, Op.i x = x.toInt64 := fun _ => rfl
  by_cases hn : (foRNuls n x.enc)[i.1]? = some 0
  · have hr0 : rdNul n x.enc i.1 = 0 := by simp [rdNul, hn]
    simp only [rdFill, hr0, bne_self_eq_false, Bool.false_eq_true, if_false] at hv
    have hg := ColB.get_i64 (o := true) x hn
    rw [hg]
    split at hv
    · rename_i hlt
      have := Int64.lt_iff_toInt_lt.1 hlt
      simp only [hi] at this
      rw [h0] at this
      rw [← hv]
      change 0 = max ((raw .i64 n x.enc)[i.1]?.getD 0).toInt64.toInt 0
      omega
    · rename_i hlt
      have : ¬ ((raw .i64 n x.enc)[i.1]?.getD 0).toInt64.toInt < (0 : UInt64).toInt64.toInt :=
        fun hh => hlt (Int64.lt_iff_toInt_lt.2 hh)
      rw [h0] at this
      rw [← hv]
      change _ = max ((raw .i64 n x.enc)[i.1]?.getD 0).toInt64.toInt 0
      omega
  · have hr1 : rdNul n x.enc i.1 ≠ 0 := fun h0' => hn (by
      rw [foRNuls_bit n x.enc i.2]; simp [rdNul] at h0'; simp [h0'])
    have hnul : x.isNul i = true := by
      cases hh : x.isNul i
      · exact absurd ((Opt.isNul_eq_false x i).1 hh) hn
      · rfl
    simp only [rdFill, bne_iff_ne, ne_eq, hr1, not_false_eq_true, if_true] at hv
    have hlt : Op.i 0x8000000000000000 < Op.i 0 := by simp only [hi]; decide
    rw [if_pos hlt] at hv
    have hg := ColB.get_null (x := x) (i := i) (by rw [Opt.get_ne x i (by decide : QAtomicType.i64 ≠ .general), hnul]; rfl)
    rw [← hv, hg, h0]; decide

/-- **`big`** (`max lo lo` post `[(.and, 0), (.or, 0x7fff…)]`) has `lo`'s flag in every row and `i64` max in the
rows `lo` does not flag. -/
theorem Opt.bigOf {n : USize} (lo : Opt .i64 n) {big : Enc}
    (h : colMap .max n lo.enc lo.enc .i64 .i64 [] [(.and, 0), (.or, 0x7fffffffffffffff)] = .ok big) :
    Enc.WF .i64 n big ∧ ∀ i < n.toNat, (foRNuls n big)[i]? = (foRNuls n lo.enc)[i]? ∧
      ((foRNuls n lo.enc)[i]? = some 0 → (raw .i64 n big)[i]? = some 0x7fffffffffffffff) := by
  have hs : kscanStream .max [(n, lo.enc), (n, lo.enc)] [] [(.and, 0), (.or, 0x7fffffffffffffff)] = false := by
    simp [kscanStream]
  obtain ⟨hW, hrow⟩ := colMap_nul_row (b := .and) (fill := 0x8000000000000000) rfl (by simp [Op.eval]) lo.wf lo.wf hs h
  refine ⟨hW, fun i hi => ?_⟩
  obtain ⟨nl, h1, h2, h3⟩ := hrow i hi
  simp only [Op.eval, UInt64.and_self, Except.ok.injEq] at h1
  subst h1
  have hf := foRNuls_bit n lo.enc hi
  refine ⟨by rw [h2]; exact hf.symm, fun h0 => ?_⟩
  have hr0 : rdNul n lo.enc i = 0 := by simp [rdNul, h0]
  obtain ⟨w, hw, hv⟩ := h3 hr0
  simp only [Op.eval, chain, List.foldlM_cons, List.foldlM_nil, bind, Except.bind, pure, Except.pure,
    Except.ok.injEq, ite_self, UInt64.and_zero, UInt64.zero_or, UInt64.zero_and, UInt64.or_zero] at hv
  rw [hw, ← hv]

/-- `min` of a word with `i64` max is the word. -/
theorem min_big (r : UInt64) : (if Op.i r < Op.i 0x7fffffffffffffff then r else 0x7fffffffffffffff) = r := by
  split
  · rfl
  · rename_i hlt
    have h1 : ¬ (r.toInt64.toInt < (0x7fffffffffffffff : UInt64).toInt64.toInt) := fun hh =>
      hlt (Int64.lt_iff_toInt_lt.2 hh)
    have hM : ((0x7fffffffffffffff : UInt64).toInt64).toInt = 2 ^ 63 - 1 := by decide
    rw [hM] at h1
    have h2 := Verify.toInt_toInt64 r
    have h3 := UInt64.toNat_lt r
    apply UInt64.toNat_inj.1
    split at h2 <;> simp only [UInt64.toNat_ofNat] <;> omega

/-- A column `y` with the flags of the `i64` column `x` owns `x`'s rows. -/
theorem Opt.ownedOn_flags {n : USize} {P : Fin n.toNat → Prop} {x : Opt .i64 n} (hx : ColB.OwnedOn (o := true) x P)
    (y : Opt .i64 n) (hf : ∀ i : Fin n.toNat, (foRNuls n y.enc)[i.1]? = (foRNuls n x.enc)[i.1]?) :
    ColB.OwnedOn (o := true) y P := fun i => by
  constructor
  · intro hp h0
    have h1 := ColB.flag_of_owned (o := true) x hx i hp
    have h2 : y.isNul i = false := (Opt.isNul_eq_false y i).2 (by rw [hf i]; exact h1)
    rw [Opt.get_ne y i (by decide), h2] at h0; simp at h0
  · intro hp
    have h1 := ColB.flag_of_unowned x hx i hp
    have h2 : y.isNul i = true := by
      cases hh : y.isNul i
      · exact absurd (((hf i).symm.trans ((Opt.isNul_eq_false y i).1 hh)) : (foRNuls n x.enc)[i.1]? = some 0) h1
      · rfl
    rw [Opt.get_ne y i (by decide), h2]; simp [Opt.filler_ne (by decide : QAtomicType.i64 ≠ .general)]

/-- **`Opt.maskWith big x`** answers `x`'s words under `big`'s flags: row `i` is flagged as `big`, and where `big` is no
null (reading `i64` max, as `Opt.bigOf` gives) it reads `x`'s long. -/
theorem Opt.maskWith_get {n : USize} {big : Enc} (hbW : Enc.WF .i64 n big)
    (hbw : ∀ i < n.toNat, (foRNuls n big)[i]? = some 0 → (raw .i64 n big)[i]? = some 0x7fffffffffffffff)
    {x : Arr .i64 n} {y : Opt .i64 n} (h : Opt.maskWith big x = .ok y) (i : Fin n.toNat) :
    (foRNuls n y.enc)[i.1]? = (foRNuls n big)[i.1]? ∧
      ((foRNuls n big)[i.1]? = some 0 → ColB.get (o := true) y i = x.get i) := by
  unfold Opt.maskWith at h
  simp only [bind, Except.bind] at h
  split at h; · cases h
  rename_i e he
  split at h
  case h_2 => cases h
  rename_i hh _
  simp only [pure, Except.pure, Except.ok.injEq] at h
  subst h
  have hs : kscanStream .min [(n, big), (n, x.enc)] [] [] = false := by simp [kscanStream]
  obtain ⟨hW, hrow⟩ := colMap_nul_row (op := .min) (b := .or) (fill := 0x7fffffffffffffff) rfl (by simp [Op.eval])
    hbW x.wf hs he
  obtain ⟨nl, h1, h2, h3⟩ := hrow i.1 i.2
  have hx0 : rdNul n x.enc i.1 = 0 := by
    have := Arr.flat x i
    unfold rdNul; rw [show (foRNuls n x.enc)[i.1]? = some 0 from this]; rfl
  rw [hx0] at h1
  simp only [Op.eval, UInt64.or_zero, Except.ok.injEq] at h1
  subst h1
  have hf := foRNuls_bit n big i.2
  refine ⟨by show (foRNuls n e)[i.1]? = _; rw [h2]; exact hf.symm, fun h0 => ?_⟩
  have hr0 : rdNul n big i.1 = 0 := by simp [rdNul, h0]
  obtain ⟨w, hw, hv⟩ := h3 hr0
  have hrb := hbw i.1 i.2 h0
  have hfy : (foRNuls n e)[i.1]? = some 0 := by rw [h2, hr0]; rfl
  simp only [rdFill, hr0, hx0, bne_self_eq_false, Bool.false_eq_true, if_false, hrb, Option.getD_some, Op.eval, chain,
    List.foldlM_nil, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at hv
  rw [min_big] at hv
  have hg := ColB.get_i64 (o := true) (Opt.mk e hh) hfy
  rw [hg, Arr.get_i64]
  show ((raw .i64 n e)[i.1]?.getD 0).toInt64 = ((raw .i64 n x.enc)[i.1]?.getD 0).toInt64
  rw [hw, Option.getD_some, hv]

/-- **`Vals.cells` over the EXPAND of the widths of dense cells keeps `Vals.WF`** (`ValsB.pack`): the cells `[lo, up)`
(`cellSpan_spec`) have widths at most `m` (`cellSpan_width`), `n · m` below `2^63`. -/
theorem Vals.cells_dense_wf {B : Obj} {n m : USize} {lo up : Arr .i64 n} {f : Vals B m} {w G u : Enc} {T : USize}
    {pay : Vals B T} {Y : Vals (.arr B) n} (hb : ¬2 ^ 63 ≤ n.toNat * m.toNat + n.toNat + m.toNat)
    (hse : ∀ i : Fin n.toNat, 0 ≤ (lo.get i).toInt ∧ (lo.get i).toInt ≤ (up.get i).toInt ∧
      (up.get i).toInt ≤ (m.toNat : Int))
    (hw : colMap .sub n up.enc lo.enc = .ok w) (hex : expand n w = .ok (T, G, u))
    (hY : Vals.cells n w pay = .ok Y) (hp : Vals.WF pay) : Vals.WF Y := by
  have hm63 : m.toNat < 2 ^ 63 := by omega
  obtain ⟨SN, EN, hse', hb1, -⟩ := cellSpan_spec hse hm63 f
  refine Vals.cells_expand_wf hex hY m.toNat (fun i hi => ?_) (by omega) (by omega) hp
  obtain ⟨e1, b1⟩ := cellSpan_width hse' hb1 hw i hi
  rw [e1, toNat_toUInt64 (by omega)]; exact b1

/-- **`ValsB.pack` keeps every owned row**: where a payload is cut (`o = false`, every row owned), cell `i`
(`[SN, EN)`, `cellSpan_spec`) is laid out at `[Σ_{<i} w, Σ_{≤i} w)` (`Vals.cells`), whose row `Σ_{<i} w + d` is
gathered from payload row `SN + d` (`Vals.cells_expand_row` at `g = id`); a summand keeps its cells and packs its
payload. -/
theorem ValsB.pack_row {k : Nat} : {o : Bool} → {A : Obj} → {n : USize} → (x : ValsB o A n) → {y : ValsB o A n} →
    ValsB.pack k x = .ok y → {P : Fin n.toNat → Prop} → ValsB.WFOn x P → (o = false → ∀ i, P i) →
    ∀ i, P i → ValsB.row y i = ValsB.row x i
  | _, .atom _, _, x, _, h, _, _, _, i, _ => by
    simp only [ValsB.pack, pure, Except.pure, Except.ok.injEq] at h; cases h; rfl
  | _, .prod _ _, _, x, _, h, _, wx, hall, i, hi => by
    simp only [ValsB.pack, bind, Except.bind, pure, Except.pure] at h
    split at h; · cases h
    rename_i y1 h1
    split at h; · cases h
    rename_i y2 h2
    cases h
    simp only [ValsB.row, ValsB.pack_row x.1 h1 wx.1 hall i hi, ValsB.pack_row x.2 h2 wx.2 hall i hi]
  | _, .sum _ _, _, s, _, h, _, wx, _, i, hi => by
    rcases hv : s.view with ⟨hb, x⟩ | ⟨hb, tag, x, y⟩ <;> simp only [ValsB.pack, hv] at h
    · simp only [pure, Except.pure, Except.ok.injEq] at h; cases h; rfl
    simp only [bind, Except.bind, pure, Except.pure] at h
    split at h; · cases h
    rename_i x' h1
    split at h; · cases h
    rename_i y' h2
    cases h
    simp only [ValsB.WFOn, hv] at wx
    simp only [ValsB.row, ValsB.view_ofGen, hv]
    cases ht : tag.get i
    · simp only [Bool.false_eq_true, ↓reduceIte, ValsB.pack_row x h1 wx.2.1 (fun h => nomatch h) i ⟨hi, ht⟩]
    · simp only [↓reduceIte, ValsB.pack_row y h2 wx.2.2 (fun h => nomatch h) i ⟨hi, ht⟩]
  | true, .arr B, n, ⟨m, lo, up, f⟩, y, h, P, wx, _, i, hp => by
    simp only [ValsB.pack] at h
    split at h; · cases h
    rename_i hb
    simp only [bind] at h
    rw [Except.bind_eq_ok'] at h; obtain ⟨_, -, h⟩ := h
    rw [Except.bind_eq_ok'] at h; obtain ⟨z, hz, h⟩ := h
    rw [Except.bind_eq_ok'] at h; obtain ⟨s, hs, h⟩ := h
    rw [Except.bind_eq_ok'] at h; obtain ⟨e, he, h⟩ := h
    rw [Except.bind_eq_ok'] at h; obtain ⟨w, hw, h⟩ := h
    split at h; · cases h
    split at h
    case isFalse =>
      rw [Except.bind_eq_ok'] at h; obtain ⟨f', hf', h⟩ := h
      cases h
      have e := fun j => ValsB.pack_row f hf' wx.2.2.2 (fun _ _ => trivial) j trivial
      simp only [ValsB.row, e]
    rw [Except.bind_eq_ok'] at h; obtain ⟨⟨T, G, u⟩, hex, h⟩ := h; try dsimp only at h
    rw [Except.bind_eq_ok'] at h; obtain ⟨sg, hsg, h⟩ := h
    rw [Except.bind_eq_ok'] at h; obtain ⟨ix, hix, h⟩ := h
    rw [Except.bind_eq_ok'] at h; obtain ⟨g', hg', h⟩ := h
    rw [Except.bind_eq_ok'] at h; obtain ⟨p, hpk, h⟩ := h
    rw [Except.bind_eq_ok'] at h; obtain ⟨⟨T', lo', hi', f'⟩, hY, h⟩ := h; try dsimp only at h
    rw [Except.bind_eq_ok'] at h; obtain ⟨big, hbig, h⟩ := h
    rw [Except.bind_eq_ok'] at h; obtain ⟨y1, h1, h⟩ := h
    rw [Except.bind_eq_ok'] at h; obtain ⟨y2, h2, h⟩ := h
    cases h
    obtain ⟨sA, rfl, hsA⟩ := Opt.maxZero lo hz hs
    obtain ⟨eA, rfl, heA⟩ := Opt.maxZero up hz he
    have hge : ∀ i : Fin n.toNat, P i → (sA.get i).toInt = (ColB.get (o := true) lo i).toInt ∧
        (eA.get i).toInt = (ColB.get (o := true) up i).toInt := fun i hp => by
      have := wx.2.2.1 i hp
      rw [hsA i, heA i]; omega
    have hse : ∀ i : Fin n.toNat, 0 ≤ (sA.get i).toInt ∧ (sA.get i).toInt ≤ (eA.get i).toInt ∧
        (eA.get i).toInt ≤ (m.toNat : Int) := fun i => by
      by_cases hp : P i
      · have := wx.2.2.1 i hp; rw [hsA i, heA i]; omega
      · rw [hsA i, heA i, ColB.get_unowned wx.1 hp, ColB.get_unowned wx.2.1 hp]; omega
    obtain ⟨hbW, hbk⟩ := Opt.bigOf lo hbig
    have hbw : ∀ j < n.toNat, (foRNuls n big)[j]? = some 0 → (raw .i64 n big)[j]? = some 0x7fffffffffffffff :=
      fun j hj h0 => (hbk j hj).2 ((hbk j hj).1.symm.trans h0)
    have hb0 : (foRNuls n big)[i.1]? = some 0 := by
      rw [(hbk i.1 i.2).1]; exact ColB.flag_of_owned (o := true) lo wx.1 i hp
    have e3 : ColB.get (o := true) y1 i = ColB.get (o := false) lo' i := (Opt.maskWith_get hbW hbw h1 i).2 hb0
    have e4 : ColB.get (o := true) y2 i = ColB.get (o := false) hi' i := (Opt.maskWith_get hbW hbw h2 i).2 hb0
    have e1 : (ColB.get (o := false) sA i).toInt = (ColB.get (o := true) lo i).toInt := (hge i hp).1
    have e2 : (ColB.get (o := false) eA i).toInt = (ColB.get (o := true) up i).toInt := (hge i hp).2
    have hr := Vals.cells_expand_row (lo := sA) (up := eA) (f := f) hb hse hw hex hsg hix id (fun t => by
      obtain ⟨j, hj, hgj⟩ := ValsB.gather_row f hg' t
      exact ⟨j, hj, (ValsB.pack_row g' hpk (Vals.gather_wf hg' wx.2.2.2) (fun _ _ => trivial) t trivial).trans hgj⟩)
      hY i
    simp only [ValsB.row, e1, e2, e3, e4, List.map_id] at hr ⊢
    exact hr
  | false, .arr B, n, ⟨m, lo, up, f⟩, y, h, _, wx, hall, i, _ => by
    have hse := fun i => wx.2.2.1 i (hall rfl i)
    simp only [ValsB.pack] at h
    split at h; · cases h
    rename_i hb
    simp only [bind] at h
    rw [Except.bind_eq_ok'] at h; obtain ⟨_, -, h⟩ := h
    rw [Except.bind_eq_ok'] at h; obtain ⟨w, hw, h⟩ := h
    split at h; · cases h
    rename_i P hP
    split at h
    case isFalse =>
      rw [Except.bind_eq_ok'] at h; obtain ⟨f', hf', h⟩ := h
      cases h
      have e := fun j => ValsB.pack_row f hf' wx.2.2.2 (fun _ _ => trivial) j trivial
      simp only [ValsB.row, e]
    rw [Except.bind_eq_ok'] at h; obtain ⟨⟨T, G, u⟩, hex, h⟩ := h; try dsimp only at h
    rw [Except.bind_eq_ok'] at h; obtain ⟨sg, hsg, h⟩ := h
    rw [Except.bind_eq_ok'] at h; obtain ⟨ix, hix, h⟩ := h
    rw [Except.bind_eq_ok'] at h; obtain ⟨g', hg', h⟩ := h
    rw [Except.bind_eq_ok'] at h; obtain ⟨p, hp, h⟩ := h
    rw [Vals.cells_expand_row hb hse hw hex hsg hix id (fun t => by
      obtain ⟨j, hj, hgj⟩ := ValsB.gather_row f hg' t
      exact ⟨j, hj, (ValsB.pack_row g' hp (Vals.gather_wf hg' wx.2.2.2) (fun _ _ => trivial) t trivial).trans hgj⟩)
      h i, List.map_id]
  | _, .one, _, _, _, _, _, _, _, _, _ => rfl

/-- **`ValsB.pack` keeps `ValsB.WFOn`**: a cut payload (`o = false`, every row owned) is the input's gathered and
packed, laid out by `Vals.cells` over the EXPAND of the cells' own widths, each at most `m` (`cellSpan_width`,
`Vals.cells_expand_wf`); a summand keeps its tag and cells and packs its payload. -/
theorem ValsB.pack_wf {k : Nat} : {o : Bool} → {A : Obj} → {n : USize} → {x y : ValsB o A n} → ValsB.pack k x = .ok y →
    {P : Fin n.toNat → Prop} → ValsB.WFOn x P → (o = false → ∀ i, P i) → ValsB.WFOn y P
  | _, .atom _, _, _, _, h, _, hx, _ => by
    simp only [ValsB.pack, pure, Except.pure, Except.ok.injEq] at h; cases h; exact hx
  | _, .one, _, _, _, _, _, _, _ => trivial
  | _, .prod _ _, _, x, _, h, _, hx, hall => by
    simp only [ValsB.pack, bind, Except.bind, pure, Except.pure] at h
    split at h; · cases h
    rename_i y1 h1
    split at h; · cases h
    rename_i y2 h2
    cases h; exact ⟨ValsB.pack_wf h1 hx.1 hall, ValsB.pack_wf h2 hx.2 hall⟩
  | _, .sum _ _, _, s, _, h, _, hx, _ => by
    rcases hv : s.view with ⟨hb, x⟩ | ⟨hb, tag, x, y⟩ <;> simp only [ValsB.pack, hv] at h
    · simp only [pure, Except.pure, Except.ok.injEq] at h; cases h; exact hx
    simp only [bind, Except.bind, pure, Except.pure] at h
    split at h; · cases h
    rename_i x' h1
    split at h; · cases h
    rename_i y' h2
    cases h
    simp only [ValsB.WFOn, hv] at hx
    simp only [ValsB.WFOn, ValsB.view_ofGen]
    exact ⟨hx.1, ValsB.pack_wf h1 hx.2.1 (fun h => nomatch h), ValsB.pack_wf h2 hx.2.2 (fun h => nomatch h)⟩
  | true, .arr B, n, ⟨m, lo, up, f⟩, y, h, P, hx, _ => by
    simp only [ValsB.pack] at h
    split at h; · cases h
    rename_i hb
    simp only [bind] at h
    rw [Except.bind_eq_ok'] at h; obtain ⟨_, -, h⟩ := h
    rw [Except.bind_eq_ok'] at h; obtain ⟨z, hz, h⟩ := h
    rw [Except.bind_eq_ok'] at h; obtain ⟨s, hs, h⟩ := h
    rw [Except.bind_eq_ok'] at h; obtain ⟨e, he, h⟩ := h
    rw [Except.bind_eq_ok'] at h; obtain ⟨w, hw, h⟩ := h
    split at h; · cases h
    split at h
    case isFalse =>
      rw [Except.bind_eq_ok'] at h; obtain ⟨f', hf', h⟩ := h
      cases h; exact ⟨hx.1, hx.2.1, hx.2.2.1, ValsB.pack_wf hf' hx.2.2.2 fun _ _ => trivial⟩
    rw [Except.bind_eq_ok'] at h; obtain ⟨⟨T, G, u⟩, hex, h⟩ := h; try dsimp only at h
    rw [Except.bind_eq_ok'] at h; obtain ⟨sg, hsg, h⟩ := h
    rw [Except.bind_eq_ok'] at h; obtain ⟨ix, hix, h⟩ := h
    rw [Except.bind_eq_ok'] at h; obtain ⟨g', hg', h⟩ := h
    rw [Except.bind_eq_ok'] at h; obtain ⟨p, hpk, h⟩ := h
    rw [Except.bind_eq_ok'] at h; obtain ⟨⟨T', lo', hi', f'⟩, hY, h⟩ := h; try dsimp only at h
    rw [Except.bind_eq_ok'] at h; obtain ⟨big, hbig, h⟩ := h
    rw [Except.bind_eq_ok'] at h; obtain ⟨y1, h1, h⟩ := h
    rw [Except.bind_eq_ok'] at h; obtain ⟨y2, h2, h⟩ := h
    cases h
    obtain ⟨sA, rfl, hsA⟩ := Opt.maxZero lo hz hs
    obtain ⟨eA, rfl, heA⟩ := Opt.maxZero up hz he
    have hse : ∀ i : Fin n.toNat, 0 ≤ (sA.get i).toInt ∧ (sA.get i).toInt ≤ (eA.get i).toInt ∧
        (eA.get i).toInt ≤ (m.toNat : Int) := fun i => by
      by_cases hp : P i
      · have := hx.2.2.1 i hp; rw [hsA i, heA i]; omega
      · rw [hsA i, heA i, ColB.get_unowned hx.1 hp, ColB.get_unowned hx.2.1 hp]; omega
    obtain ⟨hbW, hbk⟩ := Opt.bigOf lo hbig
    have hbw : ∀ j < n.toNat, (foRNuls n big)[j]? = some 0 → (raw .i64 n big)[j]? = some 0x7fffffffffffffff :=
      fun j hj h0 => (hbk j hj).2 ((hbk j hj).1.symm.trans h0)
    have hY' := Vals.cells_dense_wf (f := f) hb hse hw hex hY
      (ValsB.pack_wf hpk (Vals.gather_wf hg' hx.2.2.2) fun _ _ => trivial)
    refine ⟨Opt.ownedOn_flags hx.1 y1 fun j => ((Opt.maskWith_get hbW hbw h1 j).1).trans (hbk j.1 j.2).1,
      Opt.ownedOn_flags hx.1 y2 fun j => ((Opt.maskWith_get hbW hbw h2 j).1).trans (hbk j.1 j.2).1, fun j hj => ?_,
      hY'.2.2.2⟩
    have hb0 : (foRNuls n big)[j.1]? = some 0 := by
      rw [(hbk j.1 j.2).1]; exact ColB.flag_of_owned (o := true) lo hx.1 j hj
    have e3 : ColB.get (o := true) y1 j = ColB.get (o := false) lo' j := (Opt.maskWith_get hbW hbw h1 j).2 hb0
    have e4 : ColB.get (o := true) y2 j = ColB.get (o := false) hi' j := (Opt.maskWith_get hbW hbw h2 j).2 hb0
    rw [e3, e4]; exact hY'.2.2.1 j trivial
  | false, .arr B, n, ⟨m, lo, up, f⟩, y, h, P, hx, hall => by
    have hse := fun i => hx.2.2.1 i (hall rfl i)
    simp only [ValsB.pack] at h
    split at h; · cases h
    rename_i hb
    simp only [bind] at h
    rw [Except.bind_eq_ok'] at h; obtain ⟨_, -, h⟩ := h
    rw [Except.bind_eq_ok'] at h; obtain ⟨w, hw, h⟩ := h
    split at h; · cases h
    split at h
    case isFalse =>
      rw [Except.bind_eq_ok'] at h; obtain ⟨f', hf', h⟩ := h
      cases h; exact ⟨hx.1, hx.2.1, hx.2.2.1, ValsB.pack_wf hf' hx.2.2.2 fun _ _ => trivial⟩
    rw [Except.bind_eq_ok'] at h; obtain ⟨⟨T, G, u⟩, hex, h⟩ := h; try dsimp only at h
    rw [Except.bind_eq_ok'] at h; obtain ⟨sg, hsg, h⟩ := h
    rw [Except.bind_eq_ok'] at h; obtain ⟨ix, hix, h⟩ := h
    rw [Except.bind_eq_ok'] at h; obtain ⟨g', hg', h⟩ := h
    rw [Except.bind_eq_ok'] at h; obtain ⟨p, hp, h⟩ := h
    have hm63 : m.toNat < 2 ^ 63 := by omega
    obtain ⟨SN, EN, hse', hb1, -⟩ := cellSpan_spec hse hm63 f
    refine (ValsB.WFOn_congr y fun i => ⟨fun _ => hall rfl i, fun _ => trivial⟩).1
      (Vals.cells_expand_wf hex h m.toNat (fun i hi => ?_) (by omega) (by omega)
        (ValsB.pack_wf hp (Vals.gather_wf hg' hx.2.2.2) fun _ _ => trivial))
    obtain ⟨e1, b1⟩ := cellSpan_width hse' hb1 hw i hi
    rw [e1, toNat_toUInt64 (by omega)]; exact b1

/-- **`Tab.pack` keeps `Tab.WF`** (`ValsB.pack_wf` on both sides). -/
theorem Tab.pack_wf {R t : Tab A B} (h : R.pack = .ok t) (hR : R.WF) : t.WF := by
  simp only [Tab.pack, bind, Except.bind, pure, Except.pure] at h
  split at h; · cases h
  rename_i x hx; split at h; · cases h
  rename_i y hy; cases h
  exact ⟨ValsB.pack_wf hx hR.1 fun _ _ => trivial, ValsB.pack_wf hy hR.2 fun _ _ => trivial⟩

namespace Tab

/-- **`R.pack` denotes `R`** (`ValsB.pack_row` on both sides): `foldRounds_holds`' `hpack`. -/
theorem pack_holds {k v : Obj} {R R' : Tab k v} (h : R.pack = .ok R') (wR : R.WF) (a : k.El) (b : v.El) :
    R'.Holds a b ↔ R.Holds a b := by
  unfold Tab.pack at h; simp only [bind, Except.bind_eq_ok'] at h
  obtain ⟨key, hk, val, hv, h⟩ := h
  cases h
  simp only [Tab.Holds, fun i => ValsB.pack_row _ hk wR.1 (fun _ _ => trivial) i trivial, fun i => ValsB.pack_row _ hv wR.2 (fun _ _ => trivial) i trivial]

end Tab

end Rel
