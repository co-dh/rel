import Rel.Run.Cols
import Rel.RepCanon
import Rel.KernelSpec.Closure

/-! The laws of the column helpers of `Rel/Run/Cols.lean` (`colConst`, `colMap`, `colPrefix`, `shiftCol`, CONCAT), on
the words `Enc.raw` reads, from the five kernels' laws. -/

namespace Rel
open Rel.Ext Rel.Kernel Rel.Verify Ext.Enc

/-- `kscan` at `i64` writes its words as they are: the cut to `8 * 8` bits is the identity. -/
private theorem mod_i64 (v : UInt64) : UInt64.ofNat (v.toNat % 2 ^ (if QAtomicType.i64 = .u1 then 1 else 8 * 8)) = v := by
  simp only [if_neg (by decide : QAtomicType.i64 ≠ .u1)]; exact ofNat_toNat_mod64 v

/-- **`colPrefix op n a` is the running fold of `op` from `0`**: row `i` is `op` of row `i - 1` (`0` at row `0`) and
`a[i]`. -/
theorem colPrefix_raw {op : Op} {n : USize} {a e : Enc} (h : colPrefix op n a = .ok e) :
    (raw .i64 n a).size = n.toNat ∧ (raw .i64 n e).size = n.toNat ∧ ∀ i < n.toNat,
      op.eval (if i = 0 then 0 else (raw .i64 n e)[i - 1]?.getD 0) ((raw .i64 n a)[i]?.getD 0) =
        .ok ((raw .i64 n e)[i]?.getD 0) := by
  unfold colPrefix at h
  simp only [bind, Except.bind] at h
  split at h; · cases h
  rename_i z hz
  obtain ⟨-, hxs, c, cs, hc, out, hout, he, hrow⟩ := raw_kscan op false .i64 .i64 8 rfl n z [z, a] e h
  simp only [List.cons.injEq] at hc; obtain ⟨rfl, rfl⟩ := hc
  simp only [Bool.false_eq_true, ↓reduceIte, mod_i64, Array.map_id'] at he hrow
  have hz0 := colConst_raw hz
  have hzs := colConst_u1 hz
  refine ⟨hxs a (by simp), by rw [he, hout], fun i hi => ?_⟩
  have := hrow i (by rw [hout]; exact hi)
  simp only [List.map_cons, List.map_nil, List.foldlM_cons, List.foldlM_nil, hzs i hi, hz0,
    Array.getElem?_replicate, if_pos hi, Option.getD_some] at this
  rw [he]
  simp only [Array.getElem?_eq_getElem (show i < out.size by omega), Option.getD_some]
  rw [← this]
  by_cases h0 : i = 0
  · subst h0; simp only [Nat.lt_irrefl, false_and, ↓reduceIte]
    cases op.eval 0 ((raw .i64 n a)[0]?.getD 0) <;> rfl
  · simp only [if_neg h0, show 0 < i by omega, true_and, show UInt64.ofNat (UInt64.toNat 0 % 2) = 0 from rfl,
      ↓reduceIte]
    cases op.eval (out[i - 1]?.getD 0) ((raw .i64 n a)[i]?.getD 0) <;> rfl

/-- **`colMap op n a b` is `op` row by row**: both arguments hold `n` words, and row `i` of the answer is
`op.eval a[i] b[i]`. -/
theorem colMap_raw {op : Op} {n : USize} {a b e : Enc} (h : colMap op n a b = .ok e) :
    (raw .i64 n a).size = n.toNat ∧ (raw .i64 n b).size = n.toNat ∧ (raw .i64 n e).size = n.toNat ∧
      ∀ i < n.toNat, op.eval ((raw .i64 n a)[i]?.getD 0) ((raw .i64 n b)[i]?.getD 0) = .ok ((raw .i64 n e)[i]?.getD 0) := by
  unfold colMap at h
  simp only [bind, Except.bind] at h
  split at h; · cases h
  rename_i one hone
  obtain ⟨hg, hxs, c, cs, hc, out, hout, he, hrow⟩ := raw_kscan op false .i64 .i64 8 rfl n one [a, b] e h
  simp only [List.cons.injEq] at hc; obtain ⟨rfl, rfl⟩ := hc
  simp only [Bool.false_eq_true, ↓reduceIte, mod_i64, Array.map_id'] at he hrow
  -- `one` read as booleans: each word `1`, so every row starts a segment
  have hseg : ∀ i < n.toNat, (raw .u1 n one)[i]?.getD 0 ≠ 0 := fun i hi => by rw [colConst_u1 hone i hi]; decide
  refine ⟨hxs a (by simp), hxs b (by simp), by rw [he, hout], fun i hi => ?_⟩
  have := hrow i (by rw [hout]; exact hi)
  have hc : ¬(0 < i ∧ (raw .u1 n one)[i]?.getD 0 = 0) := fun h => hseg i hi h.2
  simp only [hc, ↓reduceIte, List.map_cons, List.map_nil, List.foldlM_cons, List.foldlM_nil] at this
  rw [he]
  simp only [Array.getElem?_eq_getElem (show i < out.size by omega), Option.getD_some]
  rw [← this]; cases op.eval ((raw .i64 n a)[i]?.getD 0) ((raw .i64 n b)[i]?.getD 0) <;> rfl

/-- **`shiftCol n s` is the words `k + s`**. -/
theorem shiftCol_raw {n : USize} {s : UInt64} {o : Enc} (h : shiftCol n s = .ok o) :
    ∀ k < n.toNat, (raw .i64 n o)[k]?.getD 0 = k.toUInt64 + s := by
  unfold shiftCol at h
  simp only [bind, Except.bind] at h
  split at h; · cases h
  rename_i c hc
  intro k hk
  have hr := (colMap_raw h).2.2.2 k hk
  have hp : (raw .i64 n (.pos : Enc))[k]?.getD 0 = k.toUInt64 := by
    simp only [raw, Array.getElem?_map, Array.getElem?_range, hk, if_true, Option.map_some, Option.getD_some]
  rw [hp, colConst_raw hc] at hr
  simp only [Op.eval, Except.ok.injEq, Array.getElem?_replicate, hk, if_true, Option.getD_some] at hr
  exact hr.symm

/-- The source column of a successful `kscatter` is one every kernel reads. -/
theorem kscatter_valid {op : Op} {m n : USize} {ix e o : Enc} {fill : UInt64} (h : kscatter op m ix e n fill = .ok o) :
    Kernel.Enc.Valid m e := by
  unfold kscatter at h
  simp only [bind, Except.bind] at h
  split at h; · cases h
  split at h; · cases h
  rename_i ws hws
  exact (foRWords_valid _ _ _).2 _ hws

/-- Two words that read alike: equal, or a boolean's word cut to its bit where both are below `2`. -/
theorem atom_of_cut {t : QAtomicType} (hg : t ≠ .general) {p q : UInt64} (hp : p = if t = .u1 then q % 2 else q)
    (hu : t = .u1 → p < 2 ∧ q < 2) : Column.atomOfBits t p hg = Column.atomOfBits t q hg := by
  congr 1
  by_cases tu : t = .u1
  · rw [hp, if_pos tu]
    have : q.toNat < 2 := UInt64.lt_iff_toNat_lt.1 (hu tu).2
    exact UInt64.toNat_inj.mp (by rw [UInt64.toNat_mod]; exact Nat.mod_eq_of_lt this)
  · rw [hp, if_neg tu]

/-- **Element `c` of `Arr.concat`** is element `c` of `x` below `n₁`, element `c - n₁` of `y` from there: `x`'s word
plus the `0` `y`'s scatter left there, or the converse (`raw_scatter`, `colMap_get`), read by `Arr.get_eq_of_raw`. -/
theorem Arr.concat_get {t : QAtomicType} {n₁ n₂ n : USize} {off : Enc} {x : Arr t n₁} {y : Arr t n₂} {z : Arr t n}
    (hn : n.toNat = n₁.toNat + n₂.toNat)
    (hoff : ∀ k < n₂.toNat, ((raw .i64 n₂ off)[k]?.getD 0).toNat = n₁.toNat + k) (h : Arr.concat n off x y = .ok z)
    (c : Fin n.toNat) :
    z.get c = if hc : c.1 < n₁.toNat then x.get ⟨c.1, hc⟩ else y.get ⟨c.1 - n₁.toNat, by omega⟩ := by
  unfold Arr.concat colArr at h
  simp only [bind, Except.bind] at h
  split at h; · cases h
  rename_i a ha
  split at h; · cases h
  rename_i b hb
  split at h
  · rename_i o ho
    cases h
    obtain ⟨-, hrow⟩ := colMap_get ho
    have hU : ∀ m : USize, m.toNat < 2 ^ 64 := fun m => Nat.lt_of_lt_of_le m.toNat_lt_size USize.size_le
    obtain ⟨-, -, -, -, -, hfixA, hlastA⟩ := raw_scatter n₁ .pos x.enc n 0 a ha
    obtain ⟨-, -, -, -, -, hfixB, hlastB⟩ := raw_scatter n₂ off y.enc n 0 b hb
    have hpos : ∀ k < n₁.toNat, ((raw .i64 n₁ (.pos : Enc))[k]?.getD 0).toNat = k := fun k hk => by
      simp [raw, hk, Nat.mod_eq_of_lt (Nat.lt_trans hk (hU n₁))]
    have wA : ∀ j < n.toNat, (raw .i64 n a)[j]?.getD 0 =
        if j < n₁.toNat then (raw .i64 n₁ x.enc)[j]?.getD 0 else 0 := fun j hj => by
      split
      · rename_i hl
        have e := hlastA j hl fun k' h1 h2 e => by
          have := congrArg UInt64.toNat e; rw [hpos k' h2, hpos j hl] at this; omega
        rw [hpos j hl] at e; simp [e]
      · rename_i hl
        have e := hfixA j hj fun k hk e => by rw [hpos k hk] at e; omega
        simp [e]
    have wB : ∀ j < n.toNat, (raw .i64 n b)[j]?.getD 0 =
        if j < n₁.toNat then 0 else (raw .i64 n₂ y.enc)[j - n₁.toNat]?.getD 0 := fun j hj => by
      split
      · rename_i hl
        have e := hfixB j hj fun k hk e => by rw [hoff k hk] at e; omega
        simp [e]
      · rename_i hl
        have e := hlastB (j - n₁.toNat) (by omega) fun k' h1 h2 e => by
          have := congrArg UInt64.toNat e; rw [hoff k' h2, hoff _ (by omega)] at this; omega
        rw [hoff _ (by omega), show n₁.toNat + (j - n₁.toNat) = j by omega] at e; simp [e]
    obtain ⟨v, hv, hz⟩ := hrow c.1 c.2
    rw [wA c.1 c.2, wB c.1 c.2] at hv
    have hcl := (colMap_closed ho).1
    split
    · rename_i hl
      simp only [hl, if_true, Op.eval, UInt64.add_zero, Except.ok.injEq] at hv
      subst hv
      exact Arr.get_eq_of_raw _ x hcl (kscatter_valid ha) c ⟨c.1, hl⟩ fun hg p q hp hq hu =>
        atom_of_cut hg (by
          change (raw .i64 n o)[c.1]? = some p at hp; change (raw .i64 n₁ x.enc)[c.1]? = some q at hq
          rw [hz, hq, Option.getD_some] at hp; exact (Option.some.inj hp).symm) hu
    · rename_i hl
      simp only [hl, if_false, Op.eval, UInt64.zero_add, Except.ok.injEq] at hv
      subst hv
      exact Arr.get_eq_of_raw _ y hcl (kscatter_valid hb) c ⟨c.1 - n₁.toNat, by omega⟩
        fun hg p q hp hq hu => atom_of_cut hg (by
          change (raw .i64 n o)[c.1]? = some p at hp
          change (raw .i64 n₂ y.enc)[c.1 - n₁.toNat]? = some q at hq
          rw [hz, hq, Option.getD_some] at hp; exact (Option.some.inj hp).symm) hu
  · cases h

/-- What `catPlan` answers: the summed count and `off` the destinations `n₁ + k`. -/
theorem catPlan_ok {n₁ n₂ n : USize} {off : Enc} (h : catPlan n₁ n₂ = .ok (n, off)) :
    n.toNat = n₁.toNat + n₂.toNat ∧ ∀ k < n₂.toNat, ((raw .i64 n₂ off)[k]?.getD 0).toNat = n₁.toNat + k := by
  unfold catPlan at h
  split at h
  · rename_i hlt
    simp only [bind, Except.bind, pure, Except.pure] at h
    split at h; · cases h
    rename_i o ho
    simp only [Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    have hU : USize.size ≤ 2 ^ 64 := USize.size_le
    refine ⟨USize.toNat_ofNat_of_lt' hlt, fun k hk => ?_⟩
    rw [shiftCol_raw ho k hk]
    simp [UInt64.toNat_add]
    omega
  · cases h

/-- **`Arr.clampShift c s x`** reads each long of `x` clamped into `[0, c]`, plus `s`, where `c + s` is below `2^63`. -/
theorem Arr.clampShift_get {n : USize} {c s : UInt64} {x y : Arr .i64 n} (hcs : c.toNat + s.toNat < 2 ^ 63)
    (h : x.clampShift c s = .ok y) (i : Fin n.toNat) :
    (y.get i).toInt = min (max (x.get i).toInt 0) c.toNat + s.toNat := by
  unfold Arr.clampShift colArr at h
  simp only [bind, Except.bind] at h
  split at h; · cases h
  rename_i z hz
  split at h; · cases h
  rename_i a ha
  split at h; · cases h
  rename_i cc hcc
  split at h; · cases h
  rename_i b hb
  split at h; · cases h
  rename_i k hk
  split at h
  · rename_i o ho
    cases h
    have r1 := (colMap_raw ha).2.2.2 i.1 i.2
    have r2 := (colMap_raw hb).2.2.2 i.1 i.2
    have r3 := (colMap_raw ho).2.2.2 i.1 i.2
    rw [colConst_raw hz] at r1; rw [colConst_raw hcc] at r2; rw [colConst_raw hk] at r3
    simp only [Array.getElem?_replicate, i.2, if_true, Option.getD_some] at r1 r2 r3
    rw [Arr.get_i64, Arr.get_i64]
    show ((raw .i64 n o)[i.1]?.getD 0).toInt64.toInt = _
    generalize (raw .i64 n x.enc)[i.1]?.getD 0 = w at r1 ⊢
    generalize (raw .i64 n a)[i.1]?.getD 0 = A at r1 r2
    generalize (raw .i64 n b)[i.1]?.getD 0 = B at r2 r3
    generalize (raw .i64 n o)[i.1]?.getD 0 = O at r3 ⊢
    have e1 : (if w.toInt64 < (0 : UInt64).toInt64 then 0 else w) = A := Except.ok.inj r1
    have e2 : (if c.toInt64 < A.toInt64 then c else A) = B := Except.ok.inj r2
    have e3 : B + s = O := Except.ok.inj r3
    subst e1 e2 e3
    have hc : c.toInt64.toInt = c.toNat := by rw [Verify.toInt_toInt64, if_pos (by omega)]
    have h0 : (0 : UInt64).toInt64.toInt = 0 := rfl
    have hw := UInt64.toNat_lt w
    have hs := UInt64.toNat_lt s
    have hW := Verify.toInt_toInt64 w
    simp only [Int64.lt_iff_toInt_lt, hc, h0]
    by_cases h1 : w.toInt64.toInt < 0
    · simp only [h1, if_true, h0]
      rw [if_neg (by omega), Verify.toInt_toInt64, UInt64.toNat_add, if_pos (by simp; omega)]
      simp; omega
    · simp only [h1, if_false]
      by_cases h2 : (c.toNat : Int) < w.toInt64.toInt
      · rw [if_pos h2, Verify.toInt_toInt64, UInt64.toNat_add, if_pos (by omega)]; omega
      · rw [if_neg h2, Verify.toInt_toInt64, UInt64.toNat_add]
        split at hW <;> rw [if_pos (by omega)] <;> omega
  · cases h

/-- The pairs of `List.finRange (a + b)` that `G` keeps: those of the first `a` positions, then of the last `b`. -/
theorem filterMap_finRange_add {α : Type} {M a b : Nat} (h : M = a + b) (G : Fin M → Option α) :
    (List.finRange M).filterMap G = (List.finRange a).filterMap (fun j => G ⟨j.1, by omega⟩) ++
      (List.finRange b).filterMap (fun j => G ⟨a + j.1, by omega⟩) := by
  subst h
  simp only [List.finRange, List.ofFn_add, List.filterMap_append]
  congr 1
  · rw [show (List.ofFn fun i : Fin a => Fin.castLE (Nat.le_add_right a b) i) =
      (List.ofFn fun i : Fin a => i).map (fun j => ⟨j.1, by omega⟩) from
      List.ext_getElem (by simp) (fun _ _ _ => by simp), List.filterMap_map]; rfl
  · rw [show (List.ofFn fun i : Fin b => Fin.natAdd a i) =
      (List.ofFn fun i : Fin b => i).map (fun j => ⟨a + j.1, by omega⟩) from
      List.ext_getElem (by simp) (fun _ _ _ => by simp [Fin.natAdd]), List.filterMap_map]; rfl

theorem sum_append_nat : ∀ l1 l2 : List Nat, (l1 ++ l2).sum = l1.sum + l2.sum
  | [], _ => by simp
  | x :: l, l2 => by simp [sum_append_nat l l2, Nat.add_assoc]

/-- A word below `2^63` read signed is its `Nat`. -/
theorem toInt64_toInt {x : UInt64} (h : x.toNat < 2 ^ 63) : x.toInt64.toInt = x.toNat := by
  rw [show x.toInt64.toInt = x.toBitVec.toInt from rfl, BitVec.toInt]; simp only [UInt64.toNat_toBitVec]
  omega

/-- The signed reading of a word: itself below `2^63`, itself less `2^64` from there. -/
theorem toInt64_toInt_cond (x : UInt64) :
    x.toInt64.toInt = if x.toNat < 2 ^ 63 then (x.toNat : Int) else (x.toNat : Int) - 2 ^ 64 := by
  split
  · exact toInt64_toInt (by assumption)
  · rename_i hx
    have := x.toNat_lt
    simp only [UInt64.toInt64, Int64.toInt, Int64.toBitVec, BitVec.toInt_eq_toNat_cond, UInt64.toNat] at *
    rw [if_neg (by omega)]; simp

/-- A word whose signed reading is not negative is below `2^63` and reads as itself. -/
theorem toInt64_nonneg {x : UInt64} (h : 0 ≤ x.toInt64.toInt) : x.toNat < 2 ^ 63 ∧ x.toInt64.toInt = x.toNat := by
  rw [toInt64_toInt_cond] at h ⊢
  have := x.toNat_lt
  split at h <;> rename_i hx
  · rw [if_pos hx]; exact ⟨hx, rfl⟩
  · omega

/-- A `Nat` below `2^64` is its word's `Nat`. -/
theorem toNat_toUInt64 {x : Nat} (h : x < 2 ^ 64) : x.toUInt64.toNat = x := by simp; omega

/-- **`colPrefix (.add)` is the running sum**: where word `G` of `w` is `wN G`, word `G` of the answer is the sum of
`wN` over `0 … G`. -/
theorem colPrefix_add_sum {K : USize} {w P : Enc} (h : colPrefix .add K w = .ok P) (wN : Nat → Nat)
    (hw : ∀ G < K.toNat, (raw .i64 K w)[G]?.getD 0 = (wN G).toUInt64) :
    ∀ G < K.toNat, (raw .i64 K P)[G]?.getD 0 = ((List.range (G + 1)).map wN).sum.toUInt64 := by
  obtain ⟨-, -, hr⟩ := colPrefix_raw h
  intro G hG
  induction G with
  | zero =>
    have := hr 0 hG
    simp only [if_pos rfl, Op.eval, hw 0 hG, Except.ok.injEq] at this
    rw [← this]; simp
  | succ G ih =>
    have := hr (G + 1) hG
    rw [if_neg (by omega), Nat.add_sub_cancel, ih (by omega), hw _ hG] at this
    simp only [Op.eval, Except.ok.injEq] at this
    rw [← this]; simp only [List.range_succ, List.map_append, sum_append_nat, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil, Nat.add_zero]; exact (UInt64.ofNat_add _ _).symm

/-- `kscan`'s answer is a `foR` column. -/
theorem kscan_foR {op : Op} {rev : Bool} {s t : QAtomicType} {n : USize} {seg : Enc} {es : List Enc} {o : Enc}
    (h : kscan op rev s t n seg es = .ok o) : ∃ md pk, o = .foR md pk := by
  unfold kscan at h
  simp only [bind, Except.bind] at h
  split at h; · cases h
  split at h; · cases h
  split at h; · cases h
  split at h; · cases h
  split at h; · cases h
  simp only [pure, Except.pure, Except.ok.injEq] at h
  exact ⟨_, _, h.symm⟩

/-- **`lastCount` reads the last word**: `x` where the last of the `K` words is `x < 2^63`, `0` at `K = 0`. -/
theorem lastCount_eq {K : USize} {P : Enc} (hw : Enc.WF .i64 K P) (hf : ∃ md pk, P = .foR md pk) {x : Nat}
    (hx : x < 2 ^ 63) (hl : 0 < K.toNat → (raw .i64 K P)[K.toNat - 1]?.getD 0 = x.toUInt64)
    (h0 : K.toNat = 0 → x = 0) : lastCount K P hw = x := by
  unfold lastCount
  split
  · rename_i hk
    obtain ⟨md, pk, rfl⟩ := hf
    rw [Arr.get_raw_foR (Arr.mk _ hw) rfl]; change ((raw .i64 K (Enc.foR md pk))[K.toNat - 1]?.getD 0).toInt64.toNatClampNeg = x
    rw [hl hk, ← Int64.toNat_toInt,
      toInt64_toInt (by rw [toNat_toUInt64 (by omega)]; omega), toNat_toUInt64 (by omega)]
    simp
  · exact (h0 (by omega)).symm

/-- **`summandPos n s tag idx`** is `idx` on the rows `tag` gives to the summand `s`, `0` on the others. -/
theorem summandPos_raw {n : USize} {s : Bool} {tag : Arr .u1 n} {idx : Enc} {p : Enc}
    (h : summandPos n s tag idx = .ok p) (hv : Kernel.Enc.Valid n tag.enc) (q : Fin n.toNat) :
    (raw .i64 n p)[q.1]?.getD 0 = if tag.get q = s then (raw .i64 n idx)[q.1]?.getD 0 else 0 := by
  obtain ⟨t, ht, et⟩ := Arr.get_u1 tag hv q
  have hi64 : ¬ (QAtomicType.i64 = .u1) := by decide
  unfold summandPos at h
  cases s
  · simp only [Bool.false_eq_true, ↓reduceIte, bind, Except.bind] at h
    split at h; · cases h
    rename_i nt hnt
    obtain ⟨v1, e1, h1⟩ := (colMap_get hnt).2 q q.2
    obtain ⟨v2, e2, h2⟩ := (colMap_get h).2 q q.2
    simp only [ht, Option.getD_some, Op.eval, Except.ok.injEq] at e1; subst e1
    simp only [h1, if_neg hi64, Option.getD_some, Op.eval, Except.ok.injEq] at e2; subst e2
    simp only [h2, if_neg hi64, Option.getD_some]
    rw [et]; cases tag.get q <;> simp
  · simp only [↓reduceIte] at h
    obtain ⟨v2, e2, h2⟩ := (colMap_get h).2 q q.2
    simp only [ht, Option.getD_some, Op.eval, Except.ok.injEq] at e2; subst e2
    simp only [h2, if_neg hi64, Option.getD_some]
    rw [et]; cases tag.get q <;> simp

/-- Both columns of a successful `Arr.concat` are ones every kernel reads (`kscatter_valid`). -/
theorem Arr.concat_valid {t : QAtomicType} {n₁ n₂ n : USize} {off : Enc} {x : Arr t n₁} {y : Arr t n₂} {z : Arr t n}
    (h : Arr.concat n off x y = .ok z) : Kernel.Enc.Valid n₁ x.enc ∧ Kernel.Enc.Valid n₂ y.enc := by
  unfold Arr.concat at h
  simp only [bind, Except.bind] at h
  split at h; · cases h
  rename_i a ha
  split at h; · cases h
  rename_i b hb
  exact ⟨kscatter_valid ha, kscatter_valid hb⟩

/-- **`Arr.pos n` read as positions**: row `c` clamped into `n` rows is `c`, `n` at most `2^63`. -/
theorem Arr.pos_clamp {n : USize} {P : Arr .i64 n} (h : Arr.pos n = .ok P) (hn : n.toNat ≤ 2 ^ 63) (c : Fin n.toNat)
    (h0 : 0 < n.toNat) : clampFin (P.get c) n.toNat h0 = c := by
  unfold Arr.pos at h
  split at h
  · rename_i o ho
    cases h
    rw [Arr.get_i64]
    show clampFin ((raw .i64 n o)[c.1]?.getD 0).toInt64 _ _ = _
    have hc : (c.1.toUInt64).toNat = c.1 := by
      have := c.2; have := n.toNat_lt_size; have := USize.size_le; simp; omega
    rw [shiftCol_raw ho c.1 c.2, UInt64.add_zero]
    exact (clampFin_word h0 (by rw [hc]; exact c.2) hn).trans (Fin.ext hc)
  · cases h

/-- **A `tagCount` of `0`**: no row is tagged into the summand `s`. -/
theorem tagCount_zero {n : USize} {s : Bool} {tag : Arr .u1 n} (h : tagCount n s tag = .ok 0)
    (hv : Kernel.Enc.Valid n tag.enc) (q : Fin n.toNat) : tag.get q ≠ s := by
  unfold tagCount at h
  split at h; · cases h
  simp only [bind, Except.bind] at h
  split at h; · cases h
  rename_i one hone
  split at h; · cases h
  rename_i p hp
  split at h
  · rename_i P hP
    simp only [Except.ok.injEq] at h
    have hf : ∃ md pk, P = .foR md pk := by
      unfold colPrefix at hP; simp only [bind, Except.bind] at hP; split at hP; · cases hP
      exact kscan_foR hP
    -- `wN G`: row `G` is tagged into `s`
    obtain ⟨wN, hwN⟩ : ∃ f : Nat → Nat, f = fun G => if hG : G < n.toNat then (if tag.get ⟨G, hG⟩ = s then 1 else 0) else 0 := ⟨_, rfl⟩
    have hw : ∀ G < n.toNat, (raw .i64 n p)[G]?.getD 0 = (wN G).toUInt64 := fun G hG => by
      rw [summandPos_raw hp hv ⟨G, hG⟩, colConst_raw hone]; rw [hwN]; simp only [dif_pos hG]
      split <;> simp [hG]
    have key : ∀ k, ((List.range k).map wN).sum ≤ k ∧ (q.1 < k → wN q.1 ≤ ((List.range k).map wN).sum) := by
      intro k; induction k with
      | zero => simp
      | succ k ih =>
        rw [List.range_succ, List.map_append, sum_append_nat]
        simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero]
        have h1 : wN k ≤ 1 := by rw [hwN]; dsimp only; split <;> (try split) <;> omega
        refine ⟨by omega, fun hk => ?_⟩
        by_cases e : q.1 = k
        · rw [e]; omega
        · have := ih.2 (by omega); omega
    have hc := lastCount_eq (colPrefix_closed hP).2 hf (x := ((List.range n.toNat).map wN).sum)
      (by have := (key n.toNat).1; omega)
      (fun hn => by rw [colPrefix_add_sum hP wN hw _ (by omega), Nat.sub_add_cancel hn])
      (fun hn => by rw [hn]; rfl)
    rw [h] at hc
    have h0 : wN q.1 = 0 := by have := (key n.toNat).2 q.2; omega
    rw [hwN] at h0; simp only [dif_pos q.2] at h0
    intro e; rw [if_pos e] at h0; exact absurd h0 (by decide)
  · cases h

/-- **Summand `s` of one side, `Vals.catSide`**, read at a row `q` the tags give to it: the summand is not empty, and
the row is its row at `q`'s position clamped. -/
theorem Vals.catSide_row {B : Obj} {m l l' : USize} {s : Bool} {tag : Arr .u1 m} {idx : Arr .i64 m} {x : Vals B l}
    {o : Vals B l'} {g : Vals B m} (h : Vals.catSide s tag idx x o = .ok g) (hv : Kernel.Enc.Valid m tag.enc)
    (h63 : l.toNat ≤ 2 ^ 63) (q : Fin m.toNat) (ht : tag.get q = s) :
    ∃ hl : 0 < l.toNat, Vals.row g q = Vals.row x (clampFin (idx.get q) l.toNat hl) := by
  unfold Vals.catSide at h
  split at h
  · simp only [bind, Except.bind] at h
    split at h; · cases h
    rename_i c hc
    split at h
    · rename_i hc0; subst hc0; exact absurd ht (tagCount_zero hc hv q)
    · cases h
  · rename_i hl0
    have hl : 0 < l.toNat := by omega
    refine ⟨hl, ?_⟩
    simp only [bind, Except.bind] at h
    split at h; · cases h
    rename_i k hk
    split at h; · cases h
    rename_i p hp
    rw [Vals.summand_row tag k s x h h63 hl (summandPos_raw hp hv) q, if_pos ht]
    -- the clamped positions clamp as the stored ones (`Arr.clampShift_get`)
    have hU : (l.toUInt64 - 1).toNat = l.toNat - 1 := by
      have := l.toNat_lt_size; have := USize.size_le
      rw [UInt64.toNat_sub_of_le _ _ (by rw [UInt64.le_iff_toNat_le]; simp; omega)]; simp
    have e := Arr.clampShift_get (by rw [hU]; simp; omega) hk q
    rw [hU] at e
    congr 1; apply Fin.ext; simp only [clampFin]; simp at e; omega

/-- **A summand of `Vals.catSummand`** read at row `c`, which the tags give to it, through positions `P` that clamp to
themselves: the summand's value of row `c` of the first side below `n₁`, of row `c - n₁` of the second from there,
given `cat` concatenates (`Vals.concat_row`). -/
theorem Vals.catSummand_row {B : Obj} {n₁ n₂ n l₁ l₂ : USize} {off : Enc} {s : Bool} {tag₁ : Arr .u1 n₁}
    {idx₁ : Arr .i64 n₁} {x₁ : Vals B l₁} {tag₂ : Arr .u1 n₂} {idx₂ : Arr .i64 n₂} {x₂ : Vals B l₂}
    {cat : {m₁ m₂ : USize} → (m : USize) → Enc → Vals B m₁ → Vals B m₂ → Except String (Vals B m)}
    {L : (m : USize) × Vals B m} (hn : n.toNat = n₁.toNat + n₂.toNat)
    (hoff : ∀ k < n₂.toNat, ((raw .i64 n₂ off)[k]?.getD 0).toNat = n₁.toNat + k)
    (hcat : ∀ {m₁ m₂ m : USize} {o : Enc} {z : Vals B m} (x : Vals B m₁) (y : Vals B m₂),
      (hm : m.toNat = m₁.toNat + m₂.toNat) → (∀ k < m₂.toNat, ((raw .i64 m₂ o)[k]?.getD 0).toNat = m₁.toNat + k) →
      cat m o x y = .ok z → ∀ c : Fin m.toNat, Vals.row z c =
        if hc : c.1 < m₁.toNat then Vals.row x ⟨c.1, hc⟩ else Vals.row y ⟨c.1 - m₁.toNat, by omega⟩)
    (hv₁ : Kernel.Enc.Valid n₁ tag₁.enc) (hv₂ : Kernel.Enc.Valid n₂ tag₂.enc)
    (h : Vals.catSummand n off s tag₁ idx₁ x₁ tag₂ idx₂ x₂ cat = .ok L)
    {P : Arr .i64 n} (hP : ∀ c h0, clampFin (P.get c) n.toNat h0 = c) (c : Fin n.toNat)
    (ht : (if hc : c.1 < n₁.toNat then tag₁.get ⟨c.1, hc⟩ else tag₂.get ⟨c.1 - n₁.toNat, by omega⟩) = s) :
    (if h0 : 0 < L.1.toNat then Vals.row L.2 (clampFin (P.get c) L.1.toNat h0) else B.dflt) =
      if hc : c.1 < n₁.toNat then
        (if h0 : 0 < l₁.toNat then Vals.row x₁ (clampFin (idx₁.get ⟨c.1, hc⟩) l₁.toNat h0) else B.dflt)
      else if h0 : 0 < l₂.toNat then
        Vals.row x₂ (clampFin (idx₂.get ⟨c.1 - n₁.toNat, by omega⟩) l₂.toNat h0) else B.dflt := by
  unfold Vals.catSummand at h
  split at h
  · simp only [bind, Except.bind, pure, Except.pure] at h
    split at h; · cases h
    rename_i p hp
    split at h; · cases h
    cases h
    obtain ⟨hpn, -⟩ := catPlan_ok (show catPlan l₁ l₂ = .ok (p.1, p.2) from hp)
    rw [dif_neg (by dsimp only; omega)]
    split <;> rw [dif_neg (by omega)]
  · split at h; · cases h
    simp only [bind, Except.bind, pure, Except.pure] at h
    split at h; · cases h
    rename_i g₁ hg₁
    split at h; · cases h
    rename_i g₂ hg₂
    split at h; · cases h
    rename_i G hG
    cases h
    have hc0 : 0 < n.toNat := by have := c.2; omega
    show (if h0 : 0 < n.toNat then Vals.row G (clampFin (P.get c) n.toNat h0) else B.dflt) = _
    rw [dif_pos hc0, hP c hc0, hcat g₁ g₂ hn hoff hG c]
    split
    · rename_i hc
      rw [dif_pos hc] at ht
      obtain ⟨hl, e⟩ := Vals.catSide_row hg₁ hv₁ (by omega) ⟨c.1, hc⟩ ht
      rw [dif_pos hl, e]
    · rename_i hc
      rw [dif_neg hc] at ht
      obtain ⟨hl, e⟩ := Vals.catSide_row hg₂ hv₂ (by omega) _ ht
      rw [dif_pos hl, e]

/-- **Row `c` of `Vals.concat`** is row `c` of `x` below `n₁`, row `c - n₁` of `y` from there. -/
theorem Vals.concat_row : {A : Obj} → {n₁ n₂ n : USize} → {off : Enc} → (hn : n.toNat = n₁.toNat + n₂.toNat) →
    (hoff : ∀ k < n₂.toNat, ((raw .i64 n₂ off)[k]?.getD 0).toNat = n₁.toNat + k) →
    (x : Vals A n₁) → (y : Vals A n₂) → {z : Vals A n} → Vals.concat n off x y = .ok z →
      ∀ c : Fin n.toNat, Vals.row z c =
        if hc : c.1 < n₁.toNat then Vals.row x ⟨c.1, hc⟩ else Vals.row y ⟨c.1 - n₁.toNat, by omega⟩
  | .atom _, _, _, _, _, hn, hoff, x, y, z, h, c => Arr.concat_get hn hoff h c
  | .prod _ _, _, _, _, _, hn, hoff, x, y, z, h, c => by
    simp only [Vals.concat, bind, Except.bind, pure, Except.pure] at h
    split at h; · cases h
    rename_i z1 h1
    split at h; · cases h
    rename_i z2 h2
    cases h
    show (Vals.row z1 c, Vals.row z2 c) = _
    rw [Vals.concat_row hn hoff x.1 y.1 h1 c, Vals.concat_row hn hoff x.2 y.2 h2 c]
    split <;> rfl
  | .arr _, n₁, n₂, _, _, hn, hoff, ⟨m₁, lo₁, hi₁, f₁⟩, ⟨m₂, lo₂, hi₂, f₂⟩, z, h, c => by
    simp only [Vals.concat] at h
    split at h
    case isFalse => cases h
    simp only [bind, Except.bind, pure, Except.pure] at h
    split at h; · cases h
    rename_i p hp
    split at h; · cases h
    rename_i L₁ hL₁
    split at h; · cases h
    rename_i L₂ hL₂
    split at h; · cases h
    rename_i lo hlo
    split at h; · cases h
    rename_i H₁ hH₁
    split at h; · cases h
    rename_i H₂ hH₂
    split at h; · cases h
    rename_i hi hhi
    split at h; · cases h
    rename_i F hF
    cases h
    obtain ⟨hpn, hpo⟩ := catPlan_ok (show catPlan m₁ m₂ = .ok (p.1, p.2) from hp)
    have hrow := Vals.concat_row hpn hpo f₁ f₂ hF
    have hU : ∀ m : USize, m.toUInt64.toNat = m.toNat := fun m => by
      have := m.toNat_lt_size; have := USize.size_le; simp
    have e0 : (0 : UInt64).toNat = 0 := rfl
    have gl := Arr.concat_get hn hoff hlo c
    have gh := Arr.concat_get hn hoff hhi c
    simp only [Vals.row]
    rw [filterMap_finRange_add hpn]
    split
    · rename_i hc
      have l1 := Arr.clampShift_get (by rw [hU, e0]; omega) hL₁ ⟨c.1, hc⟩
      have h1 := Arr.clampShift_get (by rw [hU, e0]; omega) hH₁ ⟨c.1, hc⟩
      rw [dif_pos hc] at gl gh
      rw [hU, e0] at l1 h1
      rw [List.filterMap_eq_nil_iff (l := List.finRange m₂.toNat) |>.2 fun j _ => by
          rw [if_neg]; rw [gh, h1]; dsimp only; omega, List.append_nil]
      congr 1; funext j
      rw [hrow, dif_pos j.2, gl, gh, l1, h1]
      by_cases hA : (lo₁.get ⟨c.1, hc⟩).toInt ≤ (j.1 : Int) ∧ (j.1 : Int) < (hi₁.get ⟨c.1, hc⟩).toInt
      · rw [if_pos hA, if_pos (by dsimp only; omega)]
      · rw [if_neg hA, if_neg (by dsimp only; omega)]
    · rename_i hc
      have hc' : c.1 - n₁.toNat < n₂.toNat := by omega
      have l2 := Arr.clampShift_get (by rw [hU, hU]; omega) hL₂ ⟨_, hc'⟩
      have h2 := Arr.clampShift_get (by rw [hU, hU]; omega) hH₂ ⟨_, hc'⟩
      rw [dif_neg hc] at gl gh
      rw [hU, hU] at l2 h2
      rw [List.filterMap_eq_nil_iff (l := List.finRange m₁.toNat) |>.2 fun j _ => by
          rw [if_neg]; rw [gl, l2]; have := j.2; dsimp only; omega,
        List.nil_append]
      congr 1; funext j
      rw [hrow, dif_neg (by dsimp only; omega), gl, gh, l2, h2]
      have hj : (⟨m₁.toNat + j.1 - m₁.toNat, by omega⟩ : Fin m₂.toNat) = j := Fin.ext (by simp)
      rw [hj]
      by_cases hA : (lo₂.get ⟨_, hc'⟩).toInt ≤ (j.1 : Int) ∧ (j.1 : Int) < (hi₂.get ⟨_, hc'⟩).toInt
      · rw [if_pos hA, if_pos (by dsimp only; omega)]
      · rw [if_neg hA, if_neg (by dsimp only; omega)]
  | .sum _ _, n₁, _, _, _, hn, hoff, ⟨_, _, tag₁, idx₁, x₁, y₁⟩, ⟨_, _, tag₂, idx₂, x₂, y₂⟩, z, h, c => by
    simp only [Vals.concat] at h
    split at h
    case isFalse => cases h
    rename_i hn63
    simp only [bind, Except.bind, pure, Except.pure] at h
    split at h; · cases h
    rename_i L hL
    split at h; · cases h
    rename_i R hR
    split at h; · cases h
    rename_i tag htag
    split at h; · cases h
    rename_i P hP
    cases h
    obtain ⟨hv₁, hv₂⟩ := Arr.concat_valid htag
    have hpos := fun c h0 => Arr.pos_clamp hP hn63 c h0
    have gt := Arr.concat_get hn hoff htag c
    cases hb : tag.get c
    · have e := Vals.catSummand_row hn hoff (fun x y hm ho hz => Vals.concat_row hm ho x y hz) hv₁ hv₂ hL hpos c
        (by rw [← gt, hb])
      simp only [Vals.row, hb, Bool.false_eq_true, ↓reduceIte]
      rw [e]
      split
      · rename_i hc; rw [dif_pos hc] at gt; rw [← gt, hb]; rfl
      · rename_i hc; rw [dif_neg hc] at gt; rw [← gt, hb]; rfl
    · have e := Vals.catSummand_row hn hoff (fun x y hm ho hz => Vals.concat_row hm ho x y hz) hv₁ hv₂ hR hpos c
        (by rw [← gt, hb])
      simp only [Vals.row, hb, ↓reduceIte]
      rw [e]
      split
      · rename_i hc; rw [dif_pos hc] at gt; rw [← gt, hb]; rfl
      · rename_i hc; rw [dif_neg hc] at gt; rw [← gt, hb]; rfl

/-! ## Checks: CONCAT keeps every stored word -/

section Checks

/-- The column of the words `ws` at `t`, `wordsFoR` (a kernel's answer form), where `Enc.WF` admits it. -/
private def wordsArr (t : QAtomicType) (ws : Array UInt64) (n : USize) : Option (Arr t n) :=
  if hn : n.toNat = ws.size then
    if ht : t.width.isSome then
      if hu : t = .u1 → ∀ i (h : i < ws.size), ws[i] < 2 then some (Arr.mk _ ((wordsFoR_closed ws hn).2.2 ht hu))
      else none
    else none
  else none

/-- `Arr.concat` of the words `xs` and `ys` at `t`, read back at `t`, against the two read at `t` and appended: the
stored words, compared bit for bit. -/
private def concatKeeps (t : QAtomicType) (xs ys : Array UInt64) : Bool :=
  match wordsArr t xs xs.size.toUSize, wordsArr t ys ys.size.toUSize with
  | some x, some y => match catPlan xs.size.toUSize ys.size.toUSize with
    | .ok (n, off) => match Arr.concat n off x y with
      | .ok z => raw t n z.enc == raw t xs.size.toUSize x.enc ++ raw t ys.size.toUSize y.enc
      | .error _ => false
    | .error _ => false
  | _, _ => false

-- f64 `-0.0`, `+0.0`, a NaN with payload `1`, q's null; f32 `-0.0` and a NaN with payload; i8 `-128` (as its
-- sign-extended word and as its byte), and the max of every width, at every type of fixed width but `u1`
private def W : Array UInt64 := #[0x8000000000000000, 0, 0x7ff0000000000001, 0xfff8000000000000, 0x80000000,
  0x7f800001, 0xffffffffffffff80, 0x80, 0x7f, 0xff, 0x7fff, 0xffff, 0x7fffffff, 0xffffffff, 0x7fffffffffffffff,
  0xffffffffffffffff, 1]
#guard [QAtomicType.u8, .i16, .i32, .i64, .f32, .f64, .char, .i8, .date, .datetime].all fun t =>
  concatKeeps t W W.reverse && concatKeeps t W #[] && concatKeeps t #[] W
#guard concatKeeps .u1 #[0, 1, 1, 0] #[1, 0, 1]

end Checks

end Rel
