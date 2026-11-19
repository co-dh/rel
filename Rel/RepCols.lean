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
  unfold Arr.concat at h
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
  unfold Arr.clampShift at h
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
    simp only [Array.getElem?_replicate, i.2, if_true, Option.getD_some, Op.eval, Except.ok.injEq] at r1 r2 r3
    rw [Arr.get_i64, Arr.get_i64]
    show ((raw .i64 n o)[i.1]?.getD 0).toInt64.toInt = _
    rw [← r3, ← r2, ← r1]
    generalize (raw .i64 n x.enc)[i.1]?.getD 0 = w
    have hc : c.toInt64.toInt = c.toNat := by rw [Verify.toInt_toInt64, if_pos (by omega)]
    have h0 : (0 : UInt64).toInt64.toInt = 0 := rfl
    simp only [Int64.lt_iff_toInt_lt, hc, h0]
    split <;> split <;> rename_i h1 h2 <;> simp only [Verify.toInt_toInt64] at * <;>
      simp only [UInt64.toNat_add] at * <;> split at * <;> split at * <;> omega
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
  | .arr _, n₁, _, _, _, hn, hoff, ⟨m₁, lo₁, hi₁, f₁⟩, ⟨m₂, lo₂, hi₂, f₂⟩, z, h, c => by
    simp only [Vals.concat] at h
    split at h; swap; · cases h
    rename_i hm
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
      rw [List.filterMap_eq_nil_iff.2 fun j _ => by rw [if_neg]; rw [gh, h1]; omega, List.append_nil]
      congr 1; funext j
      rw [hrow, dif_pos j.2, gl, gh, l1, h1]
      by_cases hA : (lo₁.get ⟨c.1, hc⟩).toInt ≤ (j.1 : Int) ∧ (j.1 : Int) < (hi₁.get ⟨c.1, hc⟩).toInt
      · rw [if_pos hA, if_pos (by omega)]
      · rw [if_neg hA, if_neg (by omega)]
    · rename_i hc
      have hc' : c.1 - n₁.toNat < _ := by omega
      have l2 := Arr.clampShift_get (by rw [hU, hU]; omega) hL₂ ⟨_, hc'⟩
      have h2 := Arr.clampShift_get (by rw [hU, hU]; omega) hH₂ ⟨_, hc'⟩
      rw [dif_neg hc] at gl gh
      rw [hU, hU] at l2 h2
      rw [List.filterMap_eq_nil_iff.2 fun j _ => by rw [if_neg]; rw [gl, l2]; have := j.2; omega,
        List.nil_append]
      congr 1; funext j
      rw [hrow, dif_neg (by omega), gl, gh, l2, h2]
      have hj : (⟨m₁.toNat + j.1 - m₁.toNat, by omega⟩ : Fin m₂.toNat) = j := Fin.ext (by simp)
      rw [hj]
      by_cases hA : (lo₂.get ⟨_, hc'⟩).toInt ≤ (j.1 : Int) ∧ (j.1 : Int) < (hi₂.get ⟨_, hc'⟩).toInt
      · rw [if_pos hA, if_pos (by push_cast; omega)]
      · rw [if_neg hA, if_neg (by push_cast; omega)]
  | .sum _ _, _, _, _, _, _, _, _, _, _, h, _ => by simp [Vals.concat] at h

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
