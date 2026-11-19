import Rel.Run.SetOps
import Rel.RepCanon
import Rel.Run.CRelFoldDef

/-! The laws of `Tab.union`, `Tab.inter`, `Tab.diff` and `Tab.le` (`Rel/Run/SetOps.lean`), from the five kernels' laws
and `Tab.canon`'s (`Rel/RepCanon.lean`). -/

namespace Rel
open Rel.Ext Rel.Kernel Rel.Verify

/-! ## CONCAT and `∪` -/

/-- **`fillCol n w` is `n` words `w`**, a column every kernel reads. -/
theorem fillCol_raw {n : USize} {w : UInt64} {o : Enc} (h : fillCol n w = .ok o) :
    Enc.raw .i64 n o = Array.replicate n.toNat w ∧ Kernel.Enc.Valid n o := by
  obtain ⟨-, -, -, hws, -, hfix, -⟩ := raw_scatter 0 .pos .pos n w o h
  refine ⟨Array.ext (by simp [hws]) fun j h1 h2 => ?_, (kscatter_closed h).1⟩
  have := hfix j (by omega) (fun k hk => absurd hk (by simp))
  rw [Array.getElem?_eq_getElem h1] at this
  simpa using this

/-- A `foR` column read as booleans is its 64-bit words cut to their low bit. -/
theorem raw_u1_foR {n : USize} {md pk : ByteArray} :
    Enc.raw .u1 n (.foR md pk : Enc) = (Enc.raw .i64 n (.foR md pk : Enc)).map (· % 2) := by
  apply Array.ext (by simp [Ext.Enc.raw, QAtomicType.width]) fun i h1 h2 => ?_
  simp [Ext.Enc.raw, QAtomicType.width]
  exact UInt64.toNat_inj.mp (by simp [UInt64.toNat_ofNat, UInt64.toNat_mod]; omega)

/-- **A `kscan` map**: where `one` starts a segment at every row, word `i` of the answer is `op` of `a`'s and `b`'s
words `i` (a boolean answer's cut to its bit), read back by `raw .i64`. -/
theorem kscan_map {op : Op} {t : QAtomicType} {n : USize} {one a b o : Enc}
    (hone : ∀ i < n.toNat, (Enc.raw .u1 n one)[i]?.getD 0 ≠ 0) (h : kscan op false .i64 t n one [a, b] = .ok o) :
    (Enc.raw .i64 n o).size = n.toNat ∧ ∀ i < n.toNat, ∃ v,
      op.eval ((Enc.raw .i64 n a)[i]?.getD 0) ((Enc.raw .i64 n b)[i]?.getD 0) = .ok v ∧
      (Enc.raw .i64 n o)[i]? = some (if t = .u1 then v % 2 else v) := by
  unfold kscan at h
  cases hg : rawAll .u1 n one with
  | error m => simp [hg, bind, Except.bind] at h
  | ok g =>
    obtain ⟨rfl, hgs⟩ := rawAll_ok hg
    cases hc : [a, b].mapM (rawAll .i64 n) with
    | error m => simp [hg, hc, bind, Except.bind] at h
    | ok cs =>
      obtain ⟨rfl, hsz⟩ := mapM_rawAll hc
      cases hf : (List.range n.toNat).foldlM (kscanRow op (Enc.raw .u1 n one) (Enc.raw .i64 n a) [Enc.raw .i64 n b])
          #[] with
      | error m => simp [hg, hc, hf, bind, Except.bind] at h
      | ok out =>
        obtain ⟨hos, hrow⟩ := foldlM_kscanRow _ _ _ _ _ _ hf
        cases ht : t.width with
        | none => simp [hg, hc, hf, ht, bind, Except.bind] at h
        | some w =>
          simp only [hg, hc, hf, ht, bind, Except.bind, List.map_cons, List.map_nil, pure, Except.pure,
            Bool.false_eq_true, if_false, Except.ok.injEq] at h
          change wordsFoR _ = o at h
          cases h
          have hW : (out.map fun v => if t = .u1 then v % 2 else v).size = n.toNat := by simp [hos]
          rw [(wordsFoR_closed _ hW.symm).2.1]
          refine ⟨hW, fun i hi => ?_⟩
          have hr := hrow i (by omega)
          rw [if_neg (fun hh => hone i hi hh.2)] at hr
          simp only [List.foldlM_cons, List.foldlM_nil, bind, Except.bind] at hr
          cases he : op.eval ((Enc.raw .i64 n a)[i]?.getD 0) ((Enc.raw .i64 n b)[i]?.getD 0) with
          | error s => rw [he] at hr; cases hr
          | ok v =>
            rw [he] at hr; simp only [pure, Except.pure, Except.ok.injEq] at hr
            refine ⟨v, rfl, ?_⟩
            rw [Array.getElem?_map, Array.getElem?_eq_getElem (by omega), ← hr]; rfl

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
plus the `0` `y`'s scatter left there, or the converse (`raw_scatter`, `kscan_map`), read by `Arr.get_eq_of_raw`. -/
theorem Arr.concat_get {t : QAtomicType} {n₁ n₂ n : USize} {off one : Enc} {x : Arr t n₁} {y : Arr t n₂} {z : Arr t n}
    (hn : n.toNat = n₁.toNat + n₂.toNat)
    (hoff : ∀ k < n₂.toNat, ((Enc.raw .i64 n₂ off)[k]?.getD 0).toNat = n₁.toNat + k)
    (hone : ∀ i < n.toNat, (Enc.raw .u1 n one)[i]?.getD 0 ≠ 0) (h : Arr.concat n off one x y = .ok z)
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
    obtain ⟨-, hrow⟩ := kscan_map hone ho
    have hU : ∀ m : USize, m.toNat < 2 ^ 64 := fun m => Nat.lt_of_lt_of_le m.toNat_lt_size USize.size_le
    obtain ⟨-, -, -, -, -, hfixA, hlastA⟩ := raw_scatter n₁ .pos x.enc n 0 a ha
    obtain ⟨-, -, -, -, -, hfixB, hlastB⟩ := raw_scatter n₂ off y.enc n 0 b hb
    have hpos : ∀ k < n₁.toNat, ((Enc.raw .i64 n₁ (.pos : Enc))[k]?.getD 0).toNat = k := fun k hk => by
      simp [Ext.Enc.raw, hk, Nat.mod_eq_of_lt (Nat.lt_trans hk (hU n₁))]
    have wA : ∀ j < n.toNat, (Enc.raw .i64 n a)[j]?.getD 0 =
        if j < n₁.toNat then (Enc.raw .i64 n₁ x.enc)[j]?.getD 0 else 0 := fun j hj => by
      split
      · rename_i hl
        have e := hlastA j hl fun k' h1 h2 e => by
          have := congrArg UInt64.toNat e; rw [hpos k' h2, hpos j hl] at this; omega
        rw [hpos j hl] at e; simp [e]
      · rename_i hl
        have e := hfixA j hj fun k hk e => by rw [hpos k hk] at e; omega
        simp [e]
    have wB : ∀ j < n.toNat, (Enc.raw .i64 n b)[j]?.getD 0 =
        if j < n₁.toNat then 0 else (Enc.raw .i64 n₂ y.enc)[j - n₁.toNat]?.getD 0 := fun j hj => by
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
    split
    · rename_i hl
      simp only [hl, if_true, Op.eval, UInt64.add_zero, Except.ok.injEq] at hv
      subst hv
      exact Arr.get_eq_of_raw _ x (kscan_closed ho).1 (kscatter_valid ha) c ⟨c.1, hl⟩ fun hg p q hp hq hu =>
        atom_of_cut hg (by
          change (Enc.raw .i64 n o)[c.1]? = some p at hp; change (Enc.raw .i64 n₁ x.enc)[c.1]? = some q at hq
          rw [hz, hq, Option.getD_some] at hp; exact (Option.some.inj hp).symm) hu
    · rename_i hl
      simp only [hl, if_false, Op.eval, UInt64.zero_add, Except.ok.injEq] at hv
      subst hv
      exact Arr.get_eq_of_raw _ y (kscan_closed ho).1 (kscatter_valid hb) c ⟨c.1 - n₁.toNat, by omega⟩
        fun hg p q hp hq hu => atom_of_cut hg (by
          change (Enc.raw .i64 n o)[c.1]? = some p at hp
          change (Enc.raw .i64 n₂ y.enc)[c.1 - n₁.toNat]? = some q at hq
          rw [hz, hq, Option.getD_some] at hp; exact (Option.some.inj hp).symm) hu
  · cases h

/-- `fillCol n 1` marks every row: its words read as booleans are `1`. -/
theorem fillCol_ones {n : USize} {o : Enc} (h : fillCol n 1 = .ok o) :
    ∀ i < n.toNat, (Enc.raw .u1 n o)[i]?.getD 0 ≠ 0 := by
  obtain ⟨ho, -⟩ := raw_scatter 0 .pos .pos n 1 o h
  have hr := (fillCol_raw h).1
  intro i hi
  rw [ho, raw_u1_foR, ← ho, hr]
  simp [hi]

/-- **`shiftCol n s` is the words `k + s`**. -/
theorem shiftCol_raw {n : USize} {s : UInt64} {o : Enc} (h : shiftCol n s = .ok o) :
    ∀ k < n.toNat, (Enc.raw .i64 n o)[k]?.getD 0 = k.toUInt64 + s := by
  unfold shiftCol at h
  simp only [bind, Except.bind] at h
  split at h; · cases h
  rename_i one h1
  split at h; · cases h
  rename_i c hc
  obtain ⟨-, hrow⟩ := kscan_map (fillCol_ones h1) h
  intro k hk
  obtain ⟨v, hv, hz⟩ := hrow k hk
  have hcs := (fillCol_raw hc).1
  have hp : (Enc.raw .i64 n (.pos : Enc))[k]?.getD 0 = k.toUInt64 := by
    simp only [Ext.Enc.raw, Array.getElem?_map, Array.getElem?_range, hk, if_true, Option.map_some, Option.getD_some]
  rw [hcs, hp] at hv
  simp only [Op.eval, Except.ok.injEq, Array.getElem?_replicate, hk, if_true, Option.getD_some] at hv
  simp only [hz, show QAtomicType.i64 ≠ .u1 by decide, if_false, Option.getD_some, ← hv]

/-- What `catPlan` answers: the summed count, `off` the destinations `n₁ + k`, `one` every row marked. -/
theorem catPlan_ok {n₁ n₂ n : USize} {off one : Enc} (h : catPlan n₁ n₂ = .ok (n, off, one)) :
    n.toNat = n₁.toNat + n₂.toNat ∧ (∀ k < n₂.toNat, ((Enc.raw .i64 n₂ off)[k]?.getD 0).toNat = n₁.toNat + k) ∧
      ∀ i < n.toNat, (Enc.raw .u1 n one)[i]?.getD 0 ≠ 0 := by
  unfold catPlan at h
  split at h
  · rename_i hlt
    simp only [bind, Except.bind, pure, Except.pure] at h
    split at h; · cases h
    rename_i o ho
    split at h; · cases h
    rename_i o1 h1
    simp only [Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    have hU : USize.size ≤ 2 ^ 64 := USize.size_le
    refine ⟨USize.toNat_ofNat_of_lt' hlt, fun k hk => ?_, fillCol_ones h1⟩
    rw [shiftCol_raw ho k hk]
    simp [UInt64.toNat_add]
    omega
  · cases h

/-- **Row `c` of `Vals.concat`** is row `c` of `x` below `n₁`, row `c - n₁` of `y` from there. -/
theorem Vals.concat_row {n₁ n₂ n : USize} {off one : Enc} (hn : n.toNat = n₁.toNat + n₂.toNat)
    (hoff : ∀ k < n₂.toNat, ((Enc.raw .i64 n₂ off)[k]?.getD 0).toNat = n₁.toNat + k)
    (hone : ∀ i < n.toNat, (Enc.raw .u1 n one)[i]?.getD 0 ≠ 0) :
    {A : Obj} → (x : Vals A n₁) → (y : Vals A n₂) → {z : Vals A n} → Vals.concat n off one x y = .ok z →
      ∀ c : Fin n.toNat, Vals.row z c =
        if hc : c.1 < n₁.toNat then Vals.row x ⟨c.1, hc⟩ else Vals.row y ⟨c.1 - n₁.toNat, by omega⟩
  | .atom _, x, y, z, h, c => Arr.concat_get hn hoff hone h c
  | .prod _ _, x, y, z, h, c => by
    simp only [Vals.concat, bind, Except.bind, pure, Except.pure] at h
    split at h; · cases h
    rename_i z1 h1
    split at h; · cases h
    rename_i z2 h2
    cases h
    show (Vals.row z1 c, Vals.row z2 c) = _
    rw [Vals.concat_row hn hoff hone x.1 y.1 h1 c, Vals.concat_row hn hoff hone x.2 y.2 h2 c]
    split <;> rfl
  | .arr _, _, _, _, h, _ => by simp [Vals.concat] at h
  | .sum _ _, _, _, _, h, _ => by simp [Vals.concat] at h

namespace Tab
variable {k v : Obj}

/-- **`R.concat S` denotes `R ∪ S`**, rows counted with repeats. -/
theorem concat_holds {R S C : Tab k v} (h : R.concat S = .ok C) (a : k.El) (b : v.El) :
    C.Holds a b ↔ R.Holds a b ∨ S.Holds a b := by
  unfold Tab.concat at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  split at h; · cases h
  rename_i p hp
  obtain ⟨n, off, one⟩ := p
  split at h; · cases h
  rename_i K hK
  split at h; · cases h
  rename_i V hV
  cases h
  obtain ⟨hn, hoff, hone⟩ := catPlan_ok hp
  have rk := Vals.concat_row hn hoff hone R.key S.key hK
  have rv := Vals.concat_row hn hoff hone R.val S.val hV
  simp only [Tab.Holds]
  constructor
  · rintro ⟨c, ha, hb⟩
    rw [rk] at ha; rw [rv] at hb
    split at ha
    · rename_i hl; rw [dif_pos hl] at hb; exact .inl ⟨_, ha, hb⟩
    · rename_i hl; rw [dif_neg hl] at hb; exact .inr ⟨_, ha, hb⟩
  · rintro (⟨i, ha, hb⟩ | ⟨j, ha, hb⟩)
    · refine ⟨⟨i.1, by omega⟩, ?_, ?_⟩
      · rw [rk, dif_pos i.2]; exact ha
      · rw [rv, dif_pos i.2]; exact hb
    · refine ⟨⟨R.n.toNat + j.1, by omega⟩, ?_, ?_⟩
      · rw [rk, dif_neg (by simp)]; simpa using ha
      · rw [rv, dif_neg (by simp)]; simpa using hb

/-- **`R.union S` denotes `R ∪ S`** (`Rep.rep_unionC`'s statement, pointwise). -/
theorem union_holds {R S U : Tab k v} (h : R.union S = .ok U) (a : k.El) (b : v.El) :
    U.Holds a b ↔ R.Holds a b ∨ S.Holds a b := by
  unfold Tab.union at h
  cases hc : R.concat S with
  | error s => simp [hc, bind, Except.bind] at h
  | ok C => simp only [hc, bind, Except.bind] at h; rw [canon_holds h, concat_holds hc]

/-- **`R.canon` is sorted and duplicate-free**: `Vals.nub_sorted` of its pair side, the rows of `U` being rows `sel j`
of `R`, ascending in `kasc`'s order of their codes, no two with equal codes. -/
theorem canon_sorted {R U : Tab k v} (h : R.canon = .ok U) {es : List (QAtomicType × Enc)}
    (hes : Vals.cols (A := .prod k v) (R.key, R.val) = .ok es) :
    ∃ sel : Fin U.n.toNat → Fin R.n.toNat,
      (∀ j, (U.key.row j, U.val.row j) = (R.key.row (sel j), R.val.row (sel j))) ∧
      ∀ j j' : Fin U.n.toNat, j.1 < j'.1 → lexLe (ascKeys R.n es) (sel j) (sel j') = true ∧
        seenKey R.n es (sel j) ≠ seenKey R.n es (sel j') := by
  unfold Tab.canon at h
  cases hn : Vals.nub (A := .prod k v) (R.key, R.val) with
  | error s => simp [hn, Functor.map, Except.map] at h
  | ok r =>
    simp only [hn, Functor.map, Except.map, Except.ok.injEq] at h
    subst h
    exact Vals.nub_sorted hn hes

/-- **`R.union S` is sorted and duplicate-free**: `canon_sorted` of the concatenation. -/
theorem union_sorted {R S U : Tab k v} (h : R.union S = .ok U) :
    ∃ C, R.concat S = .ok C ∧ C.canon = .ok U := by
  unfold Tab.union at h
  cases hc : R.concat S with
  | error s => simp [hc, bind, Except.bind] at h
  | ok C => simp only [hc, bind, Except.bind] at h; exact ⟨C, rfl, h⟩

end Tab

/-! ## Checks on `foR` tables -/

section Checks

/-- The table of the pairs `ps` as given, unsorted, both columns `Alg.col`'s literal `foR` columns. -/
private def tab (ps : List (Int64 × Int64)) : Tab .long .long :=
  ⟨ps.length.toUSize, List.length_map _ ▸ Alg.col (ps.map (·.1)), List.length_map _ ▸ Alg.col (ps.map (·.2))⟩

private def T₁ : List (Int64 × Int64) := [(3, 1), (1, 2), (3, 1), (-1, 2), (1, 2), (2, 7), (-5, -5), (0, 0)]
private def T₂ : List (Int64 × Int64) := [(-2, 9), (-2, 9), (1, 2), (7, -3), (-5, -5), (3, 1)]
private def T₃ : List (Int64 × Int64) := [(0, 0), (9, 9)]

#guard ((tab T₁).union (tab T₂)).toOption.map Tab.toList ==
  some [(-5, -5), (-2, 9), (-1, 2), (0, 0), (1, 2), (2, 7), (3, 1), (7, -3)]
#guard ((tab T₁).inter (tab T₂)).toOption.map Tab.toList == some [(-5, -5), (1, 2), (3, 1)]
#guard ((tab T₁).diff (tab T₂)).toOption.map Tab.toList == some [(-1, 2), (0, 0), (2, 7)]
#guard ((tab T₂).diff (tab T₁)).toOption.map Tab.toList == some [(-2, 9), (7, -3)]
#guard ((tab []).inter (tab T₁)).toOption.map Tab.toList == some []
#guard ((tab T₁).diff (tab [])).toOption.map Tab.toList == some [(-5, -5), (-1, 2), (0, 0), (1, 2), (2, 7), (3, 1)]
#guard ((tab T₁).le (tab T₁)).toOption == some true
#guard ((tab T₁).le (tab T₂)).toOption == some false
#guard ((tab []).le (tab [])).toOption == some true
-- the five-kernel operators against the old `CRel.union`, `CRel.inter`, `CRel.diff`, `Alg.leC` on the same tables,
-- both orders; the old `∩`/`−` keep `R`'s order, so their answer is compared after `Alg.canonC`
#guard [T₁, T₂, T₃, []].all fun ps => [T₁, T₂, T₃, []].all fun qs =>
  let R := tab ps; let S := tab qs
  let old (c : CRel .long .long) := c.bind fun t => let c := Alg.canonC t; if c.2 then some c.1.toList else none
  ((R.union S).toOption.map Tab.toList) == old (CRel.union (some R) (some S)) &&
  ((R.inter S).toOption.map Tab.toList) == old (CRel.inter (some R) (some S)) &&
  ((R.diff S).toOption.map Tab.toList) == old (CRel.diff (some R) (some S)) &&
  (R.le S).toOption == (let c := Alg.leC R S; if c.2 then some c.1 else none)

end Checks

end Rel
