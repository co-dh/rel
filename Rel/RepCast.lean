module

public import Rel.Run.Cast
public import Rel.RepSetOps
public import Rel.RepCanon
public import Rel.RepCols
public import Rel.RepTabDiv
public import Rel.RepTabArith
public import Rel.Lang.Den

-- exposed: every def body is a spec a downstream `rfl`/`decide`/`simp` may unfold (PLAN W.8)
@[expose] public section

/-! The law of `$` (`Tab.cast`): its table is the graph of `QAtomicType.embed` on the values in demand. -/

namespace Rel
open Rel.Ext Rel.Kernel

namespace Tab

/-- The rows of an `Arr.gather` read a valid column. -/
theorem gather_valid {u : QAtomicType} {m n : USize} {ix : Enc} {x : Arr u n} {y : Arr u m}
    (h : Arr.gather m ix x = .ok y) : Kernel.Enc.Valid n x.enc := by
  unfold Arr.gather at h; split at h
  · exact kgather_valid (by assumption)
  · cases h

/-- **A column map followed by a filter of nulls** (`$`, the unary float verbs): `Tab.keep` of the rows `(X i, w i)` at
the flag `flag` holds `a b` exactly where `a` is a value of `X` and `P a b`, given that row by row the flag is a bit,
set exactly where `P` relates the value to the answer `w i`. -/
theorem keep_map_holds {A : Obj} {t : QAtomicType} {n : USize} {X : Vals A n} {w : Arr t n} {flag : Enc}
    {T : Tab A (.atom t)} {P : A.El → (Obj.atom t).El → Prop}
    (hU : Tab.keep (k := A) (v := .atom t) ⟨n, X, w⟩ flag = .ok T)
    (row : ∀ i : Fin n.toNat, wd n flag i < 2 ∧ ∀ v, (wd n flag i ≠ 0 ∧ w.get i = v) ↔ P (X.row i) v)
    (a : A.El) (b : (Obj.atom t).El) : T.Holds a b ↔ (∃ i, X.row i = a) ∧ P a b := by
  rw [keep_holds hU (fun i hi => (row ⟨i, hi⟩).1)]
  constructor
  · rintro ⟨i, hf, rfl, rfl⟩
    exact ⟨⟨i, rfl⟩, by rw [Vals.row_atom w]; exact ((row i).2 _).1 ⟨hf, rfl⟩⟩
  · rintro ⟨⟨i, rfl⟩, hp⟩
    obtain ⟨hf, hw⟩ := ((row i).2 b).2 hp
    exact ⟨i, hf, rfl, by rw [Vals.row_atom]; exact hw⟩

/-- **`X $ t` denotes the graph of `embed s t`** on the values `X`: a value with no image at `t` has no row. -/
theorem cast_holds {s t : QAtomicType} {n : USize} {X : Vals (.atom s) n} {T : Tab (.atom s) (.atom t)}
    (h : Tab.cast X = .ok T) (a : (Obj.atom s).El) (b : (Obj.atom t).El) :
    T.Holds a b ↔ (∃ i, X.row i = a) ∧ QAtomicType.embed s t a = some b := by
  dsimp only [Tab.cast] at h
  split at h
  case isFalse => cases h
  rename_i hok
  have hst : s.storeFmt?.isSome ∧ t.storeFmt?.isSome := by
    unfold QAtomicType.castOK at hok
    revert hok; cases s.storeFmt? <;> cases t.storeFmt? <;> simp
  obtain ⟨hgs, -, -⟩ := storeFmt_ne hst.1
  obtain ⟨hgt, -, htu⟩ := storeFmt_ne hst.2
  obtain ⟨w, hw, h⟩ := Except.bind_eq_ok'.1 h
  obtain ⟨flag, hf, hU⟩ := Except.bind_eq_ok'.1 h
  have hv : Kernel.Enc.Valid n X.enc ∧ Kernel.Enc.Valid n w.enc := by
    unfold Tab.keep at hU
    obtain ⟨⟨M, sel⟩, -, hU⟩ := Except.bind_eq_ok'.1 hU
    obtain ⟨K, hK, hU⟩ := Except.bind_eq_ok'.1 hU
    obtain ⟨V, hV, -⟩ := Except.bind_eq_ok'.1 hU
    exact ⟨gather_valid (x := X) hK, gather_valid (x := w) hV⟩
  have hcm := colMap_get (colArr_ok hw)
  have hfl := colMap_post hf
  -- each row: the flag `1` and the image read back, or the flag `0` and no image
  have row : ∀ i : Fin n.toNat,
      ((Enc.raw .i64 n flag)[i.1]?.getD 0 = 1 ∧ QAtomicType.embed s t (X.get i) = some (w.get i)) ∨
      ((Enc.raw .i64 n flag)[i.1]?.getD 0 = 0 ∧ QAtomicType.embed s t (X.get i) = none) := by
    intro i
    obtain ⟨a, ha, -, hxa⟩ := Arr.get_raw_atom X hv.1 hgs i
    obtain ⟨v, hev, hwv⟩ := hcm.2 i.1 i.2
    obtain ⟨b, hb, -, hwb⟩ := Arr.get_raw_atom w hv.2 hgt i
    rw [ha] at hev
    simp only [Option.getD_some, Op.eval, Except.ok.injEq] at hev
    rw [if_neg htu] at hwv
    rw [hwv] at hb; cases hb
    have hfi := hfl.2 i.1 i.2
    rw [hwv] at hfi
    simp only [Option.getD_some] at hfi
    have hfv := eval_ne_word hfi
    simp only [ne_comm (a := nulWord)] at hfv
    rw [hxa, of_atomOfBits _ hgs hst.1, hwb, of_atomOfBits _ hgt hst.2]
    subst hev
    cases he : QAtomicType.embed s t (QAtomicType.ofBits s a) with
    | none =>
      refine .inr ⟨?_, rfl⟩
      rw [hfv]; simp [QAtomicType.castWord, he, nulWord]
    | some y =>
      have hy := QAtomicType.word_ne_nul he
      refine .inl ⟨?_, ?_⟩
      · rw [hfv]; simp [QAtomicType.castWord, he, nulWord, hy]
      · simp [QAtomicType.castWord, he, QAtomicType.ofBits_word y hst.2]
  refine keep_map_holds (P := fun x y => QAtomicType.embed s t x = some y) hU (fun i => ?_) a b
  rcases row i with h | h <;> simp only [wd, Vals.row_atom, h.1, h.2] <;> simp

/-- **A `floatOps` row `s` on the values `X`** denotes `floatDen o` of its `Op` there: no row at an object holding no
float or a target holding no number, nor where the answer has no word at the target. -/
theorem floatOp_den {A B : Obj} {n : USize} {X : Vals A n} {T : Tab A B} {s : String} {o : Op} {u : QAtomicType}
    (hs : floatOps.lookup s = some (o, u)) (h : Tab.floatOp s X = .ok T) (a : A.El) (b : B.El) :
    T.Holds a b ↔ (∃ i, X.row i = a) ∧ Lang.floatDen o A B a b := by
  match A, B, X, T, h, a, b with
  | .atom t, .atom u, X, T, h, a, b =>
    simp only [Tab.floatOp, hs] at h
    split at h
    case isFalse => cases h
    rename_i hf
    obtain ⟨⟨w, flag⟩, hm, hU⟩ := Except.bind_eq_ok'.1 h
    refine keep_map_holds hU (fun i => ?_) a b
    obtain ⟨h2, hi⟩ := fmapCols_spec hf.2.1 hf.2.2 hm i
    -- a unary `Op` reads its second operand alone (`Op.eval_acc`), so `X X` is `0 X`
    refine ⟨h2, fun v => (hi v).trans ⟨fun ⟨X, X', Y, R, hX, hX', hY, hR⟩ => ?_,
      fun ⟨_, X, Y, R, hX, hY, hR⟩ => ⟨X, X, Y, R, hX, hX, by rw [Op.eval_acc hf.1]; exact hY, hR⟩⟩⟩
    rw [hX] at hX'; cases hX'
    exact ⟨hf.1, X, Y, R, hX, by rw [← Op.eval_acc hf.1 X X]; exact hY, hR⟩
  | .prod (.atom t) (.atom t'), .atom u, X, T, h, a, b =>
    simp only [Tab.floatOp, hs] at h
    split at h
    case isFalse => cases h
    rename_i hf
    obtain ⟨ho, rfl, hf, hu⟩ := hf
    obtain ⟨⟨w, flag⟩, hm, hU⟩ := Except.bind_eq_ok'.1 h
    refine keep_map_holds hU (fun i => ?_) a b
    obtain ⟨h2, hi⟩ := fmapCols_spec hf hu hm i
    exact ⟨h2, fun v => (hi v).trans ⟨fun hr => ⟨ho, rfl, hr⟩, fun ⟨_, _, hr⟩ => hr⟩⟩
  | .atom _, .prod .., _, _, h, _, _ | .atom _, .arr _, _, _, h, _, _ | .atom _, .sum .., _, _, h, _, _
  | .prod (.atom _) (.atom _), .prod .., _, _, h, _, _ | .prod (.atom _) (.atom _), .arr _, _, _, h, _, _
  | .prod (.atom _) (.atom _), .sum .., _, _, h, _, _
  | .prod (.atom _) (.prod ..), _, _, _, h, _, _ | .prod (.atom _) (.arr _), _, _, _, h, _, _
  | .prod (.atom _) (.sum ..), _, _, _, h, _, _
  | .prod (.prod ..) _, _, _, _, h, _, _ | .prod (.arr _) _, _, _, _, h, _, _ | .prod (.sum ..) _, _, _, _, h, _, _
  | .arr _, _, _, _, h, _, _ | .sum .., _, _, _, h, _, _ => simp [Tab.floatOp, hs] at h
  | .one, _, _, _, h, _, _ | .prod .one _, _, _, _, h, _, _ | .prod (.atom _) .one, _, _, _, h, _, _
  | .atom _, .one, _, _, h, _, _ | .prod (.atom _) (.atom _), .one, _, _, h, _, _ => simp [Tab.floatOp, hs] at h

/-- `$` at any objects: the graph `castDen A B` on the values `X`, no row where a side is no atom. -/
theorem cast_den {A B : Obj} {n : USize} {X : Vals A n} {T : Tab A B} (h : Tab.cast X = .ok T) (a : A.El) (b : B.El) :
    T.Holds a b ↔ (∃ i, X.row i = a) ∧ Lang.castDen A B a b := by
  match A, B, X, T, h, a, b with
  | .atom _, .atom _, _, _, h, a, b => exact cast_holds h a b
  | .atom _, .prod .., _, _, h, _, _ | .atom _, .arr _, _, _, h, _, _ | .atom _, .sum .., _, _, h, _, _
  | .prod .., _, _, _, h, _, _ | .arr _, _, _, _, h, _, _ | .sum .., _, _, _, h, _, _ =>
    simp [Tab.cast] at h

/-- **A row `s` of `arithOps` on the pairs `X`** denotes `stepOn` of its verb there (`stepColsAt_spec`): no row at a
    pair of two atoms or of non-atoms. -/
theorem arithOp_den {B : Obj} {n : USize} {X : Vals (.prod B B) n} {T : Tab (.prod B B) B} {s : String} {k : UInt8}
    (hs : arithOps.lookup s = some k) (h : Tab.arithOp s X = .ok T) (a : (Obj.prod B B).El) (b : B.El) :
    T.Holds a b ↔ (∃ i, X.row i = a) ∧ Lang.stepOn k B a b := by
  cases B
  case atom u =>
    simp only [Tab.arithOp, hs, and_self, ↓reduceIte] at h
    obtain ⟨⟨w, flag⟩, hm, hU⟩ := Except.bind_eq_ok'.1 h
    exact keep_map_holds hU (fun i => stepColsAt_spec hm i) a b
  all_goals simp [Tab.arithOp, hs] at h

/-- **A row of `arithOps` keeps `Tab.WF`**: `X` keyed to the answer words, `keep`. -/
theorem arithOp_wf {s : String} {B : Obj} {n : USize} {X : Vals (.prod B B) n} {T : Tab (.prod B B) B}
    (h : Tab.arithOp s X = .ok T) (hX : Vals.WF X) : T.WF := by
  rcases hl : arithOps.lookup s with _ | k <;> cases B <;> simp only [Tab.arithOp, hl, and_self, ↓reduceIte] at h
  case some.atom u =>
    obtain ⟨⟨w, f⟩, -, h⟩ := Except.bind_eq_ok'.1 h
    exact keep_wf h ⟨hX, trivial⟩
  all_goals cases h

/-- **The row `succ` on the values `X`** denotes `succOn`: each `u` to `Ew.intStep`'s `u + 1` (the null to itself),
    the step of `Tab.succ_holds`; no row at an object other than `i64`. -/
theorem succOp_den {A : Obj} {n : USize} {X : Vals A n} {T : Tab A A} (h : Tab.succOp X = .ok T) (x w : A.El) :
    T.Holds x w ↔ (∃ i, X.row i = x) ∧ Lang.succOn A x w := by
  cases A
  case atom t =>
    cases t
    case i64 =>
      simp only [Tab.succOp, bind, Except.bind_eq_ok'] at h
      obtain ⟨s, hs, h⟩ := h
      cases h
      have hrow := Tab.succCol_row hs
      simp only [Tab.Holds, Lang.succOn]
      constructor
      · rintro ⟨i, rfl, rfl⟩; exact ⟨⟨i, rfl⟩, hrow i⟩
      · rintro ⟨⟨i, rfl⟩, rfl⟩; exact ⟨i, rfl, hrow i⟩
    all_goals simp [Tab.succOp] at h
  all_goals simp [Tab.succOp] at h

/-- **The row `succ` keeps `Tab.WF`**: `X` keyed to the answer words. -/
theorem succOp_wf {A : Obj} {n : USize} {X : Vals A n} {T : Tab A A} (h : Tab.succOp X = .ok T) (hX : Vals.WF X) :
    T.WF := by
  cases A
  case atom t =>
    cases t
    case i64 =>
      simp only [Tab.succOp, bind, Except.bind_eq_ok'] at h
      obtain ⟨_, -, h⟩ := h
      cases h; exact ⟨hX, trivial⟩
    all_goals simp [Tab.succOp] at h
  all_goals simp [Tab.succOp] at h

/-- **The words of `Arr.ofFn t n f`** as the kernels read them: word `i` is `f i` cut to `t`'s `8 * w` bits
(`raw_encodeAt` of the packing `foldl_pushBits` reads back). -/
theorem _root_.Rel.Arr.raw_ofFn {t : QAtomicType} {w : Nat} (ht : t.width = some w) (hu : t ≠ .u1 ∧ t.width.isSome)
    {n : USize} (f : Fin n.toNat → UInt64) (i : Fin n.toNat) :
    (Enc.raw t n (Arr.ofFn t n f hu).enc)[i.1]? = some (UInt64.ofNat ((f i).toNat % 2 ^ (8 * w))) := by
  have hw : 0 < w ∧ w ≤ 8 := by cases t <;> simp [QAtomicType.width] at ht ⊢ <;> omega
  have hf := Verify.foldl_pushBits (fun x : UInt64 => x) w hw.2 (List.ofFn f) .empty
  simp only [ht, Option.getD_some] at hf
  simp only [Arr.ofFn, Arr.ofBytes, Ext.Enc.ofBytes, ht, Option.getD_some, Kernel.Coc.encode]
  change (Enc.raw t n (Enc.foR _ _))[i.1]? = _
  rw [Verify.raw_encodeAt t w ht hu.1 Column.lgEnc (by decide) _ n
    (by rw [hf.1]; simp [Nat.mul_div_cancel_left _ hw.1])]
  have := hf.2.2 i.1 (by simp)
  simp only [ByteArray.size_empty, Nat.zero_add, List.getElem_ofFn] at this
  simp [i.2, Nat.mul_comm, this]

/-- **`ymd` keeps `Tab.WF`**: `X` keyed to the day words, `keep`. -/
theorem ymd_wf {A B : Obj} {n : USize} {X : Vals A n} {t : Tab A B} (h : Tab.ymd X = .ok t) (hX : Vals.WF X) :
    t.WF := by
  unfold Tab.ymd at h
  split at h
  · exact keep_wf h ⟨hX, trivial⟩
  · cases h

/-- **`ymd X` denotes `ymdDen`** on the texts `X`: a cell to the day it spells (`Db.Csv.ymd`), no row where it
spells none. -/
theorem ymd_den {A B : Obj} {n : USize} {X : Vals A n} {T : Tab A B} (h : Tab.ymd X = .ok T) (a : A.El) (b : B.El) :
    T.Holds a b ↔ (∃ i, X.row i = a) ∧ Lang.ymdDen A B a b := by
  unfold Tab.ymd at h
  split at h
  case h_2 => cases h
  show _ ↔ _ ∧ (Db.Csv.ymd a).map Int32.ofInt = some b
  rename_i X
  have hr : ∀ i : Fin n.toNat,
      ((Tab.toList (k := .arr (.atom .char)) (v := .one) ⟨n, X, ()⟩).toArray[i.1]?.map (·.1)).getD [] = X.row i := by
    intro i; simp [Tab.toList, i.2]
  simp only [Tab.ymd, hr] at h
  have hf : ∀ i : Fin n.toNat, (Enc.raw .i64 n (Arr.ofFn .i64 n fun j =>
      if (Db.Csv.ymd (X.row j)).isSome then 1 else 0).enc)[i.1]?.getD 0 =
      if (Db.Csv.ymd (X.row i)).isSome then 1 else 0 := by
    intro i; rw [Arr.raw_ofFn rfl]; simp only [Option.getD_some]; split <;> decide
  have hd : ∀ i : Fin n.toNat, Vals.row (A := .atom .date) (Arr.ofFn .date n fun j =>
      (Int32.ofInt ((Db.Csv.ymd (X.row j)).getD 0)).toUInt32.toUInt64) i =
      Int32.ofInt ((Db.Csv.ymd (X.row i)).getD 0) := by
    intro i
    rw [Vals.row_atom, Arr.get_word _ rfl, Arr.raw_ofFn rfl]
    simp only [Option.getD_some, QAtomicType.ofBits]
    rw [Nat.mod_eq_of_lt (by simpa using (Int32.ofInt _).toUInt32.toNat_lt)]
    simp
  rw [keep_holds h (fun i hi => by
    have := hf ⟨i, hi⟩; dsimp only at this ⊢; rw [this]; split <;> decide)]
  constructor
  · rintro ⟨i, hi, rfl, rfl⟩
    refine ⟨⟨i, rfl⟩, ?_⟩
    have hi' := hf i ▸ hi
    show _ = some (Vals.row (A := .atom .date) _ i)
    rw [hd i]; cases hy : Db.Csv.ymd (X.row i) <;> simp_all
  · rintro ⟨⟨i, rfl⟩, hb⟩
    refine ⟨i, ?_, rfl, ?_⟩
    · rw [hf i]; cases hy : Db.Csv.ymd (X.row i) <;> simp_all
    · show Vals.row (A := .atom .date) _ i = _
      rw [hd i]; cases hy : Db.Csv.ymd (X.row i) <;> simp_all

end Tab
end Rel
