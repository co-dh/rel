import Rel.Run.Div
import Rel.Run.Fix
import Rel.Run.Power
import Rel.Run.List
import Rel.RepStruct
import Rel.RepCanon
import Rel.RepSetOps
import Rel.RepTabComp
import Rel.Lang.Den
import Rel.RepTabArith
import Rel.RepOrder

/-! The laws of the operators of `Rel/Run/Div.lean` (`ldiv`, `rdiv`, `lam`, `E`, `nil`, `lt`, `leq`), and the checks
of those, `Rel/Run/Fix.lean`'s, `Rel/Run/Power.lean`'s and `Rel/Run/List.lean`'s operators on `foR` tables against their
denotations (`Rel/Lang/Den.lean`) on lists, as sets. -/

namespace Rel
open Rel.Ext Rel.Kernel Rel.Verify Ext.Enc

namespace Tab
variable {A B C : Obj}

/-- **`nil D` denotes `nilDen` on `D`**: each key of `D` to the empty array. -/
theorem nil_holds {n : USize} {D : Vals A n} {T : Tab A (.arr B)} (h : Tab.nil D = .ok T) (hD : Vals.WF D)
    (a : A.El) (ys : List B.El) : T.Holds a ys ↔ (∃ i, D.row i = a) ∧ ys = [] := by
  unfold Tab.nil at h; simp only [bind, Except.bind] at h
  split at h; · cases h
  rename_i z hz; split at h; · cases h
  rw [canon_holds h ⟨hD, fun i => by rw [Arr.zeros_get hz]; simp, Vals.none_wf ‹_›⟩]
  simp only [Tab.Holds, Vals.row]
  exact ⟨fun ⟨i, h1, h2⟩ => ⟨⟨i, h1⟩, h2.symm⟩, fun ⟨⟨i, h1⟩, h2⟩ => ⟨i, h1, h2.symm⟩⟩

/-- The order of the atom `t` (`<` at `s`, else `≤`): `ltAt` or `leAt`. -/
abbrev ordAt (s : Bool) (t : QAtomicType) (a c : (Obj.atom t).El) : Prop :=
  if s then Lang.ltAt t a c else Lang.leAt t a c

/-- `ordOp_iff` at an ordered atom `t` widened through `Op.cast r .i64` (`r` its `ordNum`): the signed order of the
widened words is `iordAt`, whichever stored words hold the two values (`castWord_ofBits`). -/
private theorem iord_iff {s : Bool} {t r : QAtomicType} (hr : t.ordNum = some r)
    (hw : ∀ {n : USize} (e : Enc), wideCol t n e = colMap .first n e e .i64 t [(.cast r .i64, 0)])
    (hl : ∀ a c, ordAt s t a c ↔ Lang.iordAt (if s then .lt else .le) t a c)
    {n : USize} (x y : Arr t n) {a' b' : Enc} (ha : wideCol t n x.enc = .ok a') (hb : wideCol t n y.enc = .ok b')
    (i : Fin n.toNat) :
    (∃ e : Bool, (if s then Op.lt else Op.le).eval ((raw .i64 n a')[i.1]?.getD 0) ((raw .i64 n b')[i.1]?.getD 0) =
      .ok (if e then 1 else 0)) ∧
    (ordAt s t (x.get i) (y.get i) ↔
      (if s then Op.lt else Op.le).eval ((raw .i64 n a')[i.1]?.getD 0) ((raw .i64 n b')[i.1]?.getD 0) = .ok 1) := by
  rw [hw] at ha hb
  -- row `i` of a widened column is `castWord r .i64` of the stored word (`colMap_chain`, `first` keeping it)
  have row : ∀ {e o : Enc}, colMap .first n e e .i64 t [(.cast r .i64, 0)] = .ok o →
      QAtomicType.castWord r .i64 ((raw t n e)[i.1]?.getD 0) = (raw .i64 n o)[i.1]?.getD 0 := fun h => by
    obtain ⟨X, _, v, w, hX, -, hv, hw', ho⟩ := (colMap_chain h).2.2.2 i.1 i.2
    cases hX; cases hv; cases hw'
    simp [ho]
  have ea := row ha
  have eb := row hb
  have hs : t.ordNum.isSome := by rw [hr]; rfl
  rw [← ea, ← eb, hl, Arr.get_word x hs i, Arr.get_word y hs i]
  refine ⟨by cases s <;> exact ⟨_, rfl⟩, ⟨?_, fun h => ⟨r, _, _, hr, rfl, rfl, h⟩⟩⟩
  rintro ⟨r', x', y', hr', hx, hy, h⟩
  rw [hr, Option.some.injEq] at hr'; subst hr'
  rwa [QAtomicType.castWord_ofBits hr hx, QAtomicType.castWord_ofBits hr hy] at h

/-- **`ordOp s t` tests `ordAt s t` on the `wideCol` words**, at every atom: a bit, `1` exactly where the order holds
(`Int64`'s on the stored words at `i64`, IEEE's on the `f64` words at a float atom, `Int64`'s on the widened words at
any other ordered atom: `iord_iff`; `ordOp` refuses an atom with no order). -/
theorem ordOp_iff {s : Bool} {t : QAtomicType} {op : Op} (hop : ordOp s t = .ok op) {n : USize} (x y : Arr t n)
    {a' b' : Enc} (ha : wideCol t n x.enc = .ok a') (hb : wideCol t n y.enc = .ok b') (i : Fin n.toNat) :
    (∃ e : Bool, op.eval ((raw .i64 n a')[i.1]?.getD 0) ((raw .i64 n b')[i.1]?.getD 0) = .ok (if e then 1 else 0)) ∧
    (ordAt s t (x.get i) (y.get i) ↔ op.eval ((raw .i64 n a')[i.1]?.getD 0) ((raw .i64 n b')[i.1]?.getD 0) = .ok 1) := by
  cases t <;> simp (config := { decide := true }) only [ordOp, throw, throwThe, MonadExceptOf.throw,
    pure, Except.pure, reduceCtorEq, Except.ok.injEq, ite_true, ite_false] at hop
  case u8 | char | i16 | i32 | date | i8 | datetime =>
    subst hop; exact iord_iff rfl (fun _ => rfl) (fun _ _ => by cases s <;> exact Iff.rfl) x y ha hb i
  case i64 =>
    simp only [wideCol, widen, ite_true, pure, Except.pure, Except.ok.injEq] at ha hb
    subst ha hb hop
    rw [Arr.get_i64, Arr.get_i64]
    generalize (raw .i64 n x.enc)[i.1]?.getD 0 = A; generalize (raw .i64 n y.enc)[i.1]?.getD 0 = B
    cases s
    · refine ⟨⟨_, rfl⟩, ?_⟩
      show A.toInt64 ≤ B.toInt64 ↔ Except.ok (if decide (A.toInt64 ≤ B.toInt64) = true then 1 else 0) = _
      by_cases h : A.toInt64 ≤ B.toInt64 <;> simp [h]
    · refine ⟨⟨_, rfl⟩, ?_⟩
      show A.toInt64 < B.toInt64 ↔ Except.ok (if decide (A.toInt64 < B.toInt64) = true then 1 else 0) = _
      by_cases h : A.toInt64 < B.toInt64 <;> simp [h]
  case f32 | f64 =>
    subst hop
    simp only [ordAt, Lang.ltAt, Lang.leAt, Lang.fordAt, wideCol_word x ha (by decide) i,
      wideCol_word y hb (by decide) i, Option.some.injEq]
    cases s <;> simp only [Bool.false_eq_true, ↓reduceIte] <;>
      exact ⟨⟨_, rfl⟩, fun ⟨_, _, e1, e2, h⟩ => e1 ▸ e2 ▸ h, fun h => ⟨_, _, rfl, rfl, h⟩⟩

/-- **`cmpPairs op X` is `X ∩ ordAt s t`**, `op` the order `ordOp s t`: row `i` of `X` kept where `op` answers `1`. -/
theorem cmpPairs_holds {s : Bool} {t : QAtomicType} {op : Op} (hop : ordOp s t = .ok op)
    {X T : Tab (.atom t) (.atom t)} (h : cmpPairs op X = .ok T) (a c : (Obj.atom t).El) :
    T.Holds a c ↔ X.Holds a c ∧ ordAt s t a c := by
  unfold cmpPairs at h; simp only [bind, Except.bind] at h
  split at h; · cases h
  rename_i ka hka
  split at h; · cases h
  rename_i kv hkv
  split at h; · cases h
  rename_i w hw
  obtain ⟨-, -, -, hev⟩ := colMap_raw hw
  have hwv : ∀ i : Fin X.n.toNat, (raw .i64 X.n w)[i.1]?.getD 0 < 2 ∧
      ((raw .i64 X.n w)[i.1]?.getD 0 ≠ 0 ↔ ordAt s t (X.key.row i) (X.val.row i)) := by
    intro i
    obtain ⟨⟨e, he⟩, hP⟩ := ordOp_iff hop X.key X.val hka hkv i
    rw [Vals.row_atom, Vals.row_atom, hP, he, ← Except.ok.inj (he.symm.trans (hev i.1 i.2))]
    cases e <;> simp
  rw [keep_holds h (fun i hi => (hwv ⟨i, hi⟩).1)]
  simp only [Tab.Holds]
  constructor
  · rintro ⟨i, hi, rfl, rfl⟩
    exact ⟨⟨i, rfl, rfl⟩, (hwv i).2.1 hi⟩
  · rintro ⟨⟨i, rfl, rfl⟩, hr⟩
    exact ⟨i, (hwv i).2.2 hr, rfl, rfl⟩

/-- **`cmpAt lt t X` is the coreflexive `ordDen lt` on `X`**: row `i` of `X` kept where `ordOp lt t` answers `1`,
    as in `cmpPairs_holds`. -/
theorem cmpAt_holds {lt : Bool} {t : QAtomicType} {n : USize} {X : Vals (.prod (.atom t) (.atom t)) n}
    {T : Tab (.prod (.atom t) (.atom t)) (.prod (.atom t) (.atom t))} (h : cmpAt lt t X = .ok T)
    (a b : (Obj.prod (.atom t) (.atom t)).El) : T.Holds a b ↔ (∃ i, X.row i = a) ∧ Lang.ordDen lt (.atom t) a b := by
  unfold cmpAt at h; simp only [bind, Except.bind] at h
  split at h; · cases h
  rename_i ka hka
  split at h; · cases h
  rename_i kv hkv
  split at h; · cases h
  rename_i op hop
  split at h; · cases h
  rename_i w hw
  obtain ⟨-, -, -, hev⟩ := colMap_raw hw
  have hwv : ∀ i : Fin n.toNat, (raw .i64 n w)[i.1]?.getD 0 < 2 ∧
      ((raw .i64 n w)[i.1]?.getD 0 ≠ 0 ↔ ordAt lt t (X.1.row i) (X.2.row i)) := by
    intro i
    obtain ⟨⟨e, he⟩, hP⟩ := ordOp_iff hop X.1 X.2 hka hkv i
    rw [Vals.row_atom, Vals.row_atom, hP, he, ← Except.ok.inj (he.symm.trans (hev i.1 i.2))]
    cases e <;> simp
  rw [keep_holds h (fun i hi => (hwv ⟨i, hi⟩).1)]
  simp only [Tab.Holds, Lang.ordDen]
  constructor
  · rintro ⟨i, hi, rfl, rfl⟩; exact ⟨⟨i, rfl⟩, rfl, (hwv i).2.1 hi⟩
  · rintro ⟨⟨i, rfl⟩, rfl, ho⟩; exact ⟨i, (hwv i).2.2 ho, rfl, rfl⟩

/-- **A row `s` of `cmpOps` on the pairs `X`** denotes `ordDen` of its order there (`cmpAt_holds`); no row at a pair of
    two atoms or of non-atoms. -/
theorem cmpOp_den {B : Obj} {n : USize} {X : Vals (.prod B B) n} {T : Tab (.prod B B) (.prod B B)} {s : String}
    {lt : Bool} (hs : cmpOps.lookup s = some lt) (h : cmpOp s X = .ok T) (a b : (Obj.prod B B).El) :
    T.Holds a b ↔ (∃ i, X.row i = a) ∧ Lang.ordDen lt B a b := by
  cases B
  case atom t =>
    simp only [cmpOp, hs] at h
    rw [dif_pos (by simp), dif_pos (by simp), dif_pos (by simp)] at h
    exact cmpAt_holds h a b
  all_goals simp [cmpOp, hs] at h

/-- **A row of `cmpOps` keeps `Tab.WF`**: `X` keyed to itself, `keep`. -/
theorem cmpOp_wf {s : String} {B : Obj} {n : USize} {X : Vals (.prod B B) n} {T : Tab (.prod B B) (.prod B B)}
    (h : cmpOp s X = .ok T) (hX : Vals.WF X) : T.WF := by
  rcases hl : cmpOps.lookup s with _ | lt <;> cases B <;> simp only [cmpOp, hl] at h
  case some.atom t =>
    rw [dif_pos (by simp), dif_pos (by simp), dif_pos (by simp)] at h
    change cmpAt lt t X = .ok T at h
    simp only [cmpAt, bind, Except.bind_eq_ok'] at h
    obtain ⟨_, -, _, -, _, -, _, -, h⟩ := h
    exact keep_wf h ⟨hX, hX⟩
  all_goals cases h

/-- **`cmpOn op K L` is `K ≫ ordAt s t ≫ L`**: `cmpPairs` of `cross K L`. -/
theorem cmpOn_holds {s : Bool} {t : QAtomicType} {op : Op} (hop : ordOp s t = .ok op)
    {n m : USize} {K : Vals (.atom t) n} {L : Vals (.atom t) m} {T : Tab (.atom t) (.atom t)} (h : cmpOn op K L = .ok T)
    (hK : Vals.WF K) (hL : Vals.WF L) (a c : (Obj.atom t).El) :
    T.Holds a c ↔ (∃ i, K.row i = a) ∧ (∃ j, L.row j = c) ∧ ordAt s t a c := by
  unfold cmpOn at h; simp only [bind, Except.bind] at h
  split at h; · cases h
  rename_i X hX
  rw [cmpPairs_holds hop h, cross_holds hX hK hL, and_assoc]

/-- **`lt t K L` denotes `K ≫ ltAt t ≫ L`**. -/
theorem lt_holds {t : QAtomicType} {n m : USize} {K : Vals (.atom t) n} {L : Vals (.atom t) m}
    {T : Tab (.atom t) (.atom t)} (h : Tab.lt t K L = .ok T) (hK : Vals.WF K) (hL : Vals.WF L)
    (a c : (Obj.atom t).El) : T.Holds a c ↔ (∃ i, K.row i = a) ∧ (∃ j, L.row j = c) ∧ Lang.ltAt t a c := by
  unfold Tab.lt at h; simp only [bind, Except.bind] at h
  split at h; · cases h
  exact cmpOn_holds (s := true) (by assumption) h hK hL a c

/-- **`leq t K L` denotes `K ≫ leAt t ≫ L`**. -/
theorem leq_holds {t : QAtomicType} {n m : USize} {K : Vals (.atom t) n} {L : Vals (.atom t) m}
    {T : Tab (.atom t) (.atom t)} (h : Tab.leq t K L = .ok T) (hK : Vals.WF K) (hL : Vals.WF L)
    (a c : (Obj.atom t).El) : T.Holds a c ↔ (∃ i, K.row i = a) ∧ (∃ j, L.row j = c) ∧ Lang.leAt t a c := by
  unfold Tab.leq at h; simp only [bind, Except.bind] at h
  split at h; · cases h
  exact cmpOn_holds (s := false) (by assumption) h hK hL a c

/-- The keys of `dom U` are the keys of `U`. -/
private theorem dom_key {k v : Obj} {U : Tab k v} {d : Tab k k} (hd : U.dom = .ok d) (hU : Vals.WF U.key)
    (x : k.El) : (∃ i, d.key.row i = x) ↔ ∃ y, U.Holds x y := by
  constructor
  · rintro ⟨i, rfl⟩; exact ((dom_holds hd hU _ _).1 ⟨i, rfl, rfl⟩).2
  · intro hv; obtain ⟨i, hi, -⟩ := (dom_holds hd hU x x).2 ⟨rfl, hv⟩; exact ⟨i, hi⟩

/-- **`lt` on both sides `dom U` denotes `ltDen`**: `lt_holds` at `K = L = dom U`. -/
theorem lt_dom_holds {t : QAtomicType} {U d T : Tab (.atom t) (.atom t)} (hd : U.dom = .ok d) (hU : U.WF)
    (h : Tab.lt t d.key d.key = .ok T) (a c : (Obj.atom t).El) : T.Holds a c ↔ Lang.ltDen t U.Holds a c := by
  have wd := dom_wf hd hU
  rw [lt_holds h wd.1 wd.1, dom_key hd hU.1, dom_key hd hU.1]

/-- **`leq` on both sides `dom U` denotes `leqDen`**: `leq_holds` at `K = L = dom U`. -/
theorem leq_dom_holds {t : QAtomicType} {U d T : Tab (.atom t) (.atom t)} (hd : U.dom = .ok d) (hU : U.WF)
    (h : Tab.leq t d.key d.key = .ok T) (a c : (Obj.atom t).El) : T.Holds a c ↔ Lang.leqDen t U.Holds a c := by
  have wd := dom_wf hd hU
  rw [leq_holds h wd.1 wd.1, dom_key hd hU.1, dom_key hd hU.1]

/-- **`mem X` denotes `∋` on the arrays `X`**: each cell of `X` to each of its elements. Cell `i` is `[lo, hi)`,
`0 ≤ lo ≤ hi ≤ m` (`Vals.WF`; `Vals.row` of an `arr` side reads `lo ≤ j < hi` over `j < m`, the same `j`); EXPAND
of the widths `hi - lo` (`expand_spec`) puts output row `Σ_{<i} w + (j - lo)` at cell `i`, element `j`. -/
theorem mem_holds {n : USize} {X : Vals (.arr B) n} {T : Tab (.arr B) B} (h : Tab.mem X = .ok T) (hX : Vals.WF X)
    (xs : List B.El) (b : B.El) : T.Holds xs b ↔ (∃ i, X.row i = xs) ∧ b ∈ xs := by
  obtain ⟨m, lo, up, f⟩ := X
  dsimp only [Tab.mem] at h
  split at h; · cases h
  rename_i hb
  simp only [bind] at h
  rw [Except.bind_eq_ok'] at h; obtain ⟨_, -, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨wd, hwd, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨⟨Tn, G, u⟩, hex, h⟩ := h; try dsimp only at h
  rw [Except.bind_eq_ok'] at h; obtain ⟨sg, hsg, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨ix, hix, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨x, hx, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨y, hy, h⟩ := h
  rw [canon_holds h ⟨Vals.gather_wf hx hX, Vals.gather_wf hy hX.2⟩]
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
  -- the words `lo`, `hi - lo`: `0 ≤ lo ≤ hi ≤ m` (`Vals.WF`), so `lo = SN`, `hi = EN`
  have hW : ∀ i < n.toNat, 0 ≤ Lf i ∧ Lf i ≤ Hf i ∧ Hf i ≤ m.toNat := fun i hi => by
    have := hX.1 ⟨i, hi⟩; rwa [Arr.get_i64, Arr.get_i64, ← hLf, ← hHf] at this
  have hsw : ∀ i < n.toNat, (raw .i64 n lo.enc)[i]?.getD 0 = (SN i).toUInt64 := by
    intro i hi
    obtain ⟨h63, hv⟩ := toInt64_nonneg (x := (raw .i64 n lo.enc)[i]?.getD 0) (by rw [← hLf]; have := hW i hi; omega)
    rw [← hLf] at hv; rw [hSN, hv, Int.toNat_natCast]; simp
  have hew : ∀ i < n.toNat, (raw .i64 n up.enc)[i]?.getD 0 = (EN i).toUInt64 := by
    intro i hi
    have := hW i hi
    obtain ⟨h63, hv⟩ := toInt64_nonneg (x := (raw .i64 n up.enc)[i]?.getD 0) (by rw [← hHf]; omega)
    rw [← hHf] at hv
    rw [← UInt64.ofNat_toNat (x := (raw .i64 n up.enc)[i]?.getD 0), hEN, hSN]; congr 1; omega
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
    rw [(kgather_word hsg lo.plain t htT).2, hG, toNat_toUInt64 (by omega), hsw g hg, hu] at es
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
    rw [if_pos ((hcell _ j.1 j.2).2 (by have := hwN g; rw [hI] at hj; simp only; omega))]
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
  have hc : 0 ≤ (lo.get i).toInt ∧ (lo.get i).toInt ≤ (hi.get i).toInt ∧ (hi.get i).toInt ≤ (m.toNat : Int) := by
    simp only [Arr.get_i64, ha, hb, toInt64_toInt_nat (show a < 2 ^ 63 by omega),
      toInt64_toInt_nat (show b < 2 ^ 63 by omega)]; omega
  have hi : (i.1.toUInt64).toNat = i.1 := by
    have := i.2; have := n.toNat_lt_size; have := USize.size_le; simp; omega
  rw [Vals.row_arr i hc]
  simp only [cellStart, cellLen, hi, ha, hb, toInt64_toInt_nat (show a < 2 ^ 63 by omega),
    toInt64_toInt_nat (show b < 2 ^ 63 by omega)]
  congr 2 <;> omega

/-- **`Vals.row_cell` for a cell that may lie past the payload**: `a ≤ b` with `b ≤ m` or `a = b`, the empty cell
being read empty wherever it lies (`uncat`'s split of a cell `cellSpan` clamped). -/
theorem Vals.row_span {B : Obj} {n m : USize} (lo hi : Arr .i64 n) (f : Vals B m) (i : Fin n.toNat) {a b : Nat}
    (ha : (raw .i64 n lo.enc)[i.1]?.getD 0 = a.toUInt64) (hb : (raw .i64 n hi.enc)[i.1]?.getD 0 = b.toUInt64)
    (hab : a ≤ b) (hbm : b ≤ m.toNat ∨ a = b) (h63 : a < 2 ^ 63) (hm : m.toNat < 2 ^ 63) :
    Vals.row (A := .arr B) ⟨m, lo, hi, f⟩ i =
      (List.range' a (b - a)).map fun k => if h : k < m.toNat then Vals.row f ⟨k, h⟩ else B.dflt := by
  rcases hbm with hbm | rfl
  · exact Vals.row_cell lo hi f i ha hb hab hbm hm
  rw [Vals.row_empty i (by rw [Arr.get_i64, Arr.get_i64, ha, hb]), Nat.sub_self, List.range'_zero, List.map_nil]

/-- **A cell `Vals.WF` admits reads as `[SN, EN)`** (`0 ≤ lo ≤ hi ≤ m`, so no clamp): `lo = SN`, `hi = EN` as
words, and the row is the payload rows `[SN, EN)`, so `SN ≤ EN`, and `EN ≤ m` or the cell is empty. -/
theorem cellSpan_spec {B : Obj} {n m : USize} {lo up : Arr .i64 n}
    (hc : ∀ i : Fin n.toNat, 0 ≤ (lo.get i).toInt ∧ (lo.get i).toInt ≤ (up.get i).toInt ∧
      (up.get i).toInt ≤ (m.toNat : Int))
    (hm63 : m.toNat < 2 ^ 63) (f : Vals B m) :
    ∃ SN EN : Nat → Nat, (∀ i < n.toNat, (raw .i64 n lo.enc)[i]?.getD 0 = (SN i).toUInt64 ∧
      (raw .i64 n up.enc)[i]?.getD 0 = (EN i).toUInt64) ∧
      (∀ i, SN i ≤ EN i ∧ SN i < 2 ^ 63 ∧ (EN i ≤ m.toNat ∨ EN i = SN i)) ∧
      ∀ i : Fin n.toNat, Vals.row (A := .arr B) ⟨m, lo, up, f⟩ i =
        (List.range' (SN i) (EN i - SN i)).map fun k => if h : k < m.toNat then Vals.row f ⟨k, h⟩ else B.dflt := by
  obtain ⟨Lf, hLf⟩ : ∃ F : Nat → Int, ∀ i, F i = ((raw .i64 n lo.enc)[i]?.getD 0).toInt64.toInt := ⟨_, fun _ => rfl⟩
  obtain ⟨Hf, hHf⟩ : ∃ F : Nat → Int, ∀ i, F i = ((raw .i64 n up.enc)[i]?.getD 0).toInt64.toInt := ⟨_, fun _ => rfl⟩
  obtain ⟨SN, hSN⟩ : ∃ F : Nat → Nat, ∀ i, F i = (Lf i).toNat := ⟨_, fun _ => rfl⟩
  obtain ⟨EN, hEN⟩ : ∃ F : Nat → Nat, ∀ i, F i = max (min (Hf i).toNat m.toNat) (SN i) := ⟨_, fun _ => rfl⟩
  have hL63 : ∀ i, Lf i < 2 ^ 63 := fun i => by
    rw [hLf, toInt64_toInt_cond]; have := ((raw .i64 n lo.enc)[i]?.getD 0).toNat_lt; split <;> omega
  have hcw : ∀ i < n.toNat, 0 ≤ Lf i ∧ Lf i ≤ Hf i ∧ Hf i ≤ m.toNat := fun i hi => by
    have := hc ⟨i, hi⟩; rw [Arr.get_i64, Arr.get_i64] at this; rw [hLf, hHf]; exact this
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
  rw [Vals.row_arr i (hc i)]
  simp only [cellStart, cellLen, hi, ← hLf, ← hHf]
  have := hcw i i.2
  rw [show (Lf i).toNat = SN i by rw [hSN], show (Hf i).toNat - SN i = EN i - SN i by rw [hEN, hSN]; omega]

/-- **The start of a cell `Vals.WF` admits is at most `m`**: `0 ≤ lo ≤ hi ≤ m`. -/
theorem cellSpan_start_le {n m : USize} {lo up : Arr .i64 n}
    (hc : ∀ i : Fin n.toNat, 0 ≤ (lo.get i).toInt ∧ (lo.get i).toInt ≤ (up.get i).toInt ∧
      (up.get i).toInt ≤ (m.toNat : Int)) (i : Fin n.toNat) : ((raw .i64 n lo.enc)[i.1]?.getD 0).toNat ≤ m.toNat := by
  have hl := hc i
  rw [Arr.get_i64, Arr.get_i64] at hl
  obtain ⟨-, hv⟩ := toInt64_nonneg (x := (raw .i64 n lo.enc)[i.1]?.getD 0) hl.1
  omega

/-- **`colArr` answers `colMap`'s column**, the converse of `colArr_ok`. -/
theorem colArr_of_ok {op : Op} {n : USize} {a b o : Enc} {t : QAtomicType} (h : colMap op n a b t = .ok o) :
    colArr op n a b t = .ok (Arr.mk o (colMap_closed h).2 (colMap_plain h)) := by
  unfold colArr
  split
  · rename_i o' h'; have := h.symm.trans h'; cases this; rfl
  · rename_i s' h'; have := h.symm.trans h'; cases this

/-- **The non-empty cells** (`uncons`, `unsnoc`): `whereCol` of `lo < hi` on cells `Vals.WF` admits lists exactly
the cells `[SN, EN)` with `SN < EN`. -/
theorem cellSpan_where {B : Obj} {n m M : USize} {lo up : Arr .i64 n} {lt sel : Enc}
    (h : ∀ i : Fin n.toNat, 0 ≤ (lo.get i).toInt ∧ (lo.get i).toInt ≤ (up.get i).toInt ∧
      (up.get i).toInt ≤ (m.toNat : Int))
    (hlt : colMap .lt n lo.enc up.enc = .ok lt) (hw : whereCol n lt = .ok (M, sel))
    (hm63 : m.toNat < 2 ^ 63) (f : Vals B m) :
    ∃ SN EN : Nat → Nat, (∀ i < n.toNat, (raw .i64 n lo.enc)[i]?.getD 0 = (SN i).toUInt64 ∧
      (raw .i64 n up.enc)[i]?.getD 0 = (EN i).toUInt64) ∧
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

/-- **A cell `[a, b)` with `a ≤ b ≤ m`**, its bounds the words of the naturals `a` and `b`, `m` below `2^63`: the cell
clause of `Vals.WF`. -/
theorem cell_wf_nat {n m : USize} {lo hi : Arr .i64 n} {i : Fin n.toNat} {a b : Nat}
    (hlo : (raw .i64 n lo.enc)[i.1]?.getD 0 = a.toUInt64) (hhi : (raw .i64 n hi.enc)[i.1]?.getD 0 = b.toUInt64)
    (hab : a ≤ b) (hbm : b ≤ m.toNat) (hm : m.toNat < 2 ^ 63) :
    0 ≤ (lo.get i).toInt ∧ (lo.get i).toInt ≤ (hi.get i).toInt ∧ (hi.get i).toInt ≤ (m.toNat : Int) := by
  rw [Arr.get_i64, Arr.get_i64, hlo, hhi, toInt64_toInt_nat (by omega), toInt64_toInt_nat (by omega)]; omega

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
  · have es := (colMap_raw (colArr_ok hhi')).2.2.2 i.1 i.2
    rw [hP'w i.1 i.2, 
      sum_range_succ'] at es
    simp only [Op.eval, Except.ok.injEq, UInt64.add_zero] at es
    rw [← es]

/-- **`Vals.cells` reads cell `i` as the payload rows `[Σ_{<i} w, Σ_{≤i} w)`** (`Vals.cells_spec`). -/
theorem Vals.cells_row {B : Obj} {n T : USize} {w : Enc} {pay : Vals B T} {Y : Vals (.arr B) n}
    (hY : Vals.cells n w pay = .ok Y) (wN : Nat → Nat) (hw : ∀ i < n.toNat, (raw .i64 n w)[i]?.getD 0 = (wN i).toUInt64)
    (hT : ((List.range n.toNat).map wN).sum ≤ T.toNat) (hT63 : T.toNat < 2 ^ 63) (i : Fin n.toNat) :
    Vals.row Y i = (List.range' ((List.range i.1).map wN).sum (wN i.1)).map
      fun k => if h : k < T.toNat then Vals.row pay ⟨k, h⟩ else B.dflt := by
  obtain ⟨lo', hi', rfl, hb⟩ := Vals.cells_spec hY wN hw hT hT63
  obtain ⟨hgT, hlo, hhi⟩ := hb i
  rw [Vals.row_cell lo' hi' pay i hlo hhi (by omega) hgT hT63, Nat.add_sub_cancel_left]

/-- **`Vals.cells` keeps `Vals.WF`**: cell `i` is `[Σ_{<i} w, Σ_{≤i} w)`, inside the `T` payload rows the widths sum
to at most (`Vals.cells_spec`). -/
theorem Vals.cells_wf {B : Obj} {n T : USize} {w : Enc} {pay : Vals B T} {Y : Vals (.arr B) n}
    (hY : Vals.cells n w pay = .ok Y) (wN : Nat → Nat) (hw : ∀ i < n.toNat, (raw .i64 n w)[i]?.getD 0 = (wN i).toUInt64)
    (hT : ((List.range n.toNat).map wN).sum ≤ T.toNat) (hT63 : T.toNat < 2 ^ 63) (hp : Vals.WF pay) : Vals.WF Y := by
  obtain ⟨lo', hi', rfl, hb⟩ := Vals.cells_spec hY wN hw hT hT63
  refine ⟨fun i => ?_, hp⟩
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
theorem cellSpan_width {n m : USize} {s e : Arr .i64 n} {w : Enc} {SN EN : Nat → Nat}
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

/-- **A payload laid out by the EXPANDed widths of `X`'s cells** (`Vals.pack`, `Tab.map`): the cells `n w pay` over a
payload whose row `t` is `g` of `X`'s payload row at the gathered position `ix[t]` are `X`'s cells mapped by `g`; the
output element `d` of cell `i` is payload row `Σ_{<i} w + d` (`expand_spec`, `colPrefix_add_sum`), there `SN i + d`. -/
theorem Vals.cells_expand_row {A B : Obj} {n m : USize} {lo up : Arr .i64 n} {f : Vals A m}
    {w G u sg ix : Enc} {T : USize} (hb : ¬2 ^ 63 ≤ n.toNat * m.toNat + n.toNat + m.toNat)
    (hse : ∀ i : Fin n.toNat, 0 ≤ (lo.get i).toInt ∧ (lo.get i).toInt ≤ (up.get i).toInt ∧
      (up.get i).toInt ≤ (m.toNat : Int))
    (hw : colMap .sub n up.enc lo.enc = .ok w) (hex : expand n w = .ok (T, G, u))
    (hsg : kgather T G n lo.enc = .ok sg) (hix : colMap .add T sg u = .ok ix) (g : A.El → B.El) {pay : Vals B T}
    (hp : ∀ t : Fin T.toNat, ∃ j : Fin m.toNat, ((raw .i64 T ix)[t.1]?.getD 0).toNat = j.1 ∧
      Vals.row pay t = g (Vals.row f j))
    {Y : Vals (.arr B) n} (hY : Vals.cells n w pay = .ok Y) (i : Fin n.toNat) :
    Vals.row Y i = (Vals.row (A := .arr A) ⟨m, lo, up, f⟩ i).map g := by
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

/-- **`Vals.pack` keeps every row**: where a payload is cut, cell `i` (`[SN, EN)`, `cellSpan_spec`) is laid out at
`[Σ_{<i} w, Σ_{≤i} w)` (`Vals.cells`), whose row `Σ_{<i} w + d` is gathered from payload row `SN + d`
(`Vals.cells_expand_row` at `g = id`). -/
theorem Vals.pack_row : {A : Obj} → {n : USize} → (x : Vals A n) → {y : Vals A n} → Vals.pack x = .ok y →
    Vals.WF x → ∀ i, Vals.row y i = Vals.row x i
  | .atom _, _, x, _, h, _, i => by
    simp only [Vals.pack, pure, Except.pure, Except.ok.injEq] at h; cases h; rfl
  | .prod _ _, _, x, _, h, wx, i => by
    simp only [Vals.pack, bind, Except.bind, pure, Except.pure] at h
    split at h; · cases h
    rename_i y1 h1
    split at h; · cases h
    rename_i y2 h2
    cases h
    simp only [Vals.row, Vals.pack_row x.1 h1 wx.1, Vals.pack_row x.2 h2 wx.2]
  | .sum _ _, _, ⟨l, r, tag, idx, x, y⟩, _, h, wx, i => by
    simp only [Vals.pack, bind, Except.bind, pure, Except.pure] at h
    split at h; · cases h
    rename_i x' h1
    split at h; · cases h
    rename_i y' h2
    cases h
    simp only [Vals.row, Vals.pack_row x h1 wx.1, Vals.pack_row y h2 wx.2]
  | .arr B, n, ⟨m, lo, up, f⟩, y, h, wx, i => by
    simp only [Vals.pack] at h
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
      simp only [Vals.row, Vals.pack_row f hf' wx.2]
    rw [Except.bind_eq_ok'] at h; obtain ⟨⟨T, G, u⟩, hex, h⟩ := h; try dsimp only at h
    rw [Except.bind_eq_ok'] at h; obtain ⟨sg, hsg, h⟩ := h
    rw [Except.bind_eq_ok'] at h; obtain ⟨ix, hix, h⟩ := h
    rw [Except.bind_eq_ok'] at h; obtain ⟨g', hg', h⟩ := h
    rw [Except.bind_eq_ok'] at h; obtain ⟨p, hp, h⟩ := h
    rw [Vals.cells_expand_row hb wx.1 hw hex hsg hix id (fun t => by
      obtain ⟨j, hj, hgj⟩ := Vals.gather_row f hg' t
      exact ⟨j, hj, (Vals.pack_row g' hp (Vals.gather_wf hg' wx.2) t).trans hgj⟩) h i, List.map_id]
  | .one, _, _, _, _, _, _ => rfl

/-- **`Vals.cat` answers below `2^63` rows** (its guard), whatever its inputs. -/
theorem Vals.cat_lt {B : Obj} {n : USize} {X Y Z : Vals (.arr B) n} (h : Vals.cat X Y = .ok Z) :
    n.toNat < 2 ^ 63 := by
  obtain ⟨m₁, lo₁, up₁, f₁⟩ := X
  obtain ⟨m₂, lo₂, up₂, f₂⟩ := Y
  simp only [Vals.cat] at h
  split at h; · cases h
  omega

/-- **`Vals.cat` joins cell by cell**, below `2^63` cells (its guard): output element `d` of cell `i` (`expand_spec`)
reads the joined payload (`Vals.concat_row`) at `SN₁ + d` where `d < w₁`, else at `m₁ + SN₂ + (d - w₁)`. -/
theorem Vals.cat_row {B : Obj} {n : USize} {X Y Z : Vals (.arr B) n} (h : Vals.cat X Y = .ok Z)
    (hX : Vals.WF X) (hY : Vals.WF Y) :
    n.toNat < 2 ^ 63 ∧ ∀ i, Vals.row Z i = Vals.row X i ++ Vals.row Y i := by
  obtain ⟨m₁, lo₁, up₁, f₁⟩ := X
  obtain ⟨m₂, lo₂, up₂, f₂⟩ := Y
  simp only [Vals.cat] at h
  split at h; · cases h
  rename_i hb
  simp only [bind] at h
  rw [Except.bind_eq_ok'] at h; obtain ⟨_, -, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨⟨N, off⟩, hpl, h⟩ := h; try dsimp only at h
  rw [Except.bind_eq_ok'] at h; obtain ⟨F, hF, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨w₁, hw₁, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨w₂, hw₂, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨w, hw, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨⟨T, G, u⟩, hex, h⟩ := h; try dsimp only at h
  rw [Except.bind_eq_ok'] at h; obtain ⟨ga, hga, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨a, ha, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨sm, hsm, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨dd, hdd, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨gd, hgd, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨b, hbb, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨gw, hgw, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨c, hc, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨ab, hab, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨cab, hcab, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨ix, hix, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨g, hg, h⟩ := h
  simp only [Vals.cells, bind] at h
  rw [Except.bind_eq_ok'] at h; obtain ⟨P', hP', h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨lo', hlo', h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨hi', hhi', h⟩ := h
  cases h
  obtain ⟨hNn, hoff⟩ := catPlan_ok hpl
  have hm₁ : m₁.toNat < 2 ^ 63 := by omega
  have hm₂ : m₂.toNat < 2 ^ 63 := by omega
  have hn63 : n.toNat < 2 ^ 63 := by omega
  refine ⟨hn63, fun i => ?_⟩
  have hmU : m₁.toUInt64 = m₁.toNat.toUInt64 := UInt64.toNat_inj.mp (by simp <;> omega)
  obtain ⟨S₁, E₁, hse₁', hb₁, hrow₁⟩ := cellSpan_spec hX.1 hm₁ f₁
  obtain ⟨S₂, E₂, hse₂', hb₂, hrow₂⟩ := cellSpan_spec hY.1 hm₂ f₂
  have hw₁w : ∀ i < n.toNat, (raw .i64 n w₁)[i]?.getD 0 = (E₁ i - S₁ i).toUInt64 := fun i hi => by
    have es := (colMap_raw hw₁).2.2.2 i hi
    rw [(hse₁' i hi).2, (hse₁' i hi).1] at es; simp only [Op.eval, Except.ok.injEq] at es
    rw [← es, toUInt64_sub (hb₁ i).1]
  have hw₂w : ∀ i < n.toNat, (raw .i64 n w₂)[i]?.getD 0 = (E₂ i - S₂ i).toUInt64 := fun i hi => by
    have es := (colMap_raw hw₂).2.2.2 i hi
    rw [(hse₂' i hi).2, (hse₂' i hi).1] at es; simp only [Op.eval, Except.ok.injEq] at es
    rw [← es, toUInt64_sub (hb₂ i).1]
  obtain ⟨wN, hwN⟩ : ∃ F : Nat → Nat, ∀ i, F i = (E₁ i - S₁ i) + (E₂ i - S₂ i) := ⟨_, fun _ => rfl⟩
  have hww : ∀ i < n.toNat, (raw .i64 n w)[i]?.getD 0 = (wN i).toUInt64 := fun i hi => by
    have es := (colMap_raw hw).2.2.2 i hi
    rw [hw₁w i hi, hw₂w i hi] at es; simp only [Op.eval, Except.ok.injEq] at es
    rw [← es, hwN, ← UInt64.ofNat_add]
  have hwm : ∀ i, wN i ≤ m₁.toNat + m₂.toNat := fun i => by have := hb₁ i; have := hb₂ i; rw [hwN]; omega
  have hsum : ∀ k, ((List.range k).map wN).sum ≤ k * (m₁.toNat + m₂.toNat) := fun k => by
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
    rw [hP'w i.1 i.2, 
      sum_range_succ'] at es
    simp only [Op.eval, Except.ok.injEq, UInt64.add_zero] at es
    rw [← es]
  rw [Vals.row_cell lo' hi' g i hlo hhi (by omega) (by omega) (by omega), hrow₁ i, hrow₂ i, Nat.add_sub_cancel_left]
  apply List.ext_getElem (by simp [hwN])
  intro d h1 _
  simp only [List.length_map, List.length_range'] at h1
  have ht : ((List.range i.1).map wN).sum + d < T.toNat := by omega
  rw [List.getElem_map, List.getElem_range', Nat.one_mul, dif_pos ht]
  obtain ⟨j, hj, hgj⟩ := Vals.gather_row F hg ⟨_, ht⟩
  rw [hgj, Vals.concat_row hNn hoff f₁ f₂ hF hX.2 hY.2]
  obtain ⟨hG, hu⟩ := hrun i.1 i.2 (((List.range i.1).map wN).sum + d) (by omega) (by omega)
  rw [Nat.add_sub_cancel_left] at hu
  have hGi : ((raw .i64 T G)[((List.range i.1).map wN).sum + d]?.getD 0).toNat = i.1 := by
    rw [hG, toNat_toUInt64 (by omega)]
  have hwl : E₁ i.1 - S₁ i.1 < 2 ^ 63 := by have := hb₁ i.1; omega
  have hd63 : d < 2 ^ 63 := by omega
  -- the words at output row `t`: `a = S₁ + d`, `b = S₂ + m₁ - w₁ + d`, `c = [d < w₁]`
  have hat : (raw .i64 T a)[((List.range i.1).map wN).sum + d]?.getD 0 = (S₁ i.1 + d).toUInt64 := by
    have es := (colMap_raw ha).2.2.2 _ ht
    rw [(kgather_word hga lo₁.plain _ ht).2, hGi, (hse₁' i.1 i.2).1, hu] at es
    simp only [Op.eval, Except.ok.injEq] at es
    rw [← es, ← UInt64.ofNat_add]
  have hddw : (raw .i64 n dd)[i.1]?.getD 0 = (S₂ i.1 + m₁.toNat - (E₁ i.1 - S₁ i.1)).toUInt64 := by
    have es1 := (colMap_post hsm).2 _ i.2
    rw [(hse₂' i.1 i.2).1, hmU] at es1
    have es := (colMap_raw hdd).2.2.2 _ i.2
    simp only [Op.eval, Except.ok.injEq] at es1 es; rw [UInt64.add_comm] at es1
    have := hb₁ i.1
    rw [← es, ← es1, hw₁w i.1 i.2, ← UInt64.ofNat_add, ← toUInt64_sub (by omega)]
  have hbt : (raw .i64 T b)[((List.range i.1).map wN).sum + d]?.getD 0 =
      (S₂ i.1 + m₁.toNat - (E₁ i.1 - S₁ i.1) + d).toUInt64 := by
    have es := (colMap_raw hbb).2.2.2 _ ht
    rw [(kgather_word hgd (colMap_plain hdd) _ ht).2, hGi, hddw, hu] at es
    simp only [Op.eval, Except.ok.injEq] at es
    rw [← es, ← UInt64.ofNat_add]
  have hct : (raw .i64 T c)[((List.range i.1).map wN).sum + d]?.getD 0 =
      if d < E₁ i.1 - S₁ i.1 then 1 else 0 := by
    have es := (colMap_raw hc).2.2.2 _ ht
    rw [(kgather_word hgw (colMap_plain hw₁) _ ht).2, hGi, hw₁w i.1 i.2, hu, eval_lt_nat hd63 hwl] at es
    exact (Except.ok.inj es).symm
  have hixt : (raw .i64 T ix)[((List.range i.1).map wN).sum + d]?.getD 0 =
      if d < E₁ i.1 - S₁ i.1 then (S₁ i.1 + d).toUInt64 else (S₂ i.1 + m₁.toNat - (E₁ i.1 - S₁ i.1) + d).toUInt64 := by
    have e1 := (colMap_raw hab).2.2.2 _ ht
    have e2 := (colMap_raw hcab).2.2.2 _ ht
    have e3 := (colMap_raw hix).2.2.2 _ ht
    rw [hat, hbt] at e1; rw [hct, ← Except.ok.inj e1] at e2; rw [hbt, ← Except.ok.inj e2] at e3
    simp only [Op.eval, Except.ok.injEq] at e3
    rw [← e3]; split
    · rw [UInt64.one_mul, UInt64.add_comm, UInt64.sub_add_cancel]
    · simp
  rw [hixt] at hj
  by_cases hd : d < E₁ i.1 - S₁ i.1
  · have hS : S₁ i.1 + d < m₁.toNat := by have := hb₁ i.1; omega
    rw [if_pos hd, toNat_toUInt64 (by omega)] at hj
    rw [List.getElem_append_left (by simpa using hd), List.getElem_map, List.getElem_range', Nat.one_mul,
      dif_pos (by omega), dif_pos hS]
    congr 1; exact Fin.ext hj.symm
  · have hS : S₂ i.1 + (d - (E₁ i.1 - S₁ i.1)) < m₂.toNat := by have := hb₁ i.1; have := hb₂ i.1; rw [hwN] at h1; omega
    rw [if_neg hd, toNat_toUInt64 (by omega)] at hj
    rw [List.getElem_append_right (by simpa using hd), List.getElem_map, List.getElem_range', Nat.one_mul,
      dif_neg (by omega)]
    simp only [List.length_map, List.length_range']
    rw [dif_pos hS]
    congr 1; apply Fin.ext; simp only; have := hb₁ i.1; omega

/-- **`Vals.tau` lays row `i` out as the cell `[i, i + 1)`** over `x`, as the words of `lo` and `hi`. -/
theorem Vals.tau_spec {B : Obj} {n : USize} {x : Vals B n} {y : Vals (.arr B) n} (h : Vals.tau x = .ok y) :
    ∃ lo hi : Arr .i64 n, y = ⟨n, lo, hi, x⟩ ∧ ∀ i : Fin n.toNat,
      (raw .i64 n lo.enc)[i.1]?.getD 0 = i.1.toUInt64 ∧ (raw .i64 n hi.enc)[i.1]?.getD 0 = (i.1 + 1).toUInt64 := by
  simp only [Vals.tau, bind] at h
  rw [Except.bind_eq_ok'] at h; obtain ⟨P, hP, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨hi, hhi, h⟩ := h
  cases h
  refine ⟨P, hi, rfl, fun i => ⟨?_, ?_⟩⟩
  · unfold Arr.pos at hP; split at hP
    · rename_i o ho; cases hP; exact (shiftCol_raw ho i.1 i.2).trans (UInt64.add_zero _)
    · cases hP
  · have es := (colMap_post (colArr_ok hhi)).2 i.1 i.2
    rw [raw_pos_word i.2] at es
    simp only [Op.eval, Except.ok.injEq] at es
    rw [← es, UInt64.add_comm]; exact (UInt64.ofNat_add _ _).symm

/-- **`Vals.tau` keeps `Vals.WF`**: the cell `[i, i + 1)` is inside the `n` rows of `x`, `n` below `2^63`. -/
theorem Vals.tau_wf {B : Obj} {n : USize} {x : Vals B n} {y : Vals (.arr B) n} (h : Vals.tau x = .ok y)
    (hn : n.toNat < 2 ^ 63) (hx : Vals.WF x) : Vals.WF y := by
  obtain ⟨lo, hi, rfl, hb⟩ := Vals.tau_spec h
  exact ⟨fun i => cell_wf_nat (hb i).1 (hb i).2 (by omega) (by omega) hn, hx⟩

/-- **`Vals.tau` reads each row as its one-element cell** `[i, i + 1)` over `x`, `n` below `2^63`. -/
theorem Vals.tau_row {B : Obj} {n : USize} {x : Vals B n} {y : Vals (.arr B) n} (h : Vals.tau x = .ok y)
    (hn : n.toNat < 2 ^ 63) (i : Fin n.toNat) : Vals.row y i = [Vals.row x i] := by
  obtain ⟨P, hi, rfl, hb⟩ := Vals.tau_spec h
  rw [Vals.row_cell P hi x i (hb i).1 (hb i).2 (by omega) (by omega) hn, Nat.add_sub_cancel_left]
  simp

/-- **`Vals.zip` zips cell by cell**: output element `d` of cell `i` (`expand_spec` over the widths `min w₁ w₂`)
reads `X`'s payload at `SN₁ + d` and `Y`'s at `SN₂ + d`. -/
theorem Vals.zip_row {A B : Obj} {n : USize} {X : Vals (.arr A) n} {Y : Vals (.arr B) n}
    {Z : Vals (.arr (.prod A B)) n} (h : Vals.zip X Y = .ok Z) (hX : Vals.WF X) (hY : Vals.WF Y) :
    ∀ i, Vals.row Z i = (Vals.row X i).zip (Vals.row Y i) := by
  obtain ⟨m₁, lo₁, up₁, f₁⟩ := X
  obtain ⟨m₂, lo₂, up₂, f₂⟩ := Y
  simp only [Vals.zip] at h
  split at h; · cases h
  rename_i hb
  simp only [bind] at h
  rw [Except.bind_eq_ok'] at h; obtain ⟨_, -, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨w₁, hw₁, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨w₂, hw₂, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨w, hw, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨⟨T, G, u⟩, hex, h⟩ := h; try dsimp only at h
  rw [Except.bind_eq_ok'] at h; obtain ⟨g₁, hg₁, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨a₁, ha₁, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨x, hx, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨g₂, hg₂, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨a₂, ha₂, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨y, hy, h⟩ := h
  simp only [Vals.cells, bind] at h
  rw [Except.bind_eq_ok'] at h; obtain ⟨P', hP', h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨lo', hlo', h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨hi', hhi', h⟩ := h
  cases h
  intro i
  have hm₁ : m₁.toNat < 2 ^ 63 := by omega
  have hm₂ : m₂.toNat < 2 ^ 63 := by omega
  have hn63 : n.toNat < 2 ^ 63 := by omega
  obtain ⟨S₁, E₁, hse₁', hb₁, hrow₁⟩ := cellSpan_spec hX.1 hm₁ f₁
  obtain ⟨S₂, E₂, hse₂', hb₂, hrow₂⟩ := cellSpan_spec hY.1 hm₂ f₂
  have hw₁w : ∀ i < n.toNat, (raw .i64 n w₁)[i]?.getD 0 = (E₁ i - S₁ i).toUInt64 := fun i hi => by
    have es := (colMap_raw hw₁).2.2.2 i hi
    rw [(hse₁' i hi).2, (hse₁' i hi).1] at es; simp only [Op.eval, Except.ok.injEq] at es
    rw [← es, toUInt64_sub (hb₁ i).1]
  have hw₂w : ∀ i < n.toNat, (raw .i64 n w₂)[i]?.getD 0 = (E₂ i - S₂ i).toUInt64 := fun i hi => by
    have es := (colMap_raw hw₂).2.2.2 i hi
    rw [(hse₂' i hi).2, (hse₂' i hi).1] at es; simp only [Op.eval, Except.ok.injEq] at es
    rw [← es, toUInt64_sub (hb₂ i).1]
  obtain ⟨wN, hwN⟩ : ∃ F : Nat → Nat, ∀ i, F i = min (E₁ i - S₁ i) (E₂ i - S₂ i) := ⟨_, fun _ => rfl⟩
  have hww : ∀ i < n.toNat, (raw .i64 n w)[i]?.getD 0 = (wN i).toUInt64 := fun i hi => by
    have es := (colMap_raw hw).2.2.2 i hi
    rw [hw₁w i hi, hw₂w i hi] at es
    have h1 := hb₁ i; have h2 := hb₂ i
    have e : Op.eval .min (E₁ i - S₁ i).toUInt64 (E₂ i - S₂ i).toUInt64 = .ok (wN i).toUInt64 := by
      show Except.ok (if (E₂ i - S₂ i).toUInt64.toInt64 < (E₁ i - S₁ i).toUInt64.toInt64 then (E₂ i - S₂ i).toUInt64
        else (E₁ i - S₁ i).toUInt64) = _
      simp only [Int64.lt_iff_toInt_lt, toInt64_toInt_nat (show E₂ i - S₂ i < 2 ^ 63 by omega),
        toInt64_toInt_nat (show E₁ i - S₁ i < 2 ^ 63 by omega), hwN]
      split <;> congr 2 <;> omega
    rw [e] at es; exact (Except.ok.inj es).symm
  have hwm : ∀ i, wN i ≤ m₁.toNat + m₂.toNat := fun i => by have := hb₁ i; have := hb₂ i; rw [hwN]; omega
  have hsum : ∀ k, ((List.range k).map wN).sum ≤ k * (m₁.toNat + m₂.toNat) := fun k => by
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
    rw [hP'w i.1 i.2, 
      sum_range_succ'] at es
    simp only [Op.eval, Except.ok.injEq, UInt64.add_zero] at es
    rw [← es]
  rw [Vals.row_cell lo' hi' (B := .prod A B) (f := ((x, y) : Vals (.prod A B) T)) i hlo hhi (by omega) (by omega)
    (by omega), hrow₁ i, hrow₂ i, Nat.add_sub_cancel_left]
  apply List.ext_getElem (by simp [hwN])
  intro d h1 _
  simp only [List.length_map, List.length_range'] at h1
  have ht : ((List.range i.1).map wN).sum + d < T.toNat := by omega
  have hd₁ : d < E₁ i.1 - S₁ i.1 := by rw [hwN] at h1; omega
  have hd₂ : d < E₂ i.1 - S₂ i.1 := by rw [hwN] at h1; omega
  have hS₁ : S₁ i.1 + d < m₁.toNat := by have := hb₁ i.1; omega
  have hS₂ : S₂ i.1 + d < m₂.toNat := by have := hb₂ i.1; omega
  rw [List.getElem_map, List.getElem_range', Nat.one_mul, dif_pos ht, List.getElem_zip, List.getElem_map,
    List.getElem_map, List.getElem_range', List.getElem_range', Nat.one_mul, dif_pos hS₁, dif_pos hS₂]
  obtain ⟨hG, hu⟩ := hrun i.1 i.2 (((List.range i.1).map wN).sum + d) (by omega) (by omega)
  rw [Nat.add_sub_cancel_left] at hu
  have hGi : ((raw .i64 T G)[((List.range i.1).map wN).sum + d]?.getD 0).toNat = i.1 := by
    rw [hG, toNat_toUInt64 (by omega)]
  have ha₁t : (raw .i64 T a₁)[((List.range i.1).map wN).sum + d]?.getD 0 = (S₁ i.1 + d).toUInt64 := by
    have es := (colMap_raw ha₁).2.2.2 _ ht
    rw [(kgather_word hg₁ lo₁.plain _ ht).2, hGi, (hse₁' i.1 i.2).1, hu] at es
    simp only [Op.eval, Except.ok.injEq] at es
    rw [← es, ← UInt64.ofNat_add]
  have ha₂t : (raw .i64 T a₂)[((List.range i.1).map wN).sum + d]?.getD 0 = (S₂ i.1 + d).toUInt64 := by
    have es := (colMap_raw ha₂).2.2.2 _ ht
    rw [(kgather_word hg₂ lo₂.plain _ ht).2, hGi, (hse₂' i.1 i.2).1, hu] at es
    simp only [Op.eval, Except.ok.injEq] at es
    rw [← es, ← UInt64.ofNat_add]
  obtain ⟨j₁, hj₁, hxj⟩ := Vals.gather_row f₁ hx ⟨_, ht⟩
  obtain ⟨j₂, hj₂, hyj⟩ := Vals.gather_row f₂ hy ⟨_, ht⟩
  rw [ha₁t, toNat_toUInt64 (by omega)] at hj₁
  rw [ha₂t, toNat_toUInt64 (by omega)] at hj₂
  show (Vals.row x ⟨_, ht⟩, Vals.row y ⟨_, ht⟩) = _
  have e1 : j₁ = ⟨S₁ i.1 + d, hS₁⟩ := Fin.ext hj₁.symm
  have e2 : j₂ = ⟨S₂ i.1 + d, hS₂⟩ := Fin.ext hj₂.symm
  rw [hxj, hyj, e1, e2]


/-- **`Vals.cat` keeps `Vals.WF`**: widths `w₁ + w₂ ≤ m₁ + m₂` over the joined payloads gathered. -/
theorem Vals.cat_wf {B : Obj} {n : USize} {X Y Z : Vals (.arr B) n} (h : Vals.cat X Y = .ok Z) (hX : Vals.WF X)
    (hY : Vals.WF Y) : Vals.WF Z := by
  obtain ⟨m₁, lo₁, up₁, f₁⟩ := X
  obtain ⟨m₂, lo₂, up₂, f₂⟩ := Y
  simp only [Vals.cat] at h
  split at h; · cases h
  rename_i hb
  simp only [bind] at h
  rw [Except.bind_eq_ok'] at h; obtain ⟨_, -, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨⟨N, off⟩, hpl, h⟩ := h; try dsimp only at h
  rw [Except.bind_eq_ok'] at h; obtain ⟨F, hF, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨w₁, hw₁, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨w₂, hw₂, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨w, hw, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨⟨T, G, u⟩, hex, h⟩ := h; try dsimp only at h
  rw [Except.bind_eq_ok'] at h; obtain ⟨ga, hga, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨a, ha, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨sm, hsm, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨dd, hdd, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨gd, hgd, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨b, hbb, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨gw, hgw, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨c, hc, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨ab, hab, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨cab, hcab, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨ix, hix, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨g, hg, h⟩ := h
  obtain ⟨hNn, hoff⟩ := catPlan_ok hpl
  have hm₁ : m₁.toNat < 2 ^ 63 := by omega
  have hm₂ : m₂.toNat < 2 ^ 63 := by omega
  obtain ⟨S₁, E₁, hse₁', hb₁, -⟩ := cellSpan_spec hX.1 hm₁ f₁
  obtain ⟨S₂, E₂, hse₂', hb₂, -⟩ := cellSpan_spec hY.1 hm₂ f₂
  refine Vals.cells_expand_wf hex h (m₁.toNat + m₂.toNat) (fun i hi => ?_) (by omega) (by omega)
    (Vals.gather_wf hg (Vals.concat_wf hNn hoff hF hX.2 hY.2))
  obtain ⟨x₁, y₁⟩ := cellSpan_width hse₁' hb₁ hw₁ i hi
  obtain ⟨x₂, y₂⟩ := cellSpan_width hse₂' hb₂ hw₂ i hi
  have es := (colMap_raw hw).2.2.2 i hi
  rw [x₁, x₂] at es; simp only [Op.eval, Except.ok.injEq] at es
  rw [← es, ← UInt64.ofNat_add, toNat_toUInt64 (by omega)]; omega

/-- **`Vals.zip` keeps `Vals.WF`**: widths `min w₁ w₂`, each one of `w₁ ≤ m₁`, `w₂ ≤ m₂`, over both payloads
gathered. -/
theorem Vals.zip_wf {A B : Obj} {n : USize} {X : Vals (.arr A) n} {Y : Vals (.arr B) n}
    {Z : Vals (.arr (.prod A B)) n} (h : Vals.zip X Y = .ok Z) (hX : Vals.WF X) (hY : Vals.WF Y) : Vals.WF Z := by
  obtain ⟨m₁, lo₁, up₁, f₁⟩ := X
  obtain ⟨m₂, lo₂, up₂, f₂⟩ := Y
  simp only [Vals.zip] at h
  split at h; · cases h
  rename_i hb
  simp only [bind] at h
  rw [Except.bind_eq_ok'] at h; obtain ⟨_, -, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨w₁, hw₁, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨w₂, hw₂, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨w, hw, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨⟨T, G, u⟩, hex, h⟩ := h; try dsimp only at h
  rw [Except.bind_eq_ok'] at h; obtain ⟨g₁, hg₁, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨a₁, ha₁, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨x, hx, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨g₂, hg₂, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨a₂, ha₂, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨y, hy, h⟩ := h
  have hm₁ : m₁.toNat < 2 ^ 63 := by omega
  have hm₂ : m₂.toNat < 2 ^ 63 := by omega
  obtain ⟨S₁, E₁, hse₁', hb₁, -⟩ := cellSpan_spec hX.1 hm₁ f₁
  obtain ⟨S₂, E₂, hse₂', hb₂, -⟩ := cellSpan_spec hY.1 hm₂ f₂
  refine Vals.cells_expand_wf hex h (m₁.toNat + m₂.toNat) (fun i hi => ?_) (by omega) (by omega)
    ⟨Vals.gather_wf hx hX.2, Vals.gather_wf hy hY.2⟩
  obtain ⟨x₁, y₁⟩ := cellSpan_width hse₁' hb₁ hw₁ i hi
  obtain ⟨x₂, y₂⟩ := cellSpan_width hse₂' hb₂ hw₂ i hi
  have es := (colMap_raw hw).2.2.2 i hi
  rw [x₁, x₂] at es; simp only [Op.eval, Except.ok.injEq] at es
  rw [← es]; split <;> rw [toNat_toUInt64 (by omega)] <;> omega

namespace Tab
variable {K B : Obj}

/-- **`cat P` denotes `P ≫ cat`**: each `(xs, ys)` of `P` to `xs ++ ys` (`Vals.cat_row`). -/
theorem cat_holds {P : Tab K (.prod (.arr B) (.arr B))} {T : Tab K (.arr B)} (h : Tab.cat P = .ok T) (hP : P.WF)
    (k : K.El) (zs : List B.El) : T.Holds k zs ↔ ∃ p, P.Holds k p ∧ zs = p.1 ++ p.2 := by
  simp only [Tab.cat, bind] at h
  rw [Except.bind_eq_ok'] at h; obtain ⟨Z, hZ, h⟩ := h
  rw [canon_holds h ⟨hP.1, Vals.cat_wf hZ hP.2.1 hP.2.2⟩]
  obtain ⟨-, hrow⟩ := Vals.cat_row hZ hP.2.1 hP.2.2
  simp only [Tab.Holds]
  constructor
  · rintro ⟨j, rfl, rfl⟩; exact ⟨_, ⟨j, rfl, rfl⟩, hrow j⟩
  · rintro ⟨p, ⟨j, rfl, rfl⟩, rfl⟩; exact ⟨j, rfl, hrow j⟩

/-- **`snoc P` denotes `P ≫ snoc`**: each `(xs, a)` of `P` to `xs ++ [a]` (`Vals.cat_row` after `Vals.tau_row`). -/
theorem snoc_holds {P : Tab K (.prod (.arr B) B)} {T : Tab K (.arr B)} (h : Tab.snoc P = .ok T) (hP : P.WF)
    (k : K.El) (ys : List B.El) : T.Holds k ys ↔ ∃ p, P.Holds k p ∧ ys = p.1 ++ [p.2] := by
  simp only [Tab.snoc, bind] at h
  rw [Except.bind_eq_ok'] at h; obtain ⟨t, ht, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨Z, hZ, h⟩ := h
  rw [canon_holds h ⟨hP.1, Vals.cat_wf hZ hP.2.1 (Vals.tau_wf ht (Vals.cat_lt hZ) hP.2.2)⟩]
  obtain ⟨hn, hrow⟩ := Vals.cat_row hZ hP.2.1 (Vals.tau_wf ht (Vals.cat_lt hZ) hP.2.2)
  simp only [Tab.Holds]
  constructor
  · rintro ⟨j, rfl, rfl⟩; exact ⟨_, ⟨j, rfl, rfl⟩, by rw [hrow j, Vals.tau_row ht hn j]; rfl⟩
  · rintro ⟨p, ⟨j, rfl, rfl⟩, rfl⟩; exact ⟨j, rfl, by rw [hrow j, Vals.tau_row ht hn j]; rfl⟩

/-- **`cons P` denotes `P ≫ cons`**: each `(a, xs)` of `P` to `a :: xs` (`Vals.cat_row` after `Vals.tau_row`). -/
theorem cons_holds {P : Tab K (.prod B (.arr B))} {T : Tab K (.arr B)} (h : Tab.cons P = .ok T) (hP : P.WF)
    (k : K.El) (ys : List B.El) : T.Holds k ys ↔ ∃ p, P.Holds k p ∧ ys = p.1 :: p.2 := by
  simp only [Tab.cons, bind] at h
  rw [Except.bind_eq_ok'] at h; obtain ⟨t, ht, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨Z, hZ, h⟩ := h
  rw [canon_holds h ⟨hP.1, Vals.cat_wf hZ (Vals.tau_wf ht (Vals.cat_lt hZ) hP.2.1) hP.2.2⟩]
  obtain ⟨hn, hrow⟩ := Vals.cat_row hZ (Vals.tau_wf ht (Vals.cat_lt hZ) hP.2.1) hP.2.2
  simp only [Tab.Holds]
  constructor
  · rintro ⟨j, rfl, rfl⟩; exact ⟨_, ⟨j, rfl, rfl⟩, by rw [hrow j, Vals.tau_row ht hn j]; rfl⟩
  · rintro ⟨p, ⟨j, rfl, rfl⟩, rfl⟩; exact ⟨j, rfl, by rw [hrow j, Vals.tau_row ht hn j]; rfl⟩

/-- **`zip P` denotes `P ≫ zip`**: each `(xs, ys)` of `P` to `xs.zip ys` (`Vals.zip_row`). -/
theorem zip_holds {A : Obj} {P : Tab K (.prod (.arr A) (.arr B))} {T : Tab K (.arr (.prod A B))}
    (h : Tab.zip P = .ok T) (wP : P.WF) (k : K.El) (zs : (Obj.arr (.prod A B)).El) :
    T.Holds k zs ↔ ∃ p, P.Holds k p ∧ zs = p.1.zip p.2 := by
  simp only [Tab.zip, bind] at h
  rw [Except.bind_eq_ok'] at h; obtain ⟨Z, hZ, h⟩ := h
  rw [canon_holds h ⟨wP.1, Vals.zip_wf hZ wP.2.1 wP.2.2⟩]
  have hrow := Vals.zip_row hZ wP.2.1 wP.2.2
  simp only [Tab.Holds]
  constructor
  · rintro ⟨j, rfl, rfl⟩; exact ⟨_, ⟨j, rfl, rfl⟩, hrow j⟩
  · rintro ⟨p, ⟨j, rfl, rfl⟩, rfl⟩; exact ⟨j, rfl, hrow j⟩

/-- **`length X` denotes `length` on the arrays `X`**: each cell `[SN, EN)` (`cellSpan_spec`) to its width
`EN - SN`. -/
theorem length_holds {n : USize} {X : Vals (.arr B) n} {T : Tab (.arr B) .long} (h : Tab.length X = .ok T)
    (hX : Vals.WF X) (xs : List B.El) (w : Int64) : T.Holds xs w ↔ (∃ i, X.row i = xs) ∧ w = Int64.ofNat xs.length := by
  obtain ⟨m, lo, up, f⟩ := X
  dsimp only [Tab.length] at h
  split at h; · cases h
  rename_i hb
  simp only [bind] at h
  rw [Except.bind_eq_ok'] at h; obtain ⟨_, -, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨wd, hwd, h⟩ := h
  rw [canon_holds h ⟨hX, trivial⟩]
  have hm63 : m.toNat < 2 ^ 63 := by omega
  obtain ⟨SN, EN, hw1, hb1, hrow⟩ := cellSpan_spec hX.1 hm63 f
  have hv : ∀ i : Fin n.toNat,
      Vals.row (A := .long) wd i = Int64.ofNat (Vals.row (A := .arr B) ⟨m, lo, up, f⟩ i).length := by
    intro i
    have es := (colMap_raw (colArr_ok hwd)).2.2.2 i.1 i.2
    rw [(hw1 i.1 i.2).2, (hw1 i.1 i.2).1] at es; simp only [Op.eval, Except.ok.injEq] at es
    rw [hrow i, List.length_map, List.length_range', Vals.row_atom, Arr.get_i64, ← es,
      ← toUInt64_sub (hb1 i).1]
    rfl
  simp only [Tab.Holds]
  constructor
  · rintro ⟨i, rfl, rfl⟩; exact ⟨⟨i, rfl⟩, hv i⟩
  · rintro ⟨⟨i, rfl⟩, rfl⟩; exact ⟨i, rfl, hv i⟩

end Tab

/-- A `foR` column read as booleans is its words read at `i64`, each cut to its low bit. -/
theorem raw_u1_foR (n : USize) (md pk : ByteArray) :
    raw .u1 n (.foR md pk : Enc) = (raw .i64 n (.foR md pk : Enc)).map fun w => UInt64.ofNat (w.toNat % 2) := by
  simp only [raw, QAtomicType.width, Array.map_map]
  refine Array.ext (by simp) fun j _ _ => ?_
  simp

/-- Folding `op` over columns of `n` words reversed, at row `n - 1 - i`, is folding it over the columns at row `i`. -/
theorem foldlM_reverse_row {op : Op} {n i : Nat} (hi : i < n) : ∀ (l : List (Array UInt64)) (a : UInt64),
    (∀ x ∈ l, x.size = n) → (l.map (·.reverse)).foldlM (fun a x => op.eval a (x[n - 1 - i]?.getD 0)) a =
      l.foldlM (fun a x => op.eval a (x[i]?.getD 0)) a
  | [], _, _ => rfl
  | x :: l, a, hl => by
    have hx := hl x List.mem_cons_self
    simp only [List.map_cons, List.foldlM_cons]
    rw [Array.getElem?_reverse (by omega), hx, show n - 1 - (n - 1 - i) = i by omega]
    congr 1; funext b; exact foldlM_reverse_row hi l b fun y hy => hl y (List.mem_cons_of_mem _ hy)

/-- **The backward `kscan`** (`rev`, `raw_kscan` read in forward row order): row `i` of the answer, read at `t`, is the
cut of `out[i]`, which is `op` folded over the columns after the first at row `i`, from the next row's `out[i + 1]`, or
from the first column's row `i` where `seg` starts a segment there (the last row always). -/
theorem raw_kscan_rev {op : Op} {s t : QAtomicType} {w : Nat} (ht : t.width = some w) {n : USize} {seg c : Enc}
    {cs : List Enc} {r : Enc × Option UInt64} (h : kscan op true s t n seg (c :: cs) = .ok r) :
    ∃ out : Array UInt64, out.size = n.toNat ∧
      r.1.raw t n = out.map (fun v => UInt64.ofNat (v.toNat % 2 ^ (if t = .u1 then 1 else 8 * w))) ∧
      ∀ i (hi : i < out.size), (cs.map (·.raw s n)).foldlM (fun a x => op.eval a (x[i]?.getD 0))
        (if i + 1 < n.toNat ∧ (seg.raw .u1 n)[i]?.getD 0 = 0 then out[i + 1]?.getD 0 else (c.raw s n)[i]?.getD 0) =
          .ok out[i] := by
  obtain ⟨hg, hxs, c', cs', hc, out, hos, he, -, hrow⟩ := raw_kscan op true s t w ht n seg (c :: cs) r h
  simp only [List.cons.injEq] at hc; obtain ⟨h1, h2⟩ := hc; subst h1; subst h2
  simp only [if_true] at he hrow
  refine ⟨out.reverse, by simp [hos], by rw [he], fun i hi => ?_⟩
  simp only [Array.size_reverse] at hi
  have := hrow (n.toNat - 1 - i) (by omega)
  have hcs : ∀ x ∈ cs.map (raw s n), x.size = n.toNat := fun x hx => by
    obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx; exact hxs y (List.mem_cons_of_mem _ hy)
  have hc := hxs c List.mem_cons_self
  rw [foldlM_reverse_row (by omega) _ _ hcs, Array.getElem?_reverse (by omega), Array.getElem?_reverse (by omega), hg,
    hc, show n.toNat - 1 - (n.toNat - 1 - i) = i by omega] at this
  have e : out.reverse[i] = out[n.toNat - 1 - i]'(by omega) := by simp [Array.getElem_reverse, hos]
  rw [e]
  by_cases hl : i + 1 < n.toNat
  · have e2 : out.reverse[i + 1]? = out[n.toNat - 1 - i - 1]? := by
      rw [Array.getElem?_reverse (by omega), hos]; congr 1
    rw [e2]
    simpa only [show 0 < n.toNat - 1 - i by omega, true_and, hl] using this
  · simpa only [show ¬ 0 < n.toNat - 1 - i by omega, false_and, hl, if_false] using this

/-- An `or` fold of `0`/`1` words from a `0`/`1` word is `0`/`1`, and `0` exactly when every word is. -/
theorem foldl_or01 : ∀ (l : List UInt64) (a : UInt64), (a = 0 ∨ a = 1) → (∀ y ∈ l, y = 0 ∨ y = 1) →
    (l.foldl (· ||| ·) a = 0 ∨ l.foldl (· ||| ·) a = 1) ∧ (l.foldl (· ||| ·) a = 0 ↔ a = 0 ∧ ∀ y ∈ l, y = 0)
  | [], a, ha, _ => by simpa using ha
  | y :: l, a, ha, hl => by
    have hy := hl y List.mem_cons_self
    have hay : (a ||| y = 0 ∨ a ||| y = 1) ∧ (a ||| y = 0 ↔ a = 0 ∧ y = 0) := by
      rcases ha with rfl | rfl <;> rcases hy with rfl | rfl <;> decide
    obtain ⟨h1, h2⟩ := foldl_or01 l (a ||| y) hay.1 fun z hz => hl z (List.mem_cons_of_mem _ hz)
    simp only [List.foldl_cons, List.forall_mem_cons]
    exact ⟨h1, h2.trans (by rw [hay.2, and_assoc])⟩

/-- The wrapping `+` fold of longs, read as words, is the words' `+` fold. -/
theorem foldl_add_toUInt64 : ∀ (xs : List Int64) (a : UInt64),
    (xs.map Int64.toUInt64).foldl (· + ·) a = a + (xs.foldr (· + ·) 0).toUInt64
  | [], a => by simp; rfl
  | x :: xs, a => by
    simp only [List.map_cons, List.foldl_cons, List.foldr_cons, Int64.toUInt64_add, foldl_add_toUInt64 xs]
    rw [UInt64.add_assoc]

/-- **A long `a + b` is exact** when it is not the null and does not overflow (`a` and `b` of one sign, `a + b` of the
other): exactly when `a + b` lies strictly inside `(-2^63, 2^63)`. -/
theorem Int64.add_exact_iff (a b : Int64) : (a + b ≠ Alg.nul ∧ ¬((a < 0 ↔ b < 0) ∧ ¬(a < 0 ↔ a + b < 0))) ↔
    -2 ^ 63 < a.toInt + b.toInt ∧ a.toInt + b.toInt < 2 ^ 63 := by
  have := Int64.le_toInt a; have := Int64.toInt_lt a; have := Int64.le_toInt b; have := Int64.toInt_lt b
  have hs := Int64.toInt_add a b
  rw [Int.bmod_def] at hs
  simp only [Int64.lt_iff_toInt_lt, Int64.toInt_zero, ne_eq, ← Int64.toInt_inj, Alg.nul, Int64.toInt_minValue, hs]
  split at hs <;> omega

/-- **The rows EXPAND names group `g` are its run** `[Σ_{<g} w, Σ_{<g} w + w g)` (`expand_spec`). -/
theorem expand_group_run {K T : USize} {w G u : Enc} (h : expand K w = .ok (T, G, u)) (wN : Nat → Nat)
    (hw : ∀ g < K.toNat, (raw .i64 K w)[g]?.getD 0 = (wN g).toUInt64)
    (hs : ((List.range K.toNat).map wN).sum < 2 ^ 63) (hK : K.toNat < 2 ^ 63) : ∀ g < K.toNat,
    (List.range T.toNat).filter (fun k => ((raw .i64 T G)[k]?.getD 0).toNat = g) =
      List.range' ((List.range g).map wN).sum (wN g) := fun g hg => by
  obtain ⟨hTn, hrun⟩ := expand_spec h wN hw hs hK
  obtain ⟨off, hoff⟩ : ∃ F : Nat → Nat, ∀ g, F g = ((List.range g).map wN).sum := ⟨_, fun _ => rfl⟩
  simp only [← hoff] at hrun hTn ⊢
  have hgS : off g + wN g ≤ T.toNat := by
    rw [hTn, hoff, hoff, ← sum_range_succ']; exact sum_range_mono wN hg
  have hnot : ∀ t < T.toNat, (t < off g ∨ off g + wN g ≤ t) → ((raw .i64 T G)[t]?.getD 0).toNat ≠ g :=
    fun t ht ho => by
      obtain ⟨g', hg', h1, h2⟩ := exists_group wN K.toNat t (by rw [← hoff, ← hTn]; exact ht)
      simp only [← hoff] at h1 h2
      rw [(hrun g' hg' t h1 h2).1, toNat_toUInt64 (by omega)]; rintro rfl; omega
  rw [List.range_eq_range', show T.toNat = off g + (wN g + (T.toNat - off g - wN g)) by omega,
    ← List.range'_append_1, ← List.range'_append_1, List.filter_append, List.filter_append,
    List.filter_eq_nil_iff.2 (fun t ht => by
      rw [List.mem_range'_1] at ht; simpa using hnot t (by omega) (by omega)),
    List.filter_eq_self.2 (fun t ht => by
      rw [List.mem_range'_1] at ht
      have := (hrun g hg t (by omega) (by omega)).1
      simp [this, toNat_toUInt64 (show g < 2 ^ 64 by omega)]),
    List.filter_eq_nil_iff.2 (fun t ht => by
      rw [List.mem_range'_1] at ht; simpa using hnot t (by omega) (by omega))]
  simp

theorem eval_eq_word {a b o : UInt64} (h : Op.eval .eq a b = .ok o) : o = if a = b then 1 else 0 := by
  have e : Op.eval .eq a b = .ok (if (a == b) = true then 1 else 0) := rfl
  rw [e, Except.ok.injEq] at h; rw [← h]; simp only [beq_iff_eq]

theorem eval_ne_word {a b o : UInt64} (h : Op.eval .ne a b = .ok o) : o = if a ≠ b then 1 else 0 := by
  have e : Op.eval .ne a b = .ok (if (a != b) = true then 1 else 0) := rfl
  rw [e, Except.ok.injEq] at h; rw [← h]; simp only [bne_iff_ne]

theorem eval_lt_word {a b o : UInt64} (h : Op.eval .lt a b = .ok o) : o = if a.toInt64 < b.toInt64 then 1 else 0 := by
  have e : Op.eval .lt a b = .ok (if decide (a.toInt64 < b.toInt64) = true then 1 else 0) := rfl
  rw [e, Except.ok.injEq] at h; rw [← h]; simp only [decide_eq_true_eq]

/-- **A row's bad word** (`Tab.sum`, `Tab.sums`): `0`/`1`, and `0` exactly when the element `v` and the sum `W` are
not the null and `W = (W - v) + v` did not wrap (the signs of `v`, `W - v` agree and differ from `W`'s). -/
theorem badWord_spec {N : USize} {v W sv d sd e1 sw e2 ovf eW ev o1 bad : Enc}
    (hsv : colMap .first N v v .i64 .i64 [] [(.gt, 0)] = .ok sv) (hd : colMap .sub N W v = .ok d)
    (hsd : colMap .first N d d .i64 .i64 [] [(.gt, 0)] = .ok sd) (he1 : colMap .eq N sv sd = .ok e1)
    (hsw : colMap .first N W W .i64 .i64 [] [(.gt, 0)] = .ok sw)
    (he2 : colMap .ne N sv sw = .ok e2) (hovf : colMap .and N e1 e2 = .ok ovf)
    (heW : colMap .first N W W .i64 .i64 [] [(.eq, 0x8000000000000000)] = .ok eW)
    (hev : colMap .first N v v .i64 .i64 [] [(.eq, 0x8000000000000000)] = .ok ev)
    (ho1 : colMap .or N eW ev = .ok o1) (hbad : colMap .or N ovf o1 = .ok bad) :
    ∀ t < N.toNat, ((raw .i64 N bad)[t]?.getD 0 = 0 ∨ (raw .i64 N bad)[t]?.getD 0 = 1) ∧
      ((raw .i64 N bad)[t]?.getD 0 = 0 ↔ ((raw .i64 N v)[t]?.getD 0).toInt64 ≠ Alg.nul ∧
        ((raw .i64 N W)[t]?.getD 0).toInt64 ≠ Alg.nul ∧
        ¬((((raw .i64 N v)[t]?.getD 0).toInt64 < 0 ↔
            ((raw .i64 N W)[t]?.getD 0 - (raw .i64 N v)[t]?.getD 0).toInt64 < 0) ∧
          ¬(((raw .i64 N v)[t]?.getD 0).toInt64 < 0 ↔ ((raw .i64 N W)[t]?.getD 0).toInt64 < 0))) := by
  intro t ht
  -- `(.gt, 0)` reads `x < 0`, `(.eq, c)` reads `c = x`: the post step's constant is the left operand
  have lt0 : ∀ {a e : Enc}, colMap .first N a a .i64 .i64 [] [(.gt, 0)] = .ok e →
      (raw .i64 N e)[t]?.getD 0 = if ((raw .i64 N a)[t]?.getD 0).toInt64 < (0 : UInt64).toInt64 then 1 else 0 :=
    fun h => eval_lt_word (b := 0) ((colMap_post h).2 t ht)
  have hsv' := lt0 hsv
  have hd' := (colMap_raw hd).2.2.2 t ht; simp only [Op.eval, Except.ok.injEq] at hd'
  have hsd' := lt0 hsd
  have he1' := eval_eq_word ((colMap_raw he1).2.2.2 t ht)
  have hsw' := lt0 hsw
  have he2' := eval_ne_word ((colMap_raw he2).2.2.2 t ht)
  have hovf' := (colMap_raw hovf).2.2.2 t ht; simp only [Op.eval, Except.ok.injEq] at hovf'
  have heW' := eval_eq_word ((colMap_post heW).2 t ht)
  have hev' := eval_eq_word ((colMap_post hev).2 t ht)
  simp only [eq_comm (a := (0x8000000000000000 : UInt64))] at heW' hev'
  have ho1' := (colMap_raw ho1).2.2.2 t ht; simp only [Op.eval, Except.ok.injEq] at ho1'
  have hbad' := (colMap_raw hbad).2.2.2 t ht; simp only [Op.eval, Except.ok.injEq] at hbad'
  rw [← hd'] at hsd'
  rw [← hbad', ← ho1', ← hovf', he1', he2', hsv', hsd', hsw', heW', hev']
  have hn : ∀ x : UInt64, x = 0x8000000000000000 ↔ x.toInt64 = Alg.nul := fun x =>
    ⟨fun h => by rw [h]; decide, fun h => by rw [← UInt64.toUInt64_toInt64 x, h]; decide⟩
  simp only [hn, show (0 : UInt64).toInt64 = 0 from rfl]
  generalize ((raw .i64 N W)[t]?.getD 0 - (raw .i64 N v)[t]?.getD 0).toInt64 = q
  generalize ((raw .i64 N W)[t]?.getD 0).toInt64 = sW
  generalize ((raw .i64 N v)[t]?.getD 0).toInt64 = sV
  by_cases p1 : sV < 0 <;> by_cases p2 : q < 0 <;> by_cases p3 : sW < 0 <;> by_cases p4 : sW = Alg.nul <;>
    by_cases p5 : sV = Alg.nul <;> simp (config := { decide := true }) [p1, p2, p3, p4, p5]

/-- An `i64` column gathered (`Arr.gather`) reads at `j` the word of `x` at `ix[j]`. -/
theorem Arr.gather_raw {m n : USize} {ix : Enc} (x : Arr .i64 n) {y : Arr .i64 m} (h : Arr.gather m ix x = .ok y)
    (j : Fin m.toNat) : ∃ i : Fin n.toNat, ((raw .i64 m ix)[j.1]?.getD 0).toNat = i.1 ∧
      (raw .i64 m y.enc)[j.1]?.getD 0 = (raw .i64 n x.enc)[i.1]?.getD 0 := by
  obtain ⟨i, hi, e⟩ := Arr.gather_row x h j
  rw [Arr.get_i64, Arr.get_i64] at e
  exact ⟨i, hi, by simpa using congrArg Int64.toUInt64 e⟩

namespace Tab
variable {B : Obj}

/-- **`uncons` keeps `Tab.WF`**: the rest of a non-empty cell `[SN, EN)` is `[SN + 1, EN)`, `EN ≤ m`
(`cellSpan_where`). -/
private theorem uncons_pre_wf {n m M : USize} {lo up : Arr .i64 n} {f : Vals B m} {lt sel : Enc}
    {sM l eM : Arr .i64 M} {gX : Vals (.arr B) M} {gf : Vals B M}
    (hX : Vals.WF (A := .arr B) (n := n) ⟨m, (lo, up, f)⟩) (hm63 : m.toNat < 2 ^ 63)
    (hlt : colMap Op.lt n lo.enc up.enc = .ok lt) (hwh : whereCol n lt = .ok (M, sel))
    (hsM : Arr.gather M sel lo = .ok sM) (hgX : Vals.gather M sel (A := .arr B) (n := n) ⟨m, (lo, up, f)⟩ = .ok gX)
    (hgf : Vals.gather M sM.enc f = .ok gf)
    (hl : colArr Op.first M sM.enc sM.enc .i64 .i64 [] [(Op.add, 1)] = .ok l)
    (heM : Arr.gather M sel up = .ok eM) :
    Tab.WF (⟨M, gX, (gf, ⟨m, (l, eM, f)⟩)⟩ : Tab (.arr B) (.prod B (.arr B))) := by
  obtain ⟨SN, EN, hw1, hb1, -, hsel, -⟩ := cellSpan_where hX.1 hlt hwh hm63 f
  refine ⟨Vals.gather_wf hgX hX, Vals.gather_wf hgf hX.2, fun j => ?_, hX.2⟩
  obtain ⟨i, hi, es⟩ := Arr.gather_raw lo hsM j
  obtain ⟨i', hi', ee⟩ := Arr.gather_raw up heM j
  obtain rfl : i = i' := Fin.ext (hi.symm.trans hi')
  have hlt' := (hsel j.1 j.2).2
  rw [hi] at hlt'
  have hEm : EN i ≤ m.toNat := by have := hb1 i; omega
  have hlw : (raw .i64 M l.enc)[j.1]?.getD 0 = (SN i + 1).toUInt64 := by
    have es' := (colMap_post (colArr_ok hl)).2 j.1 j.2
    rw [es, (hw1 i i.2).1] at es'
    simp only [Op.eval, Except.ok.injEq] at es'
    rw [← es', UInt64.add_comm]; exact (UInt64.ofNat_add _ _).symm
  exact cell_wf_nat hlw (ee.trans (hw1 i i.2).2) (by omega) hEm hm63

theorem uncons_wf {n : USize} {X : Vals (.arr B) n} {t : Tab (.arr B) (.prod B (.arr B))} (h : Tab.uncons X = .ok t)
    (hX : Vals.WF X) : t.WF := by
  obtain ⟨m, lo, up, f⟩ := X
  simp only [Tab.uncons] at h
  split at h; · cases h
  rename_i hb
  simp only [bind] at h
  rw [Except.bind_eq_ok'] at h; obtain ⟨_, -, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨lt, hlt, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨⟨M, sel⟩, hwh, h⟩ := h; try dsimp only at h
  rw [Except.bind_eq_ok'] at h; obtain ⟨sM, hsM, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨gX, hgX, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨gf, hgf, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨l, hl, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨eM, heM, h⟩ := h
  exact canon_wf h (uncons_pre_wf hX (by omega) hlt hwh hsM hgX hgf hl heM)

/-- **`unsnoc` keeps `Tab.WF`**: the front of a non-empty cell `[SN, EN)` is `[SN, EN - 1)`, `EN ≤ m`
(`cellSpan_where`). -/
private theorem unsnoc_pre_wf {n m M : USize} {lo up : Arr .i64 n} {f : Vals B m} {lt sel : Enc}
    {eM l sM : Arr .i64 M} {gX : Vals (.arr B) M} {gf : Vals B M}
    (hX : Vals.WF (A := .arr B) (n := n) ⟨m, (lo, up, f)⟩) (hm63 : m.toNat < 2 ^ 63)
    (hlt : colMap Op.lt n lo.enc up.enc = .ok lt) (hwh : whereCol n lt = .ok (M, sel))
    (heM : Arr.gather M sel up = .ok eM)
    (hl : colArr Op.first M eM.enc eM.enc .i64 .i64 [] [(Op.add, 0 - 1)] = .ok l)
    (hgX : Vals.gather M sel (A := .arr B) (n := n) ⟨m, (lo, up, f)⟩ = .ok gX) (hsM : Arr.gather M sel lo = .ok sM)
    (hgf : Vals.gather M l.enc f = .ok gf) :
    Tab.WF (⟨M, gX, (⟨m, (sM, l, f)⟩, gf)⟩ : Tab (.arr B) (.prod (.arr B) B)) := by
  obtain ⟨SN, EN, hw1, hb1, -, hsel, -⟩ := cellSpan_where hX.1 hlt hwh hm63 f
  refine ⟨Vals.gather_wf hgX hX, ⟨fun j => ?_, hX.2⟩, Vals.gather_wf hgf hX.2⟩
  obtain ⟨i, hi, es⟩ := Arr.gather_raw lo hsM j
  obtain ⟨i', hi', ee⟩ := Arr.gather_raw up heM j
  obtain rfl : i = i' := Fin.ext (hi.symm.trans hi')
  have hlt' := (hsel j.1 j.2).2
  rw [hi] at hlt'
  have hEm : EN i ≤ m.toNat := by have := hb1 i; omega
  have hlw : (raw .i64 M l.enc)[j.1]?.getD 0 = (EN i - 1).toUInt64 := by
    have es' := (colMap_post (colArr_ok hl)).2 j.1 j.2
    rw [ee, (hw1 i i.2).2] at es'
    simp only [Op.eval, Except.ok.injEq] at es'
    rw [← es', neg_add_word, toUInt64_sub (by omega)]; rfl
  exact cell_wf_nat (es.trans (hw1 i i.2).1) hlw (by omega) (by omega) hm63

theorem unsnoc_wf {n : USize} {X : Vals (.arr B) n} {t : Tab (.arr B) (.prod (.arr B) B)} (h : Tab.unsnoc X = .ok t)
    (hX : Vals.WF X) : t.WF := by
  obtain ⟨m, lo, up, f⟩ := X
  simp only [Tab.unsnoc] at h
  split at h; · cases h
  rename_i hb
  simp only [bind] at h
  rw [Except.bind_eq_ok'] at h; obtain ⟨_, -, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨lt, hlt, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨⟨M, sel⟩, hwh, h⟩ := h; try dsimp only at h
  rw [Except.bind_eq_ok'] at h; obtain ⟨eM, heM, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨l, hl, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨gX, hgX, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨sM, hsM, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨gf, hgf, h⟩ := h
  exact canon_wf h (unsnoc_pre_wf hX (by omega) hlt hwh heM hl hgX hsM hgf)

/-- **`uncons X` denotes `cons°` on the arrays `X`**: each non-empty cell of `X` to its head and its tail. -/
theorem uncons_holds {n : USize} {X : Vals (.arr B) n} {T : Tab (.arr B) (.prod B (.arr B))}
    (h : Tab.uncons X = .ok T) (hX : Vals.WF X) (xs : List B.El) (p : (Obj.prod B (.arr B)).El) :
    T.Holds xs p ↔ (∃ i, X.row i = xs) ∧ xs = p.1 :: p.2 := by
  obtain ⟨m, lo, up, f⟩ := X
  dsimp only [Tab.uncons] at h
  split at h; · cases h
  rename_i hb
  simp only [bind] at h
  rw [Except.bind_eq_ok'] at h; obtain ⟨_, -, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨lt, hlt, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨⟨M, sel⟩, hw, h⟩ := h; try dsimp only at h
  rw [Except.bind_eq_ok'] at h; obtain ⟨sM, hsM, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨K, hK, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨hd, hhd, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨lo', hlo', h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨eM, heM, h⟩ := h
  have hm63 : m.toNat < 2 ^ 63 := by omega
  rw [canon_holds h (uncons_pre_wf hX hm63 hlt hw hsM hK hhd hlo' heM)]
  obtain ⟨SN, EN, hw1, hb1, hrow, hsel, hall⟩ := cellSpan_where hX.1 hlt hw hm63 f
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
    obtain ⟨i2, hi2, hs2⟩ := Arr.gather_raw lo hsM j
    obtain ⟨i3, hi3, he3⟩ := Arr.gather_raw up heM j
    have e2 : i = i2 := Fin.ext (hi.symm.trans hi2)
    have e3 : i = i3 := Fin.ext (hi.symm.trans hi3)
    subst e2 e3
    rw [(hw1 _ i.2).1] at hs2
    rw [(hw1 _ i.2).2] at he3
    have hEm : EN i ≤ m.toNat := by have := hb1 i; omega
    obtain ⟨i4, hi4, hd4⟩ := Vals.gather_row _ hhd j
    have e4 : i4.1 = SN i := by rw [← hi4, hs2, toNat_toUInt64 (by have := hb1 i; omega)]
    have hlo : (raw .i64 M lo'.enc)[j.1]?.getD 0 = (SN i + 1).toUInt64 := by
      have es := (colMap_post (colArr_ok hlo')).2 j.1 j.2
      rw [hs2] at es
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
    (h : Tab.unsnoc X = .ok T) (hX : Vals.WF X) (xs : List B.El) (p : (Obj.prod (.arr B) B).El) :
    T.Holds xs p ↔ (∃ i, X.row i = xs) ∧ xs = p.1 ++ [p.2] := by
  obtain ⟨m, lo, up, f⟩ := X
  dsimp only [Tab.unsnoc] at h
  split at h; · cases h
  rename_i hb
  simp only [bind] at h
  rw [Except.bind_eq_ok'] at h; obtain ⟨_, -, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨lt, hlt, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨⟨M, sel⟩, hw, h⟩ := h; try dsimp only at h
  rw [Except.bind_eq_ok'] at h; obtain ⟨eM, heM, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨l, hl, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨K, hK, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨sM, hsM, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨tl, htl, h⟩ := h
  have hm63 : m.toNat < 2 ^ 63 := by omega
  rw [canon_holds h (unsnoc_pre_wf hX hm63 hlt hw heM hl hK hsM htl)]
  obtain ⟨SN, EN, hw1, hb1, hrow, hsel, hall⟩ := cellSpan_where hX.1 hlt hw hm63 f
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
    obtain ⟨i2, hi2, hs2⟩ := Arr.gather_raw lo hsM j
    obtain ⟨i3, hi3, he3⟩ := Arr.gather_raw up heM j
    have e2 : i = i2 := Fin.ext (hi.symm.trans hi2)
    have e3 : i = i3 := Fin.ext (hi.symm.trans hi3)
    subst e2 e3
    rw [(hw1 _ i.2).1] at hs2
    rw [(hw1 _ i.2).2] at he3
    have hEm : EN i ≤ m.toNat := by have := hb1 i; omega
    have hlw : (raw .i64 M l.enc)[j.1]?.getD 0 = (EN i - 1).toUInt64 := by
      have es := (colMap_post (colArr_ok hl)).2 j.1 j.2
      rw [he3] at es
      simp only [Op.eval, Except.ok.injEq] at es
      rw [← es, neg_add_word, toUInt64_sub (by omega)]; rfl
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

/-- **`uncat` keeps `Tab.WF`**: split `d ≤ EN - SN` of cell `[SN, EN)` (`expand_spec` of the counts `EN - SN + 1`) is
`[SN, SN + d)` and `[SN + d, EN)`, inside `m` (`cellSpan_start_le` where the cell is empty). -/
private theorem uncat_pre_wf {n m Tn : USize} {lo up : Arr .i64 n} {f : Vals B m} {w G u : Enc}
    {sG mid eG : Arr .i64 Tn} {K : Vals (.arr B) Tn}
    (hX : Vals.WF (A := .arr B) (n := n) ⟨m, (lo, up, f)⟩) (hb : ¬2 ^ 63 ≤ n.toNat * (m.toNat + 1) + n.toNat + m.toNat + 1)
    (hw : colMap Op.sub n up.enc lo.enc .i64 .i64 [] [(Op.add, 1)] = .ok w)
    (hex : expand n w = .ok (Tn, G, u)) (hsG : Arr.gather Tn G lo = .ok sG)
    (hmid : colArr Op.add Tn sG.enc u = .ok mid) (hK : Vals.gather Tn G (A := .arr B) (n := n) ⟨m, (lo, up, f)⟩ = .ok K)
    (heG : Arr.gather Tn G up = .ok eG) :
    Tab.WF (⟨Tn, K, (⟨m, (sG, mid, f)⟩, ⟨m, (mid, eG, f)⟩)⟩ : Tab (.arr B) (.prod (.arr B) (.arr B))) := by
  have hm63 : m.toNat < 2 ^ 63 := by omega
  have hn63 : n.toNat < 2 ^ 63 := by omega
  obtain ⟨SN, EN, hse', hb1, -⟩ := cellSpan_spec hX.1 hm63 f
  obtain ⟨wN, hwN⟩ : ∃ F : Nat → Nat, ∀ i, F i = EN i - SN i + 1 := ⟨_, fun _ => rfl⟩
  have hww : ∀ i < n.toNat, (raw .i64 n w)[i]?.getD 0 = (wN i).toUInt64 := fun i hi => by
    -- one `kscan`: `hi - lo`, then `+ 1` (`colMap_chain`)
    obtain ⟨-, -, -, hr⟩ := colMap_chain hw
    obtain ⟨x', y', v, W, hx, hy, e1, e2, ho⟩ := hr i hi
    cases hx; cases hy
    rw [(hse' i hi).2, (hse' i hi).1] at e1; simp only [Op.eval, Except.ok.injEq] at e1
    simp only [chain, List.foldlM, Op.eval, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at e2
    rw [ho, Option.getD_some, if_neg (by decide : QAtomicType.i64 ≠ .u1), ← e2, ← e1, hwN, ← toUInt64_sub (hb1 i).1,
      UInt64.add_comm]
    exact (UInt64.ofNat_add _ _).symm
  have hsn : ((List.range n.toNat).map wN).sum < 2 ^ 63 := by
    have := sum_range_le_mul (wN := wN) (k := n.toNat) (c := m.toNat + 1) fun i _ => by have := hb1 i; rw [hwN]; omega
    omega
  obtain ⟨hTn, hrun⟩ := expand_spec hex wN hww hsn hn63
  -- row `t` is split `d` of its cell `g`: `sG = SN g`, `mid = SN g + d`, `eG = EN g`, `SN g + d ≤ EN g ≤ m`
  have hJ : ∀ t : Fin Tn.toNat, ∃ a d b : Nat, (raw .i64 Tn sG.enc)[t.1]?.getD 0 = a.toUInt64 ∧
      (raw .i64 Tn mid.enc)[t.1]?.getD 0 = (a + d).toUInt64 ∧ (raw .i64 Tn eG.enc)[t.1]?.getD 0 = b.toUInt64 ∧
      a + d ≤ b ∧ b ≤ m.toNat := fun t => by
    obtain ⟨g, hg, h1, h2⟩ := exists_group wN n.toNat t (by rw [← hTn]; exact t.2)
    obtain ⟨hG, hu⟩ := hrun g hg t h1 h2
    have hGg : ((raw .i64 Tn G)[t.1]?.getD 0).toNat = g := by rw [hG, toNat_toUInt64 (by omega)]
    obtain ⟨i2, hi2, hs2⟩ := Arr.gather_raw lo hsG t
    obtain ⟨i3, hi3, he3⟩ := Arr.gather_raw up heG t
    obtain rfl : i2 = ⟨g, hg⟩ := Fin.ext (hi2.symm.trans hGg)
    obtain rfl : i3 = ⟨g, hg⟩ := Fin.ext (hi3.symm.trans hGg)
    rw [(hse' g hg).1] at hs2
    rw [(hse' g hg).2] at he3
    have hd : t.1 - ((List.range g).map wN).sum ≤ EN g - SN g := by rw [hwN] at h2; omega
    have hmw : (raw .i64 Tn mid.enc)[t.1]?.getD 0 = (SN g + (t.1 - ((List.range g).map wN).sum)).toUInt64 := by
      have es := (colMap_raw (colArr_ok hmid)).2.2.2 _ t.2
      rw [hs2, hu] at es; simp only [Op.eval, Except.ok.injEq] at es
      rw [← es, ← UInt64.ofNat_add]
    have hSm := cellSpan_start_le hX.1 ⟨g, hg⟩
    rw [(hse' g hg).1, toNat_toUInt64 (by have := hb1 g; omega)] at hSm
    have hd' : SN g + (t.1 - ((List.range g).map wN).sum) ≤ EN g := by have := hb1 g; omega
    refine ⟨SN g, _, EN g, hs2, hmw, he3, hd', ?_⟩
    have := hb1 g; omega
  refine ⟨Vals.gather_wf hK hX, ⟨fun t => ?_, hX.2⟩, ⟨fun t => ?_, hX.2⟩⟩
  · obtain ⟨a, d, b, ha, hd, -, hab, hbm⟩ := hJ t
    exact cell_wf_nat ha hd (by omega) (by omega) hm63
  · obtain ⟨a, d, b, -, hd, hb', hab, hbm⟩ := hJ t
    exact cell_wf_nat hd hb' hab hbm hm63

/-- **`uncat X` is `canon` of a well-formed table**: so a `Λ` of it is `lamOf` (`Tab.tails`), and it keeps `Tab.WF`. -/
theorem uncat_canonical {n : USize} {X : Vals (.arr B) n} {t : Tab (.arr B) (.prod (.arr B) (.arr B))}
    (h : Tab.uncat X = .ok t) (hX : Vals.WF X) : ∃ R : Tab (.arr B) (.prod (.arr B) (.arr B)), R.canon = .ok t ∧ R.WF := by
  obtain ⟨m, lo, up, f⟩ := X
  dsimp only [Tab.uncat] at h
  split at h; · cases h
  rename_i hb
  simp only [bind] at h
  rw [Except.bind_eq_ok'] at h; obtain ⟨_, -, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨w, hw, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨⟨Tn, G, u⟩, hex, h⟩ := h; try dsimp only at h
  rw [Except.bind_eq_ok'] at h; obtain ⟨sG, hsG, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨mid, hmid, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨K, hK, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨eG, heG, h⟩ := h
  exact ⟨_, h, uncat_pre_wf hX hb hw hex hsG hmid hK heG⟩

theorem uncat_wf {n : USize} {X : Vals (.arr B) n} {t : Tab (.arr B) (.prod (.arr B) (.arr B))}
    (h : Tab.uncat X = .ok t) (hX : Vals.WF X) : t.WF :=
  let ⟨_, hc, w⟩ := uncat_canonical h hX; canon_wf hc w


/-- **`uncat X` denotes `cat°` on the arrays `X`**: each cell of `X` to each of its splits. Cell `i` is `[SN, EN)`
(`cellSpan_spec`); EXPAND of the widths `EN - SN + 1` puts split `d` of cell `i` at row `Σ_{<i} w + d`, which reads
the slices `[SN, SN + d)` and `[SN + d, EN)` of the payload. -/
theorem uncat_holds {n : USize} {X : Vals (.arr B) n} {T : Tab (.arr B) (.prod (.arr B) (.arr B))}
    (h : Tab.uncat X = .ok T) (hX : Vals.WF X) (xs : List B.El) (p : (Obj.prod (.arr B) (.arr B)).El) :
    T.Holds xs p ↔ (∃ i, X.row i = xs) ∧ xs = p.1 ++ p.2 := by
  obtain ⟨m, lo, up, f⟩ := X
  dsimp only [Tab.uncat] at h
  split at h; · cases h
  rename_i hb
  simp only [bind] at h
  rw [Except.bind_eq_ok'] at h; obtain ⟨_, -, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨w, hw, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨⟨Tn, G, u⟩, hex, h⟩ := h; try dsimp only at h
  rw [Except.bind_eq_ok'] at h; obtain ⟨sG, hsG, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨mid, hmid, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨K, hK, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨eG, heG, h⟩ := h
  have hm63 : m.toNat < 2 ^ 63 := by omega
  have hn63 : n.toNat < 2 ^ 63 := by omega
  rw [canon_holds h (uncat_pre_wf hX hb hw hex hsG hmid hK heG)]
  obtain ⟨SN, EN, hse', hb1, hrow⟩ := cellSpan_spec hX.1 hm63 f
  obtain ⟨wN, hwN⟩ : ∃ F : Nat → Nat, ∀ i, F i = EN i - SN i + 1 := ⟨_, fun _ => rfl⟩
  have hww : ∀ i < n.toNat, (raw .i64 n w)[i]?.getD 0 = (wN i).toUInt64 := fun i hi => by
    -- one `kscan`: `hi - lo`, then `+ 1` (`colMap_chain`)
    obtain ⟨-, -, -, hr⟩ := colMap_chain hw
    obtain ⟨x', y', v, W, hx, hy, e1, e2, ho⟩ := hr i hi
    cases hx; cases hy
    rw [(hse' i hi).2, (hse' i hi).1] at e1; simp only [Op.eval, Except.ok.injEq] at e1
    simp only [chain, List.foldlM, Op.eval, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at e2
    rw [ho, Option.getD_some, if_neg (by decide : QAtomicType.i64 ≠ .u1), ← e2, ← e1, hwN, ← toUInt64_sub (hb1 i).1,
      UInt64.add_comm]
    exact (UInt64.ofNat_add _ _).symm
  have hwm : ∀ i, wN i ≤ m.toNat + 1 := fun i => by have := hb1 i; rw [hwN]; omega
  have hsum : ∀ k, ((List.range k).map wN).sum ≤ k * (m.toNat + 1) := fun k => by
    induction k with
    | zero => simp
    | succ k ih => rw [sum_range_succ', Nat.succ_mul]; have := hwm k; omega
  have hsn : ((List.range n.toNat).map wN).sum < 2 ^ 63 := by have := hsum n.toNat; omega
  obtain ⟨hTn, hrun⟩ := expand_spec hex wN hww hsn hn63
  -- split `d` of cell `g`: its row's key is cell `g`, its two slices join to cell `g`, the first of length `d`
  have hJ : ∀ g (hg : g < n.toNat) d, d ≤ EN g - SN g → ∃ ht : ((List.range g).map wN).sum + d < Tn.toNat,
      K.row ⟨_, ht⟩ = Vals.row (A := .arr B) ⟨m, lo, up, f⟩ ⟨g, hg⟩ ∧
      (Vals.row (A := .prod (.arr B) (.arr B)) (⟨m, sG, mid, f⟩, ⟨m, mid, eG, f⟩) ⟨_, ht⟩).1 ++
        (Vals.row (A := .prod (.arr B) (.arr B)) (⟨m, sG, mid, f⟩, ⟨m, mid, eG, f⟩) ⟨_, ht⟩).2 =
          Vals.row (A := .arr B) ⟨m, lo, up, f⟩ ⟨g, hg⟩ ∧
      (Vals.row (A := .prod (.arr B) (.arr B)) (⟨m, sG, mid, f⟩, ⟨m, mid, eG, f⟩) ⟨_, ht⟩).1.length = d := by
    intro g hg d hd
    have hgS : ((List.range g).map wN).sum + wN g ≤ ((List.range n.toNat).map wN).sum := by
      rw [← sum_range_succ']; exact sum_range_mono wN hg
    have hdw : d < wN g := by rw [hwN]; omega
    have ht : ((List.range g).map wN).sum + d < Tn.toNat := by omega
    refine ⟨ht, ?_⟩
    obtain ⟨hG, hu⟩ := hrun g hg (((List.range g).map wN).sum + d) (by omega) (by omega)
    rw [Nat.add_sub_cancel_left] at hu
    have hGg : ((raw .i64 Tn G)[((List.range g).map wN).sum + d]?.getD 0).toNat = g := by
      rw [hG, toNat_toUInt64 (by omega)]
    obtain ⟨i1, hi1, hK1⟩ := Vals.gather_row _ hK ⟨_, ht⟩
    obtain ⟨i2, hi2, hs2⟩ := Arr.gather_raw lo hsG ⟨_, ht⟩
    obtain ⟨i3, hi3, he3⟩ := Arr.gather_raw up heG ⟨_, ht⟩
    have e1 : i1 = ⟨g, hg⟩ := Fin.ext (hi1.symm.trans hGg)
    have e2 : i2 = ⟨g, hg⟩ := Fin.ext (hi2.symm.trans hGg)
    have e3 : i3 = ⟨g, hg⟩ := Fin.ext (hi3.symm.trans hGg)
    subst e1 e2 e3
    rw [(hse' g hg).1] at hs2
    rw [(hse' g hg).2] at he3
    have hmw : (raw .i64 Tn mid.enc)[((List.range g).map wN).sum + d]?.getD 0 = (SN g + d).toUInt64 := by
      have es := (colMap_raw (colArr_ok hmid)).2.2.2 _ ht
      rw [hs2, hu] at es; simp only [Op.eval, Except.ok.injEq] at es
      rw [← es, ← UInt64.ofNat_add]
    have hb := hb1 g
    show K.row ⟨_, ht⟩ = _ ∧ Vals.row (A := .arr B) ⟨m, sG, mid, f⟩ ⟨_, ht⟩ ++
      Vals.row (A := .arr B) ⟨m, mid, eG, f⟩ ⟨_, ht⟩ = _ ∧ (Vals.row (A := .arr B) ⟨m, sG, mid, f⟩ ⟨_, ht⟩).length = d
    rw [Vals.row_span sG mid f _ hs2 hmw (by omega) (by omega) (by omega) hm63,
      Vals.row_span mid eG f _ hmw he3 (by omega) (by omega) (by omega) hm63, hrow ⟨g, hg⟩,
      Nat.add_sub_cancel_left, ← List.map_append, List.range'_append_1,
      show d + (EN g - (SN g + d)) = EN g - SN g by omega]
    exact ⟨hK1.trans (hrow ⟨g, hg⟩), rfl, by simp⟩
  simp only [Tab.Holds]
  constructor
  · rintro ⟨t, rfl, rfl⟩
    obtain ⟨g, hg, h1, h2⟩ := exists_group wN n.toNat t (by rw [← hTn]; exact t.2)
    obtain ⟨ht, hk, hv, -⟩ := hJ g hg (t - ((List.range g).map wN).sum) (by rw [hwN] at h2; omega)
    have et : (⟨_, ht⟩ : Fin Tn.toNat) = t := Fin.ext (by simp only; omega)
    rw [et] at hk hv
    exact ⟨⟨_, hk.symm⟩, hk.trans hv.symm⟩
  · rintro ⟨⟨i, rfl⟩, hx⟩
    have hd : p.1.length ≤ EN i - SN i := by
      have := congrArg List.length hx; rw [hrow i] at this; simp at this; omega
    obtain ⟨ht, hk, hv, hl⟩ := hJ i i.2 _ hd
    obtain ⟨e1, e2⟩ := List.append_inj (hv.trans hx) hl
    exact ⟨⟨_, ht⟩, hk, Prod.ext e1 e2⟩

/-- A round's split of what is left at each key (`peelL` by `uncons`, `peelR` by `unsnoc`), given the law of its
converse `u`: the element read now and the rest, each the pairs `rest ≫ u` projected (`foldRounds_holds`' `hpeel`). -/
theorem peel_holds {K E C : Obj} {rest : Tab K (.arr E)} {u : Tab (.arr E) C} {c : Tab K C}
    {o₁ : Tab C E} {o₂ : Tab C (.arr E)} {el : Tab K E} {rest' : Tab K (.arr E)} (Pe : (Obj.arr E).El → C.El → Prop)
    (fst : C.El → E.El) (snd : C.El → (Obj.arr E).El)
    (hu : ∀ r q, u.Holds r q ↔ (∃ i, rest.val.row i = r) ∧ Pe r q) (hc : rest.comp u = .ok c)
    (h₁ : ∀ q x, o₁.Holds q x ↔ (∃ i, c.val.row i = q) ∧ x = fst q)
    (h₂ : ∀ q r', o₂.Holds q r' ↔ (∃ i, c.val.row i = q) ∧ r' = snd q)
    (he : c.comp o₁ = .ok el) (hr : c.comp o₂ = .ok rest') (hrest : rest.WF) (huw : u.WF) (hw₁ : o₁.WF)
    (hw₂ : o₂.WF) :
    (∀ k x, el.Holds k x ↔ ∃ r q, rest.Holds k r ∧ Pe r q ∧ fst q = x) ∧
    ∀ k r', rest'.Holds k r' ↔ ∃ r q, rest.Holds k r ∧ Pe r q ∧ snd q = r' := by
  have hc' : ∀ k q, c.Holds k q ↔ ∃ r, rest.Holds k r ∧ Pe r q := fun k q => by
    rw [comp_holds hc hrest huw]
    exact exists_congr fun r => and_congr_right fun ⟨i, _, hi⟩ => (hu r q).trans (and_iff_right ⟨i, hi⟩)
  have side {D : Obj} {o : Tab C D} (p : C.El → D.El) (ho : ∀ q y, o.Holds q y ↔ (∃ i, c.val.row i = q) ∧ y = p q)
      (hwo : o.WF) {t : Tab K D} (ht : c.comp o = .ok t) (k : K.El) (y : D.El) :
      t.Holds k y ↔ ∃ r q, rest.Holds k r ∧ Pe r q ∧ p q = y := by
    rw [comp_holds ht (comp_wf hc hrest huw) hwo]
    constructor
    · rintro ⟨q, hq, hy⟩
      obtain ⟨r, hr, hp⟩ := (hc' k q).1 hq
      exact ⟨r, q, hr, hp, ((ho q y).1 hy).2.symm⟩
    · rintro ⟨r, q, hr, hp, rfl⟩
      obtain ⟨i, -, hi⟩ := (hc' k q).2 ⟨r, hr, hp⟩
      exact ⟨q, (hc' k q).2 ⟨r, hr, hp⟩, (ho q _).2 ⟨⟨i, hi⟩, rfl⟩⟩
  exact ⟨side fst h₁ hw₁ he, side snd h₂ hw₂ hr⟩

/-- **`peelL` is `cons°` on what is left** (`uncons_holds`): `x` the head of a key's array, the rest its tail. -/
theorem peelL_holds {K E : Obj} {rest : Tab K (.arr E)} {el : Tab K E} {rest' : Tab K (.arr E)}
    (h : peelL rest = .ok (el, rest')) (hrest : rest.WF) :
    (∀ k x, el.Holds k x ↔ ∃ r r', rest.Holds k r ∧ r = x :: r') ∧
    ∀ k r', rest'.Holds k r' ↔ ∃ r x, rest.Holds k r ∧ r = x :: r' := by
  unfold peelL at h; simp only [bind, Except.bind_eq_ok'] at h
  obtain ⟨u, hu, c, hc, o₁, ho₁, a, ha, o₂, ho₂, b, hb, h⟩ := h
  cases h
  have wu := uncons_wf hu hrest.2
  have wc := comp_wf hc hrest wu
  obtain ⟨h1, h2⟩ := peel_holds (C := .prod E (.arr E)) (fun r q => r = q.1 :: q.2) Prod.fst Prod.snd
    (uncons_holds hu hrest.2) hc (outl_holds ho₁ wc.2) (outr_holds ho₂ wc.2) ha hb hrest wu (outl_wf ho₁ wc.2) (outr_wf ho₂ wc.2)
  exact ⟨fun k x => (h1 k x).trans ⟨fun ⟨r, q, hr, hp, hx⟩ => ⟨r, q.2, hr, hx ▸ hp⟩,
      fun ⟨r, r', hr, hp⟩ => ⟨r, (x, r'), hr, hp, rfl⟩⟩,
    fun k r' => (h2 k r').trans ⟨fun ⟨r, q, hr, hp, hx⟩ => ⟨r, q.1, hr, hx ▸ hp⟩,
      fun ⟨r, x, hr, hp⟩ => ⟨r, (x, r'), hr, hp, rfl⟩⟩⟩

/-- **`peelR` is `snoc°` on what is left** (`unsnoc_holds`): `x` the last element of a key's array, the rest its
front. -/
theorem peelR_holds {K E : Obj} {rest : Tab K (.arr E)} {el : Tab K E} {rest' : Tab K (.arr E)}
    (h : peelR rest = .ok (el, rest')) (hrest : rest.WF) :
    (∀ k x, el.Holds k x ↔ ∃ r r', rest.Holds k r ∧ r = r' ++ [x]) ∧
    ∀ k r', rest'.Holds k r' ↔ ∃ r x, rest.Holds k r ∧ r = r' ++ [x] := by
  unfold peelR at h; simp only [bind, Except.bind_eq_ok'] at h
  obtain ⟨u, hu, c, hc, o₂, ho₂, a, ha, o₁, ho₁, b, hb, h⟩ := h
  cases h
  have wu := unsnoc_wf hu hrest.2
  have wc := comp_wf hc hrest wu
  obtain ⟨h1, h2⟩ := peel_holds (C := .prod (.arr E) E) (fun r q => r = q.1 ++ [q.2]) Prod.snd Prod.fst
    (unsnoc_holds hu hrest.2) hc (outr_holds ho₂ wc.2) (outl_holds ho₁ wc.2) ha hb hrest wu (outr_wf ho₂ wc.2) (outl_wf ho₁ wc.2)
  exact ⟨fun k x => (h1 k x).trans ⟨fun ⟨r, q, hr, hp, hx⟩ => ⟨r, q.1, hr, hx ▸ hp⟩,
      fun ⟨r, r', hr, hp⟩ => ⟨r, (r', x), hr, hp, rfl⟩⟩,
    fun k r' => (h2 k r').trans ⟨fun ⟨r, q, hr, hp, hx⟩ => ⟨r, q.2, hr, hx ▸ hp⟩,
      fun ⟨r, x, hr, hp⟩ => ⟨r, (r', x), hr, hp, rfl⟩⟩⟩

/-- **`R.pack` denotes `R`** (`Vals.pack_row` on both sides): `foldRounds_holds`' `hpack`. -/
theorem pack_holds {k v : Obj} {R R' : Tab k v} (h : R.pack = .ok R') (wR : R.WF) (a : k.El) (b : v.El) :
    R'.Holds a b ↔ R.Holds a b := by
  unfold Tab.pack at h; simp only [bind, Except.bind_eq_ok'] at h
  obtain ⟨key, hk, val, hv, h⟩ := h
  cases h
  simp only [Tab.Holds, Vals.pack_row _ hk wR.1, Vals.pack_row _ hv wR.2]

end Tab


/-- **`r \ s` keeps `Tab.WF`**: the groups of `Q = r° ≫ ⟨𝟙, s⟩` gathered (`compOne_wf`), `∪` the vacuous part
(`cross_wf` of `ran`s). -/
theorem Tab.ldivOf_wf {A B C : Obj} {r : Tab A B} {s : Tab A C} {UB : Tab B B} {UC : Tab C C} {t : Tab B C}
    (h : ldivOf r s UB UC = .ok t) (hr : r.WF) (hs : s.WF) (hB : UB.WF) (hC : UC.WF) : t.WF := by
  simp only [Tab.ldivOf, bind, Except.bind, pure, Except.pure] at h
  split at h; · cases h
  rename_i Q hQ
  have wQ := compOne_wf hQ ⟨hr.2, hr.1⟩ ⟨hs.1, hs.1, hs.2⟩
  okSplit
  exact union_wf h ⟨Vals.gather_wf ‹_› wQ.1, Vals.gather_wf ‹_› wQ.2.2⟩
    (cross_wf ‹_› (diff_wf ‹_› (ran_wf ‹_› hB) (ran_wf ‹_› hr)).1 (ran_wf ‹_› hC).1)

/-- **`ldivOf` holds as `ldivDen`** on canonical `r`, `s`: a pair `(b, c)` of the counting stage has as many
`r`-witnesses `a` of `b` with `s a c` as `r`-witnesses of `b` at all, so (rows being distinct) every one; the vacuous
`b`s come from the `CROSS`. -/
theorem Tab.ldivOf_holds {A B C : Obj} {r : Tab A B} {s : Tab A C} {UB : Tab B B} {UC : Tab C C} {T : Tab B C}
    (hr : ∃ R : Tab A B, R.canon = .ok r ∧ R.WF) (hs : ∃ S : Tab A C, S.canon = .ok s ∧ S.WF)
    (h : Tab.ldivOf r s UB UC = .ok T)
    (hrw : r.WF) (hsw : s.WF) (hUB : UB.WF) (hUC : UC.WF) (b : B.El) (c : C.El) :
    T.Holds b c ↔ Lang.ldivDen r.Holds s.Holds UB.Holds UC.Holds b c := by
  classical
  have hw : (Tab.mk r.n r.val r.key).WF ∧ (Tab.mk s.n s.key (s.key, s.val) : Tab A (.prod A C)).WF :=
    ⟨⟨hrw.2, hrw.1⟩, hsw.1, ⟨hsw.1, hsw.2⟩⟩
  obtain ⟨R, hr, hRw⟩ := hr; obtain ⟨S, hs, hSw⟩ := hs
  rw [show r.Holds = R.Holds from funext fun a => funext fun b => propext (canon_holds hr hRw a b),
    show s.Holds = S.Holds from funext fun a => funext fun c => propext (canon_holds hs hSw a c)]
  unfold Tab.ldivOf at h
  simp only [bind] at h
  rw [Except.bind_eq_ok'] at h; obtain ⟨Q, hQ, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨es, hes, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨⟨vs, p⟩, hasc, h⟩ := h; try dsimp only at h
  rw [Except.bind_eq_ok'] at h; obtain ⟨⟨k, g, f⟩, hseen, h⟩ := h; try dsimp only at h
  rw [Except.bind_eq_ok'] at h; obtain ⟨sg1, hsg1, h⟩ := h
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
  rw [Except.bind_eq_ok'] at h; obtain ⟨sg2, hsg2, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨lt, hlt, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨cR, hcR, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨code, hcode, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨q, hq, h⟩ := h
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
  have wQ := compOne_wf hQ hw.1 hw.2
  rw [union_holds h ⟨Vals.gather_wf hX1 wQ.1, Vals.gather_wf hY1 wQ.2.2⟩ (cross_wf hcr
    (diff_wf hdf (ran_wf hub hUB) (ran_wf hrr hrw)).1 (ran_wf huc hUC).1), cross_holds hcr (diff_wf hdf (ran_wf hub hUB) (ran_wf hrr hrw)).1 (ran_wf huc hUC).1]
  have hP : (∃ j, X1.row j = b ∧ Y1.row j = c) ↔
      (∃ a, R.Holds a b ∧ S.Holds a c) ∧ ∀ a, R.Holds a b → S.Holds a c := by
    have hU64 : USize.size ≤ 2 ^ 64 := by rcases USize.size_eq with h | h <;> omega
    obtain ⟨hNn, hoff⟩ := catPlan_ok hcat
    have hzr := Vals.concat_row hNn hoff r.val Q.key hz hrw.2 (compOne_wf hQ hw.1 hw.2).1
    have hNU := N.toNat_lt_size
    obtain ⟨π1, gr1, fs1, hkN, hp1, -, hsur1, hcnt1, hg1, hf1, hrow1⟩ := group_rows (A := .prod B C) (N := Q.n) (x := (Q.key, (Q.val : Vals A Q.n × Vals C Q.n).2)) ⟨wQ.1, wQ.2.2⟩ hes hasc hseen
    obtain ⟨π2, gr2, fs2, hbkN, hp2, hinj2, hsur2, hcnt2, hg2, -, hrow2⟩ := group_rows (Vals.concat_wf hNn hoff hz hrw.2 (compOne_wf hQ hw.1 hw.2).1) hbs hbasc hbseen
    have hK : k.toUSize.toNat = k := USize.toNat_ofNat_of_lt' (by omega)
    have hbK : bk.toUSize.toNat = bk := USize.toNat_ofNat_of_lt' (by omega)
    have hnU : r.n.toUInt64 = r.n.toNat.toUInt64 := UInt64.toNat_inj.mp (by simp <;> omega)
    -- the gathered columns hold no null: a grade, a kseen group column, a fold, a gather of a grade
    have hpN := kasc_plain hasc
    have hqN : hasNul q = false := by rw [kgather_plain hq hpN]; exact hasNul_wordsFoR _
    have hbgN := (kseen_plain hbseen).1
    have hcodeN := kscatter_plain hcode hbgN
    have hcRN : hasNul cR = false := Tab.groupFold_plain hcR
    ------------------------------------------------------------------ `Q`'s rows, `r`'s rows
    have hQh : ∀ a, Q.Holds b (a, c) ↔ R.Holds a b ∧ S.Holds a c := fun a => by
      obtain ⟨U₀, hU₀, hUw₀, hH₀⟩ := compOne_canon hQ hw.1 hw.2; rw [canon_holds hU₀ hUw₀, hH₀]
      constructor
      · rintro ⟨a', ⟨i, h1, h2⟩, ⟨j, h3, h4⟩⟩
        obtain ⟨e1, e2⟩ := Prod.mk.inj (show (s.key.row j, s.val.row j) = (a, c) from h4)
        exact ⟨(canon_holds hr hRw a b).1 ⟨i, h2.trans (h3.symm.trans e1), h1⟩, (canon_holds hs hSw a c).1 ⟨j, e1, e2⟩⟩
      · rintro ⟨hab, hac⟩
        obtain ⟨i, h1, h2⟩ := (canon_holds hr hRw a b).2 hab
        obtain ⟨j, h3, h4⟩ := (canon_holds hs hSw a c).2 hac
        exact ⟨a, ⟨i, h2, h1⟩, ⟨j, h3, show (s.key.row j, s.val.row j) = (a, c) by rw [h3, h4]⟩⟩
    obtain ⟨U, hUc, hUw, -⟩ := compOne_canon hQ hw.1 hw.2
    have hQd : ∀ i i' : Fin Q.n.toNat, Q.key.row i = Q.key.row i' → Q.val.row i = Q.val.row i' → i = i' :=
      fun i i' e1 e2 => Classical.byContradiction fun hne => Tab.canon_distinct hUc hUw hne (by rw [e1, e2])
    have hrd : ∀ i i' : Fin r.n.toNat, r.key.row i = r.key.row i' → r.val.row i = r.val.row i' → i = i' :=
      fun i i' e1 e2 => Classical.byContradiction fun hne => Tab.canon_distinct hr hRw hne (by rw [e1, e2])
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
          rw [hf2', dif_pos hi]; exact ⟨_, rfl, (canon_holds hr hRw _ _).1 ⟨⟨i, hi⟩, rfl, h1⟩⟩
        · rintro ⟨a, rfl, hab⟩
          obtain ⟨i, h1, h2⟩ := (canon_holds hr hRw a b).2 hab
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
      fun G hG => fold_add_count (Tab.groupFold_ok (fn := (· + ·)) (fun _ _ => rfl) hseen hsg1 hcnt).1
        (Tab.groupFold_ok (fn := (· + ·)) (fun _ _ => rfl) hseen hsg1 hcnt).2.2 gr1 (fun _ => true) (fun q hq => (hg1 q hq).1)
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
        have e : Op.lt.eval ((raw .i64 N bp)[q]?.getD 0) r.n.toUInt64 = _ := (colMap_post hlt).2 q hq
        rw [(hp2 q hq).1, hnU,
          eval_lt_nat (by have := (hp2 q hq).2; omega) (by omega), Except.ok.injEq] at e
        rw [← e]; simp
    have hqw : ∀ G < k, (raw .i64 k.toUSize q)[G]?.getD 0 = (π1 (fs1 G)).toUInt64 := fun G hG => by
      obtain ⟨hfw, hfn, -⟩ := hf1 G hG
      rw [(kgather_word hq hpN G (by omega)).2, hfw, toNat_toUInt64 (by omega), (hp1 _ hfn).1]
    have hdG : ∀ G < k, ∀ h : π1 (fs1 G) < Q.n.toNat, Q.key.row ⟨_, h⟩ = b →
        (raw .i64 k.toUSize d)[G]?.getD 0 = ((List.range N.toNat).countP P2).toUInt64 := by
      intro G hG h hb
      have hqaw : (raw .i64 k.toUSize qa)[G]?.getD 0 = (r.n.toNat + π1 (fs1 G)).toUInt64 := by
        have e := (colMap_post hqa).2 G (by omega)
        rw [hqw G hG] at e
        simp only [Op.eval, Except.ok.injEq] at e
        rw [← e, hnU, ← UInt64.ofNat_add]
      obtain ⟨q2, hq2, hpq2⟩ := hsur2 (r.n.toNat + π1 (fs1 G)) (by omega)
      have hcqw : (raw .i64 k.toUSize cq)[G]?.getD 0 = (gr2 q2).toUInt64 := by
        rw [(kgather_word hcq hcodeN G (by omega)).2, hqaw, toNat_toUInt64 (by omega), ← hpq2,
          scatter_last_at hcode hbgN π2 (fun q hq => (hp2 q hq).1) (fun q hq => (hp2 q hq).2) hinj2 q2 hq2,
          (hg2 q2 hq2).1]
      have hgq := (hg2 q2 hq2).2
      rw [(kgather_word hd hcRN G (by omega)).2, hcqw, toNat_toUInt64 (by omega),
        fold_add_count (Tab.groupFold_ok (fn := (· + ·)) (fun _ _ => rfl) hbseen hsg2 hcR).1
          (Tab.groupFold_ok (fn := (· + ·)) (fun _ _ => rfl) hbseen hsg2 hcR).2.2 gr2 (fun q => decide (π2 q < r.n.toNat))
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
      have hixw := (kgather_word hix hqN j.1 j.2).2
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
      have hixw := (kgather_word hix hqN j hjM).2
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
      have h1 := (diff_holds hdf (ran_wf hub hUB) (ran_wf hrr hrw) _ _).1 ⟨i, rfl, rfl⟩
      obtain ⟨e, hb⟩ := (ran_holds hub hUB.2 _ _).1 h1.1
      rw [← e] at h1
      exact ⟨hb, fun ⟨a, ha⟩ => h1.2 ((ran_holds hrr hrw.2 _ _).2 ⟨rfl, a, (canon_holds hr hRw _ _).2 ha⟩)⟩
    · rintro ⟨hb, hn⟩
      obtain ⟨i, h1, -⟩ := (diff_holds hdf (ran_wf hub hUB) (ran_wf hrr hrw) b b).2 ⟨(ran_holds hub hUB.2 b b).2 ⟨rfl, hb⟩, fun h' =>
        hn (((ran_holds hrr hrw.2 b b).1 h').2.imp fun a ha => (canon_holds hr hRw a b).1 ha)⟩
      exact ⟨i, h1⟩
  have hU : (∃ j, uc.key.row j = c) ↔ ∃ c', UC.Holds c' c := by
    constructor
    · rintro ⟨j, rfl⟩
      obtain ⟨e, hc⟩ := (ran_holds huc hUC.2 _ _).1 ⟨j, rfl, rfl⟩
      exact hc
    · intro hc
      obtain ⟨j, h1, -⟩ := (ran_holds huc hUC.2 c c).2 ⟨rfl, hc⟩
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

/-- **`ldiv` holds as `ldivDen`**: `ldivOf_holds` at `canon R`, `canon S`. -/
theorem Tab.ldiv_holds {A B C : Obj} {R : Tab A B} {S : Tab A C} {UB : Tab B B} {UC : Tab C C} {T : Tab B C}
    (h : Tab.ldiv R S UB UC = .ok T) (hRw : R.WF) (hSw : S.WF) (hUB : UB.WF) (hUC : UC.WF)
    (b : B.El) (c : C.El) :
    T.Holds b c ↔ Lang.ldivDen R.Holds S.Holds UB.Holds UC.Holds b c := by
  simp only [Tab.ldiv, bind] at h
  rw [Except.bind_eq_ok'] at h; obtain ⟨r, hr, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨s, hs, h⟩ := h
  rw [ldivOf_holds ⟨R, hr, hRw⟩ ⟨S, hs, hSw⟩ h (canon_wf hr hRw) (canon_wf hs hSw) hUB hUC,
    show r.Holds = R.Holds from funext fun a => funext fun b => propext
    (canon_holds hr hRw a b), show s.Holds = S.Holds from funext fun a => funext fun c => propext
    (canon_holds hs hSw a c)]

/-- **`rdiv` holds as `rdivDen`**: it is `ldivOf` of the two converses (`canon` answers), conversed
(`R / S = (S° \ R°)°`). -/
theorem Tab.rdiv_holds {A B C : Obj} {R : Tab A C} {S : Tab B C} {UA : Tab A A} {UB : Tab B B} {T : Tab A B}
    (h : Tab.rdiv R S UA UB = .ok T) (hRw : R.WF) (hSw : S.WF) (hUA : UA.WF) (hUB : UB.WF)
    (a : A.El) (b : B.El) :
    T.Holds a b ↔ Lang.rdivDen R.Holds S.Holds UA.Holds UB.Holds a b := by
  unfold Tab.rdiv at h
  simp only [bind] at h
  rw [Except.bind_eq_ok'] at h; obtain ⟨S', hS, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨R', hR, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨L, hL, h⟩ := h
  rw [conv_holds h (ldivOf_wf hL (conv_wf hS hSw) (conv_wf hR hRw) hUB hUA),
    ldivOf_holds ⟨_, hS, hSw.2, hSw.1⟩ ⟨_, hR, hRw.2, hRw.1⟩ hL (conv_wf hS hSw) (conv_wf hR hRw) hUB hUA]
  simp only [Lang.ldivDen, Lang.rdivDen, conv_holds hS hSw, conv_holds hR hRw, and_comm (a := ∃ b', UB.Holds b' b)]

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
#guard canonOk (whole (Tab.lt .i64) (idT U)) && canonOk (whole (Tab.leq .i64) (idT U)) &&
  specOk (whole (Tab.lt .i64) (idT U)) (us.flatMap fun a => (us.filter (a < ·)).map (a, ·)) &&
  specOk (whole (Tab.leq .i64) (idT U)) (us.flatMap fun a => (us.filter (a ≤ ·)).map (a, ·)) &&
  newL (whole (Tab.lt .i64) (tab [])) == some [] &&
  newL (whole (Tab.leq .i64) (tab [(4, 0), (2, 0)])) == some [(2, 2), (2, 4), (4, 4)]

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

-- `<`, `≤`, `⊤` on the known sides `K`, `L` against `K ≫ (both sides dom U) ≫ L`, every pair of sides, at `i64`
-- and at `f64` (`FU`: `-0.0 = +0.0`, a NaN in no pair of `<` or `≤`)
#guard sides.all fun ⟨_, K⟩ => sides.all fun ⟨_, L⟩ =>
  sidesOk (Tab.lt .i64) (idT U) K L && sidesOk (Tab.leq .i64) (idT U) K L && sidesOk Tab.top (idT U) K L
#guard fsides.all fun ⟨_, K⟩ => fsides.all fun ⟨_, L⟩ =>
  sidesOk Tab.top (idT FU) K L && sidesOk (Tab.lt .f64) (idT FU) K L && sidesOk (Tab.leq .f64) (idT FU) K L

/-- The keys `3 1 4 -1 3`: `3` twice, `4` the key of no row. -/
private def ds : List Int64 := [3, 1, 4, -1, 3]
private def D := Alg.col ds

/-- `Λ(R)` (`lamDen`) on the keys `ks` in demand (`Tm.lam`): each key to the image of `R` at it, each element once. -/
private def lamSp {A B : Obj} [BEq A.El] [BEq B.El] (ks : List A.El) (R : Tab A B) : List (A.El × List B.El) :=
  ks.map fun a => (a, ((R.toList.filter (·.1 == a)).map (·.2)).eraseDups)

-- `Λ` on `D` against `lamDen` on `D`, and `nil`
#guard ts.all fun ps => canonOk (Tab.lam D (tab ps)) && cellsOk (Tab.lam D (tab ps)) (lamSp ds (tab ps))
#guard newL (Tab.lam D (tab [(3, 1), (1, 2), (3, 1), (-1, 2), (1, 2), (3, -7)])) ==
  some [(-1, [2]), (1, [2]), (3, [-7, 1]), (4, [])]
#guard canonOk (Tab.nil (A := .long) (B := .long) D) &&
  newL (Tab.nil (A := .long) (B := .long) D) == some [(-1, []), (1, []), (3, []), (4, [])]

/-- `-0.0`, `+0.0`, NaN with payloads `1` and `2`, `+inf`, `-inf`, `1.5`, `-0.0` again, as `f64` bits. -/
private def f64s : List UInt64 := [0x8000000000000000, 0, 0x7ff8000000000001, 0x7ff8000000000002, 0x7ff0000000000000,
  0xfff0000000000000, 0x3ff8000000000000, 0x8000000000000000]

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

/-- Arrays of longs: `arrCells` (empty cells, one cell twice, unsorted), a prefix of it, no cells, and
empty cells over no payload. -/
private def arrXs : List (Tab (.arr .long) .long) :=
  [arrTab arrCells arrPay, arrTab (arrCells.take 3) arrPay, arrTab [] arrPay, arrTab [(0, 0, 1), (0, 0, 1)] []]

/-- Arrays of pairs over the payload `(1,5) (2,5) (1,5) (3,6)`: `[(1,5)]` from two ranges, the empty cell, a cell
to the end, one cell twice. -/
private def pairXs : Vals (.arr (.prod .long .long)) 6 :=
  (arrOn [(0, 1, 0), (2, 3, 0), (0, 4, 0), (1, 1, 0), (2, 4, 0), (0, 4, 0)]
    ((Alg.col [1, 2, 1, 3], Alg.col [5, 5, 5, 6]) : Vals (.prod .long .long) 4)).key

/-- The test of pairs of `Q`: the pairs `D` composed with `𝟙` on `Q`'s rows, so `(b, c)` to itself iff `Q b c`. -/
private def pairsIn {B : Obj} (Q : Tab B B) (D : Tab (.prod B B) (.prod B B)) :
    Except String (Tab (.prod B B) (.prod B B)) := do D.comp (← Tab.idU (Q.key, Q.val))

/-- `est(Q)` (`estDen`, `Q` read through `pairsIn`) on the arrays `xs`: `b` of `x` when every other `c` of `x` has
`Q b c`. -/
private def estSp {B : Obj} [BEq B.El] (Q : Tab B B) (xs : List (List B.El)) : List (List B.El × B.El) :=
  xs.flatMap fun x => (x.filter fun b => x.all fun c => c == b || Q.toList.contains (b, c)).map (x, ·)

/-- `front(Q)` (`frontDen`): each `x` to its `c` that no `b` of `x` beats strictly, each once. -/
private def frontSp {B : Obj} [BEq B.El] (Q : Tab B B) (xs : List (List B.El)) : List (List B.El × List B.El) :=
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

-- `est`, `front` against `estDen`, `frontDen`, each order, on arrays of longs and of pairs
#guard arrXs.all fun T => let X := T.key; ordLs.all fun Q =>
  canonOk (Tab.est (pairsIn Q) X) && specOk (Tab.est (pairsIn Q) X) (estSp Q (Vals.rows X)) &&
  canonOk (Tab.front (pairsIn Q) X) && cellsOk (Tab.front (pairsIn Q) X) (frontSp Q (Vals.rows X))
#guard canonOk (Tab.est (pairsIn ordPs) pairXs) &&
  specOk (Tab.est (pairsIn ordPs) pairXs) (estSp ordPs (Vals.rows pairXs)) &&
  canonOk (Tab.front (pairsIn ordPs) pairXs) &&
  cellsOk (Tab.front (pairsIn ordPs) pairXs) (frontSp ordPs (Vals.rows pairXs))

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
    let s := ((x.take t).map Int64.toInt).sum; decide (-2 ^ 63 < s ∧ s < 2 ^ 63)) then some (x, x.foldl (· + ·) 0)
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
  [([1, -1], 0), ([-1], -1)]

/-- One cell `[0, 1)` over `2^63` positions (`pos`, nothing stored): its row is `[0]`. -/
private def bigCell : Except String (Vals (.arr .long) 1) := do
  pure ⟨9223372036854775808, ← colArr .add 1 (← colConst 1 0) (← colConst 1 0),
    ← colArr .add 1 (← colConst 1 1) (← colConst 1 0),
    (⟨.pos, by simp [Ext.Enc.WF], rfl⟩ : Arr .i64 9223372036854775808)⟩

-- `Vals.pack` past `2^63` elements is the error: `cellSpan` would read the size as the signed word `-2^63`, every
-- width `0`, and answer a payload of no rows
#guard match bigCell, bigCell >>= Vals.pack with
  | .ok _, .error e => e == "pack: 1 cells over 9223372036854775808 elements past 2^63"
  | _, _ => false

end Checks

/-! ## `Λ` and `E`: `lam_holds`, `E_holds` -/

namespace Tab
variable {A B : Obj}

/-- **`lamOf D r` is `canon` of one row per key `a` of `D`, its cell the rows of `r` with key `a`, in `r`'s
order**: `L` lists those rows' positions ascending. GROUP over `D ++ r.key` (`sorted_groups`): group `G` holds
the sorted positions `[Fs, Fs + cnt)`, its `D` rows first (`[Fs, Fs + cD)`, `kasc` stable) and then its `r` rows,
ascending in `r` (`hmono`); the cell `[Fs + cD, Fs + cnt)` of the payload reads `r` at `p - n`. -/
theorem lamOf_canon {n : USize} {D : Vals A n} {r : Tab A B} {T : Tab A (.arr B)} (h : Tab.lamOf D r = .ok T)
    (wD : Vals.WF D) (wr : r.WF) :
    ∃ U : Tab A (.arr B), U.canon = .ok T ∧ U.WF ∧ ∀ a ys,
      U.Holds a ys ↔ (∃ i, D.row i = a) ∧
      ∃ L : List Nat, L.Pairwise (· < ·) ∧ (∀ j, j ∈ L ↔ ∃ hj : j < r.n.toNat, r.key.row ⟨j, hj⟩ = a) ∧
        ys = L.map fun j => if hj : j < r.n.toNat then r.val.row ⟨j, hj⟩ else B.dflt := by
  dsimp only [Tab.lamOf] at h
  split at h
  · rename_i hr0
    unfold Tab.nil at h; simp only [bind, Except.bind] at h
    split at h; · cases h
    rename_i z hz; split at h; · cases h
    refine ⟨_, h, ⟨wD, fun i => by rw [Arr.zeros_get hz]; simp, Vals.none_wf ‹_›⟩, fun a ys => ?_⟩
    simp only [Tab.Holds, Vals.row]
    constructor
    · rintro ⟨i, h1, h2⟩
      exact ⟨⟨i, h1⟩, [], List.Pairwise.nil, fun j => ⟨nofun, fun ⟨hj, _⟩ => absurd hj (by omega)⟩, h2.symm⟩
    · rintro ⟨⟨i, h1⟩, L, -, hL, rfl⟩
      have : L = [] := List.eq_nil_iff_forall_not_mem.2 fun j hj => by obtain ⟨hj', _⟩ := (hL j).1 hj; omega
      subst this; exact ⟨i, h1, rfl⟩
  simp only [bind] at h
  rw [Except.bind_eq_ok'] at h; obtain ⟨⟨N, sh⟩, hcat, h⟩ := h; try dsimp only at h
  split at h; · cases h
  rename_i hN
  rw [Except.bind_eq_ok'] at h; obtain ⟨_, -, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨z, hz, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨es, hes, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨⟨vs, p⟩, hasc, h⟩ := h; try dsimp only at h
  rw [Except.bind_eq_ok'] at h; obtain ⟨⟨k, g, f⟩, hseen, h⟩ := h; try dsimp only at h
  rw [Except.bind_eq_ok'] at h; obtain ⟨lt, hlt, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨cD, hcD, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨lo, hlo, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨c1, hc1, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨cnt, hcnt, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨hi, hhi, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨b, hb, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨⟨M, sel⟩, hwh, h⟩ := h; try dsimp only at h
  rw [Except.bind_eq_ok'] at h; obtain ⟨fs, hfs, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨iD, hiD, h⟩ := h
  ------------------------------------------------------------------ the sorted rows and their groups
  obtain ⟨hNn, hoff⟩ := catPlan_ok hcat
  have wz := Vals.concat_wf hNn hoff hz wD wr.1
  have hU : USize.size ≤ 2 ^ 64 := by rcases USize.size_eq with h | h <;> omega
  have hNU := N.toNat_lt_size
  obtain ⟨cs, hcs, hp, hkq⟩ := kasc_grade hasc (fun c hc => (Vals.cols_wf _ hes c hc).1)
  have hpN := kasc_plain hasc
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
    have e := (colMap_post hlt).2 q hq
    -- `gt` with the constant on its left is `lt` with it on its right, by `Op.eval`
    change Op.lt.eval ((raw .i64 N p)[q]?.getD 0) n.toUInt64 = _ at e
    rw [hpw q hq, hnU, eval_lt_nat (by have := hpsN q hq; omega) (by omega), Except.ok.injEq] at e
    rw [← e]; simp
  obtain ⟨cDN, hcDN⟩ : ∃ F : Nat → Nat, F = fun G => (List.range N.toNat).countP
      fun q => Verify.groupOf Kk N.toNat q == G && decide (ps[q]?.getD 0 < n.toNat) := ⟨_, rfl⟩
  obtain ⟨cntN, hcntN⟩ : ∃ F : Nat → Nat, F = fun G => (List.range N.toNat).countP
      fun q => Verify.groupOf Kk N.toNat q == G && true := ⟨_, rfl⟩
  have hcDw : ∀ G < k, (raw .i64 k.toUSize cD)[G]?.getD 0 = (cDN G).toUInt64 := fun G hG => by
    rw [scatter_add_count hcD (colMap_plain hlt) (Verify.groupOf Kk N.toNat) (fun q => decide (ps[q]?.getD 0 < n.toNat)) hgw
      (fun q hq => by have := hgr q hq; omega) hltw G (by omega), hcDN]
  have hcntw : ∀ G < k, (raw .i64 k.toUSize cnt)[G]?.getD 0 = (cntN G).toUInt64 := fun G hG => by
    rw [scatter_add_count hcnt (kscatter_plain hc1 rfl) (Verify.groupOf Kk N.toNat) (fun _ => true) hgw
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
    exact Vals.row_of_codes z wz hes hcs _ _ eK
  have row_grp : ∀ q (hq : q < N.toNat) q' (hq' : q' < N.toNat),
      z.row ⟨_, hpsN q hq⟩ = z.row ⟨_, hpsN q' hq'⟩ →
      Verify.groupOf Kk N.toNat q = Verify.groupOf Kk N.toNat q' := fun q hq q' hq' e => by
    have eK := Vals.codes_of_row z wz hes hcs _ _ e
    have eK2 : Kk q = Kk q' := by rw [hkq q (by omega), hkq q' (by omega), ← hps q hq, ← hps q' hq']; exact eK
    exact (fs'.2.2.1 q hq q' hq').2 eK2
  have hinv : ∀ i < N.toNat, ∃ q, ∃ hq : q < N.toNat, ps[q]?.getD 0 = i := fun i hi => by
    obtain ⟨q, hq, e⟩ := List.mem_iff_getElem.1 (hperm.mem_iff.2 (List.mem_range.2 hi))
    exact ⟨q, by omega, by rw [hps q (by omega)]; exact e⟩
  have zD : ∀ i (hi : i < n.toNat), z.row ⟨i, by omega⟩ = D.row ⟨i, hi⟩ := fun i hi => by
    rw [Vals.concat_row hNn hoff D r.key hz wD wr.1, dif_pos hi]
  have zR : ∀ j (hj : j < r.n.toNat), z.row ⟨n.toNat + j, by omega⟩ = r.key.row ⟨j, hj⟩ := fun j hj => by
    rw [Vals.concat_row hNn hoff D r.key hz wD wr.1, dif_neg (by simp)]; simp only [Nat.add_sub_cancel_left]
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
    have e := (colMap_post hb).2 G (by omega)
    have := hle G; have := hcN G hG
    rw [hcDw G hG,
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
    rw [(kgather_word hiD hpN j hj).2, (kgather_word hfs (kseen_plain hseen).2 j hj).2, hfw _ hG, ← hFs, toNat_toUInt64 (by omega), hpw _ hF]
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
      by_cases hne : cDN G < cntN G
      · obtain ⟨hqN, -, hnq⟩ := hLin G hG (Fs G + cntN G - 1) (by omega) (by omega)
        obtain ⟨hm, -, -⟩ := hy _ hqN hnq
        have e1 : cellStart (raw .i64 M alo.enc) j.toUInt64 = Fs G + cDN G := by
          unfold cellStart; rw [hjU, wl, toInt64_toInt_nat (by omega)]; omega
        have e2 : cellLen (raw .i64 M alo.enc) (raw .i64 M ahi.enc) j.toUInt64 =
            Fs G + cntN G - (Fs G + cDN G) := by
          unfold cellLen; rw [e1, hjU, wh, toInt64_toInt_nat (by omega)]; omega
        have hc : 0 ≤ (alo.get ⟨j, hj⟩).toInt ∧ (alo.get ⟨j, hj⟩).toInt ≤ (ahi.get ⟨j, hj⟩).toInt ∧
            (ahi.get ⟨j, hj⟩).toInt ≤ (m.toNat : Int) := by
          simp only [Arr.get_i64, wl, wh, toInt64_toInt_nat (show Fs G + cDN G < 2 ^ 63 by omega),
            toInt64_toInt_nat (show Fs G + cntN G < 2 ^ 63 by omega)]; omega
        rw [Vals.row_arr ⟨j, hj⟩ hc, e1, e2,
          show Fs G + cntN G - (Fs G + cDN G) = cntN G - cDN G by omega, hLn, List.map_map]
        refine List.map_congr_left fun q hq => ?_
        rw [List.mem_range'_1] at hq
        obtain ⟨hqN, -, hnq⟩ := hLin G hG q hq.1 (by omega)
        obtain ⟨hm, hj', e⟩ := hy q hqN hnq
        simp only [Function.comp, dif_pos hm, dif_pos hj', e]
      · have e : alo.get ⟨j, hj⟩ = ahi.get ⟨j, hj⟩ := by
          simp only [Arr.get_i64, wl, wh, show cntN G = cDN G by omega]
        rw [Vals.row_empty ⟨j, hj⟩ e, hLn, show cntN G - cDN G = 0 by omega]
        rfl
    have hxj : ∀ j (hj : j < M.toNat), ∃ hi0 : ps[Fs ((raw .i64 M sel)[j]?.getD 0).toNat]?.getD 0 < n.toNat,
        xk.row ⟨j, hj⟩ = D.row ⟨_, hi0⟩ := by
      intro j hj
      obtain ⟨hG, hc⟩ := hselj j hj
      have hi0 := hgD _ hG hc
      obtain ⟨i, hi, e⟩ := Vals.gather_row D hxk ⟨j, hj⟩
      simp only at hi
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
  ------------------------------------------------------------------ the payload: `r.val` at `p - n`
  rw [Except.bind_eq_ok'] at h; obtain ⟨mx, hmx, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨y, hy, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨xk, hxk, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨alo, halo, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨ahi, hahi, h⟩ := h
  -- the cell of a kept group `G` is `[Fs G + cDN G, Fs G + cntN G)`, inside the `N` sorted rows (`hcN`)
  refine ⟨_, h, ⟨Vals.gather_wf hxk wD, fun j => ?_, Vals.gather_wf hy wr.2⟩,
    key y (fun q hq hnq => ?_) hxk halo hahi⟩
  · obtain ⟨hG, -⟩ := hselj j.1 j.2
    have wl := hgat halo hlow j.1 j.2; have wh := hgat hahi hhiw j.1 j.2
    generalize ((raw .i64 M sel)[j.1]?.getD 0).toNat = G at hG wl wh
    have hcN' := hcN G hG; have hle' := hle G
    rw [Arr.get_i64, Arr.get_i64, wl, wh, toInt64_toInt_nat (by omega), toInt64_toInt_nat (by omega)]
    omega
  · have hs63 : ps[q]?.getD 0 - n.toNat < 2 ^ 63 := by have := hpsN q hq; omega
    have hmxw : (raw .i64 N mx)[q]?.getD 0 = (ps[q]?.getD 0 - n.toNat).toUInt64 := by
      -- one `kscan`: `p + (0 - n)`, then `max` with `0` (`colMap_chain`)
      obtain ⟨-, -, -, hr⟩ := colMap_chain hmx
      obtain ⟨x', y', v, W, hx, hy', hv, hW, ho⟩ := hr q hq
      cases hx; cases hy'; cases hv
      rw [ho, Option.getD_some, if_neg (by decide : QAtomicType.i64 ≠ .u1)]
      simp only [chain, List.foldlM, Op.eval, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at hW
      rw [hpw q hq, hnU, neg_add_word, ← toUInt64_sub hnq] at hW
      rw [← hW]; split
      · rfl
      · rename_i hc
        have z0 : (0 : UInt64).toInt64.toInt = 0 := rfl
        change ¬ (0 : UInt64).toInt64 < (ps[q]?.getD 0 - n.toNat).toUInt64.toInt64 at hc
        rw [Int64.lt_iff_toInt_lt, z0, toInt64_toInt_nat hs63] at hc
        have h0 : ps[q]?.getD 0 - n.toNat = 0 := by omega
        rw [h0]; rfl
    obtain ⟨i, hi, e⟩ := Vals.gather_row r.val hy ⟨q, hq⟩
    simp only at hi
    rw [hmxw, toNat_toUInt64 (by omega)] at hi
    exact ⟨hq, by omega, by rw [e]; congr 1; exact Fin.ext hi.symm⟩


/-- **`lam D R` denotes `Λ(R)` on the keys `D`, each cell in `R`'s order codes**: `a` of `D` to the list `ys` of its
images under `R`, each once and ascending by the codes `kasc` gives the rows `(a, b)` of `R` (strictly: no two
equal by stored bits). The codes order the images strictly (`keys_of_lexLe`, `Vals.codes_of_row`), so two such
lists are one (`pairwise_eq_of_mem`), and `lam_canon`'s cell is one (`canon_sorted`). -/
theorem lamOf_holds {n : USize} {D : Vals A n} {R r : Tab A B} {T : Tab A (.arr B)} (hr : R.canon = .ok r)
    (h : Tab.lamOf D r = .ok T) (wD : Vals.WF D) (wr : r.WF) (wR : R.WF) (a : A.El) (ys : List B.El) :
    T.Holds a ys ↔ (∃ i, D.row i = a) ∧ (∀ b, b ∈ ys ↔ R.Holds a b) ∧
      ∀ es, Vals.cols (A := .prod A B) (R.key, R.val) = .ok es →
        ∃ s : Fin ys.length → Fin R.n.toNat, (∀ u, R.key.row (s u) = a ∧ R.val.row (s u) = ys[u]) ∧
          ∀ u u' : Fin ys.length, u.1 < u'.1 → lexLe (ascKeys R.n es) (s u) (s u') = true ∧
            seenKey R.n es (s u) ≠ seenKey R.n es (s u') := by
  obtain ⟨U, hU, wU, hH⟩ := lamOf_canon h wD wr
  obtain ⟨es0, cs, hes0, hcs⟩ := canon_codes hr
  rw [canon_holds hU wU, hH]
  -- the strict order the codes put on the images of `a`
  have hsk : ∀ i j : Fin R.n.toNat, R.key.row i = R.key.row j → R.val.row i = R.val.row j →
      seenKey R.n es0 i = seenKey R.n es0 j := fun i j e1 e2 =>
    Vals.codes_of_row (A := .prod A B) (R.key, R.val) wR hes0 hcs i j (Prod.ext e1 e2)
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
    · rw [← canon_holds hr wR, List.mem_map]
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

/-- **`lam D R` denotes `lamDen R` on the keys `D`** (`Tm.lam`): two rows of one key whose codes ascend strictly
(`lexLe`, distinct `seenKey`) hold values ascending in `B.lt` (`Vals.lamLaw`, `kasc`'s order is `Obj.lt`), so
`lam_holds`'s cell is `B.lt`-ascending, and `lamDen`'s list is that cell (`pairwise_eq_of_mem`). -/
theorem lamOf_den {n : USize} {D : Vals A n} {R r : Tab A B} {T : Tab A (.arr B)} (hr : R.canon = .ok r)
    (h : Tab.lamOf D r = .ok T) (wD : Vals.WF D) (wr : r.WF) (wR : R.WF) (a : A.El) (ys : List B.El) :
    T.Holds a ys ↔ (∃ i, D.row i = a) ∧ Lang.lamDen R.Holds a ys := by
  obtain ⟨U, hU, wU, hH⟩ := lamOf_canon h wD wr
  obtain ⟨es0, cs0, hes0, hcs0⟩ := canon_codes hr
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
    have := Vals.lamLaw (A := A) (B := B) (R.key, R.val) wR hes0 hcs0 (s ⟨u, hu⟩) (s ⟨u', hu'⟩) (h1.trans h3.symm) hl hne
    simp only [Fin.getElem_fin] at h2 h4
    rw [← h2, ← h4]; exact this
  rw [lamOf_holds hr h wD wr wR]
  constructor
  · rintro ⟨hD, hm, ho⟩; exact ⟨hD, up ys ho, hm⟩
  · rintro ⟨hD, hp, hm⟩
    obtain ⟨L, hLp, hLm⟩ := exists_range_filter r.n.toNat fun j hj => r.key.row ⟨j, hj⟩ = a
    have hT0 := (canon_holds hU wU _ _).2 ((hH _ _).2 ⟨hD, L, hLp, hLm, rfl⟩)
    obtain ⟨-, hm0, ho0⟩ := (lamOf_holds hr h wD wr wR a _).1 hT0
    rw [pairwise_eq_of_mem lirr lasym hp (up _ ho0) fun b => by rw [hm, hm0]]
    exact (lamOf_holds hr h wD wr wR a _).1 hT0

/-- **`lam D R` denotes `lamDen R` on the keys `D`**: `lamOf_den` at `canon R`. -/
theorem lam_den {n : USize} {D : Vals A n} {R : Tab A B} {T : Tab A (.arr B)} (h : Tab.lam D R = .ok T)
    (wD : Vals.WF D) (wR : R.WF) (a : A.El) (ys : List B.El) :
    T.Holds a ys ↔ (∃ i, D.row i = a) ∧ Lang.lamDen R.Holds a ys := by
  simp only [Tab.lam, bind] at h; rw [Except.bind_eq_ok'] at h; obtain ⟨r, hr, h⟩ := h
  exact lamOf_den hr h wD (canon_wf hr wR) wR a ys

theorem mem_wf {n : USize} {X : Vals (.arr B) n} {t : Tab (.arr B) B} (h : Tab.mem X = .ok t) (hX : Vals.WF X) :
    t.WF := by
  obtain ⟨m, lo, hi, f⟩ := X
  simp only [Tab.mem, bind, Except.bind, pure, Except.pure] at h
  okSplit
  exact canon_wf h ⟨Vals.gather_wf ‹_› hX, Vals.gather_wf ‹_› hX.2⟩

/-- **`mem X` is canonical**: its last step is `canon` (`Tab.Canonical`). -/
theorem mem_canonical {n : USize} {X : Vals (.arr B) n} {T : Tab (.arr B) B} (h : Tab.mem X = .ok T)
    (hX : Vals.WF X) : ∃ U : Tab (.arr B) B, U.canon = .ok T ∧ U.WF := by
  obtain ⟨m, lo, up, f⟩ := X
  dsimp only [Tab.mem] at h
  split at h; · cases h
  simp only [bind] at h
  rw [Except.bind_eq_ok'] at h; obtain ⟨_, -, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨wd, -, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨⟨Tn, G, u⟩, -, h⟩ := h; try dsimp only at h
  rw [Except.bind_eq_ok'] at h; obtain ⟨sg, -, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨ix, -, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨x, hx, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨y, hy, h⟩ := h
  exact ⟨_, h, Vals.gather_wf hx hX, Vals.gather_wf hy hX.2⟩

/-- **`setify X` denotes `Λ(∋)` on the arrays `X`** (`rowDens`'s `setify`): `lam_den` of `mem_holds`. -/
theorem setify_den {n : USize} {X : Vals (.arr B) n} {T : Tab (.arr B) (.arr B)} (h : Tab.setify X = .ok T)
    (hw : Vals.WF X)
    (xs : List B.El) (ys : List B.El) :
    T.Holds xs ys ↔ (∃ i, X.row i = xs) ∧ Lang.lamDen (fun xs b => b ∈ xs : Core.Rel (Obj.El (.arr B)) (Obj.El B)) xs ys := by
  unfold Tab.setify at h; simp only [bind] at h
  rw [Except.bind_eq_ok'] at h; obtain ⟨G, hG, h⟩ := h
  obtain ⟨U, hU, wU⟩ := mem_canonical hG hw
  rw [lamOf_den hU h hw (mem_wf hG hw) wU]
  have hm' : (∃ i, X.row i = xs) → ∀ b, U.Holds xs b ↔ b ∈ xs := fun hX b =>
    (canon_holds hU wU xs b).symm.trans ((mem_holds hG hw xs b).trans (and_iff_right hX))
  constructor
  · rintro ⟨hX, hp, hm⟩
    exact ⟨hX, hp, fun b => (hm b).trans (hm' hX b)⟩
  · rintro ⟨hX, hp, hm⟩
    exact ⟨hX, hp, fun b => (hm b).trans (hm' hX b).symm⟩

/-- **`tau X` denotes `τ` on `X`** (`rowDens`: `Y = [a]`): `lam_den` of `idU_holds`, the one list of
`A.lt`-ascending elements `{a}` being `[a]` (`pairwise_eq_of_mem`). -/
theorem tau_den {A : Obj} {n : USize} {X : Vals A n} {T : Tab A (.arr A)} (h : Tab.tau X = .ok T)
    (wX : Vals.WF X) (a : A.El) (ys : List A.El) : T.Holds a ys ↔ (∃ i, X.row i = a) ∧ ys = [a] := by
  unfold Tab.tau at h; simp only [bind] at h
  rw [Except.bind_eq_ok'] at h; obtain ⟨I, hI, h⟩ := h
  rw [lam_den h wX (idU_wf hI wX)]
  have lirr : ∀ x, ¬A.lt x x := fun x => List.lt_irrefl _
  have lasym : ∀ x y, A.lt x y → ¬A.lt y x := fun _ _ => List.lt_asymm
  constructor
  · rintro ⟨hX, hp, hm⟩
    refine ⟨hX, pairwise_eq_of_mem lirr lasym hp (List.pairwise_singleton _ _) fun b => (hm b).trans ?_⟩
    rw [idU_holds hI wX, List.mem_singleton]; exact ⟨fun h => h.1.symm, fun h => ⟨h.symm, hX⟩⟩
  · rintro ⟨hX, rfl⟩
    refine ⟨hX, List.pairwise_singleton _ _, fun b => ?_⟩
    rw [idU_holds hI wX, List.mem_singleton]; exact ⟨fun h => ⟨h.symm, hX⟩, fun h => h.1.symm⟩

end Tab

end Rel

namespace Rel
open Rel.Ext Rel.Kernel Rel.Verify Ext.Enc

namespace Tab

/-- **The test `q` agrees with `TQ` on the diagonal of the pairs it is given** (`D.val`): the one hypothesis on a test
`Q` of `est`, `front`, `thinL`, `merge`, which read `Q` only at `p Q p`. -/
def QDiag {k : Obj} (q : Tab k k → Except String (Tab k k)) (TQ : k.El → k.El → Prop) : Prop :=
  ∀ D T, D.WF → q D = .ok T → ∀ p, (∃ i, D.val.row i = p) → (T.Holds p p ↔ TQ p p)

/-- **`diag q D` denotes the rows `p` of a coreflexive `D` with `TQ p p`**, `q` agreeing with `TQ` there. -/
theorem diag_holds {k : Obj} {q : Tab k k → Except String (Tab k k)} {TQ : k.El → k.El → Prop} (hq : QDiag q TQ)
    (hqw : ∀ D t, q D = .ok t → D.WF → t.WF)
    {D Δ : Tab k k} (hD : ∀ p p', D.Holds p p' → p = p') (wD : D.WF) (h : diag q D = .ok Δ) (p p' : k.El) :
    Δ.Holds p p' ↔ p = p' ∧ D.Holds p p ∧ TQ p p := by
  unfold diag at h; simp only [bind] at h
  rw [Except.bind_eq_ok'] at h; obtain ⟨Q, hQ, h⟩ := h
  rw [inter_holds h (hqw _ _ hQ wD) wD]
  constructor
  · rintro ⟨hqd, hd⟩
    obtain rfl := hD _ _ hd
    obtain ⟨i, -, hv⟩ := id hd
    exact ⟨rfl, hd, (hq _ _ wD hQ p ⟨i, hv⟩).1 hqd⟩
  · rintro ⟨rfl, hd, t⟩
    obtain ⟨i, -, hv⟩ := id hd
    exact ⟨(hq _ _ wD hQ p ⟨i, hv⟩).2 t, hd⟩

end Tab

namespace Tab

/-- **`atPos k X` denotes `atDen k`** (`Tab.atPos`): the cells `[SN, EN)` wider than `k` (`cellSpan_spec`,
`whereCol` of `k < EN - SN`), each to the payload row `SN + k`. -/
theorem atPos_holds {B : Obj} {k : Nat} {n : USize} {X : Vals (.arr B) n} {T : Tab (.arr B) B}
    (h : Tab.atPos k X = .ok T) (hX : Vals.WF X) (xs : List B.El) (x : B.El) :
    T.Holds xs x ↔ (∃ i, X.row i = xs) ∧ Lang.atDen k xs x := by
  obtain ⟨m, lo, up, f⟩ := X
  dsimp only [Tab.atPos] at h
  split at h; · cases h
  rename_i hb
  simp only [bind] at h
  rw [Except.bind_eq_ok'] at h; obtain ⟨_, -, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨w, hw, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨lt, hlt, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨⟨M, sel⟩, hwh, h⟩ := h; try dsimp only at h
  rw [Except.bind_eq_ok'] at h; obtain ⟨a, ha, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨ix, hix, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨K, hK, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨V, hV, h⟩ := h
  rw [canon_holds h ⟨Vals.gather_wf hK hX, Vals.gather_wf hV hX.2⟩]
  have hm63 : m.toNat < 2 ^ 63 := by omega
  have hk63 : k < 2 ^ 63 := by omega
  obtain ⟨SN, EN, hw1, hb1, hrow⟩ := cellSpan_spec hX.1 hm63 f
  have hwl : ∀ i, EN i - SN i < 2 ^ 63 := fun i => by have := hb1 i; omega
  have hww : ∀ i < n.toNat, (raw .i64 n w)[i]?.getD 0 = (EN i - SN i).toUInt64 := fun i hi => by
    have es := (colMap_raw hw).2.2.2 i hi
    rw [(hw1 i hi).2, (hw1 i hi).1] at es; simp only [Op.eval, Except.ok.injEq] at es
    rw [← es, toUInt64_sub (hb1 i).1]
  have hltw : ∀ i < n.toNat, (raw .i64 n lt)[i]?.getD 0 = if k < EN i - SN i then 1 else 0 := fun i hi => by
    have es := (colMap_post hlt).2 i hi
    rw [hww i hi, eval_lt_nat hk63 (hwl i)] at es
    exact (Except.ok.inj es).symm
  have h2 : ∀ i < n.toNat, (raw .i64 n lt)[i]?.getD 0 < 2 := fun i hi => by rw [hltw i hi]; split <;> decide
  have hsz := whereCol_size hwh
  have hmem : ∀ y, (∃ j < M.toNat, ((raw .i64 M sel)[j]?.getD 0).toNat = y) ↔
      y < n.toNat ∧ (raw .i64 n lt)[y]?.getD 0 ≠ 0 := fun y => by
    have hs : y ∈ ((raw .i64 M sel).toList.map UInt64.toNat) ↔
        y ∈ (List.range n.toNat).filter fun i => (raw .i64 n lt)[i]?.getD 0 ≠ 0 := by rw [whereCol_spec hwh h2]
    rw [List.mem_iff_getElem] at hs
    simp only [List.mem_filter, List.mem_range, decide_eq_true_eq, List.length_map,
      Array.length_toList, hsz, List.getElem_map, Array.getElem_toList] at hs
    rw [← hs]
    constructor
    · rintro ⟨j, hj, rfl⟩; exact ⟨j, hj, by rw [Array.getElem?_eq_getElem (by omega)]; rfl⟩
    · rintro ⟨j, hj, rfl⟩; exact ⟨j, hj, by rw [Array.getElem?_eq_getElem (by omega)]; rfl⟩
  have haw : ∀ i < n.toNat, (raw .i64 n a)[i]?.getD 0 = (SN i + k).toUInt64 := fun i hi => by
    have es := (colMap_post ha).2 i hi
    rw [(hw1 i hi).1] at es; simp only [Op.eval, Except.ok.injEq] at es
    rw [← es, UInt64.add_comm, ← UInt64.ofNat_add]
  let g : Nat → B.El := fun k => if h : k < m.toNat then Vals.row f ⟨k, h⟩ else B.dflt
  have hJ : ∀ j : Fin M.toNat, ∃ i : Fin n.toNat, k < EN i - SN i ∧ ((raw .i64 M sel)[j.1]?.getD 0).toNat = i ∧
      K.row j = Vals.row (A := .arr B) ⟨m, lo, up, f⟩ i ∧ V.row j = g (SN i + k) := by
    intro j
    obtain ⟨i, hi, hKi⟩ := Vals.gather_row _ hK j
    obtain ⟨hin, hx⟩ := (hmem i).1 ⟨j.1, j.2, hi⟩
    have c : k < EN i - SN i := by rw [hltw i hin] at hx; split at hx <;> first | assumption | exact absurd rfl hx
    obtain ⟨i', hi', hVi⟩ := Vals.gather_row _ hV j
    rw [(kgather_word hix (colMap_plain ha) j.1 j.2).2, hi, haw i i.2, toNat_toUInt64 (by have := hb1 i; omega)] at hi'
    refine ⟨i, c, hi, hKi, hVi.trans ?_⟩
    have hS : SN i + k < m.toNat := by have := hb1 i; omega
    simp only [g, dif_pos hS]; congr 1; exact Fin.ext hi'.symm
  have hel : ∀ i : Fin n.toNat, Vals.row (A := .arr B) ⟨m, lo, up, f⟩ i =
      (List.range' (SN i) (EN i - SN i)).map g := hrow
  simp only [Tab.Holds]
  constructor
  · rintro ⟨j, rfl, rfl⟩
    obtain ⟨i, c, -, hKi, hVi⟩ := hJ j
    rw [hKi, hVi]
    refine ⟨⟨i, rfl⟩, ?_⟩
    rw [hel i]
    exact ⟨by simpa using c, by simp⟩
  · rintro ⟨⟨i, rfl⟩, hk, rfl⟩
    have c : k < EN i - SN i := by have := hk; rw [hel i] at this; simpa using this
    obtain ⟨j, hj, hji⟩ := (hmem i).2 ⟨i.2, by rw [hltw i i.2, if_pos c]; decide⟩
    obtain ⟨i', -, hi', hKi, hVi⟩ := hJ ⟨j, hj⟩
    have e' : i' = i := Fin.ext (by rw [← hi', hji])
    subst e'
    refine ⟨⟨j, hj⟩, hKi, hVi.trans ?_⟩
    rw [List.getElem_of_eq (hel i') hk, List.getElem_map, List.getElem_range', Nat.one_mul]

end Tab

end Rel

namespace Rel
open Rel.Ext Rel.Kernel Rel.Verify Ext.Enc

namespace Tab

/-- Rows pairwise distinct as values make `toList` duplicate-free. -/
theorem toList_nodup {k v : Obj} {R : Tab k v}
    (h : ∀ j j' : Fin R.n.toNat, j ≠ j' → (R.key.row j, R.val.row j) ≠ (R.key.row j', R.val.row j')) :
    R.toList.Nodup := by
  unfold Tab.toList; rw [List.Nodup, List.pairwise_iff_getElem]
  intro i j hi hj hij
  simp only [List.getElem_ofFn]
  exact h _ _ fun e => Nat.ne_of_lt hij (congrArg Fin.val e)

/-- **`pack` keeps the row count and every row**, in order (`Vals.pack_row`). -/
theorem pack_toList {k v : Obj} {R R' : Tab k v} (h : R.pack = .ok R') (wR : R.WF) :
    R'.n = R.n ∧ R'.toList = R.toList := by
  simp only [Tab.pack, bind] at h
  rw [Except.bind_eq_ok'] at h; obtain ⟨kk, hk, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨vv, hv, h⟩ := h
  cases h
  exact ⟨rfl, by simp only [Tab.toList, Vals.pack_row _ hk wR.1, Vals.pack_row _ hv wR.2]⟩

/-- **`R ∪ S`'s rows are distinct**: it is `canon` of the concatenation (`union_sorted`, `canon_distinct`). -/
theorem union_nodup {k v : Obj} {R S U : Tab k v} (h : R.union S = .ok U) (hR : R.WF) (hS : S.WF) :
    U.toList.Nodup := by
  obtain ⟨C, hC, hc⟩ := union_sorted h
  exact toList_nodup fun _ _ hjj => canon_distinct hc (concat_wf hC hR hS) hjj

/-- **A chain step that keeps the row count keeps the relation**: `X` inside `Y`, both duplicate-free and of one
    row count, so `Y` inside `X` (`nodup_length_eq_iff` on their rows). -/
theorem holds_of_n {k v : Obj} {X Y : Tab k v} (dX : X.toList.Nodup) (dY : Y.toList.Nodup)
    (hXY : ∀ a b, X.Holds a b → Y.Holds a b) (hn : X.n = Y.n) : ∀ a b, Y.Holds a b → X.Holds a b := by
  classical
  have e := (nodup_length_eq_iff dX dY fun p hp => (holds_iff_mem_toList Y p.1 p.2).1
    (hXY _ _ ((holds_iff_mem_toList X p.1 p.2).2 hp))).1 (by simp [Tab.toList, hn])
  exact fun a b hb => (holds_iff_mem_toList X a b).2 (e ((holds_iff_mem_toList Y a b).1 hb))

/-- **The round invariant of `Tab.fixOn`**: an `I` that every round keeps (`hI`: from `X`, `step X` then `pack`)
    holds of the answer's round, whose `pack`ed state is the answer with the row count of the state before it. -/
theorem fixOn_inv {σ : Type} {size : σ → USize} {pack : σ → Except String σ} {out : String}
    {step : σ → Except String σ} (I : σ → Prop)
    (hI : ∀ X Y Y', I X → step X = .ok Y → pack Y = .ok Y' → I Y') :
    ∀ n X T, I X → Tab.fixOn size pack out step n X = .ok T →
      ∃ X' Y, I X' ∧ step X' = .ok Y ∧ pack Y = .ok T ∧ size T = size X' := by
  intro n
  induction n with
  | zero => intro X T _ h; simp [Tab.fixOn] at h
  | succ n ih =>
    intro X T hX h
    simp only [Tab.fixOn, bind] at h
    rw [Except.bind_eq_ok'] at h; obtain ⟨Y', hY', h⟩ := h
    rw [Except.bind_eq_ok'] at hY'; obtain ⟨Y, hY, hp⟩ := hY'
    split at h
    · rename_i e; cases h; exact ⟨X, Y, hX, hY, hp, beq_iff_eq.1 e⟩
    · exact ih Y' T (hI X Y Y' hX hY hp) h

end Tab

end Rel
