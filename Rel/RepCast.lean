import Rel.Run.Cast
import Rel.RepSetOps
import Rel.RepCanon
import Rel.RepCols
import Rel.RepTabDiv
import Rel.RepTabArith
import Rel.Lang.Den

/-! The law of `$` (`Tab.cast`): its table is the graph of `QAtomicType.embed` on the values in demand. -/

namespace Rel
open Rel.Ext Rel.Kernel

namespace Tab

/-- An atom holding a number (`storeFmt?`) is none of `general`, `sym`, `u1`. -/
theorem storeFmt_ne {u : QAtomicType} (h : u.storeFmt?.isSome) : u ≠ .general ∧ u ≠ .sym ∧ u ≠ .u1 := by
  cases u <;> revert h <;> decide

/-- A word read as an atom holding a number (`atomOfBits`) is `ofBits t` of it. -/
theorem of_atomOfBits {t : QAtomicType} (a : UInt64) (hg : t ≠ .general) (h : t.storeFmt?.isSome) :
    (Dep.Carrier.of? t (.atom (Column.atomOfBits t a hg))).getD default = QAtomicType.ofBits t a := by
  cases t <;> first | rfl | exact absurd h (by decide)

/-- The rows of an `Arr.gather` read a valid column. -/
theorem gather_valid {u : QAtomicType} {m n : USize} {ix : Enc} {x : Arr u n} {y : Arr u m}
    (h : Arr.gather m ix x = .ok y) : Kernel.Enc.Valid n x.enc := by
  unfold Arr.gather at h; split at h
  · exact kgather_valid (by assumption)
  · cases h

/-- **A column map followed by a filter of nulls** (`$`, the unary float verbs): `Tab.keep` of the rows `(X i, w i)` at
the flag `flag` holds `a b` exactly where `a` is a value of `X` and `P a b`, given that row by row the flag is a bit,
set exactly where `P` relates the value to the answer `w i`. -/
theorem keep_map_holds {s t : QAtomicType} {n : USize} {X : Arr s n} {w : Arr t n} {flag : Enc}
    {T : Tab (.atom s) (.atom t)} {P : (Obj.atom s).El → (Obj.atom t).El → Prop}
    (hU : Tab.keep (k := .atom s) (v := .atom t) ⟨n, X, w⟩ flag = .ok T)
    (row : ∀ i : Fin n.toNat, wd n flag i < 2 ∧ ∀ v, (wd n flag i ≠ 0 ∧ w.get i = v) ↔ P (X.get i) v)
    (a : (Obj.atom s).El) (b : (Obj.atom t).El) : T.Holds a b ↔ (∃ i, Vals.row (A := .atom s) X i = a) ∧ P a b := by
  rw [keep_holds hU (fun i hi => (row ⟨i, hi⟩).1)]
  constructor
  · rintro ⟨i, hf, rfl, rfl⟩
    exact ⟨⟨i, rfl⟩, by rw [Vals.row_atom, Vals.row_atom]; exact ((row i).2 _).1 ⟨hf, rfl⟩⟩
  · rintro ⟨⟨i, rfl⟩, hp⟩
    rw [Vals.row_atom] at hp
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
  obtain ⟨c, hc, h⟩ := Except.bind_eq_ok'.1 h
  obtain ⟨flag, hf, hU⟩ := Except.bind_eq_ok'.1 h
  have hv : Kernel.Enc.Valid n X.enc ∧ Kernel.Enc.Valid n w.enc := by
    unfold Tab.keep at hU
    obtain ⟨⟨M, sel⟩, -, hU⟩ := Except.bind_eq_ok'.1 hU
    obtain ⟨K, hK, hU⟩ := Except.bind_eq_ok'.1 hU
    obtain ⟨V, hV, -⟩ := Except.bind_eq_ok'.1 hU
    exact ⟨gather_valid (x := X) hK, gather_valid (x := w) hV⟩
  have hcm := colMap_get (colArr_ok hw)
  have hfl := colMap_raw hf
  have hcr := colConst_raw hc
  -- each row: the flag `1` and the image read back, or the flag `0` and no image
  have row : ∀ i : Fin n.toNat,
      ((Enc.raw .i64 n flag)[i.1]?.getD 0 = 1 ∧ QAtomicType.embed s t (X.get i) = some (w.get i)) ∨
      ((Enc.raw .i64 n flag)[i.1]?.getD 0 = 0 ∧ QAtomicType.embed s t (X.get i) = none) := by
    intro i
    obtain ⟨a, ha, -, hxa⟩ := Arr.get_raw_atom X hv.1 hgs (storeFmt_ne hst.1).2.1 i
    obtain ⟨v, hev, hwv⟩ := hcm.2 i.1 i.2
    obtain ⟨b, hb, -, hwb⟩ := Arr.get_raw_atom w hv.2 hgt (storeFmt_ne hst.2).2.1 i
    rw [ha] at hev
    simp only [Option.getD_some, Op.eval, Except.ok.injEq] at hev
    rw [if_neg htu] at hwv
    rw [hwv] at hb; cases hb
    have hfi := hfl.2.2.2 i.1 i.2
    rw [hwv, hcr] at hfi
    simp only [Option.getD_some, Array.getElem?_replicate, i.2, if_true] at hfi
    have hfv := eval_ne_word hfi
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
  rcases row i with h | h <;> simp only [wd, h.1, h.2] <;> simp

/-- The `Op` a `unaryOps` row runs reads one operand. -/
theorem unaryOps_readsAcc : ∀ {l : List (String × Op)}, (∀ p ∈ l, p.2.readsAcc = false) → ∀ {s o},
    l.lookup s = some o → o.readsAcc = false
  | [], _, _, _, h => nomatch h
  | (k, v) :: l, hl, s, o, h => by
    simp only [List.lookup] at h; split at h
    · cases h; exact hl _ List.mem_cons_self
    · exact unaryOps_readsAcc (fun p hp => hl p (List.mem_cons_of_mem _ hp)) h

/-- **A `unaryOps` row `s` on the values `X`** denotes `unaryDen o` of its `Op` there: no row at an object holding no
float, nor where the answer is NaN. -/
theorem unary_den {A : Obj} {n : USize} {X : Vals A n} {T : Tab A A} {s : String} {o : Op}
    (hs : unaryOps.lookup s = some o) (h : Tab.unary s X = .ok T) (a b : A.El) :
    T.Holds a b ↔ (∃ i, X.row i = a) ∧ Lang.unaryDen o A a b := by
  have ho := unaryOps_readsAcc (by decide) hs
  match A, X, T, h, a, b with
  | .atom t, X, T, h, a, b =>
    simp only [Tab.unary, hs] at h
    split at h
    case isFalse => cases h
    rename_i hf
    obtain ⟨⟨w, flag⟩, hm, hU⟩ := Except.bind_eq_ok'.1 h
    exact keep_map_holds hU (fmapCols_spec hf ho hm) a b
  | .prod .., _, _, h, _, _ | .arr _, _, _, h, _, _ | .sum .., _, _, h, _, _ => simp [Tab.unary, hs] at h

/-- `$` at any objects: the graph `castDen A B` on the values `X`, no row where a side is no atom. -/
theorem cast_den {A B : Obj} {n : USize} {X : Vals A n} {T : Tab A B} (h : Tab.cast X = .ok T) (a : A.El) (b : B.El) :
    T.Holds a b ↔ (∃ i, X.row i = a) ∧ Lang.castDen A B a b := by
  match A, B, X, T, h, a, b with
  | .atom _, .atom _, _, _, h, a, b => exact cast_holds h a b
  | .atom _, .prod .., _, _, h, _, _ | .atom _, .arr _, _, _, h, _, _ | .atom _, .sum .., _, _, h, _, _
  | .prod .., _, _, _, h, _, _ | .arr _, _, _, _, h, _, _ | .sum .., _, _, _, h, _, _ =>
    simp [Tab.cast] at h

end Tab
end Rel
