import Rel.Run.Cast
import Rel.RepSetOps
import Rel.RepCanon
import Rel.RepCols
import Rel.RepTabDiv
import Rel.Lang.Den

/-! The law of `$` (`Tab.cast`): its table is the graph of `QAtomicType.embed` on the values in demand. -/

namespace Rel
open Rel.Ext Rel.Kernel

namespace Tab

/-- A number atom (`numFmt?`) is none of `general`, `sym`, `u1`. -/
theorem numFmt_ne {u : QAtomicType} (h : u.numFmt?.isSome) : u ≠ .general ∧ u ≠ .sym ∧ u ≠ .u1 := by
  cases u <;> revert h <;> decide

/-- A word read as an atom of a number type `t` (`atomOfBits`) is `ofBits t` of it. -/
theorem of_atomOfBits {t : QAtomicType} (a : UInt64) (hg : t ≠ .general) (h : t.numFmt?.isSome) :
    (Dep.Carrier.of? t (.atom (Column.atomOfBits t a hg))).getD default = QAtomicType.ofBits t a := by
  cases t <;> first | rfl | exact absurd h (by decide)

/-- The rows of an `Arr.gather` read a valid column. -/
theorem gather_valid {u : QAtomicType} {m n : USize} {ix : Enc} {x : Arr u n} {y : Arr u m}
    (h : Arr.gather m ix x = .ok y) : Kernel.Enc.Valid n x.enc := by
  unfold Arr.gather at h; split at h
  · exact kgather_valid (by assumption)
  · cases h

/-- **`X $ t` denotes the graph of `embed s t`** on the values `X`: a value with no image at `t` has no row. -/
theorem cast_holds {s t : QAtomicType} {n : USize} {X : Vals (.atom s) n} {T : Tab (.atom s) (.atom t)}
    (h : Tab.cast X = .ok T) (a : (Obj.atom s).El) (b : (Obj.atom t).El) :
    T.Holds a b ↔ (∃ i, X.row i = a) ∧ QAtomicType.embed s t a = some b := by
  dsimp only [Tab.cast] at h
  split at h
  case isFalse => cases h
  rename_i hok
  have hst : s.numFmt?.isSome ∧ t.numFmt?.isSome := by
    unfold QAtomicType.castOK at hok; split at hok <;> simp_all
  obtain ⟨hgs, -, -⟩ := numFmt_ne hst.1
  obtain ⟨hgt, -, htu⟩ := numFmt_ne hst.2
  obtain ⟨w, hw, h⟩ := Except.bind_eq_ok'.1 h
  obtain ⟨c, hc, h⟩ := Except.bind_eq_ok'.1 h
  obtain ⟨flag, hf, h⟩ := Except.bind_eq_ok'.1 h
  obtain ⟨U, hU, hT⟩ := Except.bind_eq_ok'.1 h
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
    obtain ⟨a, ha, -, hxa⟩ := Arr.get_raw_atom X hv.1 hgs (numFmt_ne hst.1).2.1 i
    obtain ⟨v, hev, hwv⟩ := hcm.2 i.1 i.2
    obtain ⟨b, hb, -, hwb⟩ := Arr.get_raw_atom w hv.2 hgt (numFmt_ne hst.2).2.1 i
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
  rw [canon_holds hT, keep_holds hU (fun i hi => by rcases row ⟨i, hi⟩ with h | h <;> rw [h.1] <;> decide)]
  constructor
  · rintro ⟨i, hf, rfl, rfl⟩
    rcases row i with h | h
    · exact ⟨⟨i, rfl⟩, by rw [Vals.row_atom, Vals.row_atom]; exact h.2⟩
    · exact absurd h.1 hf
  · rintro ⟨⟨i, rfl⟩, he⟩
    rcases row i with h | h
    · refine ⟨i, by rw [h.1]; decide, rfl, ?_⟩
      rw [Vals.row_atom] at he ⊢; rw [h.2] at he; exact (Option.some.inj he)
    · rw [Vals.row_atom, h.2] at he; cases he

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
