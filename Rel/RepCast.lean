import Rel.Run.Cast
import Rel.RepSetOps
import Rel.RepCanon
import Rel.RepTabComp
import Rel.Lang.Den

/-! The law of `$` (`Tab.cast`): its table is the graph of `QAtomicType.embed` on the values in demand. -/

namespace Rel
open Rel.Ext Rel.Kernel

namespace Tab

/-- A long word read as `0` or `1` is that word. -/
theorem raw_of_toInt64 {r : UInt64} {k : Nat} (hk : k < 2) (h : r.toInt64 = Int64.ofNat k) : r = UInt64.ofNat k := by
  have := congrArg Int64.toUInt64 h
  match k, hk with
  | 0, _ => simpa using this
  | 1, _ => simpa using this

/-- **`X $ t` denotes the graph of `embed s t`** on the values `X`: a value with no image at `t` has no row. -/
theorem cast_holds {s t : QAtomicType} {n : USize} {X : Vals (.atom s) n} {T : Tab (.atom s) (.atom t)}
    (h : Tab.cast X = .ok T) (a : (Obj.atom s).El) (b : (Obj.atom t).El) :
    T.Holds a b ↔ (∃ i, X.row i = a) ∧ QAtomicType.embed s t a = some b := by
  dsimp only [Tab.cast] at h
  split at h
  case isFalse => cases h
  rename_i hu
  split at h
  case isFalse => cases h
  rename_i hok
  obtain ⟨U, hU, hT⟩ := Except.bind_eq_ok'.1 h
  simp only [List.all_eq_true, List.mem_finRange, true_implies] at hok
  have hrow : ∀ i : Fin n.toNat, ∃ r, (Enc.raw .i64 n (Arr.ofFn .i64 n fun i =>
      if (QAtomicType.embed s t (X.get i)).isSome then 1 else 0).enc)[i.1]?.getD 0 = r ∧
      (r = 0 ∧ QAtomicType.embed s t (X.get i) = none ∨
       r = 1 ∧ QAtomicType.embed s t (X.get i) = some ((Arr.ofFn t n (fun i =>
         ((QAtomicType.embed s t (X.get i)).map t.word).getD 0) hu).get i)) := by
    intro i
    have hc := hok i
    refine ⟨_, rfl, ?_⟩
    revert hc
    generalize QAtomicType.embed s t (X.get i) = w
    rw [Arr.get_i64]
    cases w with
    | none => intro hc; exact .inl ⟨raw_of_toInt64 (k := 0) (by omega) (by simpa [castRow] using hc), rfl⟩
    | some y =>
      intro hc
      simp only [castRow, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hc
      exact .inr ⟨raw_of_toInt64 (k := 1) (by omega) hc.1, by rw [hc.2]⟩
  rw [canon_holds hT, keep_holds hU (fun i hi => by
    obtain ⟨r, hr, h0 | h1⟩ := hrow ⟨i, hi⟩ <;> simp only at hr <;> rw [hr]
    · rw [h0.1]; decide
    · rw [h1.1]; decide)]
  constructor
  · rintro ⟨i, hf, rfl, rfl⟩
    obtain ⟨r, hr, h0 | h1⟩ := hrow i
    · exact absurd (hr.trans h0.1) hf
    · exact ⟨⟨i, rfl⟩, by rw [Vals.row_atom, Vals.row_atom]; exact h1.2⟩
  · rintro ⟨⟨i, rfl⟩, he⟩
    obtain ⟨r, hr, h0 | h1⟩ := hrow i
    · rw [Vals.row_atom] at he; rw [h0.2] at he; cases he
    · refine ⟨i, by rw [hr, h1.1]; decide, rfl, ?_⟩
      rw [Vals.row_atom] at he ⊢; rw [h1.2] at he; exact (Option.some.inj he)

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
