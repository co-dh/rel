import Rel.Lang.GenKFold
import Rel.AscOrder
import Rel.Run.Asc

/-! The law of `Tab.asc` (`Rel/Run/Asc.lean`): `canon`'s rows `(0, b)` ascend in the codes `kasc` sorts by, which the
order law of `Λ` at `ℕ ⟶ B` (`Lang.LamLaw .long B`, taken as the hypothesis `hB`) ties to `Obj.lt`; so the values,
read in position order, are the one strictly ascending list of `dom P` (`lt_sorted_unique`). -/

namespace Rel
open Rel.Ext Rel.Kernel Rel.Verify Rel.Rep

/-- `Arr.zeros` holds `0` at every row. -/
theorem Arr.zeros_get {n : USize} {z : Arr .i64 n} (h : Arr.zeros .i64 n = .ok z) (i : Fin n.toNat) : z.get i = 0 := by
  unfold Arr.zeros at h; simp only [bind] at h
  rw [Except.bind_eq_ok'] at h; obtain ⟨c, hc, h⟩ := h
  have es := (colMap_raw (colArr_ok h)).2.2.2 _ i.2
  rw [colConst_raw hc, Array.getElem?_replicate, if_pos i.2, Option.getD_some] at es
  simp only [Op.eval, Except.ok.injEq, UInt64.add_zero] at es
  rw [Arr.get_i64, ← es]; rfl

namespace Tab

/-- **`asc P` denotes `asc(P)`** (`ascDen` of `dom P`), given the order law of `Λ` at `ℕ ⟶ B`. -/
theorem asc_holds {B : Obj} {P : Tab B B} {T : Tab .long B} (h : Tab.asc P = .ok T)
    (hB : ∀ (m : USize) (x : Vals (.prod .long B) m) es, Vals.cols x = .ok es → ∀ i i' : Fin m.toNat,
      (x.row i).1 = (x.row i').1 → lexLe (ascKeys m es) i i' = true → seenKey m es i ≠ seenKey m es i' →
        B.lt (x.row i).2 (x.row i').2) :
    rep T = ascDen B fun b => ∃ c, P.Holds b c := by
  unfold Tab.asc at h
  split at h; · cases h
  simp only [bind] at h
  rw [Except.bind_eq_ok'] at h; obtain ⟨z, hz, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨U, hU, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨p, hp, h⟩ := h
  cases h
  obtain ⟨es, -, hes, -⟩ := canon_codes hU
  obtain ⟨sel, hrow, hsort⟩ := canon_sorted hU hes
  -- `U`'s values ascend strictly: its rows are `canon`'s input rows `sel j`, of one key `0`
  have hlt : ∀ j j' : Fin U.n.toNat, j < j' → B.lt (U.val.row j) (U.val.row j') := fun j j' hj => by
    obtain ⟨hl, hs⟩ := hsort j j' hj
    have e : ∀ j, U.val.row j = P.key.row (sel j) := fun j => congrArg Prod.snd (hrow j)
    rw [e j, e j']
    exact hB _ ((z, P.key) : Vals (.prod .long B) P.n) es hes (sel j) (sel j')
      (by show Vals.row (A := .long) z _ = Vals.row (A := .long) z _; rw [Vals.row_atom, Vals.row_atom,
        Arr.zeros_get hz, Arr.zeros_get hz]) hl hs
  have hH : ∀ k b, (∃ i, U.key.row i = k ∧ U.val.row i = b) ↔
      ∃ i, Vals.row (A := .long) z i = k ∧ P.key.row i = b := canon_holds hU
  let ys := List.ofFn fun j => U.val.row j
  have hys : ys.Pairwise B.lt := List.pairwise_iff_getElem.2 fun i i' hi hi' h => by
    simp only [ys, List.getElem_ofFn]; exact hlt ⟨i, by simpa [ys] using hi⟩ ⟨i', by simpa [ys] using hi'⟩ h
  have hmem : ∀ b, b ∈ ys ↔ ∃ c, P.Holds b c := fun b => by
    simp only [ys, List.mem_ofFn]
    constructor
    · rintro ⟨j, rfl⟩
      obtain ⟨i, -, hi⟩ := (hH _ _).1 ⟨j, rfl, rfl⟩
      exact ⟨P.val.row i, i, hi, rfl⟩
    · rintro ⟨-, i, rfl, -⟩
      obtain ⟨j, -, hj⟩ := (hH _ _).2 ⟨i, rfl, rfl⟩
      exact ⟨j, hj⟩
  funext j a
  apply propext
  show (∃ i, Vals.row (A := .long) p i = j ∧ U.val.row i = a) ↔ _
  constructor
  · rintro ⟨i, rfl, rfl⟩
    refine ⟨ys, hys, hmem, i.1, by simp [ys, i.2], ?_⟩
    rw [Vals.row_atom, Lang.Arr.pos_get hp]; rfl
  · rintro ⟨ys', hs', hm', k, hk, rfl⟩
    rw [lt_sorted_unique hs' hys fun b => (hm' b).trans (hmem b).symm] at hk
    simp only [ys, List.getElem?_ofFn] at hk
    split at hk
    · rename_i hkn
      refine ⟨⟨k, hkn⟩, ?_, Option.some.inj hk⟩
      rw [Vals.row_atom, Lang.Arr.pos_get hp]; rfl
    · cases hk

end Tab

namespace Lang.GenK

/-- A row whose table is made from its relation's whole table (`ofRel`) represents `Y` when `f` makes a table of
meaning `Y` from one of meaning `X`. -/
theorem ofRel_sound {A B C D : Obj} {d : Bool} {R : Rel A B} {X : Core.Rel A.El B.El}
    {f : Tab A B → Except String (Tab C D)} {Y : Core.Rel C.El D.El} (hR : ∀ K, R.Reps K X)
    (hf : ∀ r t, f r = .ok t → rep r = X → rep t = Y) : ∀ K, (GenK.ofRel A B C D d R f).Reps K Y :=
  lift1_sound hR fun _ r t ht hr => by rw [hf r t ht (agrees_empty hr).symm]; exact fun _ _ _ _ => Iff.rfl

end Lang.GenK

end Rel
