import Rel.Run.SetOps
import Rel.RepCols
import Rel.Run.CRelFoldDef

/-! The laws of `Tab.union`, `Tab.inter`, `Tab.diff` and `Tab.le` (`Rel/Run/SetOps.lean`), from the five kernels' laws
and `Tab.canon`'s (`Rel/RepCanon.lean`). -/

namespace Rel
open Rel.Ext Rel.Kernel Rel.Verify

/-! ## CONCAT and `∪` -/
namespace Tab
variable {k v : Obj}

/-- **`R.concat S` denotes `R ∪ S`**, rows counted with repeats. -/
theorem concat_holds {R S C : Tab k v} (h : R.concat S = .ok C) (a : k.El) (b : v.El) :
    C.Holds a b ↔ R.Holds a b ∨ S.Holds a b := by
  unfold Tab.concat at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  split at h; · cases h
  rename_i p hp
  obtain ⟨n, off⟩ := p
  split at h; · cases h
  rename_i K hK
  split at h; · cases h
  rename_i V hV
  cases h
  obtain ⟨hn, hoff⟩ := catPlan_ok hp
  have rk := Vals.concat_row hn hoff R.key S.key hK
  have rv := Vals.concat_row hn hoff R.val S.val hV
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

/-- **The source tag of `R.tagged S`**: its table is `R.concat S`, and row `c`'s tag is `1` iff `c ≥ R.n` (a row of
`S`), `0` below (a row of `R`). -/
theorem tagged_ok {R S C : Tab k v} {tag : Enc} (h : R.tagged S = .ok (C, tag)) :
    R.concat S = .ok C ∧ C.n.toNat = R.n.toNat + S.n.toNat ∧ (Enc.raw .i64 C.n tag).size = C.n.toNat ∧
      ∀ c < C.n.toNat, (Enc.raw .i64 C.n tag)[c]?.getD 0 = if R.n.toNat ≤ c then 1 else 0 := by
  unfold Tab.tagged at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  split at h; · cases h
  rename_i p hp
  obtain ⟨n, off⟩ := p
  split at h; · cases h
  rename_i K hK
  split at h; · cases h
  rename_i V hV
  split at h; · cases h
  rename_i one h1
  split at h; · cases h
  rename_i t ht
  cases h
  obtain ⟨hn, hoff⟩ := catPlan_ok hp
  refine ⟨by unfold Tab.concat; simp only [hp, hK, hV, bind, Except.bind, pure, Except.pure], hn, ?_⟩
  obtain ⟨-, -, -, hws, -, hfix, hlast⟩ := raw_scatter S.n off one n 0 _ ht
  refine ⟨hws, fun c hc => ?_⟩
  have hc' : c < n.toNat := hc
  split
  · rename_i hl
    have e := hlast (c - R.n.toNat) (by omega) fun k' h1 h2 e => by
      have := congrArg UInt64.toNat e; rw [hoff k' h2, hoff _ (by omega)] at this; omega
    rw [hoff _ (by omega), show R.n.toNat + (c - R.n.toNat) = c by omega] at e
    rw [e, colConst_raw h1]
    simp [show c - R.n.toNat < S.n.toNat by omega]
  · rename_i hl
    have e := hfix c hc' fun k hk e => by rw [hoff k hk] at e; omega
    simp [e]

end Tab

/-! ## Checks on `foR` tables -/

section Checks


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
