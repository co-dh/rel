module

public import Rel.Run.Table
public import Rel.RepAsc
public import Rel.RepWF
public import Rel.RepTabDiv
public import Rel.RepTabComp
public import Rel.RepStruct
public import Rel.RepCanon

-- exposed: every def body is a spec a downstream `rfl`/`decide`/`simp` may unfold (PLAN W.8)
@[expose] public section

/-! The law of `Table.symLt` and `Table.symAsc` (`Rel/Run/Table.lean`): `<` and `asc` on a `sym` column go through
the rank of the symbol's text (owner decision J), so they follow the order of the texts and not of the ids. -/

namespace Rel.Lang.Table

open Rel Rel.Rep

/-- **`rank` is `iasc(D)°`**: an id `i` of `D` goes to `r` when its text `t` is the `r`-th smallest text of `D`
(`ascDen` of `ran D`), `rank D = D ≫ asc(ran D)°`. -/
theorem rank_holds {D : Dict} {R : Tab .long .long} (h : rank D = .ok R) (wD : D.WF) (i r : Int64) :
    R.Holds i r ↔ ∃ t, D.Holds i t ∧ ascDen (.arr (.atom .char)) (fun u => ∃ i', D.Holds i' u) r t := by
  unfold rank at h
  simp only [Bind.bind] at h
  rw [Except.bind_eq_ok'] at h; obtain ⟨S, hS, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨T, hT, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨C, hC, h⟩ := h
  have wS := Tab.ran_wf hS wD
  have wT := Tab.asc_wf hT wS
  have wC := Tab.conv_wf hC wT
  have hp : (fun b => ∃ c, S.Holds b c) = fun u => ∃ i', D.Holds i' u := funext fun b => propext
    ⟨fun ⟨c, hc⟩ => ((Tab.ran_holds hS wD.2 b c).1 hc).2, fun h => ⟨b, (Tab.ran_holds hS wD.2 b b).2 ⟨rfl, h⟩⟩⟩
  have hA := Tab.asc_holds hT wS
  rw [hp] at hA
  rw [Tab.comp_holds h wD wC]
  refine exists_congr fun t => and_congr_right fun _ => ?_
  rw [Tab.conv_holds hC wT, ← hA]
  rfl

/-- A `sym` column read as the `i64` column of the same words: each id is the word as an `Int64`. -/
theorem get_sym_i64 {n : USize} (v : Arr .sym n) (w : Arr .i64 n) (he : w.enc = v.enc) (i : Fin n.toNat) :
    w.get i = (v.get i).toInt64 := by
  rw [Arr.get_ne _ _ (by decide), Arr.get_ne _ _ (by decide), he]
  have h := v.wf
  generalize v.enc = e at h ⊢
  cases e <;> simp_all [Ext.Enc.WF, QAtomicType.width, Ext.Enc.get, Column.atomOfBits, Dep.Carrier.of?]

/-- The id of a `sym` read as the `i64` the rank table is keyed by. -/
theorem symIds_row {A : Obj} (I : Tab A (.atom .sym)) (i : Fin I.n.toNat) :
    (symIds I).val.row i = (I.val.row i).toInt64 := by
  unfold symIds
  rw [Vals.row_atom, Vals.row_atom]
  exact get_sym_i64 _ _ rfl i

/-- **`K ≫ rank`**: a symbol `a` of the column `K` goes to `r` when `a`'s id is `rank`'s `r`. -/
theorem symRanked_holds {w : String} {D : Dict} {n : USize} {K : Vals (.atom .sym) n} {P : Tab (.atom .sym) .long}
    {R : Tab .long .long} (h : symRanked w D K = .ok P) (hR : rank D = .ok R) (wR : R.WF) (a : UInt64) (r : Int64) :
    D.n.toNat < 2 ^ 63 ∧ (P.Holds a r ↔ (∃ i, K.row i = a) ∧ R.Holds a.toInt64 r) := by
  unfold symRanked at h
  simp only [Bind.bind, hR] at h
  rw [Except.bind_eq_ok'] at h; obtain ⟨P0, hP0, h⟩ := h
  injection hP0 with e; subst e
  rw [Except.bind_eq_ok'] at h; obtain ⟨Q, hQ, h⟩ := h
  have hQP : Q = P ∧ D.n.toNat < 2 ^ 63 := by
    by_cases c1 : Q.n = n <;> by_cases c2 : D.n.toNat < 2 ^ 63 <;>
      simp [c1, c2, pure, Except.pure, Except.bind] at h <;> exact ⟨h, c2⟩
  obtain ⟨rfl, hb⟩ := hQP
  have wI : (symIds (⟨n, K, K⟩ : Tab (.atom .sym) (.atom .sym))).WF := ⟨trivial, trivial⟩
  refine ⟨hb, ?_⟩
  rw [Tab.comp_holds hQ wI wR]
  constructor
  · rintro ⟨b, ⟨i, hi, hb⟩, hr⟩
    have hb' : b = a.toInt64 := by rw [← hb, ← hi]; exact symIds_row ⟨n, K, K⟩ i
    exact ⟨⟨i, hi⟩, hb' ▸ hr⟩
  · rintro ⟨⟨i, hi⟩, hr⟩
    exact ⟨a.toInt64, ⟨i, hi, by rw [← hi]; exact symIds_row ⟨n, K, K⟩ i⟩, hr⟩

/-- **Ranks order as their elements do**: two elements numbered by `asc`'s `ascDen` are in `Int64` order exactly
when they are in `B.lt` order, so long as the numbers do not wrap (`hb`: no ascending list of the set is `2^63` long). -/
theorem ascDen_lt {B : Obj} {p : B.El → Prop} {j₁ j₂ : Int64} {t₁ t₂ : B.El}
    (hb : ∀ ys : List B.El, ys.Pairwise B.lt → (∀ b, b ∈ ys ↔ p b) → ys.length < 2 ^ 63)
    (h₁ : ascDen B p j₁ t₁) (h₂ : ascDen B p j₂ t₂) : j₁ < j₂ ↔ B.lt t₁ t₂ := by
  obtain ⟨ys, hys, hm, k₁, e₁, rfl⟩ := h₁
  obtain ⟨ys', hys', hm', k₂, e₂, rfl⟩ := h₂
  obtain rfl : ys' = ys := lt_sorted_unique hys' hys fun b => (hm' b).trans (hm b).symm
  obtain ⟨l₁, rfl⟩ := List.getElem?_eq_some_iff.1 e₁
  obtain ⟨l₂, rfl⟩ := List.getElem?_eq_some_iff.1 e₂
  have hl := hb ys' hys' hm'
  have hi : Int64.ofNat k₁ < Int64.ofNat k₂ ↔ k₁ < k₂ := by
    rw [Int64.lt_iff_toInt_lt, Int64.toInt_ofNat', Int64.toInt_ofNat', Int64.size, Int.bmod_eq_of_le (by omega) (by omega),
      Int.bmod_eq_of_le (by omega) (by omega)]
    omega
  rw [hi]
  constructor
  · exact fun hk => List.pairwise_iff_getElem.1 hys' k₁ k₂ l₁ l₂ hk
  · intro h
    refine Nat.lt_of_not_le fun hk => ?_
    rcases Nat.lt_or_eq_of_le hk with hk' | rfl
    · exact B.lt_asymm h (List.pairwise_iff_getElem.1 hys' k₂ k₁ l₂ l₁ hk')
    · exact B.lt_irrefl _ h

end Rel.Lang.Table
