import Rel.Run.Canon
import Rel.Run.CRelRelDef
import Rel.KernelSpec.KSeen

/-! The laws of `Vals.nub`, `Tab.canon`, `Tab.ran` and `Tab.dom` (`Rel/Run/Canon.lean`), from the five kernels' laws:
`asc_perm` (the sorted columns are the input's through a permutation), `kseen_ok` with `firsts_spec` (the first row of
each group, and every row's group), `raw_kgather` (a gathered word is the source's word at the index) and the closure
law `wordsFoR_closed` (a kernel's answer reads back as the words it wrote). `Arr.get_eq_of_raw` carries a word law to
the elements, and `Vals.gather_row` to the rows. -/

namespace Rel
open Rel.Ext Rel.Kernel Rel.Verify

/-- **Equal words, equal elements**: two `Arr`s of one type in a column every kernel reads (`foR`; `pos` is no `Arr`)
whose raw words at `i` and `j` agree hold one element there. What lifts a kernel's word law to `Arr.get`, at every
type, `Arr.get_raw_foR` being its `i64` reading. -/
theorem Arr.get_eq_of_raw {t : QAtomicType} {n m : USize} (x : Arr t n) (y : Arr t m) (hx : Kernel.Enc.Valid n x.enc)
    (hy : Kernel.Enc.Valid m y.enc) (i : Fin n.toNat) (j : Fin m.toNat)
    (h : (Enc.raw .i64 n x.enc)[i.1]? = (Enc.raw .i64 m y.enc)[j.1]?) : x.get i = y.get j := by
  have foR_of : ∀ {t n} (z : Arr t n), Kernel.Enc.Valid n z.enc → ∃ md pk, z.enc = .foR md pk := by
    intro t n z hz; have hw := z.wf
    cases hc : z.enc with
    | foR md pk => exact ⟨md, pk, rfl⟩
    | pos => rw [hc] at hw; cases t <;> simp only [Enc.WF] at hw
    | _ => all_goals (rw [hc] at hz; simp only [Kernel.Enc.Valid] at hz)
  obtain ⟨md, pk, hcx⟩ := foR_of x hx
  obtain ⟨md', pk', hcy⟩ := foR_of y hy
  have hwx := x.wf; rw [hcx] at hwx
  have hg : t ≠ .general := by rintro rfl; simp only [Enc.WF] at hwx; exact absurd hwx.1 (by decide)
  rw [hcx, hcy] at h
  simp only [raw_foR .i64 8 rfl (by decide : QAtomicType.i64 ≠ .u1), Array.getElem?_map, Array.getElem?_range, i.2,
    j.2, if_true, Option.map_some, Option.some.injEq, Nat.reduceMul, ofNat_toNat_mod64, ← foRBits_starts] at h
  rw [Arr.get_ne x i hg, Arr.get_ne y j hg, hcx, hcy]
  cases t <;> first | exact absurd rfl hg | (simp only [Enc.get, if_pos i.2, if_pos j.2, QAtomicType.width, h])

/-- **The row form of the bridge**: row `j` of `Vals.gather m ix x` is row `ix[j]` of `x`, the index being below `n`. -/
theorem Vals.gather_row {m : USize} {ix : Enc} : {A : Obj} → {n : USize} → (x : Vals A n) → {y : Vals A m} →
    Vals.gather m ix x = .ok y → ∀ j : Fin m.toNat, ∃ i : Fin n.toNat,
      ((Enc.raw .i64 m ix)[j.1]?.getD 0).toNat = i.1 ∧ Vals.row y j = Vals.row x i
  | .atom t, n, x, y, h, j => by
    simp only [Vals.gather] at h
    split at h
    · rename_i o ho
      cases h
      have hv := kgather_valid ho
      obtain ⟨his, hes, hlt, ho'⟩ := raw_kgather m ix n _ o ho
      have hc := wordsFoR_closed ((Enc.raw .i64 m ix).map fun i => (Enc.raw .i64 n (Arr.enc (t := t) x))[i.toNat]?.getD 0)
        (n := m) (by rw [Array.size_map, his])
      have hj : j.1 < (Enc.raw .i64 m ix).size := by rw [his]; exact j.2
      have hi := hlt j j.2
      refine ⟨⟨_, hi⟩, rfl, (Arr.get_eq_of_raw (t := t) x _ hv (by show Kernel.Enc.Valid m o; rw [ho']; exact hc.1)
        _ j ?_).symm⟩
      show _ = (Enc.raw .i64 m o)[j.1]?
      dsimp only
      rw [ho', hc.2.1, Array.getElem?_map]
      cases hw : (Enc.raw .i64 m ix)[j.1]? with
      | none => simp [Array.getElem?_eq_getElem hj] at hw
      | some w =>
        rw [hw] at hi
        simp only [Option.getD_some, Option.map_some] at hi ⊢
        simp only [Array.getElem?_eq_getElem (show w.toNat < _ by rw [hes]; exact hi), Option.getD_some]
    · cases h
  | .prod a b, n, x, y, h, j => by
    simp only [Vals.gather, bind, Except.bind, pure, Except.pure] at h
    split at h; · cases h
    rename_i y1 h1
    split at h; · cases h
    rename_i y2 h2
    cases h
    obtain ⟨i1, e1, r1⟩ := Vals.gather_row x.1 h1 j
    obtain ⟨i2, e2, r2⟩ := Vals.gather_row x.2 h2 j
    obtain rfl : i1 = i2 := Fin.ext (e1.symm.trans e2)
    exact ⟨i1, e1, by simp only [Vals.row, r1, r2]⟩
  | .arr _, _, _, _, h, _ => by simp [Vals.gather] at h
  | .sum _ _, _, _, _, h, _ => by simp [Vals.gather] at h

/-- What `Vals.nub` answers, unfolded: each kernel's answer named, in the order of the composition. -/
theorem Vals.nub_ok {A : Obj} {n : USize} {x : Vals A n} {r : (m : USize) × Vals A m} (h : Vals.nub x = .ok r) :
    ∃ es vs p k g f ix y, Vals.cols x = .ok es ∧ kasc n es = .ok (vs, p) ∧
      kseen n ((es.map (·.1)).zip vs) = .ok (k, g, f) ∧ kgather k.toUSize f n p = .ok ix ∧
      Vals.gather k.toUSize ix x = .ok y ∧ r = ⟨k.toUSize, y⟩ := by
  simp only [Vals.nub, bind, Except.bind] at h
  repeat (split at h; · cases h)
  rename_i _ es hes _ vp hvp _ kgf hkgf _ ix hix
  cases hg : Vals.gather kgf.1.toUSize ix x with
  | error s => simp [hg, Functor.map, Except.map] at h
  | ok y =>
    simp only [hg, Functor.map, Except.map, Except.ok.injEq] at h
    exact ⟨es, vp.1, vp.2, kgf.1, kgf.2.1, kgf.2.2, ix, y, hes, hvp, hkgf, hix, hg, h.symm⟩

/-- **Every row of `Vals.nub x` is a row of `x`.** -/
theorem Vals.nub_sub {A : Obj} {n : USize} {x : Vals A n} {r : (m : USize) × Vals A m} (h : Vals.nub x = .ok r) :
    ∀ j : Fin r.1.toNat, ∃ i : Fin n.toNat, Vals.row r.2 j = Vals.row x i := by
  obtain ⟨_, _, _, _, _, _, _, y, _, _, _, _, hy, rfl⟩ := Vals.nub_ok h
  exact fun j => (Vals.gather_row x hy j).imp fun _ h => h.2

/-- **Every row of `x` has a row of `Vals.nub x` equal to it in the kernels' order codes** (`seenKey` over the side's
columns `es`): the first input row of its run among the sorted rows. Where equal codes mean equal rows, the two sides
hold the same rows (`Vals.nub_rows`). -/
theorem Vals.nub_cover {A : Obj} {n : USize} {x : Vals A n} {r : (m : USize) × Vals A m} (h : Vals.nub x = .ok r)
    {es : List (QAtomicType × Enc)} (hes : Vals.cols x = .ok es) (i : Fin n.toNat) :
    ∃ j : Fin r.1.toNat, ∃ i' : Fin n.toNat, Vals.row r.2 j = Vals.row x i' ∧ seenKey n es i' = seenKey n es i := by
  obtain ⟨es', vs, p, k, g, f, ix, y, hes', ha, hs, hix, hy, rfl⟩ := Vals.nub_ok h
  have hee : es = es' := Except.ok.inj (hes.symm.trans hes'); subst hee
  obtain ⟨ps, hp, hperm, hvl, hcol⟩ := asc_perm n es vs p ha
  obtain ⟨hk, -, hf⟩ := kseen_ok hs
  have hlen : ps.length = n.toNat := by simpa using hperm.length_eq
  have hn := n.toNat_lt_size
  have hU : USize.size ≤ 2 ^ 64 := by rcases USize.size_eq with h | h <;> omega
  -- the sorted rows' key at `q` is the input's at `ps[q]`
  have hkey : ∀ q (hq : q < ps.length), seenKey n ((es.map (·.1)).zip vs) q = seenKey n es ps[q] := by
    intro q hq
    simp only [seenKey, ascKeys, List.map_map]
    apply List.ext_getElem (by simp [hvl])
    intro c h1 h2
    have hc2 : c < es.length := by simpa using h2
    obtain ⟨ws, hv, hws, hwq⟩ := hcol c es[c] (vs[c]'(by omega)) (List.getElem?_eq_getElem hc2)
      (List.getElem?_eq_getElem _)
    simp only [List.getElem_map, List.getElem_zip, Function.comp_apply, hv, (wordsFoR_closed ws hws.symm).2.1,
      Array.getElem?_map, hwq q hq]
  generalize seenKey n ((es.map (·.1)).zip vs) = K at hk hf hkey
  obtain ⟨q, hq, hqi⟩ := List.getElem_of_mem (hperm.mem_iff.2 (List.mem_range.2 i.2))
  obtain ⟨hgl, -, hgk, -⟩ := (firsts_spec K n.toNat).2.2.2.2.2 q (by omega)
  have hq' : (firstsOf K n.toNat)[Verify.groupOf K n.toNat q] < n.toNat := firsts_lt K n.toNat (List.getElem_mem hgl)
  have hkn : k ≤ n.toNat := by rw [hk]; unfold firstsOf; exact Nat.le_trans (List.length_filter_le _ _) (by simp)
  have hkU : k.toUSize.toNat = k := USize.toNat_ofNat_of_lt' (by omega)
  obtain ⟨i', e1, r1⟩ := Vals.gather_row x hy ⟨Verify.groupOf K n.toNat q, by rw [hkU, hk]; exact hgl⟩
  refine ⟨_, i', r1, ?_⟩
  -- `ix[G]` is `ps[firsts[G]]`
  obtain ⟨his, hps, -, hix'⟩ := raw_kgather _ _ _ _ _ hix
  have hrf : Enc.raw .i64 k.toUSize f = ((firstsOf K n.toNat).map Nat.toUInt64).toArray := by
    rw [hf]; exact (wordsFoR_closed _ (by rw [hkU, hk]; simp)).2.1
  have hrp : Enc.raw .i64 n p = (ps.map Nat.toUInt64).toArray := by
    rw [hp]; exact (wordsFoR_closed _ (by simp [hlen])).2.1
  have hri : Enc.raw .i64 k.toUSize ix = (((firstsOf K n.toNat).map Nat.toUInt64).toArray.map fun w =>
      ((ps.map Nat.toUInt64).toArray)[w.toNat]?.getD 0) := by
    rw [hix', (wordsFoR_closed _ (by rw [Array.size_map, his])).2.1, hrf, hrp]
  have hc64 : ∀ a, a < n.toNat → a.toUInt64.toNat = a := fun a ha => by simp; omega
  have hfG : (firstsOf K n.toNat)[Verify.groupOf K n.toNat q] < ps.length := by omega
  have hi' : i'.1 = ps[(firstsOf K n.toNat)[Verify.groupOf K n.toNat q]] := by
    rw [← e1, hri]
    simp only [Array.getElem?_map, List.getElem?_toArray, List.getElem?_map, List.getElem?_eq_getElem hgl,
      Option.map_some, Option.getD_some, hc64 _ hq', List.getElem?_eq_getElem hfG]
    exact hc64 _ (List.mem_range.1 (hperm.mem_iff.1 (List.getElem_mem hfG)))
  rw [hi', ← hkey _ hfG, hgk, hkey q hq, hqi]

/-- **`Vals.nub x` holds exactly `x`'s rows** where rows with equal order codes are equal (`hK`: no float `±0` or NaN
pair, whose codes merge): `Vals.nub_sub` one way, `Vals.nub_cover` the other. -/
theorem Vals.nub_rows {A : Obj} {n : USize} {x : Vals A n} {r : (m : USize) × Vals A m} (h : Vals.nub x = .ok r)
    (hK : ∀ es, Vals.cols x = .ok es → ∀ i i' : Fin n.toNat, seenKey n es i = seenKey n es i' → x.row i = x.row i')
    (a : A.El) : (∃ j, Vals.row r.2 j = a) ↔ ∃ i, Vals.row x i = a := by
  obtain ⟨es, _, _, _, _, _, _, _, hes, _⟩ := Vals.nub_ok h
  constructor
  · rintro ⟨j, rfl⟩; obtain ⟨i, hi⟩ := Vals.nub_sub h j; exact ⟨i, hi.symm⟩
  · rintro ⟨i, rfl⟩; obtain ⟨j, i', h1, h2⟩ := Vals.nub_cover h hes i; exact ⟨j, h1.trans (hK es hes i' i h2)⟩

namespace Tab
variable {k v : Obj}

/-- **`R.canon` denotes `R`**, where rows of `R` with equal order codes are equal. -/
theorem canon_holds {R S : Tab k v} (h : R.canon = .ok S)
    (hK : ∀ es, Vals.cols (A := .prod k v) (R.key, R.val) = .ok es → ∀ i i' : Fin R.n.toNat,
      seenKey R.n es i = seenKey R.n es i' → R.key.row i = R.key.row i' ∧ R.val.row i = R.val.row i')
    (a : k.El) (b : v.El) : S.Holds a b ↔ R.Holds a b := by
  unfold Tab.canon at h
  cases hn : Vals.nub (A := .prod k v) (R.key, R.val) with
  | error s => simp [hn, Functor.map, Except.map] at h
  | ok r =>
    simp only [hn, Functor.map, Except.map, Except.ok.injEq] at h
    subst h
    have := Vals.nub_rows hn (fun es he i i' e => Prod.ext (hK es he i i' e).1 (hK es he i i' e).2) (a, b)
    simp only [Tab.Holds, Vals.row, Prod.mk.injEq] at this ⊢
    exact this

/-- **`R.ran` denotes `𝟙 ∩ R° ≫ R°°`** (`CRel.rep_ran`'s statement, pointwise), where rows of `R`'s value side with
equal order codes are equal. -/
theorem ran_holds {R : Tab k v} {S : Tab v v} (h : R.ran = .ok S)
    (hK : ∀ es, Vals.cols R.val = .ok es → ∀ i i' : Fin R.n.toNat, seenKey R.n es i = seenKey R.n es i' →
      R.val.row i = R.val.row i') (a b : v.El) : S.Holds a b ↔ a = b ∧ ∃ x, R.Holds x a := by
  unfold Tab.ran at h
  cases hn : Vals.nub R.val with
  | error s => simp [hn, Functor.map, Except.map] at h
  | ok r =>
    simp only [hn, Functor.map, Except.map, Except.ok.injEq] at h
    subst h
    have := Vals.nub_rows hn hK a
    simp only [Tab.Holds]
    constructor
    · rintro ⟨j, rfl, rfl⟩; obtain ⟨i, hi⟩ := this.1 ⟨j, rfl⟩; exact ⟨rfl, Vals.row R.key i, i, rfl, hi⟩
    · rintro ⟨rfl, x, i, -, hi⟩; obtain ⟨j, hj⟩ := this.2 ⟨i, hi⟩; exact ⟨j, hj, hj⟩

/-- **`R.dom` denotes `𝟙 ∩ R ≫ R°`** (`CRel.rep_dom`'s statement, pointwise), where rows of `R`'s key side with equal
order codes are equal. -/
theorem dom_holds {R : Tab k v} {S : Tab k k} (h : R.dom = .ok S)
    (hK : ∀ es, Vals.cols R.key = .ok es → ∀ i i' : Fin R.n.toNat, seenKey R.n es i = seenKey R.n es i' →
      R.key.row i = R.key.row i') (a b : k.El) : S.Holds a b ↔ a = b ∧ ∃ y, R.Holds a y := by
  unfold Tab.dom at h
  cases hn : Vals.nub R.key with
  | error s => simp [hn, Functor.map, Except.map] at h
  | ok r =>
    simp only [hn, Functor.map, Except.map, Except.ok.injEq] at h
    subst h
    have := Vals.nub_rows hn hK a
    simp only [Tab.Holds]
    constructor
    · rintro ⟨j, rfl, rfl⟩; obtain ⟨i, hi⟩ := this.1 ⟨j, rfl⟩; exact ⟨rfl, Vals.row R.val i, i, hi, rfl⟩
    · rintro ⟨rfl, y, i, hi, -⟩; obtain ⟨j, hj⟩ := this.2 ⟨i, hi⟩; exact ⟨j, hj, hj⟩

end Tab

/-! ## Checks on `foR` tables -/

section Checks

/-- The table of the pairs `ps` as given, unsorted, both columns `Alg.col`'s literal `foR` columns. -/
private def tab (ps : List (Int64 × Int64)) : Tab .long .long :=
  ⟨ps.length.toUSize, List.length_map _ ▸ Alg.col (ps.map (·.1)), List.length_map _ ▸ Alg.col (ps.map (·.2))⟩

#guard ((tab [(3, 1), (1, 2), (3, 1), (-1, 2), (1, 2), (2, 7)]).canon.toOption.map Tab.toList) ==
  some [(-1, 2), (1, 2), (2, 7), (3, 1)]
#guard ((tab [(3, 1), (1, 2), (3, 5), (0, -4)]).ran.toOption.map Tab.toList) == some [(-4, -4), (1, 1), (2, 2), (5, 5)]
#guard ((tab [(3, 1), (1, 2), (3, 5)]).dom.toOption.map Tab.toList) == some [(1, 1), (3, 3)]
#guard ((tab []).canon.toOption.map Tab.toList) == some []
-- `Alg.ofPairs`' columns are `col`'s, `foR` where they are built
#guard ((Alg.ofPairs [(1, 2)]).canon.toOption.map Tab.toList) == some [(1, 2)]
-- the five-kernel `canon`, `ran`, `dom` against the old `canonC`, `CRel.ran`, `CRel.dom` on the same tables
#guard [[(3, 1), (1, 2), (3, 1), (-1, 2), (1, 2), (2, 7), (-5, -5), (0, 0)], [(-2, 9), (-2, 9), (7, -3)], []].all
  fun (ps : List (Int64 × Int64)) =>
    let c := Alg.canonC (tab ps)
    ((tab ps).canon.toOption.map Tab.toList) == (if c.2 then some c.1.toList else none) &&
    ((tab ps).ran.toOption.map Tab.toList) == ((CRel.ran (some (tab ps))).map Tab.toList) &&
    ((tab ps).dom.toOption.map Tab.toList) == ((CRel.dom (some (tab ps))).map Tab.toList)

end Checks

#print axioms Tab.canon_holds
#print axioms Tab.ran_holds

end Rel
