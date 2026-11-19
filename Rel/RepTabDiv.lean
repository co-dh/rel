import Rel.Run.Div
import Rel.RepCanon
import Rel.RepSetOps
import Rel.RepTabComp
import Rel.Run.Alg
import Rel.Lang.Den

/-! The laws of the operators of `Rel/Run/Div.lean` (`ldiv`, `rdiv`, `lam`, `E`, `nil`, `lt`, `leq`), and their
checks against the old layer (`Alg.leftDivC`, `rightDivC`, `lamOnC`, `memC`, `EC`, `nil`, `ltC`, `leqC`) on the same
`foR` tables, as sets. -/

namespace Rel
open Rel.Ext Rel.Kernel Rel.Verify Ext.Enc

namespace Tab
variable {A B C : Obj}

/-- **`nil D` denotes `nilDen` on `D`**: each key of `D` to the empty array. -/
theorem nil_holds {n : USize} {D : Vals A n} {T : Tab A (.arr B)} (h : Tab.nil D = .ok T) (a : A.El)
    (ys : List B.El) : T.Holds a ys ↔ (∃ i, D.row i = a) ∧ ys = [] := by
  unfold Tab.nil at h; simp only [bind, Except.bind] at h
  split at h; · cases h
  split at h; · cases h
  rw [canon_holds h]
  simp only [Tab.Holds, Vals.row]
  exact ⟨fun ⟨i, h1, h2⟩ => ⟨⟨i, h1⟩, h2.symm⟩, fun ⟨⟨i, h1⟩, h2⟩ => ⟨i, h1, h2.symm⟩⟩

/-- **`cross X Y` denotes `X × Y`**: every pair of a row of `X` and a row of `Y`. Output row `t` reads `X` at
`t div m` and `Y` at `t mod m` (`eval_div_nat`, `eval_mod_nat`); the pair `(i, j)` is row `j + i·m`. -/
theorem cross_holds {n m : USize} {X : Vals A n} {Y : Vals B m} {T : Tab A B} (h : cross X Y = .ok T) (a : A.El)
    (b : B.El) : T.Holds a b ↔ (∃ i, X.row i = a) ∧ ∃ j, Y.row j = b := by
  unfold cross at h
  split at h; · cases h
  rename_i hb
  simp only [bind, Except.bind] at h
  split at h; · cases h
  split at h; · cases h
  rename_i mc hmc
  split at h; · cases h
  rename_i dv hdv
  split at h; · cases h
  rename_i x hx
  split at h; · cases h
  rename_i mv hmv
  split at h; · cases h
  rename_i y hy
  rw [canon_holds h]
  have hU : USize.size ≤ 2 ^ 64 := by rcases USize.size_eq with h | h <;> omega
  have hT : (n.toNat * m.toNat).toUSize.toNat = n.toNat * m.toNat := by
    rw [Nat.toUSize]; exact USize.toNat_ofNat_of_lt (by omega)
  constructor
  · rintro ⟨t, rfl, rfl⟩
    obtain ⟨i, -, hi⟩ := Vals.gather_row X hx t
    obtain ⟨j, -, hj⟩ := Vals.gather_row Y hy t
    exact ⟨⟨i, hi.symm⟩, ⟨j, hj.symm⟩⟩
  · rintro ⟨⟨i, rfl⟩, ⟨j, rfl⟩⟩
    have hm : 0 < m.toNat := by have := j.2; omega
    have hn : 0 < n.toNat := by have := i.2; omega
    have hmn := Nat.le_mul_of_pos_left m.toNat hn
    have hlt : j.1 + i.1 * m.toNat < n.toNat * m.toNat := by
      have := Nat.mul_le_mul_right m.toNat (show i.1 + 1 ≤ n.toNat from i.2); rw [Nat.succ_mul] at this; omega
    have ht : j.1 + i.1 * m.toNat < (n.toNat * m.toNat).toUSize.toNat := by rw [hT]; exact hlt
    have hw : ∀ (op : Op) (e : Enc) (r : Nat), colMap op (n.toNat * m.toNat).toUSize .pos mc = .ok e →
        Op.eval op (j.1 + i.1 * m.toNat).toUInt64 m.toNat.toUInt64 = .ok r.toUInt64 → r < 2 ^ 64 →
        ((raw .i64 (n.toNat * m.toNat).toUSize e)[j.1 + i.1 * m.toNat]?.getD 0).toNat = r := by
      intro op e r he hr hr64
      obtain ⟨-, -, -, hev⟩ := colMap_raw he
      have := hev _ ht
      rw [raw_pos_word ht, colConst_raw hmc, Array.getElem?_replicate, if_pos ht, Option.getD_some, hr] at this
      rw [← Except.ok.inj this, toNat_toUInt64 hr64]
    have hd := hw .div dv i.1 hdv (by
      rw [eval_div_nat (by omega) (by omega) hm, Nat.add_mul_div_right _ _ hm, Nat.div_eq_of_lt j.2, Nat.zero_add])
      (by have := n.toNat_lt_size; omega)
    have hmo := hw .mod mv j.1 hmv (by
      rw [eval_mod_nat (by omega) (by omega) hm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt j.2])
      (by have := m.toNat_lt_size; omega)
    obtain ⟨i', hi', hxi⟩ := Vals.gather_row X hx ⟨_, ht⟩
    obtain ⟨j', hj', hyj⟩ := Vals.gather_row Y hy ⟨_, ht⟩
    have e1 : i' = i := Fin.ext (by rw [← hi', hd])
    have e2 : j' = j := Fin.ext (by rw [← hj', hmo])
    subst e1 e2
    exact ⟨⟨_, ht⟩, hxi, hyj⟩

end Tab

/-- **`whereCol` answers `K` words** (to move beside `whereCol_spec`, `Rel/RepSetOps.lean`): its last step is a
`kgather` of `K` rows. -/
theorem whereCol_size {m K : USize} {b o : Enc} (h : whereCol m b = .ok (K, o)) : (raw .i64 K o).size = K.toNat := by
  unfold whereCol at h
  have hB : m.toNat < min (USize.size - 1) (2 ^ 63) := by
    refine Classical.byContradiction fun hn => ?_; simp only [hn, if_false] at h; cases h
  simp only [hB, if_true, bind, Except.bind, Functor.map, Except.map] at h
  repeat (split at h; · cases h)
  rename_i o' ho'
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj h).symm
  obtain ⟨his, -, -, hoe⟩ := raw_kgather _ _ _ _ _ ho'
  rw [hoe, (wordsFoR_closed _ (by rw [Array.size_map, his])).2.1, Array.size_map, his]

namespace Tab
variable {A B : Obj}

/-- **`keep T b` holds the rows of `T` whose word of `b` is `1`**, `b` holding `0`/`1` words: answer row `j` is input
row `sel[j]`, and `sel` lists every position of a `1` (`whereCol_spec`, `whereCol_size`). -/
theorem keep_holds {T U : Tab A B} {b : Enc} (h : T.keep b = .ok U)
    (hb : ∀ i < T.n.toNat, (raw .i64 T.n b)[i]?.getD 0 < 2) (a : A.El) (c : B.El) :
    U.Holds a c ↔ ∃ i : Fin T.n.toNat, (raw .i64 T.n b)[i.1]?.getD 0 ≠ 0 ∧ T.key.row i = a ∧ T.val.row i = c := by
  unfold keep at h; simp only [bind, Except.bind] at h
  split at h; · cases h
  rename_i Ms hMs; obtain ⟨M, sel⟩ := Ms
  split at h; · cases h
  rename_i x hx
  split at h; · cases h
  rename_i y hy
  cases h
  have hsel := whereCol_spec hMs hb
  have hsz := whereCol_size hMs
  simp only [Tab.Holds]
  constructor
  · rintro ⟨j, rfl, rfl⟩
    obtain ⟨i, hi, hxi⟩ := Vals.gather_row _ hx j
    obtain ⟨i', hi', hyi⟩ := Vals.gather_row _ hy j
    have e : i' = i := Fin.ext (by rw [← hi', hi])
    subst e
    have hj : j.1 < (raw .i64 M sel).size := by rw [hsz]; exact j.2
    have hGm := List.mem_map_of_mem (f := UInt64.toNat) (Array.getElem_mem_toList hj)
    rw [hsel, List.mem_filter, decide_eq_true_eq] at hGm
    rw [Array.getElem?_eq_getElem hj, Option.getD_some] at hi
    rw [hi] at hGm
    exact ⟨i', hGm.2, hxi.symm, hyi.symm⟩
  · rintro ⟨i, hbi, rfl, rfl⟩
    have hm : i.1 ∈ (raw .i64 M sel).toList.map UInt64.toNat := by
      rw [hsel, List.mem_filter, List.mem_range, decide_eq_true_eq]; exact ⟨i.2, hbi⟩
    obtain ⟨w, hw, hwi⟩ := List.mem_map.1 hm
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hw
    have hj' : j < (raw .i64 M sel).size := by simpa using hj
    have hjM : j < M.toNat := by rw [← hsz]; exact hj'
    simp only [Array.getElem_toList] at hwi
    have hsj : ((raw .i64 M sel)[j]?.getD 0).toNat = i.1 := by
      rw [Array.getElem?_eq_getElem hj', Option.getD_some, hwi]
    obtain ⟨i1, hi1, hx1⟩ := Vals.gather_row _ hx ⟨j, hjM⟩
    obtain ⟨i2, hi2, hy2⟩ := Vals.gather_row _ hy ⟨j, hjM⟩
    have e1 : i1 = i := Fin.ext (by rw [← hi1, hsj])
    have e2 : i2 = i := Fin.ext (by rw [← hi2, hsj])
    subst e1 e2
    exact ⟨⟨j, hjM⟩, hx1, hy2⟩

/-- **`cmpOn op U` is the pairs of `dom U` that `r` relates**, `op` testing `r` on the signed words: `keep` of
`cross` of the domain with itself, row `i` kept where `op` answers `1`. -/
theorem cmpOn_holds {op : Op} {r : Int64 → Int64 → Bool}
    (hop : ∀ x y : UInt64, op.eval x y = .ok (if r x.toInt64 y.toInt64 then 1 else 0))
    {U T : Tab .long .long} (h : cmpOn op U = .ok T) (a c : Int64) :
    T.Holds a c ↔ (∃ v, U.Holds a v) ∧ (∃ v, U.Holds c v) ∧ r a c = true := by
  unfold cmpOn at h; simp only [bind, Except.bind] at h
  split at h; · cases h
  rename_i d hd
  split at h; · cases h
  rename_i X hX
  split at h; · cases h
  rename_i w hw
  obtain ⟨-, -, -, hev⟩ := colMap_raw hw
  have hwv : ∀ i : Fin X.n.toNat, (raw .i64 X.n w)[i.1]?.getD 0 =
      if r (X.key.row i) (X.val.row i) then 1 else 0 := by
    intro i
    have := hev i.1 i.2
    rw [hop] at this
    rw [← Except.ok.inj this, Vals.row_atom, Vals.row_atom, Arr.get_i64, Arr.get_i64]
  have hdom : ∀ x : Int64, (∃ i, d.key.row i = x) ↔ ∃ v, U.Holds x v := fun x => by
    constructor
    · rintro ⟨i, rfl⟩; exact ((dom_holds hd _ _).1 ⟨i, rfl, rfl⟩).2
    · intro hv; obtain ⟨i, hi, -⟩ := (dom_holds hd x x).2 ⟨rfl, hv⟩; exact ⟨i, hi⟩
  rw [keep_holds h (fun i hi => by rw [hwv ⟨i, hi⟩]; split <;> decide), ← hdom a, ← hdom c, ← and_assoc,
    ← cross_holds hX a c]
  simp only [Tab.Holds]
  constructor
  · rintro ⟨i, hi, rfl, rfl⟩
    rw [hwv i] at hi
    exact ⟨⟨i, rfl, rfl⟩, by cases hr : r (X.key.row i) (X.val.row i) <;> simp_all⟩
  · rintro ⟨⟨i, rfl, rfl⟩, hr⟩
    exact ⟨i, by rw [hwv i, if_pos hr]; decide, rfl, rfl⟩

/-- **`lt U` denotes `ltDen`**: `<` on `dom U`. -/
theorem lt_holds {U T : Tab .long .long} (h : Tab.lt U = .ok T) (a c : Int64) :
    T.Holds a c ↔ Lang.ltDen U.Holds a c := by
  rw [cmpOn_holds (r := fun x y => decide (x < y)) (fun _ _ => rfl) h, decide_eq_true_eq]

/-- **`leq U` denotes `leqDen`**: `≤` on `dom U`. -/
theorem leq_holds {U T : Tab .long .long} (h : Tab.leq U = .ok T) (a c : Int64) :
    T.Holds a c ↔ Lang.leqDen U.Holds a c := by
  rw [cmpOn_holds (r := fun x y => decide (x ≤ y)) (fun _ _ => rfl) h, decide_eq_true_eq]

end Tab

/-! ## Checks on `foR` tables -/

section Checks

/-- Two lists hold the same elements: the old layer orders a float NaN first, `kasc` by `ordCode`, and the old `memC`,
`ltC` keep repeats (that the new answer has none is `canonOk`). -/
private def sameSet {α : Type} [BEq α] : Option (List α) → Option (List α) → Bool
  | some a, some b => a.all b.contains && b.all a.contains
  | _, _ => false

/-- A new operator's answer as a list, `none` on `.error`. -/
private def newL {k v : Obj} (r : Except String (Tab k v)) : Option (List (k.El × v.El)) := r.toOption.map Tab.toList

/-- An old operator's answer as a list, `none` where it ran past its capacity. -/
private def oldL {k v : Obj} (c : Tab k v × Bool) : Option (List (k.El × v.El)) := if c.2 then some c.1.toList else none

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
private def U := Alg.col [1, 2, 5, 7, 9, -3, 2]

-- `\` and `/` against `leftDivC`, `rightDivC` on every pair of tables, within `U`; each answer canonical
#guard ts.all fun ps => ts.all fun qs =>
  let R := tab ps; let S := tab qs
  canonOk (R.ldiv S (idT U) (idT U)) && canonOk (R.rdiv S (idT U) (idT U)) &&
  sameSet (newL (R.ldiv S (idT U) (idT U))) (oldL (Alg.leftDivC R S U U)) &&
  sameSet (newL (R.rdiv S (idT U) (idT U))) (oldL (Alg.rightDivC R S U U))

#guard newL ((tab [(1, 2), (1, 5), (2, 2), (2, 5), (3, 2)]).ldiv (tab [(1, 7), (2, 7), (2, 8), (3, 7)])
  (idT (Alg.col [2, 5, 6])) (idT (Alg.col [7, 9]))) == some [(2, 7), (5, 7), (6, 7), (6, 9)]

-- `<`, `≤` against `ltC`, `leqC`, on `U` and on no values
#guard canonOk (Tab.lt (idT U)) && canonOk (Tab.leq (idT U)) &&
  sameSet (newL (Tab.lt (idT U))) (oldL (Alg.ltC U)) && sameSet (newL (Tab.leq (idT U))) (oldL (Alg.leqC U)) &&
  newL (Tab.lt (tab [])) == some [] && newL (Tab.leq (tab [(4, 0), (2, 0)])) == some [(2, 2), (2, 4), (4, 4)]

/-- The keys `3 1 4 -1 3`: `3` twice, `4` the key of no row. -/
private def D := Alg.col [3, 1, 4, -1, 3]

/-- The old answer's rows whose key is a row of `D`: `lamOnC` runs on `dom R ∪ D`, the new `lam` on the keys in
demand `D` (`Tm.lam`), the denotation `lamDen` on every key. -/
private def onD {v : Obj} (o : Option (List (Int64 × v.El))) : Option (List (Int64 × v.El)) :=
  o.map (·.filter fun r => [3, 1, 4, -1].contains r.1)

/-- Each key has one cell in each answer, holding the same elements: the cells' order is `kasc`'s in the new answer and
the old layer's (a float NaN first) in the old one. -/
private def sameCells {k v : Type} [BEq k] [BEq v] (a b : Option (List (k × List v))) : Bool :=
  let sub (x y : List (k × List v)) := x.all fun (a, ys) => y.any fun (a', ys') =>
    a == a' && ys.length == ys'.length && ys.all ys'.contains && ys'.all ys.contains
  match a, b with
  | some x, some y => sub x y && sub y x
  | _, _ => false

-- `Λ` on `D` against `lamOnC` on `D`, and `nil`
#guard ts.all fun ps => canonOk (Tab.lam D (tab ps)) &&
  sameSet (newL (Tab.lam D (tab ps))) (onD (oldL (Alg.lamOnC (tab ps) D)))
#guard newL (Tab.lam D (tab [(3, 1), (1, 2), (3, 1), (-1, 2), (1, 2), (3, -7)])) ==
  some [(-1, [2]), (1, [2]), (3, [-7, 1]), (4, [])]
#guard canonOk (Tab.nil (A := .long) (B := .long) D) &&
  newL (Tab.nil (A := .long) (B := .long) D) == some [(-1, []), (1, []), (3, []), (4, [])]

/-- `-0.0`, `+0.0`, NaN with payloads `1` and `2`, `+inf`, `-inf`, `1.5`, `-0.0` again, as `f64` bits. -/
private def f64s : List UInt64 := [0x8000000000000000, 0, 0x7ff8000000000001, 0x7ff8000000000002, 0x7ff0000000000000,
  0xfff0000000000000, 0x3ff8000000000000, 0x8000000000000000]

-- `E` against `EC` on `arrCells` (empty cells, `[5]` from three ranges, `[5,1]` twice), on no cells, and with a
-- relation of no rows
#guard [(arrCells, arrPay), ([], arrPay)].all fun (cs, ps) =>
  let X := (arrTab cs ps).key
  [tab [(5, 1), (9, 2), (1, 3), (5, 4)], tab [(9, 0)], tab []].all fun R =>
    canonOk (Tab.E X R) && sameCells (newL (Tab.E X R)) (oldL (Alg.EC R X))

-- `E` on float and tuple elements: cells over `f64s` (`[-0.0]` from `[0,1)` and `[7,8)`, the empty cell, both NaNs)
-- and over pairs (`[(1,5)]` from two ranges)
#guard
  let x := Arr.ofFn .f64 8 (f64s.getD · 0) ⟨by decide, by decide⟩
  let X := (arrOn [(0, 1, 0), (7, 8, 0), (2, 4, 0), (3, 3, 0), (0, 8, 0), (5, 7, 0)] x).key
  let R : Tab (.atom .f64) .long := ⟨8, x, Alg.col [1, 1, 2, 3, 4, 4, 5, 6]⟩
  let Y := (arrOn [(0, 1, 0), (2, 3, 0), (0, 4, 0), (1, 1, 0)] ((Alg.col [1, 2, 1, 3], Alg.col [5, 5, 5, 6]) :
    Vals (.prod .long .long) 4)).key
  let S : Tab (.prod .long .long) .long := ⟨3, (Alg.col [1, 1, 3], Alg.col [5, 5, 6]), Alg.col [7, 8, 9]⟩
  canonOk (Tab.E X R) && sameCells (newL (Tab.E X R)) (oldL (Alg.EC R X)) &&
  canonOk (Tab.E Y S) && sameCells (newL (Tab.E Y S)) (oldL (Alg.EC S Y))

-- `∋` on cells (empty ones, clamped ones, one cell twice) against `memC`, and on no cells
#guard [(arrCells, arrPay), (arrCells.take 3, arrPay), ([], arrPay), ([(0, 0, 1), (0, 0, 1)], [])].all fun (cs, ps) =>
  let X := (arrTab cs ps).key
  canonOk (Tab.mem X) && sameSet (newL (Tab.mem X)) (oldL (Alg.memC X))

-- a float value column (stored-bit equality) and a tuple value column, through `\`, `/` and `Λ`
#guard
  let x := Arr.ofFn .f64 8 (f64s.getD · 0) ⟨by decide, by decide⟩
  let R : Tab .long (.atom .f64) := ⟨8, Alg.col [3, 1, 2, 1, 4, 4, 0, 1], x⟩
  let S : Tab .long .long := tab [(3, 5), (1, 6), (2, 5), (1, 5), (4, 5), (0, 5), (0, 6)]
  let Ux := Arr.ofFn .f64 3 (f64s.getD · 0) ⟨by decide, by decide⟩
  canonOk (R.ldiv S (idT Ux) (idT U)) && sameSet (newL (R.ldiv S (idT Ux) (idT U))) (oldL (Alg.leftDivC R S Ux U)) &&
  sameCells (newL (Tab.lam D R)) (onD (oldL (Alg.lamOnC R D)))
#guard
  let R : Tab .long (.prod .long .long) := ⟨5, Alg.col [3, 1, 3, 1, 2], (Alg.col [1, 1, 2, 1, 2], Alg.col [5, 6, 5, 6, 5])⟩
  let S : Tab .long .long := tab [(3, 5), (1, 6), (1, 5), (2, 5)]
  let Up : Vals (.prod .long .long) 2 := (Alg.col [9, 9], Alg.col [9, 8])
  canonOk (R.ldiv S (idT Up) (idT U)) && sameSet (newL (R.ldiv S (idT Up) (idT U))) (oldL (Alg.leftDivC R S Up U)) &&
  sameSet (newL (Tab.lam D R)) (onD (oldL (Alg.lamOnC R D)))

end Checks

end Rel
