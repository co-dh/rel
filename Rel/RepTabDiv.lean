import Rel.Run.Div
import Rel.RepCanon
import Rel.RepSetOps
import Rel.RepTabComp
import Rel.Run.Alg

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

-- `E` composes `lam` on the arrays `X`, whose `Vals.concat` at an `arr` side is the error until `Rel/Run/Cols.lean`
-- concatenates `arr` sides
#guard Tab.E (arrTab arrCells arrPay).key (tab [(5, 1), (9, 2)]) matches .error "concat: an arr side is not atom columns"

-- `∋` on cells (empty ones, clamped ones, one cell twice) against `memC`, and on no cells
#guard [(arrCells, arrPay), (arrCells.take 3, arrPay), ([], arrPay), ([(0, 0, 1), (0, 0, 1)], [])].all fun (cs, ps) =>
  let X := (arrTab cs ps).key
  canonOk (Tab.mem X) && sameSet (newL (Tab.mem X)) (oldL (Alg.memC X))

/-- `-0.0`, `+0.0`, NaN with payloads `1` and `2`, `+inf`, `-inf`, `1.5`, `-0.0` again, as `f64` bits. -/
private def f64s : List UInt64 := [0x8000000000000000, 0, 0x7ff8000000000001, 0x7ff8000000000002, 0x7ff0000000000000,
  0xfff0000000000000, 0x3ff8000000000000, 0x8000000000000000]

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
