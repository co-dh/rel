import Rel.RepCanon

/-! The `#guard` checks of `Rel.RepCanon`, kept outside the module: a `#guard` runs compiled code, whose IR a `module` does not export (PLAN perf9e). -/

namespace Rel
open Rel.Ext Rel.Kernel Rel.Verify Ext.Enc


section Checks

/-- The table of the pairs `ps` as given, unsorted, both columns `Alg.col`'s literal `foR` columns. -/
def tab (ps : List (Int64 × Int64)) : Tab .long .long :=
  ⟨ps.length.toUSize, List.length_map _ ▸ Alg.col (ps.map (·.1)), List.length_map _ ▸ Alg.col (ps.map (·.2))⟩

/-- The answer `r` runs and holds the rows `sp` as a set, each once (`kasc` orders by `ordCode`, so not as listed):
the check of every operation against its denotation on lists. -/
def specOk {A B : Obj} [BEq A.El] [BEq B.El] (r : Except String (Tab A B)) (sp : List (A.El × B.El)) : Bool :=
  match r with
  | .ok T => let a := T.toList; let b := sp.eraseDups; a.length == b.length && a.all b.contains && b.all a.contains
  | .error _ => false

/-- The rows of a side, in position order. -/
def Vals.rows {A : Obj} {n : USize} (X : Vals A n) : List A.El := List.ofFn (Vals.row X)

#guard ((tab [(3, 1), (1, 2), (3, 1), (-1, 2), (1, 2), (2, 7)]).canon.toOption.map Tab.toList) ==
  some [(-1, 2), (1, 2), (2, 7), (3, 1)]
#guard ((tab [(3, 1), (1, 2), (3, 5), (0, -4)]).ran.toOption.map Tab.toList) == some [(-4, -4), (1, 1), (2, 2), (5, 5)]
#guard ((tab [(3, 1), (1, 2), (3, 5)]).dom.toOption.map Tab.toList) == some [(1, 1), (3, 3)]
#guard ((tab []).canon.toOption.map Tab.toList) == some []
/-- The five-kernel `canon`, `ran`, `dom` of `R` against their denotations on `R`'s rows as sets, each row once: `R`,
`𝟙 ∩ R° ≫ R°°` and `𝟙 ∩ R ≫ R°` (`kasc` orders by `ordCode`, so not as listed). -/
def canonAgrees {k v : Obj} [BEq k.El] [BEq v.El] (R : Tab k v) : Bool :=
  specOk R.canon R.toList && specOk R.ran (R.toList.map fun (_, b) => (b, b)) &&
    specOk R.dom (R.toList.map fun (a, _) => (a, a))

#guard [[(3, 1), (1, 2), (3, 1), (-1, 2), (1, 2), (2, 7), (-5, -5), (0, 0)], [(-2, 9), (-2, 9), (7, -3)], []].all
  fun ps => canonAgrees (tab ps)
/-- The table whose row `i` is `(tag, position, value)` = `ts[i]`, its key the sum side over the payloads `x` (tag
`false`) and `y` (tag `true`), every column `foR` (`Alg.tags`, `Alg.col`). `[R, S]`, `R + S`, `inl` and `inr` write
their position columns through the old `tilCol`/`razeTo`, which `kgather` declines (not `foR`). -/
def sumOn {a b : Obj} (ts : List (Bool × Int64 × Int64)) {l r : USize} (x : Vals a l) (y : Vals b r) :
    Tab (.sum a b) .long :=
  ⟨ts.length.toUSize, ⟨l, r, Arr.bools _ fun i => (ts.getD i (false, 0, 0)).1,
    List.length_map _ ▸ Alg.col (ts.map (·.2.1)), x, y⟩, List.length_map _ ▸ Alg.col (ts.map (·.2.2))⟩

/-- `sumOn` over the payloads of the longs `ls` and `rs`. -/
def sumTab (ts : List (Bool × Int64 × Int64)) (ls rs : List Int64) : Tab (.sum .long .long) .long :=
  sumOn ts (Alg.col ls) (Alg.col rs)

-- sum sides, as the key, the value and both: left payload positions `0` and `2` hold one value, so their rows are one
-- row; a summand of no rows, on each side
#guard [((([(false, 0, 1), (true, 1, 2), (false, 2, 1), (false, 1, 1), (true, 0, 2), (true, 1, 2), (false, 0, 3)] :
      List (Bool × Int64 × Int64)), [5, 7, 5], [9, 4])),
    ([(true, 1, 1), (true, 0, 2), (true, 1, 1)], [], [9, 4]), ([(false, 0, 1), (false, 0, 1)], [6], []),
    ([], [], [])].all fun (ts, ls, rs) =>
  let R := sumTab ts ls rs
  R.canon.toOption.isSome && canonAgrees R && canonAgrees (Tab.mk R.n R.val R.key) &&
    canonAgrees (Tab.mk R.n R.key R.key)

/-- The table whose row `i` is `(lo, hi, value)` = `cs[i]`, its key the `arr` side of the cells `[lo, hi)` over the
payload `f`, every column `foR` (`Alg.col`). -/
def arrOn {B : Obj} (cs : List (Int64 × Int64 × Int64)) {m : USize} (f : Vals B m) : Tab (.arr B) .long :=
  ⟨cs.length.toUSize, ⟨m, List.length_map _ ▸ Alg.col (cs.map (·.1)), List.length_map _ ▸ Alg.col (cs.map (·.2.1)), f⟩,
    List.length_map _ ▸ Alg.col (cs.map (·.2.2))⟩

/-- `arrOn` over the payload of the longs `ps`. -/
def arrTab (cs : List (Int64 × Int64 × Int64)) (ps : List Int64) : Tab (.arr .long) .long := arrOn cs (Alg.col ps)

/-- Cells over the payload `5 1 5 9 5`: `[5,1]` twice from one range, `[5]` from three ranges (`[0,1)`, `[2,3)`, and
`[4,5)`), the empty cell from `[3,3)` and from `[1,1)`, a proper prefix `[5]` of `[5,1]`, and `[3,5)` = `[9,5]`; every
cell `0 ≤ lo ≤ hi ≤ 5` (`Vals.WF`, which every table keeps). -/
def arrCells : List (Int64 × Int64 × Int64) :=
  [(0, 2, 1), (2, 3, 1), (0, 2, 1), (3, 3, 2), (4, 5, 2), (2, 4, 7), (0, 1, 1), (1, 1, 2), (4, 5, 1), (3, 5, 0)]
def arrPay : List Int64 := [5, 1, 5, 9, 5]

-- `arr` sides, as the key, the value and both, and a side of no cells
#guard [(arrCells, arrPay), (arrCells.take 3, arrPay), ([], arrPay), ([(0, 0, 1), (0, 0, 1)], [])].all fun (cs, ps) =>
  let R := arrTab cs ps
  R.canon.toOption.isSome && R.ran.toOption.isSome && R.dom.toOption.isSome && canonAgrees R &&
    canonAgrees (Tab.mk R.n R.val R.key) && canonAgrees (Tab.mk R.n R.key R.key)

end Checks

end Rel
