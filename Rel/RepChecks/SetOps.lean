import Rel.RepChecks.Canon
import Rel.RepSetOps

/-! The `#guard` checks of `Rel.RepSetOps`, kept outside the module: a `#guard` runs compiled code, whose IR a `module` does not export (PLAN perf9e). -/

namespace Rel
open Rel.Ext Rel.Kernel Rel.Verify Ext.Enc


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
/-- The five-kernel `∪`, `∩`, `−`, `⊑` of `R` and `S`, each answering `.ok`, against their denotations on the rows of
`R` and `S` as sets, each row once. -/
private def setOk {k v : Obj} [BEq k.El] [BEq v.El] (R S : Tab k v) : Bool :=
  let r := R.toList; let s := S.toList
  specOk (R.union S) (r ++ s) && specOk (R.inter S) (r.filter s.contains) &&
  specOk (R.diff S) (r.filter (!s.contains ·)) &&
  (R.le S).toOption == some (r.all s.contains)

-- both orders of every pair of tables
#guard [T₁, T₂, T₃, []].all fun ps => [T₁, T₂, T₃, []].all fun qs => setOk (tab ps) (tab qs)

/-- Cells over the payload `9 5 1 5`, the second part of each pair being shifted past `arrPay` by `Vals.concat`:
`[5]` and `[5,1]` (in `arrCells` too, from other ranges), the empty cell, `[1,5]`, and `[9,5]`. -/
private def arrCells₂ : List (Int64 × Int64 × Int64) := [(1, 2, 1), (1, 3, 7), (0, 0, 2), (2, 4, 1), (3, 4, 5), (0, 2, 9)]
private def arrPay₂ : List Int64 := [9, 5, 1, 5]

-- `arr` sides as the key and as the value: cells over different payloads, a side of no payload rows, a table of no
-- rows; tuple elements (`arr (long × long)`) and nested arrays (`arr (arr long)`)
#guard let As := [arrTab arrCells arrPay, arrTab arrCells₂ arrPay₂, arrTab [(0, 0, 1), (0, 0, 2)] [], arrTab [] arrPay]
  As.all fun R => As.all fun S => setOk R S && setOk (Tab.mk R.n R.val R.key) (Tab.mk S.n S.val S.key)
#guard let P (cs : List (Int64 × Int64 × Int64)) (ps qs : List Int64) (h : qs.length = ps.length) :
    Tab (.arr (.prod .long .long)) .long := arrOn cs (B := .prod .long .long) (Alg.col ps, h ▸ Alg.col qs)
  let As := [P arrCells arrPay [0, 1, 0, 0, 2] rfl, P arrCells₂ arrPay₂ [0, 1, 1, 1] rfl, P [] [] [] rfl]
  As.all fun R => As.all fun S => setOk R S
#guard let As := [arrOn arrCells (arrTab arrCells₂ arrPay₂).key, arrOn arrCells₂ (arrTab arrCells arrPay).key,
    arrOn [(0, 0, 1)] (arrTab [] arrPay).key]
  As.all fun R => As.all fun S => setOk R S && setOk (Tab.mk R.n R.val R.key) (Tab.mk S.n S.val S.key)

/-- Sum rows `(tag, position, value)`: left payload positions holding one value, a clamped position `5`. -/
private def sumRows₁ : List (Bool × Int64 × Int64) :=
  [(false, 0, 1), (true, 1, 2), (false, 2, 1), (false, 1, 1), (true, 0, 2), (true, 1, 2), (false, 5, 3)]
private def sumRows₂ : List (Bool × Int64 × Int64) := [(true, 0, 2), (false, 1, 1), (false, 0, 9), (true, 1, 3)]

-- `sum` sides as the key and as the value, with long and with `arr` summands
#guard let Ss := [sumTab sumRows₁ [5, 7, 5] [9, 4], sumTab sumRows₂ [7, 5] [9, 8]]
  Ss.all fun R => Ss.all fun S => setOk R S && setOk (Tab.mk R.n R.val R.key) (Tab.mk S.n S.val S.key)
#guard let Ss := [sumOn sumRows₁ (arrTab arrCells arrPay).key (b := .long) (Alg.col [9, 4]),
    sumOn sumRows₂ (arrTab arrCells₂ arrPay₂).key (b := .long) (Alg.col [9, 8])]
  Ss.all fun R => Ss.all fun S => setOk R S && setOk (Tab.mk R.n R.val R.key) (Tab.mk S.n S.val S.key)
-- an all-`inl` and an all-`inr` side: each summand is empty on one side, where no row is tagged into it
#guard let Ss := [sumTab [(false, 0, 1), (false, 1, 2), (false, 0, 1)] [5, 7] [], sumTab [(true, 1, 3), (true, 0, 1)] [] [9, 4],
    sumTab [(true, 0, 1)] [] [5]]
  Ss.all fun R => Ss.all fun S => setOk R S && setOk (Tab.mk R.n R.val R.key) (Tab.mk S.n S.val S.key)
-- a row tagged into a summand empty on its side reads `Obj.dflt`, which no payload row holds: the error
#guard (sumTab [(false, 0, 1)] [] [9]).union (sumTab [(false, 0, 1)] [5] []) matches .error _

end Checks

end Rel
