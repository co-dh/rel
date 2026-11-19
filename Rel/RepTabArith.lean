import Rel.Run.Arith
import Rel.Run.Alg

/-! Checks of `Tab.arith` and `Tab.succ` (`Rel/Run/Arith.lean`) against the meanings `arithDen`, `succDen` of
`Rel/Lang/Den.lean`, read on lists, and against the old `Alg.arith`, `Alg.succ` on the same data. -/

namespace Rel
open Rel.Ext Rel.Kernel Rel.Verify

section Checks

/-- The `Int64`s `l.map f` as an `i64` column of stored words (`Arr.ofFn`). -/
private def colOf {α : Type} (f : α → Int64) (l : List α) : Arr .i64 l.length.toUSize :=
  Arr.ofFn .i64 _ (fun i => ((l.map f).getD i.1 0).toUInt64)

/-- The rows `l` as a table keyed by the first and valued by the pair. -/
private def dTab (l : List (Int64 × Int64 × Int64)) : Tab .long (.prod .long .long) :=
  ⟨_, colOf (·.1) l, (colOf (·.2.1) l, colOf (·.2.2) l)⟩

/-- The coreflexive on the elements `u`. -/
private def uTab (u : List Int64) : Tab .long .long := ⟨_, colOf id u, colOf id u⟩

private def sameSet {α : Type} [BEq α] (a b : List α) : Bool := a.all b.contains && b.all a.contains

/-- `stepDen k`'s exactness test (`Rel/Lang/Den.lean`), as a `Bool`. -/
private def exactB (k : UInt8) (a b w : Int64) : Bool :=
  if k == Ew.add then (decide (0 ≤ b) == decide (a ≤ w)) else if k == Ew.sub then (decide (0 ≤ b) == decide (w ≤ a))
  else if k == Ew.mul then (Ew.intStep Ew.idiv Alg.nul w a == b || a == 0) else true

/-- Whether `Tab.arith k` answers `D ≫ arithDen k U` on lists, and agrees with the old `Alg.arith` on the pairs of
`D` whose operands are in `U`, then `≫ U`. -/
private def arithOk (k : UInt8) (d : List (Int64 × Int64 × Int64)) (u : List Int64) : Bool :=
  let inU (x : Int64) := u.contains x
  let spec := d.filterMap fun (x, a, b) => let w := Ew.intStep k Alg.nul a b
    if inU a && inU b && w != Alg.nul && exactB k a b w && inU w then some (x, w) else none
  let d' := d.filter fun (_, a, b) => inU a && inU b
  let old := ((Alg.arith k (dTab d').val).toList).filter (inU ·.2)
  let viaOld := d.flatMap fun (x, p) => (old.filter (·.1 == p)).map fun q => (x, q.2)
  match (dTab d).arith k (uTab u) with
  | .ok T => sameSet T.toList spec && sameSet T.toList viaOld
  | .error _ => false

/-- Whether `Tab.succ` answers `D ≫ succDen U` on lists, and agrees with the old `Alg.succ` composed after `D`. -/
private def succOk (d : List (Int64 × Int64)) (u : List Int64) : Bool :=
  let inU (x : Int64) := u.contains x
  let spec := d.filterMap fun (x, v) => let w := Ew.intStep Ew.add Alg.nul v 1
    if inU v && inU w then some (x, w) else none
  let old := (Alg.succ (colOf id u)).toList
  let viaOld := d.flatMap fun (x, v) => (old.filter (·.1 == v)).map fun q => (x, q.2)
  match (⟨_, colOf (·.1) d, colOf (·.2) d⟩ : Tab .long .long).succ (uTab u) with
  | .ok T => sameSet T.toList spec && sameSet T.toList viaOld
  | .error _ => false

/-- Operands and answers: the null `Int64.minValue`, its neighbour, `Int64.maxValue`, zero, signs, a value outside
`U`, so wraps, zero divisors, null operands and answers outside `U` all occur. -/
private def us : List Int64 := [Int64.minValue, Int64.minValue + 1, Int64.maxValue, 0, 1, 2, 3, 4, 6, -1, -2, -3,
  -4, 7, -7, 12, -12, 5, -5, 21, -21, 9]
/-- Pairs of `us` (and `100`, outside `U`), keyed `0, 1, …`, with a duplicate row and two rows of one key. -/
private def ds : List (Int64 × Int64 × Int64) :=
  let ps := [(Int64.minValue, 1), (1, Int64.minValue), (Int64.maxValue, 1), (Int64.maxValue, -1), (Int64.minValue + 1, -1),
    (Int64.minValue + 1, -2), (-7, 2), (7, -2), (-7, 3), (7, 0), (0, 0), (6, 3), (-12, -3), (3, 4), (100, 1), (1, 100),
    (Int64.maxValue, 2), (Int64.minValue, -1), (Int64.minValue, 0), (-1, -1), (2, 2)]
  (List.range ps.length).zip ps |>.map (fun (i, p) => (Int64.ofNat i, p)) |> (· ++ [(0, Int64.minValue, 1), (0, 4, 5)])

-- every verb of `Op.table` (`+ * − div mod max min`) on all of `ds`, an empty `D`, an empty `U`, and `U` without
-- the null (so a wrapped `max + 1` is not in `U`)
#guard [Ew.add, Ew.sub, Ew.mul, Ew.idiv, Ew.imod, Ew.greater, Ew.lesser].all fun k =>
  arithOk k ds us && arithOk k [] us && arithOk k ds [] && arithOk k ds (us.filter (· != Int64.minValue))
-- a code outside `Op.table` is the error naming it
#guard (dTab ds).arith 3 (uTab us) matches .error _
-- `succ`: the top of `U` goes nowhere, `maxValue` to the null only where `U` holds it, the null to itself
#guard succOk ((List.range us.length).zip us |>.map fun (i, u) => (Int64.ofNat i, u)) us
#guard succOk [(1, 3), (1, 3), (2, Int64.maxValue), (3, Int64.minValue), (4, 9), (5, 100)] [3, 4, 9, Int64.maxValue]
#guard succOk [(1, 3), (2, 4)] [] && succOk [] us

end Checks

end Rel
