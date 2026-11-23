import Rel.Run.Merge
import Rel.BitsTest
import Rel.Run.Div
import Rel.Run.List
import Rel.Run.Struct
import Rel.OptAtoms

/-! `Tab.mergeDiff` (bisection `rank`, then the merge by `scatter`/`scan`/`gather`) against `Tab.unionDiff` (one `asc`
over `X ++ T`), both run on the same input and compared as lists of rows (the `arr` payload layout differs, so not byte
equality); and the doc's rank instance (architecture §4.7). -/

namespace Rel.MergeTest
open Rel.Kernel Rel.Verify Rel.BitsTest

/-- The words of an `i64` column of `n` rows. -/
def words (n : USize) (e : Enc) : List UInt64 := (Rel.Ext.Enc.raw .i64 n e).toList

/-- `rank` and its hit column of `T`'s rows in the canonical `X`, as words. -/
def rankOf (X T : List (Int64 × Int64)) : Except String (List UInt64 × List UInt64) := do
  let X ← (← tab X).canon; let T ← (← tab T).canon
  let (r, h) ← Vals.rank (A := .prod .long .long) (n := X.n) (X.key, X.val) (T.key, T.val)
  pure (words T.n r, words T.n h)

/-- `mergeDiff` and `unionDiff` of the same tables answer the same two row lists, both succeeding. -/
def sameMerge {k v : Obj} [BEq k.El] [BEq v.El] (X T : Except String (Tab k v)) : Bool :=
  match (do let X ← (← X).canon; X.mergeDiff (← T)), (do let X ← (← X).canon; X.unionDiff (← (← T).canon)) with
  | .ok (V, U), .ok (V', U') => V.toList == V'.toList && U.toList == U'.toList
  | _, _ => false

-- the doc's instance: `X = 10 30 50`, `T = 30 40 60` (value `0`): `r = 1 2 3`, `h = 1 0 0`
#guard (rankOf [(10, 0), (30, 0), (50, 0)] [(30, 0), (40, 0), (60, 0)]).toOption = some ([1, 2, 3], [1, 0, 0])
#guard ((do let X ← (← tab [(10, 0), (30, 0), (50, 0)]).canon
            X.mergeDiff (← tab [(30, 0), (40, 0), (60, 0)])) : Except String _).toOption.map
    (fun (V, U) => (V.toList.map (·.1), U.toList.map (·.1))) = some ([10, 30, 40, 50, 60], [40, 60])
#guard sameMerge (tab [(1, 1), (2, 2), (3, 3)]) (tab [(3, 3), (1, 1)])
#guard sameMerge (tab [(1, 1), (2, 2)]) (tab [(5, 5), (6, 6), (7, 7)])
#guard sameMerge (tab [(5, 5), (6, 6)]) (tab [(1, 1), (2, 2), (2, 2)])
#guard sameMerge (tab [(1, 1), (1, 3), (2, 2)]) (tab [(1, 2), (1, 3), (2, 1)])
-- `prod` on both sides, as `BitsTest`'s tuple-valued middle
#guard sameMerge (do let R ← tab [(1, 10), (2, 20), (1, 20)]; pure (⟨R.n, (R.key, R.val), R.key⟩ : Tab (.prod .long .long) .long))
  (do let R ← tab [(1, 10), (3, 30), (2, 20)]; pure (⟨R.n, (R.key, R.val), R.key⟩ : Tab (.prod .long .long) .long))
-- 200 rows against 37, and against 5 (`sameMerge` runs `mergeDiff` itself, whatever `unionDiffSel` would pick)
#guard sameMerge (tab (rnd 1 200 50)) (tab (rnd 2 37 50))
#guard sameMerge (tab (rnd 3 400 100)) (tab (rnd 4 5 100))
-- `n = 0`, `m = 0`, both empty: `rank` (no row below, no hit) and the merge
#guard (rankOf [] [(1, 1), (2, 2)]).toOption = some ([0, 0], [0, 0])
#guard (rankOf [(1, 1), (2, 2)] []).toOption = some ([], [])
#guard (rankOf [] []).toOption = some ([], [])
#guard sameMerge (tab []) (tab [(1, 1), (2, 2)])
#guard sameMerge (tab [(1, 1), (2, 2)]) (tab [])
#guard sameMerge (tab []) (tab [])

-- one guard per `Obj` shape `Vals.cols` has a branch for
/-- `arr` on both sides: the lists of the images of each key's rows and their prefixes, a payload shared between rows and
a cell that is a strict prefix of another. -/
def arrTab (ps : List (Int64 × Int64)) : Except String (Tab (.arr .long) (.arr .long)) := do
  let R ← (← tab ps).canon; Tab.prefix (← Tab.lam R.key R).val
#guard sameMerge (arrTab (rnd 5 60 4)) (arrTab (rnd 6 20 4))
#guard sameMerge (arrTab (rnd 7 40 6)) (arrTab [])

/-- A table of `long` keys with `1+long` values, `none` the null (the band column `Opt`). -/
def optTab (ps : List (Int64 × Option Int64)) : Except String (Tab .long (.sum .one .long)) := do
  let k ← arr (ps.map (·.1))
  match Opt.ofAtoms .i64 (ps.map fun p => p.2.map QAtom.i64).toArray with
  | some o => pure ⟨_, by simpa using k, (o : Opt .i64 _)⟩
  | none => throw "optTab: Opt.ofAtoms refused the column"
#guard sameMerge (optTab [(1, some 5), (2, none), (3, some 7)]) (optTab [(2, none), (3, some 8), (4, none), (1, some 5)])
#guard sameMerge (optTab [(1, none), (1, some 0), (2, some 3)]) (optTab [(1, none), (2, some 3), (2, none)])

/-- A general sum: `inl` rows beside `inr` rows. -/
def sumTab (l r : List (Int64 × Int64)) : Except String (Tab .long (.sum .long .long)) := do
  Tab.union (← Tab.inl (B := .long) (← tab l).key) (← Tab.inr (A := .long) (← tab r).key)
#guard sameMerge (sumTab [(1, 1), (2, 2), (3, 3)] [(2, 2), (4, 4)]) (sumTab [(3, 3), (5, 5)] [(1, 1), (2, 2), (6, 6)])
#guard sameMerge (sumTab [(1, 1)] [(2, 2)]) (sumTab [] [])

-- `1` on a side: a unit key, a unit value, both
#guard sameMerge (do let R ← tab [(1, 1), (2, 2)]; pure (⟨R.n, R.key, ()⟩ : Tab .long .one))
  (do let R ← tab [(2, 2), (3, 3)]; pure (⟨R.n, R.key, ()⟩ : Tab .long .one))
#guard sameMerge (do let R ← tab [(1, 1), (2, 2)]; pure (⟨R.n, (), R.val⟩ : Tab .one .long))
  (do let R ← tab [(2, 2), (3, 3)]; pure (⟨R.n, (), R.val⟩ : Tab .one .long))
#guard sameMerge (do let R ← tab [(1, 1), (2, 2)]; pure (⟨R.n, (), ()⟩ : Tab .one .one))
  (do let R ← tab [(1, 1)]; pure (⟨R.n, (), ()⟩ : Tab .one .one))

end Rel.MergeTest
