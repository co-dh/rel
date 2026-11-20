import Rel.Programs.Prelude
import Rel.Run.SetOps

/-! `Tab.sums` (q's `sums` per key, `Rel/Run/SetOps.lean`) on the tables of a `rel_program`'s literals: ungrouped
    (one key), grouped by a key, positions missing, a non-simple `x` (the error naming the position), a step that
    wraps (that key's rows from there dropped), and `10^6` rows. Expected rows worked by hand below each. -/

namespace Rel.Lang.TestSums
open Rel

rel_program sumsT where
    obj N
    one : N×N ⟶ N ≜ {((0,0),3),((0,1),4),((0,3),5),((0,7),-2)}
    grp : N×N ⟶ N ≜ {((1,5),1),((0,0),3),((1,0),7),((0,2),5),((0,1),4)}
    dup : N×N ⟶ N ≜ {((0,0),3),((0,0),4),((0,1),1)}
    ovf : N×N ⟶ N ≜ {((0,0),9223372036854775807),((0,1),1),((0,2),5),((1,0),2),((1,1),-3)}

/-- `x`'s `sums`, its rows in position order. -/
def run (x : Except String (Tab (.prod .long .long) .long)) : Except String (List ((Int64 × Int64) × Int64)) := do
  pure (← Tab.sums (← x)).toList

-- one key: 3, 3+4, 3+4+5, 12−2; position 2 is missing, so position 3 follows position 1
#guard run sumsT.one == .ok [((0,0),3),((0,1),7),((0,3),12),((0,7),10)]
-- key 0: 3, 7, 12; key 1 starts again from 0: 7, 8
#guard run sumsT.grp == .ok [((0,0),3),((0,1),7),((0,2),12),((1,0),7),((1,5),8)]
-- two values at (0,0): the error names position 0
#guard match run sumsT.dup with
  | .error e => e.startsWith "sums: x is not simple: two values at the position 0 "
  | .ok _ => false
-- key 0: 2^63−1, then +1 wraps, so it and every later row of key 0 are dropped; key 1: 2, −1
#guard run sumsT.ovf == .ok [((0,0),9223372036854775807),((1,0),2),((1,1),-1)]

/-- `n` rows `(0, i) ↦ 1`, one key: the row count and the last sum, both `n`. -/
def ones (n : USize) : Except String (Nat × Int64) := do
  let p ← Arr.pos n
  let t ← Tab.sums (⟨n, (← Arr.zeros .i64 n, p), ← colArr .add n (← colConst n 1) (← colConst n 0)⟩ :
    Tab (.prod .long .long) .long)
  if h : 0 < t.n.toNat then pure (t.n.toNat, Vals.row (A := .long) t.val ⟨t.n.toNat - 1, by omega⟩)
  else throw "sums: no rows"

#guard ones 1000000 == .ok (1000000, 1000000)

end Rel.Lang.TestSums
