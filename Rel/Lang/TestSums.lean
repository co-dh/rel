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
#guard (run sumsT.one).toOption == some [((0,0),3),((0,1),7),((0,3),12),((0,7),10)]
-- key 0: 3, 7, 12; key 1 starts again from 0: 7, 8
#guard (run sumsT.grp).toOption == some [((0,0),3),((0,1),7),((0,2),12),((1,0),7),((1,5),8)]
-- two values at (0,0): the error names position 0
#guard match run sumsT.dup with
  | .error e => e.startsWith "sums: x is not simple: two values at the position 0 "
  | .ok _ => false
-- key 0: 2^63−1, then +1 wraps, so it and every later row of key 0 are dropped; key 1: 2, −1
#guard (run sumsT.ovf).toOption == some [((0,0),9223372036854775807),((1,0),2),((1,1),-1)]

/-- `n` rows `(0, i) ↦ 1`, one key: the row count and the last sum, both `n`. -/
def ones (n : USize) : Except String (Nat × Int64) := do
  let p ← Arr.pos n
  let t ← Tab.sums (⟨n, (← Arr.zeros .i64 n, p), ← colArr .add n (← colConst n 1) (← colConst n 0)⟩ :
    Tab (.prod .long .long) .long)
  if h : 0 < t.n.toNat then pure (t.n.toNat, Vals.row (A := .long) t.val ⟨t.n.toNat - 1, by omega⟩)
  else throw "sums: no rows"

#guard (ones 1000000).toOption == some (1000000, 1000000)

-- The row `sums(x)` in a program, run on the kernel path (`kernRows`), each `check` against rows worked by hand:
-- `one` one key, as `sumsT.one`; `grp` key 0: −3, −3+4, 1+5; key 1: 7, 8; `ovf` as `sumsT.ovf`; `nul` key 0:
-- 1, then the null −2^63, so it and key 0's later rows have no image; key 1: −6, −6+2.
rel_program sumsP where
    obj N
    one : N×N ⟶ N ≜ {((0,0),3),((0,1),4),((0,3),5),((0,7),-2)}
    grp : N×N ⟶ N ≜ {((1,5),1),((0,0),-3),((1,0),7),((0,2),5),((0,1),4)}
    ovf : N×N ⟶ N ≜ {((0,0),9223372036854775807),((0,1),1),((0,2),5),((1,0),2),((1,1),-3)}
    nul : N×N ⟶ N ≜ {((0,0),1),((0,1),-9223372036854775808),((0,2),4),((1,0),-6),((1,4),2)}
    sone : N×N ⟶ N ≜ sums(one)
    sgrp : N×N ⟶ N ≜ sums(grp)
    sovf : N×N ⟶ N ≜ sums(ovf)
    snul : N×N ⟶ N ≜ sums(nul)
    check sone = {((0,0),3),((0,1),7),((0,3),12),((0,7),10)}
    check sgrp = {((0,0),-3),((0,1),1),((0,2),6),((1,0),7),((1,5),8)}
    check sovf = {((0,0),9223372036854775807),((1,0),2),((1,1),-1)}
    check snul = {((0,0),1),((1,0),-6),((1,4),-4)}

#guard sumsP.failures.isEmpty

-- The positions and the values are two objects: positions in `P = 0…9`, values in `N`. Key 0: 3, 3+4, 7+5;
-- key 1: −2, −2+6, 4+9 at positions 2, 8, 9.
rel_program sumsPN where
    obj N
    obj P = 0…9
    x : N×P ⟶ N ≜ {((0,0),3),((0,1),4),((0,3),5),((1,2),-2),((1,9),9),((1,8),6)}
    s : N×P ⟶ N ≜ sums(x)
    check s = {((0,0),3),((0,1),7),((0,3),12),((1,2),-2),((1,8),4),((1,9),13)}

#guard sumsPN.failures.isEmpty

-- The values summed by `plus`, so they are a number object of i64 as `plus`'s are: an object of i32 or of f64 is
-- refused, naming it, its atom and the one accepted.
/-- error: line 82, col 5: sums on I: I is an object of i32, and sums runs on objects of i64 only -/
#guard_msgs in
rel_program sumsI where
    obj N
    obj I : i32
    x : N×N ⟶ I ≜ {((0,0),3),((0,1),4)}
    s : N×N ⟶ I ≜ sums(x)

/-- error: line 90, col 5: sums on F: F is an object of f64, and sums runs on objects of i64 only -/
#guard_msgs in
rel_program sumsF where
    obj N
    obj F : f64
    x : N×N ⟶ F ≜ {((0,0),3.5),((0,1),4)}
    s : N×N ⟶ F ≜ sums(x)

end Rel.Lang.TestSums
