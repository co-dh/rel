import Rel.Run.Cols

/-! Converse and composition as compositions of the five kernels (PLAN 6.14 W3), at the `Tab → Tab` boundary, on the
encoded columns as they are, in the style of `Rel/Run/Canon.lean`.

`R ≫ S` ranks the middle values of both sides in one order: the middle columns of `R.val` and `S.key` concatenated
(`Vals.concat`, CONCAT of `doc/rel-kernels.md`), `kasc` → `kseen` numbers the groups of equal middle values; `kasc`
being stable, a group's sorted rows are its `R` rows, then its `S` rows. Per group `kscatter (.add)` counts both runs,
their product is the group's output width, a prefix `kscan (.add)` places the groups (EXPAND: `kscatter` of each group
id at its offset, a prefix `kscan (.max)` fills it forward), and output row `t` of group `G` at offset `u` within it
pairs `R` row `p[f[G] + u / cS[G]]` with `S` row `p[f[G] + cR[G] + u % cS[G]] - n`. Both sides are `kgather`ed there
and the answer is `Tab.canon`ed. No column is decoded or re-encoded: every argument is a kernel's answer or a side's
own column; the output count is the one element `Arr.get` reads. -/

namespace Rel
open Rel.Ext Rel.Kernel Rel.Verify

/-- The last of the `n` words of the `i64` column `e`, or `0` at `n = 0`, read as a count (`Arr.get`, one element). -/
def lastCount (n : USize) (e : Enc) (h : Enc.WF .i64 n e) : Nat :=
  if hn : 0 < n.toNat then (Arr.get (Arr.mk e h) ⟨n.toNat - 1, by omega⟩).toNatClampNeg else 0

namespace Tab
variable {A B C : Obj}

/-- **`R°`**: the two sides swapped, then `canon`, as the old converse (`Gen.conv`: `ofC (r.rel°, _)`). -/
def conv (R : Tab A B) : Except String (Tab B A) := Tab.canon ⟨R.n, R.val, R.key⟩

/-- **`R ≫ S`** (first `R`, then `S`): the groups of equal middle values (`kasc` → `kseen` over `Vals.concat` of
`R.val` and `S.key`), per group the run of `R` rows (`cR`, those whose input row `p[q]` is below `n`) and of `S` rows
(`cS`), the output rows of each group (`cR * cS`, placed by a prefix sum `P`, offsets `o = P - w`, `T` rows in all),
each output row's group `G` (`kscatter (.max)` of the group ids at the offsets, filled forward by `colPrefix (.max)`,
the spare cell `T` cut off by `kgather`) and its `R` and `S` input rows, both sides `kgather`ed there, then `canon`. -/
def comp (R : Tab A B) (S : Tab B C) : Except String (Tab A C) := do
  let n := R.n; let m := S.n
  -- `.lt`, `.max`, `.div`, `.mod` read counts, row numbers and offsets signed: every one is below `n * m + n + m`
  if 2 ^ 63 ≤ n.toNat * m.toNat + n.toNat + m.toNat then throw s!"comp: {n} × {m} rows past 2^63"
  let (N, sh) ← catPlan n m
  let es ← Vals.cols (← Vals.concat N sh R.val S.key)
  let (vs, p) ← kasc N es
  let (k, g, f) ← kseen N ((es.map (·.1)).zip vs)
  let K := k.toUSize
  let cR ← kscatter .add N g (← colMap .lt N p (← colConst N n.toUInt64)) K 0
  let cS ← colMap .sub K (← kscatter .add N g (← colConst N 1) K 0) cR
  let w ← colMap .mul K cR cS
  match hP : colPrefix .add K w with
  | .error s => throw s
  | .ok P =>
    let T := lastCount K P (by
      unfold colPrefix at hP; simp only [bind, Except.bind] at hP; split at hP; · cases hP
      exact (kscan_closed hP).2)
    if USize.size ≤ T + 1 then throw s!"comp: {T} output rows past USize"
    let T := T.toUSize
    let o ← colMap .sub K P w
    let G ← kgather T .pos (T + 1) (← colPrefix .max (T + 1) (← kscatter .max K o .pos (T + 1) 0))
    let ft ← kgather T G K f
    let u ← colMap .sub T .pos (← kgather T G K o)
    let ct ← kgather T G K cS
    let iR ← kgather T (← colMap .add T ft (← colMap .div T u ct)) N p
    let qS ← colMap .add T (← colMap .add T ft (← kgather T G K cR)) (← colMap .mod T u ct)
    let iS ← colMap .sub T (← kgather T qS N p) (← colConst T n.toUInt64)
    Tab.canon ⟨T, ← Vals.gather T iR R.key, ← Vals.gather T iS S.val⟩

end Tab

end Rel
