module

public import Rel.Run.SetOps
public import Rel.Run.List

-- exposed: every def body is a spec a downstream `rfl`/`decide`/`simp` may unfold (PLAN W.8)
@[expose] public section

/-! `rank` and the merge of sorted tables (architecture §4.7), as compositions of the five kernels, no new one: a row
compare `P < T`, `P = T` by one `kasc ≫ kseen` over `P ++ T` (`Vals.cmpRows`), `rank(X)` on `T` by bisection with that
compare as its step (`Vals.rank`), and `(X ∪ T, T − X)` of a canonical `X` from the rank without sorting `X`
(`Tab.mergeDiff`). `Tab.unionDiffSel` picks it where `X` is large against `T` (`(m + 1024) · L ≤ n`), else `Tab.unionDiff`. -/

namespace Rel
open Rel.Ext Rel.Kernel Rel.Verify

/-- **The row compare** `P < T` and `P = T`, row by row, as `0`/`1` words: `P ++ T` (`2m` rows) is grouped by `kasc ≫
kseen`, whose group numbers grow with the order, so `<` and `=` of two rows are `<` and `=` of their numbers; `kscatter
.last` through the permutation writes each number back at its input row, `kgather` reads the two halves, `colMap` of
`lt`, `eq`. The order is `asc`'s own, so one path serves every `Obj`. -/
def Vals.cmpRows {A : Obj} {m : USize} (P T : Vals A m) : Except String (Enc × Enc) := do
  let n2 ← catRows m m
  let C ← ValsB.concat n2 P T
  let es ← ValsB.cols C
  let (vs, p) ← kasc n2 es
  let (_, g, _) ← kseen n2 ((es.map (·.1)).zip vs)
  let code ← kscatter .last n2 p g n2 0
  let a ← kgather m .pos n2 code
  let b ← kgather m (← shiftCol m m.toUInt64) n2 code
  pure (← colMap .lt m a b, ← colMap .eq m a b)

/-- **`rank(X)` on `T`** and its hit test, `(r, h)`: `r[i]` the number of rows of the strictly ascending `X` below `T[i]`
(`Λ(> X) length`), `h[i] = 1` iff `T[i]` is a row of `X`. Bisection on the scalar `len` (from `n`, independent of the
data) and the column `base` (from `0`): the lower bound stays in `[base, base + len]`; a round probes `X[base + half − 1]`
(`half = len / 2`), moves `base` by `half` where the probe is below `T`, and `len -= half`, so `⌈log₂ n⌉` rounds leave
`len = 1`. Then `r = base + (X[base] < T)` and `h` compares `X[min(r, n − 1)]` with `T`. `fuel` only bounds the
recursion. `n = 0`: no row below, no hit. -/
def Vals.bisect {A : Obj} {n m : USize} (X : Vals A n) (T : Vals A m) : Nat → Nat → Enc → Except String Enc
  | 0, _, base => pure base
  | fuel + 1, len, base => do
    if len ≤ 1 then return base
    let half := len / 2
    let q ← colMap .first m base base .i64 .i64 [] [(.add, (half - 1).toUInt64)]
    let (c, _) ← Vals.cmpRows (← ValsB.pack 2 (← ValsB.gather m q X)) T
    bisect X T fuel (len - half) (← colMap .add m base (← colMap .first m c c .i64 .i64 [] [(.mul, half.toUInt64)]))

/-- `(r, h)` of `bisect`'s last two steps; see `bisect`. -/
def Vals.rank {A : Obj} {n m : USize} (X : Vals A n) (T : Vals A m) : Except String (Enc × Enc) := do
  if 2 ^ 63 ≤ n.toNat then throw s!"rank: {n} rows in X, not below 2^63 (positions are read signed)"
  if 2 ^ 62 ≤ m.toNat then throw s!"rank: {m} rows in T, not below 2^62 (the row compare's group numbers reach 2m and are read signed)"
  -- one bind, not `(← colConst m 0, ← colConst m 0)`: Lean 4.28 merges the two equal calls and emits both `ctor_get`s of
  -- the one result with a single `inc`, so the column is freed twice (heap corruption, exit 139 / "not a field")
  if n = 0 then let z ← colConst m 0; return (z, z)
  let base ← Vals.bisect X T (n.toNat.log2 + 1) n.toNat (← colConst m 0)
  let (c, _) ← Vals.cmpRows (← ValsB.pack 2 (← ValsB.gather m base X)) T
  let r ← colMap .add m base c
  let q ← colMap .first m r r .i64 .i64 [] [(.min, (n.toNat - 1).toUInt64)]
  let (_, h) ← Vals.cmpRows (← ValsB.pack 2 (← ValsB.gather m q X)) T
  pure (r, h)

namespace Tab
variable {k v : Obj}

/-- **`(X ∪ T, T − X)` of a canonical `X`, without sorting `X`**: `T` canonical, `rank` once; `U = T − X` the rows of
`T` with no hit (`whereCol` once, `r` gathered at the same positions is `rΔ`). Each row of `X` moves up by the number
of rows of `U` ranked at or before it (`cnt`: ones `kscatter .add`ed to `rΔ`, `colPrefix` of its first `n` cells), and
the `j`-th row of `U` sits at `rΔ[j] + j`; `kscatter .last` of `pos` at those `N = n + d` positions inverts them, and
one `gather` of `X ++ U` there is the union. -/
def mergeDiff (X T : Tab k v) : Except String (Tab k v × Tab k v) := do
  let T ← T.canon
  let n := X.n
  let (r, h) ← Vals.rank (A := .prod k v) (n := n) (X.key, X.val) (T.key, T.val)
  let (d, sel) ← whereCol T.n (← colMap .not T.n h h)
  let U : Tab k v := ⟨d, ← ValsB.gather d sel T.key, ← ValsB.gather d sel T.val⟩
  let rD ← kgather d sel T.n r
  let posD ← colArr .add d rD .pos
  let cnt ← kscatter .add d rD (← colConst d 1) (n.toNat + 1).toUSize 0
  let c ← colPrefix .add n (← kgather n .pos (n.toNat + 1).toUSize cnt)
  let posX ← colArr .add n c .pos
  let N ← catRows n d
  let ix ← ValsB.concat (o := false) (A := .atom .i64) N posX posD
  let ix ← kscatter .last N ix.enc .pos N 0
  let V ← ValsB.gather N ix (← ValsB.concat (A := .prod k v) N (X.key, X.val) (U.key, U.val))
  pure (⟨N, V.1, V.2⟩, U)

/-- The bisection's round count `L = ⌈log₂ n⌉ + 2`. -/
def bisectRounds (n : Nat) : Nat := n.log2 + 3

/-- The fixed cost of `mergeDiff`'s `L` bisection rounds (each a dozen small kernel calls, whatever the row count), in
rows of `T`: measured, `mergeDiff` is no slower than `unionDiff` once `(m + 1024) · L ≤ n` (`m = 1 .. 1000`). -/
def mergeCallRows : Nat := 1024

/-- **`(X ∪ T, T − X)`**: `mergeDiff` where `n` pays for its `L` rounds, `(m + mergeCallRows) · L ≤ n`, else
`unionDiff`; both give the same relations (`unionDiffSel_holds`), so the choice carries no proof obligation. -/
def unionDiffSel (X T : Tab k v) : Except String (Tab k v × Tab k v) :=
  if (T.n.toNat + mergeCallRows) * bisectRounds X.n.toNat ≤ X.n.toNat then X.mergeDiff T else X.unionDiff T

end Tab

end Rel
