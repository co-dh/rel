import Rel.Run.Cols
import Rel.Run.SetOps

/-! Converse and composition as compositions of the five kernels (PLAN 6.14 W3), at the `Tab → Tab` boundary, on the
encoded columns as they are, in the style of `Rel/Run/Canon.lean`.

`R ≫ S` ranks the middle values of both sides in one order: the middle columns of `R.val` and `S.key` concatenated
(`Vals.concat`, CONCAT of `doc/rel-kernels.md`), `kasc` → `kseen` numbers the groups of equal middle values; `kasc`
being stable, a group's sorted rows are its `R` rows, then its `S` rows. Per group `kscatter (.add)` counts both runs,
their product is the group's output width, `expand` places the groups, and output row `t` of group `G` at offset `u` within it
pairs `R` row `p[f[G] + u / cS[G]]` with `S` row `p[f[G] + cR[G] + u % cS[G]] - n`. Both sides are `kgather`ed there
and the answer is `Tab.canon`ed. No column is decoded or re-encoded: every argument is a kernel's answer or a side's
own column; the output count is the one element `Arr.get` reads. -/

namespace Rel
open Rel.Ext Rel.Kernel Rel.Verify

/-- **EXPAND** (`doc/rel-kernels.md`) of the `K` widths `w`: `T` output rows, each row's group `G` and its offset `u`
in the group. A prefix sum `P` places the groups (`o = P - w`), `kscatter (.max)` of each group id at its offset,
filled forward by `colPrefix (.max)`, the spare cell `T` cut off by `kgather`; `u = pos - o[G]`. The one scalar read
is the count `T` (`lastCount`). -/
def expand (K : USize) (w : Enc) : Except String (USize × Enc × Enc) := do
  match hP : colPrefix .add K w with
  | .error s => throw s
  | .ok P =>
    let T := lastCount K P (colPrefix_closed hP).2
    if USize.size ≤ T + 1 then throw s!"expand: {T} output rows past USize"
    let T := T.toUSize
    let o ← colMap .sub K P w
    let G ← kgather T .pos (T + 1) (← colPrefix .max (T + 1) (← kscatter .max K o .pos (T + 1) 0))
    pure (T, G, ← colMap .sub T .pos (← kgather T G K o))

namespace Tab
variable {A B C : Obj}

/-- **`R°`**: the two sides swapped, then `canon`, as the old converse (`Gen.conv`: `ofC (r.rel°, _)`). -/
def conv (R : Tab A B) : Except String (Tab B A) := Tab.canon ⟨R.n, R.val, R.key⟩

/-- The groups of `R ≫ S` (first `R`, then `S`): the groups of equal middle values (`kasc` → `kseen` over
`Vals.concat` of `R.val` and `S.key`; `N` rows, permutation `p`, group `g` of each sorted row, first sorted row `f`
of each of the `K` groups), per group the run of `R` rows (`cR`, those whose input row `p[q]` is below `n`) and of
`S` rows (`cS`), and the output rows of each group (`w = cR * cS`). -/
def compGroups (R : Tab A B) (S : Tab B C) :
    Except String (USize × Enc × Enc × Enc × USize × Enc × Enc × Enc) := do
  let n := R.n; let m := S.n
  -- `.lt`, `.max`, `.div`, `.mod` read counts, row numbers and offsets signed: every one is below `n * m + n + m`
  if 2 ^ 63 ≤ n.toNat * m.toNat + n.toNat + m.toNat then throw s!"comp: {n} × {m} rows past 2^63"
  let (N, sh) ← catPlan n m
  let es ← Vals.cols (← Vals.concat N sh R.val S.key)
  let (vs, p) ← kasc N es
  let (k, g, f) ← kseen N ((es.map (·.1)).zip vs)
  let K := k.toUSize
  -- `p < n` as one `kscan` with the constant in its post chain (`gt` reads `n` on its left), no `colConst`
  -- (`colMap_const_eq`)
  let cR ← kscatter .add N g (← colMap .first N p p .i64 .i64 [] [(.gt, n.toUInt64)]) K 0
  let cS ← colMap .sub K (← kscatter .add N g (← colConst N 1) K 0) cR
  pure (N, p, g, f, K, cR, cS, ← colMap .mul K cR cS)

/-- The output rows of `compGroups`' groups: each output row's group `G` and offset `u` in it (`expand` of `w`), its
`R` and `S` input rows, both sides `kgather`ed there, then `canon`. -/
def compExpand (R : Tab A B) (S : Tab B C) :
    USize × Enc × Enc × Enc × USize × Enc × Enc × Enc → Except String (Tab A C)
  | (N, p, _, f, K, cR, cS, w) => do
    let n := R.n
    let (T, G, u) ← expand K w
    let ft ← kgather T G K f
    let ct ← kgather T G K cS
    let iR ← kgather T (← colMap .add T ft (← colMap .div T u ct)) N p
    let qS ← colMap .add T (← colMap .add T ft (← kgather T G K cR)) (← colMap .mod T u ct)
    let pq ← kgather T qS N p
    -- `pq - n` as `pq + (0 - n)` in one `kscan`'s post chain, no `colConst` (`colMap_const_eq`)
    let iS ← colMap .first T pq pq .i64 .i64 [] [(.add, 0 - n.toUInt64)]
    Tab.canon ⟨T, ← Vals.gather T iR R.key, ← Vals.gather T iS S.val⟩

/-- **`R ≫ S` in one expansion**: `compGroups`, then `compExpand` of all its groups at once; its peak is the
expansion `Σ cR·cS`, before `canon` removes duplicates. -/
def compOne (R : Tab A B) (S : Tab B C) : Except String (Tab A C) := compGroups R S >>= compExpand R S

/-- The most output rows `Tab.comp` expands at once before `canon`: past it the groups go in blocks. -/
def blockRows : Nat := 2 ^ 24

/-- The blocks of `compGroups`' answer `x` when its expansion `T` is past `bound` (`none`: one block). A group starts
a block when the window `(P - 1) / bound` of its last output row (`P` the prefix sum of `w`) differs from the previous
group's, or when it or the previous group alone reaches `bound`: groups are never split, and a block is one group or
below `2 · bound` rows. The block of each group is the prefix sum of those starts; an `R` row's block is its
group's (`kscatter .last` of `g` through `p`, then `kgather`). `nb` is the count of blocks. -/
def compCuts (bound : Nat) (n : USize) :
    USize × Enc × Enc × Enc × USize × Enc × Enc × Enc → Except String (Option (Nat × Arr .i64 n))
  | (N, p, g, _, K, _, _, w) =>
    match hP : colPrefix .add K w with
    | .error s => throw s
    | .ok P => if lastCount K P (colPrefix_closed hP).2 ≤ bound then pure none else do
      let z ← colConst K 0
      let one ← colConst K 1
      let bc ← colConst K (max bound 1).toUInt64
      let win ← colMap .div K (← colMap .max K (← colMap .sub K P one) z) bc
      let big ← colMap .le K bc w
      let prev ← colMap .max K (← colMap .sub K .pos one) z
      let pw ← kgather K prev K win
      let pb ← kgather K prev K big
      let cut ← colMap .or K (← colMap .ne K win pw) (← colMap .or K big pb)
      match hI : colPrefix .add K (← colMap .and K cut (← colMap .lt K z .pos)) with
      | .error s => throw s
      | .ok I =>
        let rowG ← kgather n .pos N (← kscatter .last N p g N 0)
        pure (some (lastCount K I (colPrefix_closed hI).2 + 1, ← Arr.gather n rowG (Arr.mk I (colPrefix_closed hI).2)))

/-- Block `j` of `R ≫ S`: the rows of `R` whose block word in `c` is `j` (`keep`), composed with `S` by `compOne`. -/
def compBlock (R : Tab A B) (S : Tab B C) (c : Enc) (j : Nat) : Except String (Tab A C) := do
  compOne (← R.keep (← colMap .first R.n c c .i64 .i64 [] [(.eq, j.toUInt64)])) S

/-- **`R ≫ S` over the blocks `bid`** (`nb` of them, one word per row of `R`): `bid` clamped into `[0, nb - 1]`
(`Arr.clampShift`), so every row of `R` is in one block whatever `bid` holds; the blocks' tables met by `∪`. Only
`R` is cut: `S` whole in every block makes each block exact on its own, with no claim that `bid` is a function of the
middle value. -/
def compBlocks (R : Tab A B) (S : Tab B C) (nb : Nat) (bid : Arr .i64 R.n) : Except String (Tab A C) := do
  if 2 ^ 63 ≤ nb then throw s!"comp: {nb} blocks past 2^63"
  let c ← bid.clampShift (nb - 1).toUInt64 0
  (List.range (nb - 1)).foldlM (fun acc j => do acc.union (← compBlock R S c.enc (j + 1))) (← compBlock R S c.enc 0)

/-- The output rows of `compGroups`' answer before `canon`: the last word of the prefix sum of `w` (`compCuts`' `P`). -/
def compRows : USize × Enc × Enc × Enc × USize × Enc × Enc × Enc → Except String Nat
  | (_, _, _, _, K, _, _, w) => match hP : colPrefix .add K w with
    | .error s => throw s
    | .ok P => pure (lastCount K P (colPrefix_closed hP).2)

/-- `R ≫ S` from `compGroups`' answer `x`: `compExpand` where the expansion is within `bound`, else `compBlocks` over
`compCuts`' blocks. -/
def compFrom (bound : Nat) (R : Tab A B) (S : Tab B C)
    (x : USize × Enc × Enc × Enc × USize × Enc × Enc × Enc) : Except String (Tab A C) := do
  match ← compCuts bound R.n x with
  | none => compExpand R S x
  | some (nb, bid) => compBlocks R S nb bid

/-- **`R ≫ S` expanding at most about `bound` rows at once**: `compOne` where `R.n · S.n` is within `bound`, else
`compFrom`. Each block is deduplicated (`canon`) before the `∪`, so the peak is a block plus the result, not the
whole expansion. -/
def compWith (bound : Nat) (R : Tab A B) (S : Tab B C) : Except String (Tab A C) :=
  if R.n.toNat * S.n.toNat ≤ bound then compOne R S else compGroups R S >>= compFrom bound R S

/-- **`R ≫ S`** (first `R`, then `S`): `compWith blockRows`. -/
def comp (R : Tab A B) (S : Tab B C) : Except String (Tab A C) := compWith blockRows R S

end Tab

end Rel
