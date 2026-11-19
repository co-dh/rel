import Rel.Run.Cols

/-! The Boolean operators `∪`, `∩`, `−` and `⊑` of `Tab` as compositions of the five kernels (PLAN 6.14 W3), on the
encoded columns as they are, as `Tab.canon` (`Rel/Run/Canon.lean`) is. Two tables are concatenated by CONCAT
(`doc/rel-kernels.md`): each side's rows are `kscatter`ed into one output of the summed length, `R`'s at `pos`, `S`'s
at `R.n + pos`, and `colMap .add` sums the two outputs (`Rel/Run/Cols.lean`). `∪` is `Tab.canon` of the
concatenation. `∩` and `−` tag each row with its source (`0` for `R`, `1` for `S`), group the concatenation's rows with
`kasc ≫ kseen`, fold the tags of each group with `kscatter` (`and`: some row of `R`; `or`: some row of `S`), and keep
the groups whose flag holds, their positions found by `whereCol`. No column is decoded or re-encoded between the
calls. -/

namespace Rel
open Rel.Ext Rel.Kernel Rel.Verify

/-- The positions of the `1` words among the `m` words `b` (each `0` or `1`), ascending, and their count `K`. WHERE
as `scan → scatter`, O(m) and no sort: the prefix sum `s` of `b` (`kscan .add`, one segment) returns the count `K` as
its fold result; `m = 0` folds no row and returns `none`, and an empty `where` counts `0` positions by definition, so
`none` is `K = 0`. The destination `d = s − b` (`colMap .sub`) is the number of kept rows before each row: a kept row's
own cell `0 … K − 1`, and a dropped row's the next kept row's cell, which that later row overwrites (`kscatter .last`,
the last row winning), or the spare cell `K` past every kept row. `kscatter` of `pos` at `d` into `K + 1` cells, then
`kgather` of the first `K` (at `pos`): 6 kernel calls (`colConst`, `kscan`, `colMap` = `colConst` + `kscan`,
`kscatter`, `kgather`), where `kasc ≫ kseen` took 13. `m` is below `B`, so `K + 1 ≤ m + 1` cells fit a `USize`. -/
def whereCol (m : USize) (b : Enc) : Except String (USize × Enc) :=
  let B := min (USize.size - 1) (2 ^ 63)
  if m.toNat < B then do
    let z ← colConst m 0
    let sk ← kscan .add false .i64 .i64 m z [z, b]
    let K := (sk.2.getD 0).toNat.toUSize
    let d ← colMap .sub m sk.1 b
    let e ← kscatter .last m d .pos (K.toNat + 1).toUSize 0
    (K, ·) <$> kgather K .pos (K.toNat + 1).toUSize e
  else .error s!"where: {m} rows, not below {B}: m + 1 cells fit a USize and the counts 0 … m are i64 words below it"

-- `1 0 1 1 0`: the destinations `0 1 1 2 3` send the dropped row 1 to row 2's cell and row 4 to the spare cell `3`
#guard (whereCol 5 (.bytes (Column.packIds 64 5 fun i => [1, 0, 1, 1, 0][i]?.getD 0))).toOption.map
  (fun r => (r.1.toNat, (Enc.raw .i64 r.1 r.2).toList)) = some (3, [0, 2, 3])
-- no kept row, and no row at all: `K = 0`
#guard (whereCol 3 (.bytes (Column.packIds 64 3 fun _ => 0))).toOption.map
  (fun r => (r.1.toNat, (Enc.raw .i64 r.1 r.2).toList)) = some (0, [])
#guard (whereCol 0 .pos).toOption.map (fun r => (r.1.toNat, (Enc.raw .i64 r.1 r.2).toList)) = some (0, [])

namespace Tab
variable {k v : Obj}

/-- The rows of `T` where the `0`/`1` words `b` are `1`: `whereCol`, both sides `kgather`ed there. Row order is
kept, so a canonical `T` stays canonical. -/
def keep (T : Tab k v) (b : Enc) : Except String (Tab k v) := do
  let (M, sel) ← whereCol T.n b
  pure ⟨M, ← Vals.gather M sel T.key, ← Vals.gather M sel T.val⟩

/-- **`R` then `S`**: the rows of both, `R`'s first (`Vals.concat` of each side on `catPlan`). -/
def concat (R S : Tab k v) : Except String (Tab k v) := do
  let (n, off) ← catPlan R.n S.n
  pure ⟨n, ← Vals.concat n off R.key S.key, ← Vals.concat n off R.val S.val⟩

/-- `R.concat S` and its source tag: `0` at `R`'s rows and `1` at `S`'s (`n₂` ones `kscatter`ed to `off`). -/
def tagged (R S : Tab k v) : Except String (Tab k v × Enc) := do
  let (n, off) ← catPlan R.n S.n
  pure (⟨n, ← Vals.concat n off R.key S.key, ← Vals.concat n off R.val S.val⟩,
    ← kscatter .last S.n off (← colConst S.n 1) n 0)

/-- **`R ∪ S`**: `Tab.canon` of the concatenation. -/
def union (R S : Tab k v) : Except String (Tab k v) := R.concat S >>= canon

/-- The groups of equal rows of `R.concat S` whose source flags pass `keep`, canonical: `kasc ≫ kseen` over the pair
columns (`m` groups `g`, first sorted rows `f`), the tags in sorted order (`kgather` through `p`), per group the `and`
of its tags (`0` iff it holds a row of `R`) and their `or` (`1` iff it holds a row of `S`) by `kscatter`, `keep` of
the two (one `0`/`1` word per group), `whereCol` of that, and each kept group's first input row gathered. -/
def select (keep : USize → Enc → Enc → Except String Enc) (R S : Tab k v) : Except String (Tab k v) := do
  let (C, tag) ← R.tagged S
  let x : Vals (.prod k v) C.n := (C.key, C.val)
  let es ← Vals.cols x
  let (vs, p) ← kasc C.n es
  let (m, g, f) ← kseen C.n ((es.map (·.1)).zip vs)
  let ts ← kgather C.n p C.n tag
  let mn ← kscatter .and C.n g ts m.toUSize 1
  let mx ← kscatter .or C.n g ts m.toUSize 0
  let (K, sel) ← whereCol m.toUSize (← keep m.toUSize mn mx)
  let ix ← kgather K (← kgather K sel m.toUSize f) C.n p
  (fun y => ⟨K, y.1, y.2⟩) <$> Vals.gather K ix x

/-- **`R ∩ S`**: the groups holding a row of each, `and < or` (a `kscan` map of `lt`). -/
def inter (R S : Tab k v) : Except String (Tab k v) :=
  select (fun m mn mx => colMap .lt m mn mx) R S

/-- **`R − S`**: the groups holding no row of `S`, `not` of the `or` (a `kscan` map). -/
def diff (R S : Tab k v) : Except String (Tab k v) :=
  select (fun m _ mx => colMap .not m mx mx) R S

/-- **`R ⊑ S`**: `R − S` has no row. -/
def le (R S : Tab k v) : Except String Bool := (fun D => D.n == 0) <$> diff R S

end Tab

end Rel
