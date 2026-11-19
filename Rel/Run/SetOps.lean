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
by the kernels that answer a count: `d = b · (pos + 1)` (a `kscan` map), so a kept position `G` is `G + 1` and every
other is `0`; a spare cell holding `0` appended (`kscatter` into `m + 1`); `kasc ≫ kseen` over `d` answers `K + 1`
groups, the `0`s first, then each kept position alone, ascending; the first rows of groups `1 … K` (`kgather` at
`shiftCol K 1`) read through `kasc`'s permutation are the kept positions. -/
def whereCol (m : USize) (b : Enc) : Except String (USize × Enc) :=
  if m.toNat + 1 < USize.size then do
    let d ← colMap .mul m b (← shiftCol m 1)
    let m' := (m.toNat + 1).toUSize
    let es := [(QAtomicType.i64, ← kscatter .last m .pos d m' 0)]
    let (vs, p) ← kasc m' es
    let (c, _, f) ← kseen m' ((es.map (·.1)).zip vs)
    let K := (c - 1).toUSize
    let fs ← kgather K (← shiftCol K 1) c.toUSize f
    (K, ·) <$> kgather K fs m' p
  else .error s!"where: {m} + 1 rows do not fit a USize"

namespace Tab
variable {k v : Obj}

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
