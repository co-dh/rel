import Rel.Run.Cols

/-! The Boolean operators `∪`, `∩`, `−` and `⊑` of `Tab` as compositions of the five kernels (PLAN 6.14 W3), on the
encoded columns as they are, as `Tab.canon` (`Rel/Run/Canon.lean`) is. Two tables are concatenated by CONCAT
(`doc/rel-kernels.md`): each side's rows are `kscatter`ed into one output of the summed length, `R`'s at `pos`, `S`'s
at `R.n + pos`, and `colMap .add` sums the two outputs (`Rel/Run/Cols.lean`). `∪` is `Tab.canon` of the
concatenation. `∩` and `−` tag each row with its source (`0` for `R`, `1` for `S`), group the concatenation's rows with
`kasc ≫ kseen`, fold the tags of each group by a segmented `kscan` (`groupFold`; `and`: some row of `R`; `or`: some row of `S`), and keep
the groups whose flag holds, their positions found by `whereCol`. No column is decoded or re-encoded between the
calls. -/

namespace Rel
open Rel.Ext Rel.Kernel Rel.Verify

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

/-- **The fold of each group of a sorted table** (design §4, rows `∩ −` and `R\S`): over `n` rows in `kasc` order
whose `m` groups `g` are runs starting at the rows `f` (`kseen`), the segment marks are the rows `f` (`kscatter` of
ones), a segmented `kscan` folds `op` over `x` from `z` within each run, and a group's answer is its run's last row
(`kscatter .last` through `g`, the later row overwriting). -/
def groupFold (op : Op) (n : USize) (g f : Enc) (m : USize) (z : UInt64) (x : Enc) : Except String Enc := do
  let seg ← kscatter .last m f (← colConst m 1) n 0
  let (o, _) ← kscan op false .i64 .i64 n seg [← colConst n z, x]
  kscatter .last n g o m z

/-- The groups of equal rows of `R.concat S` whose source flags pass `keep`, canonical: `kasc ≫ kseen` over the pair
columns (`m` groups `g`, first sorted rows `f`), the tags in sorted order (`kgather` through `p`), per group the `and`
of its tags (`0` iff it holds a row of `R`) and their `or` (`1` iff it holds a row of `S`) by `groupFold`, `keep` of
the two (one `0`/`1` word per group), `whereCol` of that, and each kept group's first input row gathered. -/
def select (keep : USize → Enc → Enc → Except String Enc) (R S : Tab k v) : Except String (Tab k v) := do
  let (C, tag) ← R.tagged S
  let x : Vals (.prod k v) C.n := (C.key, C.val)
  let es ← Vals.cols x
  let (vs, p) ← kasc C.n es
  let (m, g, f) ← kseen C.n ((es.map (·.1)).zip vs)
  let ts ← kgather C.n p C.n tag
  let mn ← groupFold .and C.n g f m.toUSize 1 ts
  let mx ← groupFold .or C.n g f m.toUSize 0 ts
  let (K, sel) ← whereCol m.toUSize (← keep m.toUSize mn mx)
  let ix ← kgather K (← kgather K sel m.toUSize f) C.n p
  (fun y => ⟨K, y.1, y.2⟩) <$> Vals.gather K ix x

/-- **`R ∩ S`**: the groups holding a row of each, `and < or` (a `kscan` map of `lt`). -/
def inter (R S : Tab k v) : Except String (Tab k v) :=
  select (fun m mn mx => colMap .lt m mn mx) R S

/-- **`R − S`**: the groups holding no row of `S`, `not` of the `or` (a `kscan` map). -/
def diff (R S : Tab k v) : Except String (Tab k v) :=
  select (fun m _ mx => colMap .not m mx mx) R S

/-- **The pairs of `D` that the test `q` holds on the diagonal**: `q(D) ∩ D`, `D` coreflexive (a `ran`), so a row `p`
stays where `q` relates `p` to `p`. The one reading of a test `Q` in `thin`, `thinL`, `merge`. -/
def diag (q : Tab k k → Except String (Tab k k)) (D : Tab k k) : Except String (Tab k k) := do (← q D).inter D

/-- **`R ⊑ S`**: `R − S` has no row. -/
def le (R S : Tab k v) : Except String Bool := (fun D => D.n == 0) <$> diff R S

end Tab

end Rel
