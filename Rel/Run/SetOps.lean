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

/-- **q's `sums` per key** (`rowDens`: `agg(dom(x) (𝟙 × ≥) dom(x), F(x) ⦇[0, plus]⦈)`): `canon` sorts `x` by
`(κ, ν)`, so each key `κ` is one run; `kseen` on the whole key checks `x` simple (one value per `(κ, ν)`, else the
error naming a doubled position), `kseen` on the `κ` columns gives each run's first row, ones `kscatter`ed there are
the segment marks (`groupFold`'s first line), and a segmented `kscan .add` from `0` is the prefix sum `W`. A step is
bad where it wrapped (`v` and `W − v` of one sign, `W` of the other) or reads or makes the null `-2^63`, as in
`Tab.sum`; a segmented `kscan .or` carries it to the rest of its key, and those rows are dropped (`keep`). The
positions are those of an integer-stored atom (`intOrd`), whose canon order is their value order; elsewhere the
error. -/
def sums {K : Obj} : {P : Obj} → Tab (.prod K P) .long → Except String (Tab (.prod K P) .long)
  | .prod .., _ | .sum .., _ | .arr _, _ => throw "sums: the positions are no atom"
  | .atom t, x => do
  unless t.intOrd do throw s!"sums: positions of {repr t} are not ordered by value"
  let C ← canon x
  let n := C.n
  let (m, _, f) ← kseen n (← Vals.cols (A := .prod K (.atom t)) C.key)
  if m ≠ n.toNat then
    let firsts ← kscatter .last m.toUSize f (← colConst m.toUSize 1) n 0
    let (d, sel) ← whereCol n (← colMap .eq n firsts (← colConst n 0))
    let p ← Vals.gather (A := .atom t) d sel C.key.2
    let at0 := if h : 0 < d.toNat then s!"{t.num (Vals.row (A := .atom t) p ⟨0, h⟩)}" else "?"
    throw s!"sums: x is not simple: two values at the position {at0} of one key ({n.toNat - m} doubled in all); \
      sums folds one value per (key, position)"
  let (gk, _, fk) ← kseen n (← Vals.cols C.key.1)
  let seg ← kscatter .last gk.toUSize fk (← colConst gk.toUSize 1) n 0
  let z ← colConst n 0
  let v := Arr.enc (t := .i64) C.val
  let W := (← kscan .add false .i64 .i64 n seg [z, v]).1
  let sv ← colMap .lt n v z
  let ovf ← colMap .and n (← colMap .eq n sv (← colMap .lt n (← colMap .sub n W v) z)) (← colMap .ne n sv
    (← colMap .lt n W z))
  let nul ← colConst n 0x8000000000000000
  let bad ← colMap .or n ovf (← colMap .or n (← colMap .eq n W nul) (← colMap .eq n v nul))
  let badR := (← kscan .or false .i64 .i64 n seg [z, bad]).1
  keep ⟨n, C.key, ← colArr .add n W z⟩ (← colMap .not n badR badR)

end Tab

end Rel
