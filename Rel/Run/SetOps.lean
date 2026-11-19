import Rel.Run.Canon

/-! The Boolean operators `∪`, `∩`, `−` and `⊑` of `Tab` as compositions of the five kernels (PLAN 6.14 W3), on the
encoded columns as they are, as `Tab.canon` (`Rel/Run/Canon.lean`) is. Two tables are concatenated by CONCAT
(`doc/rel-kernels.md`): each side's rows are `kscatter`ed into one output of the summed length, `R`'s at `pos`, `S`'s
at `R.n + pos`, and a `kscan` map adds the two outputs (each cell is `0` in one of them). `∪` is `Tab.canon` of the
concatenation. `∩` and `−` tag each row with its source (`0` for `R`, `1` for `S`), group the concatenation's rows with
`kasc ≫ kseen`, fold the tags of each group with `kscatter` (`and`: some row of `R`; `or`: some row of `S`), and keep
the groups whose flag holds, their positions found by `whereCol`. No column is decoded or re-encoded between the
calls. -/

namespace Rel
open Rel.Ext Rel.Kernel Rel.Verify

/-- `n` words `w`: `kscatter` of no rows into `n` cells that start as `w`. -/
def fillCol (n : USize) (w : UInt64) : Except String Enc := kscatter .last 0 .pos .pos n w

/-- The `n` words `i + s`: a `kscan` map adding the positions (`pos`) and `fillCol n s`, every row a segment. -/
def shiftCol (n : USize) (s : UInt64) : Except String Enc := do
  kscan .add false .i64 .i64 n (← fillCol n 1) [.pos, ← fillCol n s]

/-- **CONCAT of two columns of one type**: `x` `kscatter`ed to the cells `0 … n₁-1` of `n`, `y` to `off` (`n₁ + k`),
the rest `0`, and the two added by a `kscan` map (`one`, `n` ones, makes every row a segment); the answer is `Enc.WF`
at `t` by `kscan_closed`. -/
def Arr.concat {t : QAtomicType} {n₁ n₂ : USize} (n : USize) (off one : Enc) (x : Arr t n₁) (y : Arr t n₂) :
    Except String (Arr t n) := do
  let a ← kscatter .last n₁ .pos x.enc n 0
  let b ← kscatter .last n₂ off y.enc n 0
  match h : kscan .add false .i64 t n one [a, b] with
  | .ok o => .ok (Arr.mk o (kscan_closed h).2)
  | .error s => .error s

/-- The rows of `x`, then those of `y`, as `n` rows: `Arr.concat` of each atom column (`off`, `one` as there). -/
def Vals.concat (n : USize) (off one : Enc) : {A : Obj} → {n₁ n₂ : USize} → Vals A n₁ → Vals A n₂ →
    Except String (Vals A n)
  | .atom _, _, _, x, y => Arr.concat n off one x y
  | .prod _ _, _, _, x, y => do pure (← Vals.concat n off one x.1 y.1, ← Vals.concat n off one x.2 y.2)
  | .arr _, _, _, _, _ => .error "concat: an arr side is not atom columns"
  | .sum _ _, _, _, _, _ => .error "concat: a sum side is not atom columns"

/-- The layout of `n₁` rows followed by `n₂`: the summed count `n`, the destinations `off` of the second part
(`shiftCol n₂ n₁`), and `n` ones; the error where `n` does not fit a `USize`. -/
def catPlan (n₁ n₂ : USize) : Except String (USize × Enc × Enc) :=
  if n₁.toNat + n₂.toNat < USize.size then do
    let n := (n₁.toNat + n₂.toNat).toUSize
    pure (n, ← shiftCol n₂ n₁.toUInt64, ← fillCol n 1)
  else .error s!"concat: {n₁} + {n₂} rows do not fit a USize"

/-- The positions of the `1` words among the `m` words `b` (each `0` or `1`), ascending, and their count `K`. WHERE
by the kernels that answer a count: `d = b · (pos + 1)` (a `kscan` map), so a kept position `G` is `G + 1` and every
other is `0`; a spare cell holding `0` appended (`kscatter` into `m + 1`); `kasc ≫ kseen` over `d` answers `K + 1`
groups, the `0`s first, then each kept position alone, ascending; the first rows of groups `1 … K` (`kgather` at
`shiftCol K 1`) read through `kasc`'s permutation are the kept positions. -/
def whereCol (m : USize) (b : Enc) : Except String (USize × Enc) :=
  if m.toNat + 1 < USize.size then do
    let d ← kscan .mul false .i64 .i64 m (← fillCol m 1) [b, ← shiftCol m 1]
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
  let (n, off, one) ← catPlan R.n S.n
  pure ⟨n, ← Vals.concat n off one R.key S.key, ← Vals.concat n off one R.val S.val⟩

/-- `R.concat S` and its source tag: `0` at `R`'s rows and `1` at `S`'s (`n₂` ones `kscatter`ed to `off`). -/
def tagged (R S : Tab k v) : Except String (Tab k v × Enc) := do
  let (n, off, one) ← catPlan R.n S.n
  pure (⟨n, ← Vals.concat n off one R.key S.key, ← Vals.concat n off one R.val S.val⟩,
    ← kscatter .last S.n off (← fillCol S.n 1) n 0)

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
  select (fun m mn mx => do kscan .lt false .i64 .i64 m (← fillCol m 1) [mn, mx]) R S

/-- **`R − S`**: the groups holding no row of `S`, `not` of the `or` (a `kscan` map). -/
def diff (R S : Tab k v) : Except String (Tab k v) :=
  select (fun m _ mx => do kscan .not false .i64 .i64 m (← fillCol m 1) [mx, mx]) R S

/-- **`R ⊑ S`**: `R − S` has no row. -/
def le (R S : Tab k v) : Except String Bool := (fun D => D.n == 0) <$> diff R S

end Tab

end Rel
