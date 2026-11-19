import Rel.Run.SetOps
import Rel.Run.Div
import Rel.Kernel.BitRows

/-! `R ≫ S` and `R \ S` on a bit matrix (`kbitrows`, the fused kernel of `doc/rel-architecture.zh.typ` §4), with the
types and answers of `Tab.comp` (`Rel/Run/Comp.lean`) and `Tab.ldiv` (`Rel/Run/Div.lean`). One file for both because
they share every step but the fold: number each side's values (`kasc ≫ kseen`), scatter the right-hand side into a
`u1` matrix (`kscatter`), group the left-hand side's rows (`csr`), fold (`kbitrows`), and read the set bits back as
rows (`whereCol`, `colMap .div/.mod`, `kgather`). A bit matrix is a `u1` `Enc` and its width, no other structure. The
choice between these and `Tab.comp`'s expansion or `Tab.ldiv`'s count is `bitsWin`, read by `compSel` and `ldivSel`. -/

namespace Rel
open Rel.Ext Rel.Kernel Rel.Verify
variable {A B C : Obj}

/-- The `n` rows of `x` numbered by value: `kasc ≫ kseen` (`k` distinct values, numbered in `kasc` order), each input
row's number (`kscatter .last` of the run numbers through `p`), and each number's first input row. -/
def Vals.code {n : USize} (x : Vals A n) : Except String (USize × Enc × Enc) := do
  let es ← Vals.cols x
  let (vs, p) ← kasc n es
  let (k, g, f) ← kseen n ((es.map (·.1)).zip vs)
  pure (k.toUSize, ← kscatter .last n p g n 0, ← kgather k.toUSize f n p)

/-- The words `a` (`n₁`) then `b` (`n₂`), CONCAT as `Arr.concat` on bare columns: the count and the column. -/
def colCat (n₁ n₂ : USize) (a b : Enc) : Except String (USize × Enc) := do
  let (N, sh) ← catPlan n₁ n₂
  pure (N, ← colMap .add N (← kscatter .last n₁ .pos a N 0) (← kscatter .last n₂ sh b N 0))

/-- `x` and `y` numbered by value in one order (`Vals.code` of their CONCAT `z`): the count, `x`'s numbers, `y`'s, and
`z` with each number's first row in it. -/
def Vals.code2 {n₁ n₂ : USize} (x : Vals A n₁) (y : Vals A n₂) :
    Except String (USize × Enc × Enc × ((N : USize) × Vals A N × Enc)) := do
  let (N, sh) ← catPlan n₁ n₂
  let z ← Vals.concat N sh x y
  let (k, c, rep) ← Vals.code z
  pure (k, ← kgather n₁ .pos N c, ← kgather n₂ sh N c, ⟨N, z, rep⟩)

/-- The `n` rows `(gid, x)` grouped by `gid` (each below `g`) as `kbitrows` reads a grouping: each group's end
(`kscatter .add` of ones, `colPrefix .add`) and `x` in group order (`kasc` of `gid`, stable). -/
def csr (n g : USize) (gid x : Enc) : Except String (Enc × Enc) := do
  let ends ← colPrefix .add g (← kscatter .add n gid (← colConst n 1) g 0)
  let (_, p) ← kasc n [(.atom .i64, gid)]
  pure (ends, ← kgather n p n x)

/-- The matrix of `na` rows of `w` bits with bit `r[k]·w + c[k]` set for each of the `n` rows: ones `kscatter`ed. -/
def bitMatrix (n na w : USize) (r c : Enc) : Except String Enc := do
  kscatter .last n (← colMap .add n (← colMap .mul n r (← colConst n w.toUInt64)) c) (← colConst n 1) (na * w) 0

namespace Tab

/-- The set bits of the `g · w` bits `o`, bit `a·w + c` the row `(x[ra[a]], y[rc[c]])`: `whereCol`, then `a` and `c` by
`colMap .div/.mod`, each side `kgather`ed. Ascending by `(a, c)`, so canonical where the numbers are `kasc` ranks. -/
def ofBits {n m : USize} (g w : USize) (o : Enc) (x : Vals A n) (ra : Enc) (y : Vals C m) (rc : Enc) :
    Except String (Tab A C) := do
  let (M, sel) ← whereCol (g * w) o
  let wc ← colConst M w.toUInt64
  let ix ← kgather M (← colMap .div M sel wc) g ra
  let iy ← kgather M (← colMap .mod M sel wc) w rc
  pure ⟨M, ← Vals.gather M ix x, ← Vals.gather M iy y⟩

/-- **`R ≫ S` on a bit matrix**: `S` as `kb` rows (middle values, numbered with `R.val`'s) of `kc` bits (its values),
`R`'s rows grouped by key (`ka` groups), each group the `∨` of the rows of its middle values (`kbitrows false`). -/
def compBits (R : Tab A B) (S : Tab B C) : Except String (Tab A C) := do
  let (kb, bR, bS, _) ← Vals.code2 R.val S.key
  let (ka, aR, ra) ← Vals.code R.key
  let (kc, cS, rc) ← Vals.code S.val
  if 2 ^ 63 ≤ (kb.toNat + ka.toNat) * kc.toNat then throw s!"compBits: {kb} or {ka} rows of {kc} bits past 2^63"
  let (ends, idx) ← csr R.n ka aR bR
  Tab.ofBits ka kc (← kbitrows false kc kb R.n ka ends idx (← bitMatrix S.n kb kc bS cS)) R.key ra S.val rc

/-- **`R \ S` within `UB`, `UC` on a bit matrix** (`ldivDen`): `S` as `ka` rows (keys, numbered with `R.key`'s) of `kc`
bits (values, numbered with `UC`'s), plus row `ka` holding `ran UC`; `R`'s rows grouped by value over `ran R ∪ ran UB`
(`kb` groups), each the `∧` of the rows of its keys (`kbitrows true`). A value of no `R` row is given the one row `ka`,
so its `∧` is `ran UC`: the vacuous part `(ran UB − ran R) × ran UC`. -/
def ldivBits (R : Tab A B) (S : Tab A C) (UB : Tab B B) (UC : Tab C C) : Except String (Tab B C) := do
  let (ka, aR, aS, _) ← Vals.code2 R.key S.key
  let (kb, bR, _, ⟨_, zb, rb⟩) ← Vals.code2 R.val UB.val
  let (kc, cS, cU, ⟨_, zc, rc⟩) ← Vals.code2 S.val UC.val
  if 2 ^ 63 ≤ (ka.toNat + 1 + kb.toNat) * kc.toNat + kb.toNat then
    throw s!"ldivBits: {ka} or {kb} rows of {kc} bits past 2^63"
  let cnt ← kscatter .add R.n bR (← colConst R.n 1) kb 0
  let (E, eb) ← whereCol kb (← colMap .eq kb cnt (← colConst kb 0))
  let (N, gid) ← colCat R.n E bR eb
  let (_, ix) ← colCat R.n E aR (← colConst E ka.toUInt64)
  let (ends, idx) ← csr N kb gid ix
  let (NS, r) ← colCat S.n UC.n aS (← colConst UC.n ka.toUInt64)
  let (_, c) ← colCat S.n UC.n cS cU
  Tab.ofBits kb kc (← kbitrows true kc (ka + 1) N kb ends idx (← bitMatrix NS (ka + 1) kc r c)) zb rb zc rc

/-- The most bits a matrix `compSel`, `ldivSel` build (`doc/rel-architecture.zh.typ` §4, `bitrows`). -/
def bitsMax : Nat := 2 ^ 27

/-- **The bit-matrix rule**: the `kbitrows` input of `na` rows and output of `g` rows, both of `w` bits, replace an
expansion of `T` rows when each is within `bits` and below `kbitrows`' `2^32`, and the two together are below `T`. -/
def bitsWin (bits T na g w : Nat) : Bool :=
  na * w ≤ bits && g * w ≤ bits && na * w < 2 ^ 32 && g * w < 2 ^ 32 && na * w + g * w < T

/-- **`R ≫ S`, on a bit matrix where `bitsWin` holds** (`compBits`, `Tab.compBits_holds`), else `compFrom` on the
same `compGroups` (`Tab.comp_canon`). `T` is `compGroups`' expansion, the matrix `K` rows (`K` the middle values, as
`compBits`' `kb`) and `ka` rows of `kc` bits. A nonempty expansion has `ka, kc ≥ 1`, so `T ≤ K + 1` fails `bitsWin`
before the two codes are paid for. -/
def compSel (bits : Nat) (R : Tab A B) (S : Tab B C) : Except String (Tab A C) := do
  let x ← compGroups R S
  let T ← compRows x
  let K := x.2.2.2.2.1.toNat
  if T ≤ K + 1 then compFrom blockRows R S x else do
    let ka := (← Vals.code R.key).1.toNat
    let kc := (← Vals.code S.val).1.toNat
    if bitsWin bits T K ka kc then compBits R S else compFrom blockRows R S x

/-- **`R \ S` within `UB`, `UC`, on a bit matrix where `bitsWin` holds** (`ldivBits`, `Tab.ldivBits_holds`), else
`ldiv` (`Tab.ldiv_holds`). `T` is the expansion of `R° ≫ S` (`compGroups`; `ldiv`'s `Q` before `R`, `S` are
deduplicated), the matrix `ka + 1` rows (`ka` the keys, as `ldivBits`' `ka`) and `kb` rows of `kc` bits. A nonempty
expansion has `kb, kc ≥ 1`, so `T ≤ ka + 2` fails `bitsWin` before the two codes are paid for. -/
def ldivSel (bits : Nat) (R : Tab A B) (S : Tab A C) (UB : Tab B B) (UC : Tab C C) : Except String (Tab B C) := do
  let x ← compGroups (⟨R.n, R.val, R.key⟩ : Tab B A) S
  let T ← compRows x
  let ka := x.2.2.2.2.1.toNat
  if T ≤ ka + 2 then ldiv R S UB UC else do
    let kb := (← Vals.code2 R.val UB.val).1.toNat
    let kc := (← Vals.code2 S.val UC.val).1.toNat
    if bitsWin bits T (ka + 1) kb kc then ldivBits R S UB UC else ldiv R S UB UC

end Tab

end Rel
