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

/-- **`R ≫ S` on a bit matrix**: `S` as `kb` rows (middle values, numbered with `R.val`'s) of `kc` bits (its values),
`R`'s rows grouped by key (`ka` groups), each group the `∨` of the rows of its middle values (`kbitrows false`). -/
def compMat (R : Tab A B) (S : Tab B C) : Except String (USize × USize × Enc × Enc × Enc) := do
  let (kb, bR, bS, _) ← Vals.code2 R.val S.key
  let (ka, aR, ra) ← Vals.code R.key
  let (kc, cS, rc) ← Vals.code S.val
  if 2 ^ 63 ≤ (kb.toNat + ka.toNat) * kc.toNat then throw s!"compBits: {kb} or {ka} rows of {kc} bits past 2^63"
  let (ends, idx) ← csr R.n ka aR bR
  pure (ka, kc, ← kbitrows false kc kb R.n ka ends idx (← bitMatrix S.n kb kc bS cS), ra, rc)

/-- `compMat`'s matrix read back as rows (`Tab.ofBits`). -/
def compBits (R : Tab A B) (S : Tab B C) : Except String (Tab A C) := do
  let (ka, kc, o, ra, rc) ← compMat R S
  Tab.ofBits ka kc o R.key ra S.val rc

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

/-- The bits an expanded row costs at least: one 64-bit word (it carries more: both sides and its row numbers). The
rule compares bits with bits, because memory IO is what both forms pay. -/
def rowBits : Nat := 64

/-- **The bit-matrix rule**: the `kbitrows` input of `na` rows and output of `g` rows, both of `w` bits, replace an
expansion of `T` rows when each is within `bits` and below `kbitrows`' `2^32`, and the two together are below the
expansion's `rowBits · T` bits. -/
def bitsWin (bits T na g w : Nat) : Bool :=
  na * w ≤ bits && g * w ≤ bits && na * w < 2 ^ 32 && g * w < 2 ^ 32 && na * w + g * w < rowBits * T

/-- What `bitsWin` runs as: `< 2 ^ 32` as a shift, since a `Nat` literal past `2^32` is built from its digits by GMP
(`lean_cstr_to_nat`) on every call. -/
private def bitsWinImpl (bits T na g w : Nat) : Bool :=
  na * w ≤ bits && g * w ≤ bits && (na * w) >>> 32 == 0 && (g * w) >>> 32 == 0 && na * w + g * w < rowBits * T

@[csimp] private theorem bitsWin_eq_impl : @bitsWin = @bitsWinImpl := by
  have e (x : Nat) : (x >>> 32 == 0) = decide (x < 2 ^ 32) := by
    cases h : decide (x < 2 ^ 32) <;> simp_all [Nat.shiftRight_eq_div_pow, Nat.div_eq_zero_iff]
  funext bits T na g w; simp only [bitsWin, bitsWinImpl, e]

/-- **`R ≫ S`, on a bit matrix where `bitsWin` holds** (`compBits`, `Tab.compBits_holds`), else `compFrom` on the
same `compGroups` (`Tab.comp_canon`). `T` is `compGroups`' expansion, the matrix `K` rows (`K` the middle values, as
`compBits`' `kb`) and `ka` rows of `kc` bits. A nonempty expansion has `ka, kc ≥ 1`, so `rowBits · T ≤ K + 1` fails
`bitsWin` before the two codes are paid for. -/
def compSelM (bits : Nat) (R : Tab A B) (S : Tab B C) :
    Except String (Tab A C ⊕ (USize × USize × Enc × Enc × Enc)) := do
  let x ← compGroups R S
  let T ← compRows x
  let K := x.2.2.2.2.1.toNat
  if rowBits * T ≤ K + 1 then do let t ← compFrom blockRows R S x; pure (.inl t) else do
    let ka := (← Vals.code R.key).1.toNat
    let kc := (← Vals.code S.val).1.toNat
    if bitsWin bits T K ka kc then do let m ← compMat R S; pure (.inr m)
    else do let t ← compFrom blockRows R S x; pure (.inl t)

/-- `compSelM` as a table: its matrix read back as rows (`Tab.ofBits`, as `compBits`). -/
def compSel (bits : Nat) (R : Tab A B) (S : Tab B C) : Except String (Tab A C) := do
  match ← compSelM bits R S with
  | .inl t => pure t
  | .inr (ka, kc, o, ra, rc) => Tab.ofBits ka kc o R.key ra S.val rc

/-- **`R \ S` within `UB`, `UC`, on a bit matrix where `bitsWin` holds** (`ldivBits`, `Tab.ldivBits_holds`), else
the division `d`: `ldiv` (`Tab.ldiv_holds`), or `ldivOf` where `R`, `S` are `Tab.Canonical` (`Tab.ldivOf_holds`), so
no `canon` runs on them. `T` is the expansion of `R° ≫ S` (`compGroups`; `ldiv`'s `Q` before `R`, `S` are
deduplicated), the matrix `ka + 1` rows (`ka` the keys, as `ldivBits`' `ka`) and `kb` rows of `kc` bits. A nonempty
expansion has `kb, kc ≥ 1`, so `rowBits · T ≤ ka + 2` fails `bitsWin` before the two codes are paid for. -/
def ldivSel (d : Tab A B → Tab A C → Tab B B → Tab C C → Except String (Tab B C)) (bits : Nat) (R : Tab A B)
    (S : Tab A C) (UB : Tab B B) (UC : Tab C C) : Except String (Tab B C) := do
  let x ← compGroups (⟨R.n, R.val, R.key⟩ : Tab B A) S
  let T ← compRows x
  let ka := x.2.2.2.2.1.toNat
  if rowBits * T ≤ ka + 2 then d R S UB UC else do
    let kb := (← Vals.code2 R.val UB.val).1.toNat
    let kc := (← Vals.code2 S.val UC.val).1.toNat
    if bitsWin bits T (ka + 1) kb kc then ldivBits R S UB UC else d R S UB UC

/-- `0 … n-1`: the prefix sums of `n` ones, less one. -/
def colIota (n : USize) : Except String Enc := do
  colMap .sub n (← colPrefix .add n (← colConst n 1)) (← colConst n 1)

/-- Each row of `v`, its position among the `g` distinct values `xr`, or `g` where it is none of them: both numbered in
one order (`Vals.code2`), each number's position in `xr` `kscatter`ed (`g` where `xr` holds none), read through `v`'s. -/
def index {g n : USize} (xr : Vals A g) (v : Vals A n) : Except String Enc := do
  let (k, cx, cv, _) ← Vals.code2 xr v
  kgather n cv k (← kscatter .last g cx (← colIota g) k g.toUInt64)

/-- **`T ∩ M`, `M` the `g · w` bits `o` over `x[ra[·]]` and `y[rc[·]]`** (`ofBits`' arguments): the rows of the canonical
`T` whose bit is set, each side's position by `index`, so `M` is never read back as rows. -/
def keepBits (T : Tab A C) {n m : USize} (g w : USize) (o : Enc) (x : Vals A n) (ra : Enc) (y : Vals C m) (rc : Enc) :
    Except String (Tab A C) := do
  let t ← T.canon
  let ia ← index (← Vals.gather g ra x) t.key
  let ic ← index (← Vals.gather w rc y) t.val
  let ok ← colMap .and t.n (← colMap .lt t.n ia (← colConst t.n g.toUInt64))
    (← colMap .lt t.n ic (← colConst t.n w.toUInt64))
  let (M, sel) ← whereCol t.n ok
  let u ← t.keep ok
  let pos ← colMap .add M (← colMap .mul M (← kgather M sel t.n ia) (← colConst M w.toUInt64)) (← kgather M sel t.n ic)
  u.keep (← kgather M pos (g * w) o)

/-- **`R ≫ M`, `M` as in `keepBits`, on its matrix**: `R`'s rows whose value is a row of `M` (`index`), grouped by key
(`csr`), each group the `∨` of its rows of `M` (`kbitrows false`): `ka` rows of `w` bits, with `R.key`'s values at
`ra'`. -/
def compTabMat (R : Tab A B) {n : USize} (g w : USize) (o : Enc) (x : Vals B n) (ra : Enc) :
    Except String (USize × Enc × ((M : USize) × Vals A M) × Enc) := do
  let ix ← index (← Vals.gather g ra x) R.val
  let (M, sel) ← whereCol R.n (← colMap .lt R.n ix (← colConst R.n g.toUInt64))
  let key ← Vals.gather M sel R.key
  let (ka, aR, ra') ← Vals.code key
  let (ends, idx) ← csr M ka aR (← kgather M sel R.n ix)
  pure (ka, ← kbitrows false w g M ka ends idx o, (⟨M, key⟩ : (M : USize) × Vals A M), ra')

/-- **`R \ M` within `UB`, `UC`, `M` as in `keepBits`, on its matrix** (`ldivDen`): `R`'s rows whose key is a row of
`M` (`index`) grouped by value (`csr`; values numbered with `UB`'s, `Vals.code2`), each group the `∧` of its rows of
`M` (`kbitrows true`), so `M` is never read back as rows. A value with a key outside `M` keeps no bit, a value of no
`R` row (`UB`'s alone) every column of `UC`; the `kb · w` bits are scattered to `M`'s columns numbered with `UC`'s
(`Vals.code2`): `kb` rows of `kc` bits, with `zb[rb[·]]`, `zc[rc'[·]]`. `none` where a matrix passes `bitsMax`.

Its law is `Tab.ldivTabMat_law` (`Rel/Lang/GenKBits.lean`). -/
def ldivTabMat (R : Tab A B) (UB : Tab B B) (UC : Tab C C) {n m : USize} (g w : USize) (o : Enc) (x : Vals A n)
    (ra : Enc) (y : Vals C m) (rc : Enc) : Except String
      (Option (USize × USize × Enc × ((N : USize) × Vals B N) × Enc × ((N : USize) × Vals C N) × Enc)) := do
  let (kb, bR, _, ⟨_, zb, rb⟩) ← Vals.code2 R.val UB.val
  let (kc, cM, cU, ⟨_, zc, rc'⟩) ← Vals.code2 (← Vals.gather w rc y) UC.val
  if bitsMax < kb.toNat * w.toNat ∨ bitsMax < kb.toNat * kc.toNat ∨ bitsMax < kb.toNat * UC.n.toNat then
    return none
  let ix ← index (← Vals.gather g ra x) R.key
  let on ← colMap .lt R.n ix (← colConst R.n g.toUInt64)
  let (P, sel) ← whereCol R.n on
  let (ends, idx) ← csr P kb (← kgather P sel R.n bR) (← kgather P sel R.n ix)
  let o1 ← kbitrows true w g P kb ends idx o
  let cnt ← kscatter .add R.n bR (← colConst R.n 1) kb 0
  let vac ← colMap .eq kb cnt (← colConst kb 0)
  -- `keep`: some `R` row, and every one's key a row of `M`
  let keep ← colMap .lt kb vac (← colMap .eq kb cnt (← kscatter .add R.n bR on kb 0))
  let N := kb * w
  let i ← colIota N
  let r ← colMap .div N i (← colConst N w.toUInt64)
  let p1 ← colMap .add N (← colMap .mul N r (← colConst N kc.toUInt64))
    (← kgather N (← colMap .mod N i (← colConst N w.toUInt64)) w cM)
  let s1 ← kscatter .last N p1 (← colMap .mul N o1 (← kgather N r kb keep)) (kb * kc) 0
  let (E, eb) ← whereCol kb vac
  let NU := E * UC.n
  let j ← colIota NU
  let s2 ← bitMatrix NU kb kc (← kgather NU (← colMap .div NU j (← colConst NU UC.n.toUInt64)) E eb)
    (← kgather NU (← colMap .mod NU j (← colConst NU UC.n.toUInt64)) UC.n cU)
  pure (some (kb, kc, ← colMap .add (kb * kc) s1 s2, ⟨_, zb⟩, rb, ⟨_, zc⟩, rc'))

end Tab

end Rel
