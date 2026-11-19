import Rel.Kernel.Asc

/-! `seen` (PLAN D.12): the seen-set scan over the rows of several key columns. A row's group is the first row with an
equal key, numbered in order of first occurrence, so `B A B` answers `g = 0 1 0` and `first = 0 1`. It replaces
`distinct`, which numbered runs of adjacent equal rows and so was this scan on a sorted input only. The body is the
foR-reading form of `Order.idsBy`: `Order.firstsBy` over the rows, a row's group `Order.groupIn` them. Rows out of
order whose key range is too wide for direct addressing are the error (`seenEngine`): `crate/src/seen.rs` has no hash.

Equality is `kasc`'s: two rows are equal when every column's order code at its type (`ascCol`) is, so `-0.0` and `0.0`
are one group and every NaN is one group, and `kasc ≫ kseen` numbers exactly `kasc`'s runs of ties. The `k` in the name
is temporary, as for `kscan`; 6.11 renames. -/

namespace Rel.Kernel
open Ext.Enc

/-- `kwin::range` at `i64` (`asc::Key::new`): the least and greatest word of a `foR` column of `n` rows as its block
metadata bounds them, each with its sign bit flipped so unsigned order is signed order: every block's `base` and `maxv`
(`Column.baseAt`, `Column.maxvAt`) on the grid of `n` and every element of the patch list, read as `Column.foRExc`
reads one. No residual is read. -/
def foRBounds (n : Nat) (md pk : ByteArray) : UInt64 × UInt64 :=
  let e := Column.blockStart md (Column.nblk md)
  let esz := (Column.bitsAt pk (e + 8) 8).toNat % 256
  let s := (64 - 8 * esz).toUInt64
  let exc := if pk.size ≤ e then [] else (List.range (Column.bitsAt pk e 8).toNat).map fun k =>
    let v := Column.bitsAt pk (e + 16 + k * esz) esz
    if esz == 1 then v else ((v <<< s).toInt64 >>> s.toInt64).toUInt64
  let ws := (List.range ((n + Column.blk md - 1) / Column.blk md)).flatMap
    (fun b => [Column.baseAt md b, Column.maxvAt md b]) ++ exc
  (ws.foldl (fun a w => min a (w ^^^ 2 ^ 63)) (~~~0), ws.foldl (fun a w => max a (w ^^^ 2 ^ 63)) 0)

/-- `asc::Key::span`: the least and greatest order code of the key column `c` at `n` rows. Where `foRBounds` lies in
the range where the type's code is the word plus one constant (`Key::linear`), the bounds' codes; else every code of the
type's width. A column `ascCol` refuses, or a `pos` one, never reaches it: `(0, 0)`. -/
def keySpan (n : Nat) (c : QAtomicType × Enc) : Nat × Nat :=
  match ascLayout c.1, c.2 with
  | some (w, fl, sg), .foR md pk =>
    let (mn, mx) := foRBounds n md pk
    -- the bounds as signed words, Rust's `lo` and `hi`
    let (lo, hi) : Int × Int := (mn.toNat - 2 ^ 63, mx.toNat - 2 ^ 63)
    let top : Int := 2 ^ (8 * w - 1)
    let (a, b) : Int × Int := if fl then (0, if w == 8 then 0x7ff0000000000000 else 0x7f800000)
      else if sg then (-top, top - 1) else (0, 2 * top - 1)
    if a ≤ lo ∧ hi ≤ b then ((ordKey w fl sg (mn ^^^ 2 ^ 63)).toNat, (ordKey w fl sg (mx ^^^ 2 ^ 63)).toNat)
    else (0, 2 ^ (8 * w) - 1)
  | _, _ => (0, 0)

/-- `seen::blocks`' choice of engine (`crate/src/seen.rs`) over the `n` rows of the columns `es` and their codes `ks`:
a `pos` column (every row new), no row, direct addressing (the product `r` of the columns' `keySpan` widths, saturating
at `2^128` as a `u128` does, passes `group::direct_ok`) or rows already in `lexLe` order (`asc::sorted`) answer. Else
the rows need a hash, which is not built: the error, naming each column's type and code span. -/
def seenEngine (n : Nat) (es : List (QAtomicType × Enc)) (ks : List (Array UInt64)) : Except String Unit :=
  let sp := es.map (keySpan n)
  let r := sp.foldl (fun p (a, b) => min (p * (b - a + 1)) (2 ^ 128 - 1)) 1
  let hex := fun (x : Nat) => "0x" ++ String.ofList (Nat.toDigits 16 x)
  let cols := (es.zip sp).zipIdx.map fun ((c, a, b), i) => s!"es[{i}] type {c.1.ctorIdx} codes {hex a}..={hex b}"
  if es.any (·.2 matches .pos) ∨ n = 0 ∨ (r ≤ 2 ^ 64 ∧ r - 1 < 4 * n + 1024 ∧ r - 1 ≠ 2 ^ 64 - 1 ∧ n < 2 ^ 32)
    ∨ (List.range (n - 1)).all (fun i => lexLe ks i (i + 1)) then .ok ()
  else .error s!"seen: key range of {r} codes ({", ".intercalate cols}) over {n} rows out of order needs a hash, not built (PLAN D.12)"

/-- **The seen kernel** (PLAN D.12): over the `n` rows of the columns `es`, each a type and a `foR` read as `kasc` reads
it (`ascCol`), the number `k` of distinct keys, each row's group `g` (`n` words, groups numbered by first occurrence,
`Order.groupIn`) and each group's first row `first` (`k` words, ascending), both as `wordsFoR`. A key is a row's order
codes across `es`. The first column that does not read is the error, `ascCol`'s text after its place in `es`; then
rows no engine serves (`seenEngine`). -/
@[extern "qlean_k_seen"]
def kseen (n : USize) (es : @& List (QAtomicType × Enc)) : Except String (Nat × Enc × Enc) := do
  let ks ← es.zipIdx.mapM fun (c, i) => (·.2) <$> (ascCol n c).mapError (s!"seen: es[{i}]: " ++ ·)
  seenEngine n.toNat es ks
  let key := fun i => ks.map (·[i]?.getD 0)
  let fs := Order.firstsBy n.toNat key
  pure (fs.length, wordsFoR (Array.ofFn (n := n.toNat) fun i => (Order.groupIn fs key i.1).toUInt64),
    wordsFoR (fs.map Nat.toUInt64).toArray)

end Rel.Kernel
