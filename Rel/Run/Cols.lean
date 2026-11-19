import Rel.Run.Canon

/-! Column helpers shared by the set operators (`Rel/Run/SetOps.lean`) and composition (`Rel/Run/Comp.lean`), each a
composition of the five kernels on encoded columns: a constant column, a pointwise map, a running fold, and CONCAT
(`doc/rel-kernels.md`) of two tables' columns. Their laws are in `Rel/RepCols.lean`. -/

namespace Rel
open Rel.Ext Rel.Kernel Rel.Verify

/-- The running fold of `op` over the `n` words of `a` from the word `0`: `kscan` with one segment. -/
def colPrefix (op : Op) (n : USize) (a : Enc) : Except String Enc := do
  let z ← colConst n 0
  kscan op false .i64 .i64 n z [z, a]

/-- The `n` words `i + s`: `colMap .add` of the positions and `colConst n s`. -/
def shiftCol (n : USize) (s : UInt64) : Except String Enc := do colMap .add n .pos (← colConst n s)

/-- **CONCAT of two columns of one type**: `x` `kscatter`ed to the cells `0 … n₁-1` of `n`, `y` to `off` (`n₁ + k`),
the rest `0`, and the two added by `colMap .add` at `t` (each cell is `0` in one of the two). `.add` is the wrapping
add of raw words at every type (`Op.eval`), so `x + 0` is `x`'s stored word, a float's sign and NaN payload included;
the answer is `Enc.WF` at `t` by `kscan_closed`. -/
def Arr.concat {t : QAtomicType} {n₁ n₂ : USize} (n : USize) (off : Enc) (x : Arr t n₁) (y : Arr t n₂) :
    Except String (Arr t n) := do
  let a ← kscatter .last n₁ .pos x.enc n 0
  let b ← kscatter .last n₂ off y.enc n 0
  match h : colMap .add n a b t with
  | .ok o => .ok (Arr.mk o (colMap_closed h).2)
  | .error s => .error s

/-- The layout of `n₁` rows followed by `n₂`: the summed count `n` and the destinations `off` of the second part
(`shiftCol n₂ n₁`); the error where `n` does not fit a `USize`. -/
def catPlan (n₁ n₂ : USize) : Except String (USize × Enc) :=
  if n₁.toNat + n₂.toNat < USize.size then do
    pure ((n₁.toNat + n₂.toNat).toUSize, ← shiftCol n₂ n₁.toUInt64)
  else .error s!"concat: {n₁} + {n₂} rows do not fit a USize"

/-- The words of `x` clamped into `[0, c]` (`colMap .max` with `0`, then `.min` with `c`), then `s` added. -/
def Arr.clampShift {n : USize} (c s : UInt64) (x : Arr .i64 n) : Except String (Arr .i64 n) := do
  let a ← colMap .max n x.enc (← colConst n 0)
  let b ← colMap .min n a (← colConst n c)
  let k ← colConst n s
  match h : colMap .add n b k with
  | .ok o => .ok (Arr.mk o (colMap_closed h).2)
  | .error e => .error e

/-- The positions of a sum side's summand `s` (`false` left, `true` right): `idx` on the rows `tag` gives to it, `0` on
the others (`colMap .mul` by `tag` or by its `.not`), as `Vals.cols` gathers a summand. -/
def summandPos (n : USize) (s : Bool) (tag : Arr .u1 n) (idx : Arr .i64 n) : Except String Enc :=
  if s then colMap .mul n idx.enc tag.enc else do colMap .mul n idx.enc (← colMap .not n tag.enc tag.enc)

/-- The positions `0 … n-1`, a `foR` column (`shiftCol n 0`). -/
def Arr.pos (n : USize) : Except String (Arr .i64 n) :=
  match h : shiftCol n 0 with
  | .ok o => .ok (Arr.mk o (by
      unfold shiftCol at h; simp only [bind, Except.bind] at h
      split at h <;> first | cases h | exact (colMap_closed h).2))
  | .error e => .error e

/-- Summand `s` of the concat of two sum sides of `n₁` and `n₂` rows, its rows `x₁` and `x₂` on each: their concat
`cat` where both are empty (every row of the summand reads `Obj.dflt`), else each gathered at its side's
`summandPos` of its positions clamped into the summand, as `Vals.row` reads them (row `i` its own row `i`'s value) and the two concatenated, `n` rows read at the positions `Arr.pos`.
A summand empty on one side only is the error: its rows read `Obj.dflt`, which no payload row holds. -/
def Vals.catSummand {B : Obj} {n₁ n₂ l₁ l₂ : USize} (n : USize) (off : Enc) (s : Bool) (tag₁ : Arr .u1 n₁)
    (idx₁ : Arr .i64 n₁) (x₁ : Vals B l₁) (tag₂ : Arr .u1 n₂) (idx₂ : Arr .i64 n₂) (x₂ : Vals B l₂)
    (cat : {m₁ m₂ : USize} → (m : USize) → Enc → Vals B m₁ → Vals B m₂ → Except String (Vals B m)) :
    Except String ((m : USize) × Vals B m) :=
  if l₁.toNat = 0 ∧ l₂.toNat = 0 then do let p ← catPlan l₁ l₂; pure ⟨p.1, ← cat p.1 p.2 x₁ x₂⟩
  else if l₁.toNat = 0 ∨ l₂.toNat = 0 then
    .error s!"concat: a sum summand of {l₁} rows on one side and {l₂} on the other: a side of none reads Obj.dflt"
  else if 2 ^ 63 < l₁.toNat ∨ 2 ^ 63 < l₂.toNat then .error s!"concat: a sum summand of {l₁} or {l₂} rows, past 2^63"
  else do
    let g₁ ← Vals.gather n₁ (← summandPos n₁ s tag₁ (← idx₁.clampShift (l₁.toUInt64 - 1) 0)) x₁
    let g₂ ← Vals.gather n₂ (← summandPos n₂ s tag₂ (← idx₂.clampShift (l₂.toUInt64 - 1) 0)) x₂
    pure ⟨n, ← cat n off g₁ g₂⟩

/-- The rows of `x`, then those of `y`, as `n` rows: `Arr.concat` of each atom column (`off` as there). An `arr` side
concatenates its payloads (`catPlan`, the recursive call) and its `lo`, `hi` columns, each side's clamped into its own
payload (`Vals.row` reads a cell clamped) and the second's shifted past the first payload; a payload past `2^63` rows,
which an `Int64` bound cannot reach, is the error. A `sum` side concatenates its tags and each summand
(`Vals.catSummand`), its positions `Arr.pos`; past `2^63` rows, which an `Int64` position cannot reach, the error. -/
def Vals.concat : {A : Obj} → {n₁ n₂ : USize} → (n : USize) → Enc → Vals A n₁ → Vals A n₂ → Except String (Vals A n)
  | .atom _, _, _, n, off, x, y => Arr.concat n off x y
  | .prod _ _, _, _, n, off, x, y => do pure (← Vals.concat n off x.1 y.1, ← Vals.concat n off x.2 y.2)
  | .arr _, _, _, n, off, ⟨m₁, lo₁, hi₁, f₁⟩, ⟨m₂, lo₂, hi₂, f₂⟩ =>
    if m₁.toNat + m₂.toNat < 2 ^ 63 then do
      let p ← catPlan m₁ m₂
      let lo ← Arr.concat n off (← lo₁.clampShift m₁.toUInt64 0) (← lo₂.clampShift m₂.toUInt64 m₁.toUInt64)
      let hi ← Arr.concat n off (← hi₁.clampShift m₁.toUInt64 0) (← hi₂.clampShift m₂.toUInt64 m₁.toUInt64)
      pure ⟨p.1, lo, hi, ← Vals.concat p.1 p.2 f₁ f₂⟩
    else .error s!"concat: {m₁} + {m₂} payload rows, past an Int64 bound"
  | .sum _ _, _, _, n, off, ⟨_, _, tag₁, idx₁, x₁, y₁⟩, ⟨_, _, tag₂, idx₂, x₂, y₂⟩ =>
    if n.toNat ≤ 2 ^ 63 then do
      let L ← Vals.catSummand n off false tag₁ idx₁ x₁ tag₂ idx₂ x₂ fun m o x y => Vals.concat m o x y
      let R ← Vals.catSummand n off true tag₁ idx₁ y₁ tag₂ idx₂ y₂ fun m o x y => Vals.concat m o x y
      pure ⟨L.1, R.1, ← Arr.concat n off tag₁ tag₂, ← Arr.pos n, L.2, R.2⟩
    else .error s!"concat: a sum side of {n} rows, past an Int64 position"

end Rel
