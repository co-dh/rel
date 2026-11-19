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

/-- The rows of `x`, then those of `y`, as `n` rows: `Arr.concat` of each atom column (`off` as there). An `arr` side
concatenates its payloads (`catPlan`, the recursive call) and its `lo`, `hi` columns, each side's clamped into its own
payload (`Vals.row` reads a cell clamped) and the second's shifted past the first payload; a payload past `2^63` rows,
which an `Int64` bound cannot reach, is the error. -/
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
  | .sum _ _, _, _, _, _, _, _ => .error "concat: a sum side is not atom columns"

end Rel
