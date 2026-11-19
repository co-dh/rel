import Rel.Run.Canon

/-! Column helpers shared by the set operators (`Rel/Run/SetOps.lean`) and composition (`Rel/Run/Comp.lean`), each a
composition of the five kernels on encoded columns: a constant column, a pointwise map, a running fold, and CONCAT
(`doc/rel-kernels.md`) of two tables' columns. Their laws are in `Rel/RepCols.lean`. -/

namespace Rel
open Rel.Ext Rel.Kernel Rel.Verify

/-- `n` cells holding the word `w`: `kscatter` of no rows. -/
def colConst (n : USize) (w : UInt64) : Except String Enc := kscatter .last 0 .pos .pos n w

/-- `op` row by row over the `n` words of `a` and `b`, `out[i] = op(a[i], b[i])` written at `t`: `kscan` with every row
starting a segment (`colConst n 1`). -/
def colMap (op : Op) (n : USize) (a b : Enc) (t : QAtomicType := .i64) : Except String Enc := do
  kscan op false .i64 t n (← colConst n 1) [a, b]

/-- `colMap`'s answer is a column every kernel reads, `Enc.WF` at `t` (`kscan_closed`). -/
theorem colMap_closed {op : Op} {n : USize} {a b o : Enc} {t : QAtomicType} (h : colMap op n a b t = .ok o) :
    Kernel.Enc.Valid n o ∧ Enc.WF t n o := by
  unfold colMap at h; simp only [bind, Except.bind] at h; split at h; · cases h
  exact kscan_closed h

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

/-- The rows of `x`, then those of `y`, as `n` rows: `Arr.concat` of each atom column (`off` as there). -/
def Vals.concat (n : USize) (off : Enc) : {A : Obj} → {n₁ n₂ : USize} → Vals A n₁ → Vals A n₂ →
    Except String (Vals A n)
  | .atom _, _, _, x, y => Arr.concat n off x y
  | .prod _ _, _, _, x, y => do pure (← Vals.concat n off x.1 y.1, ← Vals.concat n off x.2 y.2)
  | .arr _, _, _, _, _ => .error "concat: an arr side is not atom columns"
  | .sum _ _, _, _, _, _ => .error "concat: a sum side is not atom columns"

/-- The layout of `n₁` rows followed by `n₂`: the summed count `n` and the destinations `off` of the second part
(`shiftCol n₂ n₁`); the error where `n` does not fit a `USize`. -/
def catPlan (n₁ n₂ : USize) : Except String (USize × Enc) :=
  if n₁.toNat + n₂.toNat < USize.size then do
    pure ((n₁.toNat + n₂.toNat).toUSize, ← shiftCol n₂ n₁.toUInt64)
  else .error s!"concat: {n₁} + {n₂} rows do not fit a USize"

end Rel
