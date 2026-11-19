import Rel.Run.Comp

/-! The structural operators of the core term `Tm` (`Rel/Run/Lang/Tm.lean`) on `Tab`, as compositions of the five
kernels (PLAN 6.14 W3), in the style of `Rel/Run/Comp.lean`: `zero`, `id` (on the values `X` its context gives),
`top`, `outl`, `outr`, `pair`, `prod`, `junc`, `juncD`, `flat`. Each one's law (`Rel/RepStruct.lean`) has the
constructor's denotation `Tm.den` (`Rel/Lang/Den.lean`) as its right-hand side. `Tm.join` is `Tab.union`
(`Rel/Run/SetOps.lean`). No column is decoded or re-encoded between the calls.

CROSS (`doc/rel-kernels.md`): `n · m` rows, row `t` pairing row `t / m` of one side with row `t % m` of the other,
both index columns one `kscan` map (`colMap .div`, `.mod`) of the positions by the constant `m`. -/

namespace Rel
open Rel.Ext Rel.Kernel Rel.Verify

/-- No row at the atom type `t`: `colMap` of no rows, written at `t` (`colMap_closed`). -/
def Arr.none (t : QAtomicType) : Except String (Arr t 0) := do
  let z ← colConst 0 0
  match h : colMap .add 0 z z t with
  | .ok o => .ok (Arr.mk o (colMap_closed h).2)
  | .error s => .error s

/-- No row of `A`: `Arr.none` per atom column; an `arr` side of no cells over no payload, a `sum` side over two
summands of no rows. -/
def Vals.none : (A : Obj) → Except String (Vals A 0)
  | .atom t => Arr.none t
  | .prod a b => do pure (← Vals.none a, ← Vals.none b)
  | .arr b => do pure ⟨0, ← Arr.none .i64, ← Arr.none .i64, ← Vals.none b⟩
  | .sum a b => do pure ⟨0, 0, ← Arr.none .u1, ← Arr.none .i64, ← Vals.none a, ← Vals.none b⟩

/-- The index columns of CROSS: `T = n · m` rows, `iR = pos / m`, `iS = pos % m` (`colMap` of the positions and
`colConst T m`). `.div`, `.mod` read their words signed, so `n · m + m` stays below `2^63`, and `T` fits a `USize`. -/
def crossIx (n m : USize) : Except String (USize × Enc × Enc) := do
  if 2 ^ 63 ≤ n.toNat * m.toNat + m.toNat ∨ USize.size ≤ n.toNat * m.toNat then
    throw s!"cross: {n} × {m} rows past 2^63 or USize"
  let T := (n.toNat * m.toNat).toUSize
  let c ← colConst T m.toUInt64
  pure (T, ← colMap .div T .pos c, ← colMap .mod T .pos c)

/-- **CROSS of two sides**, `x` and `y` side by side at every pair of their rows: `x` gathered at `iR`, `y` at `iS`
(`crossIx`). -/
def Vals.cross {A B : Obj} {n m : USize} (x : Vals A n) (y : Vals B m) :
    Except String ((T : USize) × Vals A T × Vals B T) := do
  let (T, iR, iS) ← crossIx n m
  pure ⟨T, ← Vals.gather T iR x, ← Vals.gather T iS y⟩

namespace Tab
variable {A B C D I : Obj}

/-- **`𝟘`**: no row. -/
def zero : Except String (Tab A B) := do pure ⟨0, ← Vals.none A, ← Vals.none B⟩

/-- **`𝟙` on the values `X`**, `idU X`: the domain of `⟨n, X, X⟩` (`Tab.dom`), each value once, paired with itself. -/
def idU {n : USize} (X : Vals A n) : Except String (Tab A A) := Tab.dom ⟨n, X, X⟩

/-- **`⊤ ≫ V` on the values `X`**, `idU X ≫ ⊤ ≫ V`: every value of `X` beside every value of `V` (CROSS of `X` and
`V.val`), canonical. -/
def top {n : USize} (X : Vals A n) (V : Tab B B) : Except String (Tab A B) := do
  let ⟨T, x, y⟩ ← Vals.cross X V.val
  canon ⟨T, x, y⟩

/-- **`π₁` on the pairs `X`**, `idU X ≫ π₁`: each pair beside its first component, canonical. -/
def outl {n : USize} (X : Vals (.prod A B) n) : Except String (Tab (.prod A B) A) := canon ⟨n, X, X.1⟩

/-- **`π₂` on the pairs `X`**, `idU X ≫ π₂`. -/
def outr {n : USize} (X : Vals (.prod A B) n) : Except String (Tab (.prod A B) B) := canon ⟨n, X, X.2⟩

/-- **`⟨R, S⟩`**: `L ≫ S` with `L = ⟨𝟙, R⟩°` on `R`'s rows (`((a, b), a)`), its rows `((a, b), c)` rebracketed as
`(a, (b, c))` — the join of `R` and `S` on equal keys that `Tab.comp` runs, `R.val` carried in the key. The
rebracketing keeps the column order, so the answer is `comp`'s canonical table. -/
def pair (R : Tab A B) (S : Tab A C) : Except String (Tab A (.prod B C)) :=
  (fun (T : Tab (.prod A B) C) => ⟨T.n, T.key.1, (T.key.2, T.val)⟩) <$>
    comp (⟨R.n, (R.key, R.val), R.key⟩ : Tab (.prod A B) A) S

/-- **`R × S`**: CROSS of `R`'s rows and `S`'s, each output row `((a, c), (b, d))`, canonical. -/
def prod (R : Tab A B) (S : Tab C D) : Except String (Tab (.prod A C) (.prod B D)) := do
  let ⟨T, x, y⟩ ← Vals.cross (A := .prod A B) (B := .prod C D) (R.key, R.val) (S.key, S.val)
  canon ⟨T, (x.1, y.1), (x.2, y.2)⟩

/-- **`Rᴵ` on the pairs `X`**, `idU X ≫ Rᴵ`: `R`'s rows `(i, (a, b))` re-keyed as `((i, a), b)` (column plumbing),
composed after `idU X`. -/
def flat {n : USize} (X : Vals (.prod I A) n) (R : Tab I (.prod A B)) : Except String (Tab (.prod I A) B) := do
  comp (← idU X) ⟨R.n, (R.key, R.val.1), R.val.2⟩

end Tab

end Rel
