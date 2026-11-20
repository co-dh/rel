import Rel.Run.SetOps
import Rel.Run.Comp

/-! The structural operators of the core term `Tm` (`Rel/Run/Lang/Tm.lean`) on `Tab`, as compositions of the five
kernels (PLAN 6.14 W3), in the style of `Rel/Run/Comp.lean`: `zero`, `id` (on the values `X` its context gives),
`top`, `outl`, `outr`, `pair`, `prod`, `inl`, `inr`, their converses `inlConv`, `inrConv` (on the sum values in
demand, which `[R,S] = inl° ≫ R ∪ inr° ≫ S` runs on), and `flat` from `outl`, `outr` and an equality test. Each law (`Rel/RepStruct.lean`) has the
constructor's denotation `Tm.den` (`Rel/Lang/Den.lean`) as its right-hand side. `Tm.join` is `Tab.union`
(`Rel/Run/SetOps.lean`). No column is decoded or re-encoded between the calls.

CROSS (`doc/rel-kernels.md`): `n · m` rows, row `t` pairing row `t / m` of one side with row `t % m` of the other,
both index columns one `kscan` map (`colMap .div`, `.mod`) of the positions by the constant `m`. -/

namespace Rel
open Rel.Ext Rel.Kernel Rel.Verify

/-- `n` zero words at the atom type `t`: `colArr .add` of two `colConst n 0`, written at `t`. -/
def Arr.zeros (t : QAtomicType) (n : USize) : Except String (Arr t n) := do
  let z ← colConst n 0
  colArr .add n z z t

/-- No row of `A`: `Arr.zeros _ 0` per atom column; an `arr` side of no cells over no payload, a `sum` side over two
summands of no rows. -/
def Vals.none : (A : Obj) → Except String (Vals A 0)
  | .atom t => Arr.zeros t 0
  | .prod a b => do pure (← Vals.none a, ← Vals.none b)
  | .arr b => do pure ⟨0, ← Arr.zeros .i64 0, ← Arr.zeros .i64 0, ← Vals.none b⟩
  | .sum a b => do pure ⟨0, 0, ← Arr.zeros .u1 0, ← Arr.zeros .i64 0, ← Vals.none a, ← Vals.none b⟩

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

/-- The tag and position columns of a sum side whose `n` rows are all in one summand: every tag `s` (`colConst`,
written at `u1` by `colMap .add` of `0`), row `k` at position `k` (`colMap .add` of the positions and `0`). A summand
past `2^63` rows, which an `Int64` position cannot reach, is the error. -/
def injCols (n : USize) (s : Bool) : Except String (Arr .u1 n × Arr .i64 n) := do
  if 2 ^ 63 < n.toNat then throw s!"inj: {n} rows, past an Int64 position"
  let z ← colConst n 0
  pure (← colArr .add n z (← colConst n (if s then 1 else 0)) .u1, ← colArr .add n .pos z .i64)

namespace Tab
variable {A B C D I : Obj}

/-- **`𝟘`**: no row. -/
def zero : Except String (Tab A B) := do pure ⟨0, ← Vals.none A, ← Vals.none B⟩

/-- **`𝟙` on the values `X`**, `idU X`: the domain of `⟨n, X, X⟩` (`Tab.dom`), each value once, paired with itself. -/
def idU {n : USize} (X : Vals A n) : Except String (Tab A A) := Tab.dom ⟨n, X, X⟩

/-- **`X × Y`**, every pair `(X[i], Y[j])`: `Vals.cross`, canonical. -/
def cross {n m : USize} (X : Vals A n) (Y : Vals B m) : Except String (Tab A B) := do
  let ⟨T, x, y⟩ ← Vals.cross X Y
  canon ⟨T, x, y⟩

/-- **`⊤` between the known sides `K` and `L`**, `K ≫ ⊤ ≫ L = K × L`: every value of `K` beside every value of `L`
(`idU X ≫ ⊤ ≫ V` is `top X V.val`). -/
def top {n m : USize} (K : Vals A n) (L : Vals B m) : Except String (Tab A B) := cross K L

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

/-- **`inl` on the values `X`**, `idU X ≫ inl`: row `k` is `X`'s row `k` beside the left summand's row `k`, the sum
side over `X` itself and no right row (`injCols` with tag `0`), canonical. -/
def inl {n : USize} (X : Vals A n) : Except String (Tab A (.sum A B)) := do
  let (tag, idx) ← injCols n false
  canon ⟨n, X, ⟨n, 0, tag, idx, X, ← Vals.none B⟩⟩

/-- **`inr` on the values `Y`**, `idU Y ≫ inr`: the mirror of `inl`, tag `1`. -/
def inr {n : USize} (Y : Vals B n) : Except String (Tab B (.sum A B)) := do
  let (tag, idx) ← injCols n true
  canon ⟨n, Y, ⟨0, n, tag, idx, ← Vals.none A, Y⟩⟩

/-- **`inl°` on the sum values `X`**, `idU X ≫ inl°`: `X` beside `(inl x)°`, `x` its left payload, which every
left row reads. A left payload of no value reads `A.dflt` at a left row (`Vals.row`), which `x` cannot give: there
the answer is none where `X` has only right rows (`idU X − dom(idU X ≫ (inr y)°)` empty), else the error. -/
def inlConv {n : USize} (X : Vals (.sum A B) n) : Except String (Tab (.sum A B) A) := do
  let D ← idU X
  if X.1.toNat = 0 then
    if (← D.diff (← (← D.comp (← (← inr (A := A) X.2.2.2.2.2).conv)).dom)).n = 0 then zero
    else throw "inl°: a left row over a left payload of no value"
  else D.comp (← (← inl (B := B) X.2.2.2.2.1).conv)

/-- **`inr°` on the sum values `X`**, `idU X ≫ inr°`: the mirror of `inlConv`. -/
def inrConv {n : USize} (X : Vals (.sum A B) n) : Except String (Tab (.sum A B) B) := do
  let D ← idU X
  if X.2.1.toNat = 0 then
    if (← D.diff (← (← D.comp (← (← inl (B := B) X.2.2.2.2.1).conv)).dom)).n = 0 then zero
    else throw "inr°: a right row over a right payload of no value"
  else D.comp (← (← inr (A := A) X.2.2.2.2.2).conv)

/-- **`Rᴵ` on the pairs `X`**, `idU X ≫ Rᴵ` = `((π₁ ≫ R) ∩ (π₂ ≫ π₁°)) ≫ π₂` (`flatDen_eq`): the rows `(i, a)` of `X`
beside `R`'s `(a', b)` at `i`, kept where the equality test `a = a'` holds (`∩` with `π₂ ≫ π₁°` on `R`'s values), then
`b`. -/
def flat {n : USize} (X : Vals (.prod I A) n) (R : Tab I (.prod A B)) : Except String (Tab (.prod I A) B) := do
  let L ← comp (← outl X) R
  let M ← comp (← outr X) (← conv (← outl R.val))
  comp (← inter L M) (← outr R.val)


end Tab

end Rel
