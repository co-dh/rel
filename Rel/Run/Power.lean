import Rel.Run.List

/-! The power operators `est`, `thin`, `atPos` of `Tm` (`Rel/Run/Lang/Tm.lean`) and the `prims` rows `τ`, `length`,
`setify` (`rowDens`) as operators on `Tab` over the five kernels (PLAN 6.14 W3, step T5), on the encoded columns as they
are, as `Rel/Run/Div.lean`. Each is run on the values in demand `X` its context gives, as the old `Gen.*` and
`RowCode.*` bodies read them, and its right-hand side is its denotation (`Rel/Lang/Den.lean`: `estDen`, `thinDen`,
`atDen`, `rowDens`). `est` and `thin` read their order as a test `q` of pairs, run only on the pairs one array holds
(`Gen.est`, `Gen.thin`); `τ` and `setify` are `Λ` of `𝟙` and of `∋`; `length` and `atPos` read the cell bounds. -/

namespace Rel
open Rel.Ext Rel.Kernel Rel.Verify

namespace Tab
variable {A B : Obj}

/-- **`τ` on `X`** (`rowDens`: `Y = [a]`): `Λ(𝟙)`, each value to the cell holding it alone (`lam` of `idU`). -/
def tau {n : USize} (X : Vals A n) : Except String (Tab A (.arr A)) := do lam X (← idU X)

/-- **`setify` on the arrays `X`** (`rowDens`: `Λ(∋)`): each array to the cell of its elements, ascending and each
once (`lam` of `mem`). -/
def setify {n : USize} (X : Vals (.arr B) n) : Except String (Tab (.arr B) (.arr B)) := do lam X (← mem X)

/-- **`length` on the arrays `X`** (`rowDens`: `w = xs.length`), the fused form of the fold: each cell to its width
`e - s` (`cellSpan`, a `colMap .sub`); then `canon`. A payload of `2^63` rows or more, whose width an `Int64`
cannot hold, is the error. -/
def length {n : USize} (X : Vals (.arr B) n) : Except String (Tab (.arr B) .long) :=
  match X with
  | ⟨m, lo, hi, f⟩ => do
    if 2 ^ 63 ≤ m.toNat then throw s!"length: a payload of {m} rows, past an Int64 count"
    let (s, e) ← cellSpan m lo hi
    Tab.canon ⟨n, ⟨m, lo, hi, f⟩, ← colArr .sub n e.enc s.enc⟩

/-- **`at(k)` on the arrays `X`** (`atDen`), positions from `0`: the cells wider than `k` (`whereCol` of
`k < e - s`), each to the payload at `s + k` (`kgather` there); then `canon`. `s + k` and the widths are read signed,
so `m + k` stays below `2^63`. -/
def atPos {n : USize} (k : Nat) (X : Vals (.arr B) n) : Except String (Tab (.arr B) B) :=
  match X with
  | ⟨m, lo, hi, f⟩ => do
    if 2 ^ 63 ≤ m.toNat + k then throw s!"at: position {k} in a payload of {m} rows, past 2^63"
    let (s, e) ← cellSpan m lo hi
    let kc ← colConst n k.toUInt64
    let (M, sel) ← whereCol n (← colMap .lt n kc (← colMap .sub n e.enc s.enc))
    let ix ← kgather M sel n (← colMap .add n s.enc kc)
    Tab.canon ⟨M, ← Vals.gather (A := .arr B) M sel ⟨m, lo, hi, f⟩, ← Vals.gather M ix f⟩

/-- **`est(Q)` on the arrays `X`** (`estDen`), `Q` the test `q` run on the pairs `D = ran ⟨G, G⟩` of elements of one
array (`G = ∋` on `X`): `Y = D − q(D)` the failing pairs, less the diagonal `ran ⟨V, V⟩` of `V = ran G`; `(xs, b)` of
`G` dropped where `⟨G, G⟩ ≫ π₁` on `Y` reaches it. -/
def est {n : USize} (q : Tab (.prod B B) (.prod B B) → Except String (Tab (.prod B B) (.prod B B)))
    (X : Vals (.arr B) n) : Except String (Tab (.arr B) B) := do
  let G ← mem X
  let P ← pair G G
  let D ← ran P
  let V ← ran G
  let Y ← (← D.diff (← q D)).diff (← ran (← pair V V))
  G.diff (← P.comp (← outl Y.key))

/-- **`thin(Q)` on the arrays `X`** (`thinDen`), `Q` the test `q` run on the pairs `D = ran ⟨G, G⟩` of elements of
one array (`G = ∋` on `X`): `S` the pairs whose swap passes (`dom (w ≫ q (ran w))`, `w = ⟨π₂, π₁⟩` on `D`),
`Y = q(D) − S` the pairs `(b, c)` where `b` beats `c` strictly; `(xs, c)` of `G` dropped where `⟨G, G⟩ ≫ π₂` on `Y`
reaches it; then `Λ` on `X`. -/
def thin {n : USize} (q : Tab (.prod B B) (.prod B B) → Except String (Tab (.prod B B) (.prod B B)))
    (X : Vals (.arr B) n) : Except String (Tab (.arr B) (.arr B)) := do
  let G ← mem X
  let P ← pair G G
  let D ← ran P
  let w ← pair (← outr D.key) (← outl D.key)
  let S ← dom (← w.comp (← q (← ran w)))
  let Y ← (← q D).diff S
  lam X (← G.diff (← P.comp (← outr Y.key)))

end Tab

end Rel
