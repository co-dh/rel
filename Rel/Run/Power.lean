module

public import Rel.Run.List

-- exposed: every def body is a spec a downstream `rfl`/`decide`/`simp` may unfold (PLAN W.8)
@[expose] public section

/-! The power operators `est`, `front` of `Tm` (`Rel/Run/Lang/Tm.lean`) and the `prims` rows `τ`, `length`,
`setify`, `at` (`rowDens`) as operators on `Tab` over the five kernels (PLAN 6.14 W3, step T5), on the encoded columns as
they are, as `Rel/Run/Div.lean`. Each is run on the values in demand `X` its context gives, as the old `Gen.*` and
`RowCode.*` bodies read them, and its right-hand side is its denotation (`Rel/Lang/Den.lean`: `estDen`, `frontDen`,
`atOnDen`, `rowDens`). `est` and `front` read their order as a test `q` of pairs, run only on the pairs one array holds
(`Gen.est`, `Gen.front`); `τ` and `setify` are `Λ` of `𝟙` and of `∋`; `length` and `at` read the cell bounds. -/

namespace Rel
open Rel.Ext Rel.Kernel Rel.Verify

namespace Tab
variable {A B : Obj}

/-- **`τ` on `X`** (`rowDens`: `Y = [a]`): `Λ(𝟙)`, each value to the cell holding it alone (`lam` of `idU`). -/
def tau {n : USize} (X : Vals A n) : Except String (Tab A (.arr A)) := do lam X (← idU X)

/-- **`setify` on the arrays `X`** (`rowDens`: `Λ(∋)`): each array to the cell of its elements, ascending and each
once (`Λ` of `mem`, a `canon` answer: `lamOf`). -/
def setify {n : USize} (X : Vals (.arr B) n) : Except String (Tab (.arr B) (.arr B)) := do lamOf X (← mem X)

/-- **`length` on the arrays `X`** (`rowDens`: `w = xs.length`), the fused form of the fold: each cell to its width
`hi - lo` (a `colMap .sub`); then `canon`. A payload of `2^63` rows or more, whose width an `Int64` cannot hold, is
the error. -/
def length {n : USize} (X : Vals (.arr B) n) : Except String (Tab (.arr B) .long) :=
  match X with
  | ⟨m, lo, hi, f⟩ => do
    if 2 ^ 63 ≤ m.toNat then throw s!"length: a payload of {m} rows, past an Int64 count"
    Tab.canon ⟨n, ⟨m, lo, hi, f⟩, ← colArr .sub n hi.enc lo.enc⟩

/-- **`at` on the pairs `X = (xs, k)`** (`atOnDen`), positions from `0`: the rows whose
index is nonneg and below the cell's width (`colMap .and` of `k < hi - lo` and `0 ≤ k`, `whereCol`), each to the
payload at `lo + k` (`kgather` there); then `canon`. -/
def atIx {n : USize} (X : Vals (.prod (.arr B) .long) n) : Except String (Tab (.prod (.arr B) .long) B) :=
  match X with
  | (⟨m, lo, hi, f⟩, k) => do
    if 2 ^ 63 ≤ m.toNat then throw s!"at: a payload of {m} rows, past 2^63"
    let w ← colMap .sub n hi.enc lo.enc
    let c ← colMap .and n (← colMap .lt n k.enc w) (← colMap .first n k.enc k.enc .i64 .i64 [] [(.le, 0)])
    let (M, sel) ← whereCol n c
    let ix ← kgather M sel n (← colMap .add n lo.enc k.enc)
    Tab.canon ⟨M, ← ValsB.gather (A := .prod (.arr B) .long) M sel (⟨m, lo, hi, f⟩, k), ← ValsB.gather M ix f⟩

/-- **The row `at` on the pairs `X`** (`rowDens`: `atOn`): `atIx` where the index object is `i64`, no row elsewhere. -/
def atRow {N : Obj} {n : USize} (X : Vals (.prod (.arr B) N) n) : Except String (Tab (.prod (.arr B) N) B) :=
  match N, X with
  | .atom .i64, X => atIx X
  | _, _ => .error "at runs from an array and an i64 index"

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

/-- **`front(Q)` on the arrays `X`** (`frontDen`), `Q` the test `q` run on the pairs `D = ran ⟨G, G⟩` of elements of
one array (`G = ∋` on `X`), read on the diagonal: `Δ = diag q D` the pairs `p` with `q p p`; `S = dom (w ≫ Δ)`
the pairs whose swap is in `Δ` (`w = ⟨π₂, π₁⟩` on `D`; `D` holds every swap), `Y = Δ − S` the pairs `(b, c)` where
`b` beats `c` strictly; `(xs, c)` of `G` dropped where `⟨G, G⟩ ≫ π₂` on `Y` reaches it; then `Λ` on `X`. `q` runs
once, and only its diagonal is read, as `est` reads it. -/
def front {n : USize} (q : Tab (.prod B B) (.prod B B) → Except String (Tab (.prod B B) (.prod B B)))
    (X : Vals (.arr B) n) : Except String (Tab (.arr B) (.arr B)) := do
  let G ← mem X
  let P ← pair G G
  let D ← ran P
  let Δ ← diag q D
  let w ← pair (← outr D.key) (← outl D.key)
  let Y ← Δ.diff (← dom (← w.comp Δ))
  lam X (← G.diff (← P.comp (← outr Y.key)))

end Tab

end Rel
