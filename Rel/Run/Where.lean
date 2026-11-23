module

public import Rel.Run.List
public import Rel.Run.Bits

-- exposed: every def body is a spec a downstream `rfl`/`decide`/`simp` may unfold (PLAN W.8)
@[expose] public section

/-! The row `positions(p)` of `prims` on `Tab`: architecture §4's where(`b`) (`whereCol`, `scan → scatter`, no sort)
run on each array's elements, `b` the test `p`. -/

namespace Rel
open Rel.Ext Rel.Kernel Rel.Verify

/-- The positions `t` of `xs`, ascending, whose element passes `p`: dataframe §3.1's `where(dom(xs ≫ p))`, q's
`where` of the mask `p` over `xs`. -/
def positionsL {α : Type} (p : α → Bool) (xs : List α) : List Int64 :=
  ((List.range xs.length).filter fun t => xs[t]?.any p).map Int64.ofNat

namespace Tab
variable {B : Obj}

/-- **`positions(p)` on the cells `X`** (`positionsL`): the elements EXPANDed into `(G, u)` (as `map`), each tested
against `dom P` (`index`, a `0`/`1` word), `whereCol` of the tests listing the kept element rows ascending, whose
offsets `u` are the new payload, laid out by each cell's count of kept rows (`kscatter .add` at `G`, `Vals.cells`);
then `canon`. The positions, widths and prefix sums are read signed, so `n · m + n + m` stays below `2^63`. -/
def positions {n : USize} (P : Tab B B) (X : Vals (.arr B) n) : Except String (Tab (.arr B) (.arr .long)) :=
  match X with
  | ⟨m, lo, hi, f⟩ => do
    if 2 ^ 63 ≤ n.toNat * m.toNat + n.toNat + m.toNat then throw s!"positions: {n} cells over {m} elements past 2^63"
    let w ← colMap .sub n hi.enc lo.enc
    let (T, G, u) ← expand n w
    let v ← Vals.gather T (← colMap .add T (← kgather T G n lo.enc) u) f
    let D ← P.dom
    -- `index` answers `D.n` exactly where the element is no key of `D`: tested by `≠`, no signed compare
    let ix ← index D.key v
    let b ← colMap .first T ix ix .i64 .i64 [] [(.ne, D.n.toUInt64)]
    let (K, sel) ← whereCol T b
    let uK ← kgather K sel T u
    let pay ← colArr .first K uK uK
    canon ⟨n, ⟨m, lo, hi, f⟩, ← Vals.cells n (← kscatter .add T G b n 0) (pay : Vals .long K)⟩

end Tab

end Rel
