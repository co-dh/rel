import Rel.Programs.FrameJoin

/-! The dataframe library (plan M2) at the unbounded number object: positions and values in `obj N`, which declares
    no length, so no row below reads a bound the frame did not bring. The fixture and the hand-worked rows are those
    of `TestFrameCols`/`Pos`; the rows of `Pos`/`Group`/`Join` not here fail at `N` with "a leaf on demand ran with
    its domain unknown" (a generic constant whose body holds `length`, `sum` or `F`), and wait on that request. -/

namespace Rel.Lang.TestFrameUnbounded

open Rel.Programs.prelude Rel.Programs.frame in
rel_program frameUnboundedT where
    obj K = {A,B,C}
    obj N
    x : N ⟶ K×N ≜ {(0,(B,5)),(1,(A,3)),(2,(B,5)),(3,(C,1)),(4,(A,7)),(5,(C,2)),(6,(B,1)),(7,(A,3))}
    -- plan R1: `(+n)°` as `minus`, `Λ` with its domain written, `F(v) sum`; `v − 1` = 4 2 4 0 6 1 0 2
    check x π₂ ⟨𝟙, ⊤ {(∗,1)}⟩minus = {(0,4),(1,2),(2,4),(3,0),(4,6),(5,1),(6,0),(7,2)}
    check agg((x π₁)°, length) = {(A,3),(B,3),(C,2)}
    check summarize(F(x π₂) sum, x) = {(∗,27)}
    -- generic constants at `N`: row windows, first and last row
    check take({(∗,3)}, x) = {(0,(B,5)),(1,(A,3)),(2,(B,5))}
    check drop({(∗,3)}, x) = {(0,(C,1)),(1,(A,7)),(2,(C,2)),(3,(B,1)),(4,(A,3))}
    check range({(∗,2)}, {(∗,5)}, x) = {(0,(B,5)),(1,(C,1)),(2,(A,7))}
    check firstOrNothing(x π₂) [𝟙, {(∗,40)}] = {(∗,5)}
    check lastOrNothing(x π₂) [𝟙, {(∗,40)}] = {(∗,3)}
    check firstOrNothing(take({(∗,0)}, x π₂)) [𝟙, {(∗,40)}] = {(∗,40)}

#guard frameUnboundedT.ok

end Rel.Lang.TestFrameUnbounded
