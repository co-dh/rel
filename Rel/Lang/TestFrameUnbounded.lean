import Rel.Programs.FrameJoin

/-! The dataframe library (plan M2) at the unbounded number object: positions and values in `obj N`, which declares
    no length, so no row below reads a bound the frame did not bring. The fixture and the hand-worked rows are those
    of `TestFrameCols`/`Pos`/`Group`/`Join`. A closed `asc(P)` needs no keys (`Prim.whole`), so a join, whose
    `asc(ran⟨𝟙,K⟩)` has no demand, runs whole at `N`; generic constants holding `length`, `sum` are `TestGenericN`. -/

namespace Rel.Lang.TestFrameUnbounded

open Rel.Programs.prelude Rel.Programs.frame Rel.Programs.frameGroup Rel.Programs.frameJoin in
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
    check filterBy(dom(π₂ {(3,3),(5,5),(7,7)}), x) = {(0,(B,5)),(1,(A,3)),(2,(B,5)),(3,(A,7)),(4,(A,3))}
    check dom(x) iasc(x π₁) = {(0,1),(1,4),(2,7),(3,0),(4,2),(5,6),(6,3),(7,5)}
    check sortBy(π₁, x) = {(0,(A,3)),(1,(A,7)),(2,(A,3)),(3,(B,5)),(4,(B,5)),(5,(B,1)),(6,(C,1)),(7,(C,2))}
    check firstOcc(x π₁) = {(0,0),(1,1),(2,3)}
    check group(x π₁)° = {(0,0),(1,1),(2,0),(3,2),(4,1),(5,2),(6,0),(7,1)}
    check lastOcc(x π₁) = {(0,6),(1,7),(2,5)}
    check distinct(x) = {(0,(B,5)),(1,(A,3)),(2,(C,1)),(3,(A,7)),(4,(C,2)),(5,(B,1))}
    y : N ⟶ K×N ≜ {(0,(A,9)),(1,(C,8)),(2,(A,6))}
    check J(π₁, π₁, x, y) = {(1,0),(1,2),(3,1),(4,0),(4,2),(5,1),(7,0),(7,2)}
    check semiJoin(π₁, π₁, x, y) = {(0,(A,3)),(1,(C,1)),(2,(A,7)),(3,(C,2)),(4,(A,3))}
    check antiJoin(π₁, π₁, x, y) = {(0,(B,5)),(1,(B,5)),(2,(B,1))}
    -- `J`'s 8 pairs numbered in `(i, j)` order, each read in `x` and `y`: `joinOn`'s `asc(ran⟨𝟙, K⟩)` with `⟨𝟙, K⟩`
    -- cut to `dom(K)`, which bounds the `𝟙` that `N` does not
    check asc(ran(dom(J(π₁, π₁, x, y)) ⟨𝟙, J(π₁, π₁, x, y)⟩)) (x × y) ={(0,((A,3),(A,9))),(1,((A,3),(A,6))),(2,((C,1),(C,8))),(3,((A,7),(A,9))),(4,((A,7),(A,6))),(5,((C,2),(C,8))),(6,((A,3),(A,9))),(7,((A,3),(A,6)))}
    -- the same rows by `innerJoin` itself: `⟨𝟙, K⟩` runs the table `K` first, whose domain bounds `𝟙` (`GenK.pairK`)
    check innerJoin(π₁, π₁, x, y) ={(0,((A,3),(A,9))),(1,((A,3),(A,6))),(2,((C,1),(C,8))),(3,((A,7),(A,9))),(4,((A,7),(A,6))),(5,((C,2),(C,8))),(6,((A,3),(A,9))),(7,((A,3),(A,6)))}
    -- a top-level `asc` of a closed set: `j ↦` its `j`-th smallest element
    s : N ⟶ N ≜ {(9,9),(2,2),(5,5)}
    sa : N ⟶ N ≜ asc(s)
    check sa = {(0,2),(1,5),(2,9)}

#guard frameUnboundedT.ok

end Rel.Lang.TestFrameUnbounded
