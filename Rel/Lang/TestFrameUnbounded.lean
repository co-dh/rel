import Rel.Programs.FrameJoin

/-! The dataframe library (plan M2) at the unbounded number object: positions and values in `obj N`, which declares
    no length, so no row below reads a bound the frame did not bring. The fixture and the hand-worked rows are those
    of `TestFrameCols`/`Pos`/`Group`/`Join`; `v > 2` is `π₂ > {(2,∗)}`, as a closed `big` has nothing bounding it. -/

namespace Rel.Lang.TestFrameUnbounded

open Rel.Programs.prelude Rel.Programs.frame Rel.Programs.frameGroup Rel.Programs.frameJoin in
rel_program frameUnboundedT where
    obj K = {A,B,C}
    obj S = {a,b}
    obj N
    x : N ⟶ K×N ≜ {(0,(B,5)),(1,(A,3)),(2,(B,5)),(3,(C,1)),(4,(A,7)),(5,(C,2)),(6,(B,1)),(7,(A,3))}
    y : N ⟶ K×N ≜ {(0,(A,9)),(1,(C,8)),(2,(A,6))}
    y2 : N ⟶ K×N ≜ {(0,(A,3)),(1,(C,2)),(2,(B,4))}
    w : N ⟶ N×N ≜ {(0,(1,2)),(1,(3,4)),(2,(5,6))}
    t : N ⟶ K×(N×N) ≜ {(0,(A,(1,2))),(1,(B,(3,4))),(2,(C,(5,6)))}
    -- the four rows of plan R1: `(+n)°` as `minus`, `Λ` with its domain written, `F(v) sum`, `count`
    check x π₂ ⟨𝟙, ⊤ {(∗,1)}⟩minus = {(0,4),(1,2),(2,4),(3,0),(4,6),(5,1),(6,0),(7,2)}
    check agg((x π₁)°, length) = {(A,3),(B,3),(C,2)}
    check summarize(F(x π₂) sum, x) = {(∗,27)}
    check count(x) = {(∗,8)}
    check over(π₁, F(x π₂) sum, x) = {(0,((B,5),11)),(1,((A,3),13)),(2,((B,5),11)),(3,((C,1),3)),(4,((A,7),13)),
      (5,((C,2),3)),(6,((B,1),11)),(7,((A,3),13))}
    -- positions (TestFramePos)
    check take({(∗,3)}, x) = {(0,(B,5)),(1,(A,3)),(2,(B,5))}
    check drop({(∗,3)}, x) = {(0,(C,1)),(1,(A,7)),(2,(C,2)),(3,(B,1)),(4,(A,3))}
    check range({(∗,2)}, {(∗,5)}, x) = {(0,(B,5)),(1,(C,1)),(2,(A,7))}
    pz : N ⟶ N ≜ nth(>, dom(x π₂ > {(2,∗)}))
    check pz = {(0,0),(1,1),(2,2),(3,4),(4,7)}
    check filterBy(dom(π₂ > {(2,∗)}), x) = {(0,(B,5)),(1,(A,3)),(2,(B,5)),(3,(A,7)),(4,(A,3))}
    rk : N ⟶ N ≜ dom(x) rank((x π₁ (x π₁)°) ∩ >)
    check rk = {(0,0),(1,0),(2,1),(3,0),(4,1),(5,1),(6,2),(7,2)}
    check takeLast({(∗,3)}, x) = {(0,(C,2)),(1,(B,1)),(2,(A,3))}
    check takeLast({(∗,10)}, x) = x
    check dropLast({(∗,3)}, x) = {(0,(B,5)),(1,(A,3)),(2,(B,5)),(3,(C,1)),(4,(A,7))}
    check dropLast({(∗,10)}, x) = 𝟘
    check rolling({(∗,3)}, F(x π₂) sum, x) = {(0,5),(1,8),(2,13),(3,9),(4,13),(5,10),(6,10),(7,6)}
    check firstOrNothing(x π₂) [𝟙, {(∗,40)}] = {(∗,5)}
    check lastOrNothing(x π₂) [𝟙, {(∗,40)}] = {(∗,3)}
    check firstOrNothing(take({(∗,0)}, x π₂)) [𝟙, {(∗,40)}] = {(∗,40)}
    -- sort and group (TestFrameGroup)
    check iasc(π₁, x) = {(0,1),(1,4),(2,7),(3,0),(4,2),(5,6),(6,3),(7,5)}
    check idesc(π₁, x) = {(0,3),(1,5),(2,0),(3,2),(4,6),(5,1),(6,4),(7,7)}
    check sortBy(π₁, x) = {(0,(A,3)),(1,(A,7)),(2,(A,3)),(3,(B,5)),(4,(B,5)),(5,(B,1)),(6,(C,1)),(7,(C,2))}
    check topBy({(∗,2)}, π₁, x) = {(0,(A,3)),(1,(A,7))}
    check firstOcc(π₁, x) = {(0,0),(1,1),(2,3)}
    check g(π₁, x) = {(0,0),(1,1),(2,0),(3,2),(4,1),(5,2),(6,0),(7,1)}
    check lastOcc(π₁, x) = {(0,6),(1,7),(2,5)}
    check firstOcc(𝟙, x) = {(0,0),(1,1),(2,3),(3,4),(4,5),(5,6)}
    check distinct(x) = {(0,(B,5)),(1,(A,3)),(2,(C,1)),(3,(A,7)),(4,(C,2)),(5,(B,1))}
    check aggregate(π₁, F(x π₂) sum, x) = {(0,(B,11)),(1,(A,13)),(2,(C,3))}
    check aggregate(π₁, F(x π₂) Λ(∋) last, x) = {(0,(B,5)),(1,(A,7)),(2,(C,2))}
    check aggregate(π₁, F(x π₂) Λ(∋) head, x) = {(0,(B,1)),(1,(A,3)),(2,(C,1))}
    vc : N ⟶ K×N ≜ valueCounts(π₁, x)
    check vc = {(0,(B,3)),(1,(A,3)),(2,(C,2))}
    check collect(π₁, π₂, x) = {(0,(B,5 5 1)),(1,(A,3 7 3)),(2,(C,1 2))}
    check aggregate(π₁, F(x π₂) head, x) = {(0,(B,5)),(1,(A,3)),(2,(C,1))}
    check aggregate(π₁, F(x π₂) last, x) = {(0,(B,1)),(1,(A,3)),(2,(C,2))}
    check countDistinct(x π₁) = {(∗,3)}
    check countDistinct(x π₂) = {(∗,5)}
    check countDistinct(x) = {(∗,6)}
    check mode(π₁, x) = {(∗,B)}
    check mode(π₂, x) = {(∗,5)}
    check median(π₂, x) = {(∗,3)}
    check median(π₂, take({(∗,5)}, x)) = {(∗,5)}
    check median(π₂, take({(∗,4)}, x)) = {(∗,4)}
    -- joins and concatenation (TestFrameJoin)
    check J(π₁, π₁, x, y) = {(1,0),(1,2),(3,1),(4,0),(4,2),(5,1),(7,0),(7,2)}
    ij : N ⟶ (K×N)×(K×N) ≜ innerJoin(π₁, π₁, x, y)
    check ij = {(0,((A,3),(A,9))),(1,((A,3),(A,6))),(2,((C,1),(C,8))),(3,((A,7),(A,9))),(4,((A,7),(A,6))),
      (5,((C,2),(C,8))),(6,((A,3),(A,9))),(7,((A,3),(A,6)))}
    check semiJoin(π₁, π₁, x, y) = {(0,(A,3)),(1,(C,1)),(2,(A,7)),(3,(C,2)),(4,(A,3))}
    check antiJoin(π₁, π₁, x, y) = {(0,(B,5)),(1,(B,5)),(2,(B,1))}
    cj : N ⟶ N×N ≜ crossJoin(dom(x), dom(y))
    check cj = {(0,(0,0)),(1,(0,1)),(2,(0,2)),(3,(1,0)),(4,(1,1)),(5,(1,2)),(6,(2,0)),(7,(2,1)),(8,(2,2)),
      (9,(3,0)),(10,(3,1)),(11,(3,2)),(12,(4,0)),(13,(4,1)),(14,(4,2)),(15,(5,0)),(16,(5,1)),(17,(5,2)),
      (18,(6,0)),(19,(6,1)),(20,(6,2)),(21,(7,0)),(22,(7,1)),(23,(7,2))}
    check append(x, y) = {(0,(B,5)),(1,(A,3)),(2,(B,5)),(3,(C,1)),(4,(A,7)),(5,(C,2)),(6,(B,1)),(7,(A,3)),
      (8,(A,9)),(9,(C,8)),(10,(A,6))}
    check union(x, y) = {(0,(B,5)),(1,(A,3)),(2,(C,1)),(3,(A,7)),(4,(C,2)),(5,(B,1)),(6,(A,9)),(7,(C,8)),(8,(A,6))}
    check intersect(x, y2) = {(0,(A,3)),(1,(C,2))}
    check difference(x, y2) = {(0,(B,5)),(1,(C,1)),(2,(A,7)),(3,(B,1))}
    check melt({(∗,a)}, π₁, {(∗,b)}, π₂, w) = {(0,(a,1)),(1,(a,3)),(2,(a,5)),(3,(b,2)),(4,(b,4)),(5,(b,6))}
    check pivotLong(π₁, {(∗,a)}, π₂ π₁, {(∗,b)}, π₂ π₂, t) =
      {(0,(A,(a,1))),(1,(B,(a,3))),(2,(C,(a,5))),(3,(A,(b,2))),(4,(B,(b,4))),(5,(C,(b,6)))}

-- by hand: `v − 1` = 4 2 4 0 6 1 0 2; keys A B C occur 3 3 2 times; the rest as in the bounded files
#eval frameUnboundedT.failures.map toString
#guard frameUnboundedT.ok

end Rel.Lang.TestFrameUnbounded
