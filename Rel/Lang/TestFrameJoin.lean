import Rel.Lang.TestFrameCols
import Rel.Programs.FrameJoin

/-! The join and concatenation rows of `Rel.Programs.frameJoin` (plan M1): the fixture of `TestFrameCols` against
    a second table `y` (keys A C A) and a third `y2` sharing rows with `x`, against rows worked by hand. -/

namespace Rel.Lang.TestFrameJoin

open Rel.Programs.prelude Rel.Programs.frame Rel.Programs.frameGroup Rel.Programs.frameJoin
  Rel.Lang.TestFrameCols.frameData in
rel_program frameJoinT where
    obj Q = 0…31
    obj S = {a,b}
    y : P ⟶ K×N ≜ {(0,(A,9)),(1,(C,8)),(2,(A,6))}
    y2 : P ⟶ K×N ≜ {(0,(A,3)),(1,(C,2)),(2,(B,4))}
    w : P ⟶ N×N ≜ {(0,(1,2)),(1,(3,4)),(2,(5,6))}
    -- x's A rows 1 4 7 meet y's 0 2, its C rows 3 5 meet y's 1; numbered in (i, j) order
    check J(π₁, π₁, x, y) = {(1,0),(1,2),(3,1),(4,0),(4,2),(5,1),(7,0),(7,2)}
    ij : P ⟶ (K×N)×(K×N) ≜ innerJoin(π₁, π₁, x, y)
    check ij = {(0,((A,3),(A,9))),(1,((A,3),(A,6))),(2,((C,1),(C,8))),(3,((A,7),(A,9))),(4,((A,7),(A,6))),
      (5,((C,2),(C,8))),(6,((A,3),(A,9))),(7,((A,3),(A,6)))}
    check semiJoin(π₁, π₁, x, y) = {(0,(A,3)),(1,(C,1)),(2,(A,7)),(3,(C,2)),(4,(A,3))}
    check antiJoin(π₁, π₁, x, y) = {(0,(B,5)),(1,(B,5)),(2,(B,1))}
    -- 8 × 3 rows: row 3i + j pairs x's row i with y's row j
    cj : Q ⟶ P×P ≜ crossJoin(dom(x), dom(y))
    check cj = {(0,(0,0)),(1,(0,1)),(2,(0,2)),(3,(1,0)),(4,(1,1)),(5,(1,2)),(6,(2,0)),(7,(2,1)),(8,(2,2)),
      (9,(3,0)),(10,(3,1)),(11,(3,2)),(12,(4,0)),(13,(4,1)),(14,(4,2)),(15,(5,0)),(16,(5,1)),(17,(5,2)),
      (18,(6,0)),(19,(6,1)),(20,(6,2)),(21,(7,0)),(22,(7,1)),(23,(7,2))}
    -- `<>`, then union drops rows 2 and 7 (repeats of 0 and 1)
    check append(x, y) = {(0,(B,5)),(1,(A,3)),(2,(B,5)),(3,(C,1)),(4,(A,7)),(5,(C,2)),(6,(B,1)),(7,(A,3)),
      (8,(A,9)),(9,(C,8)),(10,(A,6))}
    check union(x, y) = {(0,(B,5)),(1,(A,3)),(2,(C,1)),(3,(A,7)),(4,(C,2)),(5,(B,1)),(6,(A,9)),(7,(C,8)),(8,(A,6))}
    -- x's rows in y2: (A,3) at 1 7, (C,2) at 5
    check intersect(x, y2) = {(0,(A,3)),(1,(C,2))}
    check difference(x, y2) = {(0,(B,5)),(1,(C,1)),(2,(A,7)),(3,(B,1))}
    check melt({(∗,a)}, π₁, {(∗,b)}, π₂, w) = {(0,(a,1)),(1,(a,3)),(2,(a,5)),(3,(b,2)),(4,(b,4)),(5,(b,6))}
    t : P ⟶ K×(N×N) ≜ {(0,(A,(1,2))),(1,(B,(3,4))),(2,(C,(5,6)))}
    check pivotLong(π₁, {(∗,a)}, π₂ π₁, {(∗,b)}, π₂ π₂, t) =
      {(0,(A,(a,1))),(1,(B,(a,3))),(2,(C,(a,5))),(3,(A,(b,2))),(4,(B,(b,4))),(5,(C,(b,6)))}

#guard frameJoinT.ok

end Rel.Lang.TestFrameJoin
