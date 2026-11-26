import Rel.Lang.TestFrameCols

/-! The position rows of `Rel.Programs.frame` (plan M1) on the fixture of `TestFrameCols`, against rows worked by
    hand. -/

namespace Rel.Lang.TestFramePos

open Rel.Programs.prelude Rel.Programs.frame Rel.Lang.TestFrameCols.frameData in
rel_program framePos where
    check take({(∗,3)}, x) = {(0,(B,5)),(1,(A,3)),(2,(B,5))}
    check drop({(∗,3)}, x) = {(0,(C,1)),(1,(A,7)),(2,(C,2)),(3,(B,1)),(4,(A,3))}
    check range({(∗,2)}, {(∗,5)}, x) = {(0,(B,5)),(1,(C,1)),(2,(A,7))}
    -- `v > 2` holds at positions 0 1 2 4 7: `asc` numbers them, `filterBy` reads the rows
    pz : P ⟶ P ≜ asc(dom(x π₂ big))
    check pz = {(0,0),(1,1),(2,2),(3,4),(4,7)}
    check filterBy(dom(π₂ big), x) = {(0,(B,5)),(1,(A,3)),(2,(B,5)),(3,(A,7)),(4,(A,3))}
    -- the last 3 rows are 5 6 7; asking for more rows than there are keeps all (takeLast) or none (dropLast)
    check takeLast({(∗,3)}, x) = {(0,(C,2)),(1,(B,1)),(2,(A,3))}
    check takeLast({(∗,10)}, x) = x
    check dropLast({(∗,3)}, x) = {(0,(B,5)),(1,(A,3)),(2,(B,5)),(3,(C,1)),(4,(A,7))}
    check dropLast({(∗,10)}, x) = 𝟘
    -- sum of `v` over positions i−2…i: 5, 5+3, 5+3+5, 3+5+1, 5+1+7, 1+7+2, 7+2+1, 2+1+3
    check rolling({(∗,3)}, F(x π₂) sum, x) = {(0,5),(1,8),(2,13),(3,9),(4,13),(5,10),(6,10),(7,6)}
    -- running sum and running max of `v = 5 3 5 1 7 2 1 3`
    check cumAgg(F(x π₂) sum, x) = {(0,5),(1,8),(2,13),(3,14),(4,21),(5,23),(6,24),(7,27)}
    check cumAgg(F(x π₂) ^(∋) last, x) = {(0,5),(1,5),(2,5),(3,5),(4,7),(5,7),(6,7),(7,7)}
    -- the running sum as above, in `v`'s object `N` apart from the positions `P`; per key: B at 0 2 6 is 5 10 11,
    -- A at 1 4 7 is 3 10 13, C at 3 5 is 1 3
    check cumSum(x π₂) = {(0,5),(1,8),(2,13),(3,14),(4,21),(5,23),(6,24),(7,27)}
    check sumsBy(x π₁, x π₂) = {(0,5),(1,3),(2,10),(3,1),(4,10),(5,3),(6,11),(7,13)}
    -- first and last `v`; an empty frame gives the null, read here as 40
    check firstOrNothing(x π₂) [{(∗,40)}, 𝟙] = {(∗,5)}
    check lastOrNothing(x π₂) [{(∗,40)}, 𝟙] = {(∗,3)}
    check firstOrNothing(take({(∗,0)}, x π₂)) [{(∗,40)}, 𝟙] = {(∗,40)}

#guard framePos.ok

end Rel.Lang.TestFramePos
