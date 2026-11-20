import Rel.Lang.TestFrameCols
import Rel.Programs.FrameGroup

/-! The sort and group rows of `Rel.Programs.frameGroup` (plan M1) on the fixture of `TestFrameCols`, against rows
    worked by hand. -/

namespace Rel.Lang.TestFrameGroup

open Rel.Programs.prelude Rel.Programs.frame Rel.Programs.frameGroup Rel.Lang.TestFrameCols.frameData in
rel_program frameGroupT where
    -- by key: A at 1 4 7, B at 0 2 6, C at 3 5; descending C B A, ties in position order
    check iasc(π₁, x) = {(0,1),(1,4),(2,7),(3,0),(4,2),(5,6),(6,3),(7,5)}
    check idesc(π₁, x) = {(0,3),(1,5),(2,0),(3,2),(4,6),(5,1),(6,4),(7,7)}
    check sortBy(π₁, x) = {(0,(A,3)),(1,(A,7)),(2,(A,3)),(3,(B,5)),(4,(B,5)),(5,(B,1)),(6,(C,1)),(7,(C,2))}
    check topBy({(∗,2)}, π₁, x) = {(0,(A,3)),(1,(A,7))}
    -- groups numbered by first occurrence: B 0, A 1, C 2
    check firstOcc(π₁, x) = {(0,0),(1,1),(2,3)}
    check g(π₁, x) = {(0,0),(1,1),(2,0),(3,2),(4,1),(5,2),(6,0),(7,1)}
    check lastOcc(π₁, x) = {(0,6),(1,7),(2,5)}
    -- rows 2 and 7 repeat rows 0 and 1
    check firstOcc(𝟙, x) = {(0,0),(1,1),(2,3),(3,4),(4,5),(5,6)}
    check distinct(x) = {(0,(B,5)),(1,(A,3)),(2,(C,1)),(3,(A,7)),(4,(C,2)),(5,(B,1))}
    -- sum, max, min, count per group: B 5 5 1, A 3 7 3, C 1 2
    check aggregate(π₁, F(x π₂) sum, x) = {(0,(B,11)),(1,(A,13)),(2,(C,3))}
    check aggregate(π₁, F(x π₂) Λ(∋) last, x) = {(0,(B,5)),(1,(A,7)),(2,(C,2))}
    check aggregate(π₁, F(x π₂) Λ(∋) head, x) = {(0,(B,1)),(1,(A,3)),(2,(C,1))}
    vc : P ⟶ K×P ≜ valueCounts(π₁, x)
    check vc = {(0,(B,3)),(1,(A,3)),(2,(C,2))}
    check collect(π₁, π₂, x) = {(0,(B,5 5 1)),(1,(A,3 7 3)),(2,(C,1 2))}
    -- first and last `v` per group, in position order
    check aggregate(π₁, F(x π₂) head, x) = {(0,(B,5)),(1,(A,3)),(2,(C,1))}
    check aggregate(π₁, F(x π₂) last, x) = {(0,(B,1)),(1,(A,3)),(2,(C,2))}
    -- keys A B C; values 5 3 1 7 2; rows: 8 less the repeats 2 and 7
    check countDistinct(x π₁) = {(∗,3)}
    check countDistinct(x π₂) = {(∗,5)}
    check countDistinct(x) = {(∗,6)}
    -- B and A both occur 3 times, B first; 5, 3 and 1 occur twice, 5 first
    check mode(π₁, x) = {(∗,B)}
    check mode(π₂, x) = {(∗,5)}
    -- sorted `v`: 1 1 2 3 3 5 5 7 (middle 3, 3); first 5 rows 1 3 5 5 7 (5); first 4 rows 1 3 5 5 ((3+5)/2)
    check median(π₂, x) = {(∗,3)}
    check median(π₂, take({(∗,5)}, x)) = {(∗,5)}
    check median(π₂, take({(∗,4)}, x)) = {(∗,4)}

#eval frameGroupT.failures.map toString
#guard frameGroupT.ok

end Rel.Lang.TestFrameGroup
