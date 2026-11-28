import Rel.Lang.TestFrameCols
import Rel.Programs.FrameGroup

/-! The sort and group rows of `Rel.Programs.frameGroup` (plan M1) on the fixture of `TestFrameCols`, against rows
    worked by hand. -/

namespace Rel.Lang.TestFrameGroup

open Rel.Programs.prelude Rel.Programs.frame Rel.Programs.frameGroup Rel.Lang.TestFrameCols.frameData in
rel_program frameGroupT where
    -- by key: A at 1 4 7, B at 0 2 6, C at 3 5; descending C B A, ties in position order
    test iasc(x π₁) = {(0,1),(1,4),(2,7),(3,0),(4,2),(5,6),(6,3),(7,5)}
    test idesc(x π₁) = {(0,3),(1,5),(2,0),(3,2),(4,6),(5,1),(6,4),(7,7)}
    test sortBy(π₁, x) = {(0,(A,3)),(1,(A,7)),(2,(A,3)),(3,(B,5)),(4,(B,5)),(5,(B,1)),(6,(C,1)),(7,(C,2))}
    test topBy({(∗,2)}, π₁, x) = {(0,(A,3)),(1,(A,7))}
    test sortByDesc(π₁, x) = {(0,(C,1)),(1,(C,2)),(2,(B,5)),(3,(B,5)),(4,(B,1)),(5,(A,3)),(6,(A,7)),(7,(A,3))}
    -- `v` descending, ties by position: 7 at 4, 5 at 0 and 2
    test topK({(∗,3)}, π₂, x) = {(0,(A,7)),(1,(B,5)),(2,(B,5))}
    -- groups numbered by first occurrence: B 0, A 1, C 2
    test firstOcc(x π₁) = {(0,0),(1,1),(2,3)}
    test group(x π₁)° = {(0,0),(1,1),(2,0),(3,2),(4,1),(5,2),(6,0),(7,1)}
    test lastOcc(x π₁) = {(0,6),(1,7),(2,5)}
    -- rows 2 and 7 repeat rows 0 and 1
    test firstOcc(x) = {(0,0),(1,1),(2,3),(3,4),(4,5),(5,6)}
    test distinct(x) = {(0,(B,5)),(1,(A,3)),(2,(C,1)),(3,(A,7)),(4,(C,2)),(5,(B,1))}
    -- sum, max, min, count per group: B 5 5 1, A 3 7 3, C 1 2
    test aggregate(π₁, F(x π₂) sum, x) = {(0,(B,11)),(1,(A,13)),(2,(C,3))}
    test aggregate(π₁, F(x π₂) Λ(∋) last, x) = {(0,(B,5)),(1,(A,7)),(2,(C,2))}
    test aggregate(π₁, F(x π₂) Λ(∋) head, x) = {(0,(B,1)),(1,(A,3)),(2,(C,1))}
    -- several aggregates in one call: sum, count, max per group
    ag3 : P ⟶ K×(N×(P×N)) ≜ aggregate(π₁, ⟨F(x π₂) sum, ⟨length, F(x π₂) Λ(∋) last⟩⟩, x)
    test ag3 = {(0,(B,(11,(3,5)))),(1,(A,(13,(3,7)))),(2,(C,(3,(2,2))))}
    -- a pair of columns as the key: (B,5) at 0 2, (A,3) at 1 7, the others once
    vc2 : P ⟶ (K×N)×P ≜ aggregate(⟨π₁, π₂⟩, length, x)
    test vc2 = {(0,((B,5),2)),(1,((A,3),2)),(2,((C,1),1)),(3,((A,7),1)),(4,((C,2),1)),
      (5,((B,1),1))}
    -- by `v`, then key: (B,1)6 (C,1)3 (C,2)5 (A,3)1 (A,3)7 (B,5)0 (B,5)2 (A,7)4; descending, ties in position order
    test iasc(x ⟨π₂, π₁⟩) = {(0,6),(1,3),(2,5),(3,1),(4,7),(5,0),(6,2),(7,4)}
    test sortByDesc(⟨π₂, π₁⟩, x) = {(0,(A,7)),(1,(B,5)),(2,(B,5)),(3,(A,3)),(4,(A,3)),(5,(C,2)),(6,(C,1)),(7,(B,1))}
    vc : P ⟶ K×P ≜ valueCounts(π₁, x)
    test vc = {(0,(B,3)),(1,(A,3)),(2,(C,2))}
    test collect(π₁, π₂, x) = {(0,(B,5 5 1)),(1,(A,3 7 3)),(2,(C,1 2))}
    -- first and last `v` per group, in position order
    test aggregate(π₁, F(x π₂) head, x) = {(0,(B,5)),(1,(A,3)),(2,(C,1))}
    test aggregate(π₁, F(x π₂) last, x) = {(0,(B,1)),(1,(A,3)),(2,(C,2))}
    -- keys A B C; values 5 3 1 7 2; rows: 8 less the repeats 2 and 7
    test countDistinct(x π₁) = {(∗,3)}
    test countDistinct(x π₂) = {(∗,5)}
    test countDistinct(x) = {(∗,6)}
    -- B and A both occur 3 times, B first; 5, 3 and 1 occur twice, 5 first
    test mode(π₁, x) = {(∗,B)}
    test mode(π₂, x) = {(∗,5)}



end Rel.Lang.TestFrameGroup
