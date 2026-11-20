import Rel.Programs.Frame

/-! The dataframe fixture every `TestFrame*` file reads, and the column rows of `Rel.Programs.frame` (plan M0): each
    API row once, against rows worked by hand. -/

namespace Rel.Lang.TestFrameCols

-- `P` holds 16 positions for an 8-row frame: `count(x) = 8` and `x <> y` (11 rows) must be positions too
open Rel.Programs.prelude in
rel_program frameData where
    obj K = {A,B,C}
    obj N = 0…40
    obj P = 0…15
    x : P ⟶ K×N ≜ {(0,(B,5)),(1,(A,3)),(2,(B,5)),(3,(C,1)),(4,(A,7)),(5,(C,2)),(6,(B,1)),(7,(A,3))}
    big : N ⟶ N ≜ dom(<°{(2,∗)})

open Rel.Programs.prelude Rel.Programs.frame frameData in
rel_program frameCols where
    z : P ⟶ N ≜ {(0,1),(1,2),(2,3)}
    -- a sum literal does not parse, so the null column is built with `tot`: null at position 1
    w : P ⟶ N+1 ≜ dom(z) tot({(0,5),(2,3)})
    c : P ⟶ [K] ≜ {(0,A B C),(1,B A),(2,C A B)}
    code : K ⟶ N ≜ {(A,1),(B,2)}
    -- select, apply (double `v`), derive (append `v+v`)
    check x π₁ = {(0,B),(1,A),(2,B),(3,C),(4,A),(5,C),(6,B),(7,A)}
    check x ⟨π₁, π₂ ⟨𝟙,𝟙⟩plus⟩ = {(0,(B,10)),(1,(A,6)),(2,(B,10)),(3,(C,2)),(4,(A,14)),(5,(C,4)),(6,(B,2)),(7,(A,6))}
    check x ⟨𝟙, π₂ ⟨𝟙,𝟙⟩plus⟩ = {(0,((B,5),10)),(1,((A,3),6)),(2,((B,5),10)),(3,((C,1),2)),(4,((A,7),14)),
      (5,((C,2),4)),(6,((B,1),2)),(7,((A,3),6))}
    -- applyWhere: `succ` on `v` of the rows keyed A (positions 1 4 7)
    check x applyWhere(dom(π₁ {(A,A)}), ⟨π₁, π₂ succ⟩) =
      {(0,(B,5)),(1,(A,4)),(2,(B,5)),(3,(C,1)),(4,(A,8)),(5,(C,2)),(6,(B,1)),(7,(A,4))}
    -- selectRows by an index frame
    ix : P ⟶ P ≜ {(0,3),(1,0),(2,3)}
    check ix x = {(0,(C,1)),(1,(B,5)),(2,(C,1))}
    -- sum, count (`dimensions`), mean (integer), max, min, columnAsVector
    check summarize(F(x π₂) sum, x) = {(∗,27)}
    check count(x) = {(∗,8)}
    check summarize(F(x π₂) ⟨sum, length⟩div, x) = {(∗,3)}
    check summarize(F(x π₂) Λ(∋) last, x) = {(∗,7)}
    check summarize(F(x π₂) Λ(∋) head, x) = {(∗,1)}
    check summarize(F(x π₁), x) = {(∗,B A B C A C B A)}
    -- `|||`: rows where both frames have one
    check ⟨x, z⟩ = {(0,((B,5),1)),(1,((A,3),2)),(2,((B,5),3))}
    -- impute, recode, recode with default
    check w [𝟙, {(∗,0)}] = {(0,5),(1,0),(2,3)}
    check x π₁ code = {(0,2),(1,1),(2,2),(4,1),(6,2),(7,1)}
    check x π₁ tot(code) [𝟙, {(∗,0)}] = {(0,2),(1,1),(2,2),(3,0),(4,1),(5,0),(6,2),(7,1)}
    -- over: each row with its key's sum, B 5+5+1, A 3+7+3, C 1+2
    check over(π₁, F(x π₂) sum, x) = {(0,((B,5),11)),(1,((A,3),13)),(2,((B,5),11)),(3,((C,1),3)),(4,((A,7),13)),
      (5,((C,2),3)),(6,((B,1),11)),(7,((A,3),13))}
    -- contains `A B` (rows 0 and 2), length
    check dom(c contains({(A B,A B)})) = {(0,0),(2,2)}
    cl : P ⟶ N ≜ c length
    check cl = {(0,3),(1,2),(2,3)}
    -- reduce by a given `arith`: `max` from 0 over 5 3 5 1 7 2 1 3
    check summarize(F(x π₂) ⦇[{(∗,0)}, max]⦈, x) = {(∗,7)}
    -- describe `v`: count 8, mean 27 div 8 = 3, min 1, max 7
    check describe(x π₂) = {(∗,(8,(3,(1,7))))}
    -- arith verbs: `v div 2`, `v mod 2`; `and`, `or`, `not` of tests as `∩`, `∪`, `−` of coreflexives
    check x π₂ ⟨𝟙, ⊤ {(∗,2)}⟩div = {(0,2),(1,1),(2,2),(3,0),(4,3),(5,1),(6,0),(7,1)}
    check x π₂ ⟨𝟙, ⊤ {(∗,2)}⟩mod = {(0,1),(1,1),(2,1),(3,1),(4,1),(5,0),(6,1),(7,1)}
    check filterBy(dom(π₁ {(A,A)}) ∩ dom(π₂ big), x) = {(0,(A,3)),(1,(A,7)),(2,(A,3))}
    seven : N ⟶ N ≜ {(7,7)}
    check filterBy(dom(π₁ {(C,C)}) ∪ dom(π₂ seven), x) = {(0,(C,1)),(1,(A,7)),(2,(C,2))}
    check filterBy(𝟙 − dom(π₂ big), x) = {(0,(C,1)),(1,(C,2)),(2,(B,1))}

-- by hand from the fixture `k = B A B C A C B A`, `v = 5 3 5 1 7 2 1 3`: sum 27, mean 27 div 8 = 3
#guard frameCols.ok

end Rel.Lang.TestFrameCols
