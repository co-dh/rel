import Rel.Lang.TestFrameCols
import Rel.Programs.FrameJoin

/-! The null rows of `Rel.Programs.frame`/`frameJoin` (plan M4) on the fixture of `TestFrameCols`, against rows
    worked by hand. A sum literal does not parse, so a null is built with `tot` and read back through an impute. -/

namespace Rel.Lang.TestFrameNull

open Rel.Programs.prelude Rel.Programs.frame Rel.Programs.frameGroup Rel.Programs.frameJoin
  Rel.Lang.TestFrameCols.frameData in
rel_program frameNullT where
    obj Z = -10…40
    obj S = {a,b}
    -- a nullable column beside `k`: a value at positions 0 2 4 7, null at 1 3 5 6
    nc : P ⟶ N+1 ≜ dom(x) tot({(0,5),(2,5),(4,7),(7,3)})
    xn : P ⟶ K×(N+1) ≜ ⟨x π₁, nc⟩
    check filterJust(π₂, xn) ⟨π₁, π₂ inl°⟩ = {(0,(B,5)),(1,(B,5)),(2,(A,7)),(3,(A,3))}
    check filterNothing(π₂, xn) π₁ = {(0,A),(1,C),(2,C),(3,B)}
    -- `v = 5 3 5 1 7 2 1 3` moved down one and two rows; the null reads as 40
    check shift({(∗,1)}, x π₂) [𝟙, {(∗,40)}] = {(0,40),(1,5),(2,3),(3,5),(4,1),(5,7),(6,2),(7,1)}
    check shift({(∗,2)}, x π₂) [𝟙, {(∗,40)}] = {(0,40),(1,40),(2,5),(3,3),(4,5),(5,1),(6,7),(7,2)}
    -- `v` in `Z`, so a difference may be negative: 3−5, 5−3, 1−5, 7−1, 2−7, 1−2, 3−1
    v : P ⟶ Z ≜ {(0,5),(1,3),(2,5),(3,1),(4,7),(5,2),(6,1),(7,3)}
    check diff({(∗,1)}, v) [𝟙, {(∗,40)}] = {(0,40),(1,-2),(2,2),(3,-4),(4,6),(5,-5),(6,-1),(7,2)}
    -- `y` has keys A C: x's A rows 1 4 7 meet (A,9), its C rows 3 5 meet (C,8), its B rows 0 2 6 the null,
    -- read as (B,0); one row per x row since each key occurs once in `y`
    y : P ⟶ K×N ≜ {(0,(A,9)),(1,(C,8))}
    lj : P ⟶ (K×N)×(K×N) ≜ leftJoin(π₁, π₁, x, y) ⟨π₁, π₂ [𝟙, {(∗,(B,0))}]⟩
    check lj = {(0,((B,5),(B,0))),(1,((A,3),(A,9))),(2,((B,5),(B,0))),(3,((C,1),(C,8))),(4,((A,7),(A,9))),
      (5,((C,2),(C,8))),(6,((B,1),(B,0))),(7,((A,3),(A,9)))}
    -- rightJoin of y with x: x's rows in order, each with its match in y or the null (read as (B,0))
    rj : P ⟶ (K×N)×(K×N) ≜ rightJoin(π₁, π₁, y, x) ⟨π₁ [𝟙, {(∗,(B,0))}], π₂⟩
    check rj = {(0,((B,0),(B,5))),(1,((A,9),(A,3))),(2,((B,0),(B,5))),(3,((C,8),(C,1))),(4,((A,9),(A,7))),
      (5,((C,8),(C,2))),(6,((B,0),(B,1))),(7,((A,9),(A,3)))}
    -- fullOuterJoin of y with x: y's (A,9) meets x's 1 4 7, (C,8) meets 3 5; then x's B rows 0 2 6, null on the left
    fj : P ⟶ (K×N)×(K×N) ≜ fullOuterJoin(π₁, π₁, y, x) ⟨π₁ [𝟙, {(∗,(B,0))}], π₂ [𝟙, {(∗,(B,0))}]⟩
    check fj = {(0,((A,9),(A,3))),(1,((A,9),(A,7))),(2,((A,9),(A,3))),(3,((C,8),(C,1))),(4,((C,8),(C,2))),
      (5,((B,0),(B,5))),(6,((B,0),(B,5))),(7,((B,0),(B,1)))}
    -- toMaybe, fromJust, isJust, isNothing, whenPresent (succ, the null read as 40)
    check x π₂ inl [𝟙, {(∗,40)}] = x π₂
    check nc inl° = {(0,5),(2,5),(4,7),(7,3)}
    check dom(nc inl°) = {(0,0),(2,2),(4,4),(7,7)}
    check dom(nc inr°) = {(1,1),(3,3),(5,5),(6,6)}
    check nc (succ ⊕ 𝟙) [𝟙, {(∗,40)}] = {(0,6),(1,40),(2,6),(3,40),(4,8),(5,40),(6,40),(7,4)}
    -- imputeWith the mean of the values present, (5+5+7+3) div 4 = 5
    check nc [𝟙, summarize(F(nc inl°) ⟨sum, length⟩div, nc inl°)] = {(0,5),(1,5),(2,5),(3,5),(4,7),(5,5),(6,5),(7,3)}
    check nulls(π₂, xn) = {(∗,4)}
    -- fills: 5 · 5 · 7 · · 3 → 5 5 5 5 7 7 7 3; a leading null stays: · · 4 · · 1 · · → · · 4 4 4 1 1 1
    check fills(nc) [𝟙, {(∗,40)}] = {(0,5),(1,5),(2,5),(3,5),(4,7),(5,7),(6,7),(7,3)}
    n2 : P ⟶ N+1 ≜ dom(x) tot({(2,4),(5,1)})
    check fills(n2) [𝟙, {(∗,40)}] = {(0,40),(1,40),(2,4),(3,4),(4,4),(5,1),(6,1),(7,1)}
    -- relu of `v − 3` = 2 0 2 −2 4 −1 −2 0
    check v ⟨𝟙, ⊤ {(∗,3)}⟩minus ⟨𝟙, ⊤ {(∗,0)}⟩max = {(0,2),(1,0),(2,2),(3,0),(4,4),(5,0),(6,0),(7,0)}
    -- aj: quotes A at 2 and 6, C at 1, B at 9; each x row takes its key's latest quote at or before its `v`
    q : P ⟶ K×N ≜ {(0,(A,2)),(1,(A,6)),(2,(C,1)),(3,(B,9))}
    aq : P ⟶ (K×N)×(K×N) ≜ aj(π₁, π₂, π₁, π₂, x, q) ⟨π₁, π₂ [𝟙, {(∗,(B,0))}]⟩
    check aq = {(0,((B,5),(B,0))),(1,((A,3),(A,2))),(2,((B,5),(B,0))),(3,((C,1),(C,1))),(4,((A,7),(A,6))),
      (5,((C,2),(C,1))),(6,((B,1),(B,0))),(7,((A,3),(A,2)))}
    -- aj on tied times, as q: A quotes 0 and 2 both at time 2, C quotes 1 and 4 both at 1; the later position wins
    -- (A at 3 → 12, C at 1 and 2 → 14, A at 7 → 13); B has no quote: the null, read as 0
    qt : P ⟶ K×(N×N) ≜ {(0,(A,(2,10))),(1,(C,(1,11))),(2,(A,(2,12))),(3,(A,(6,13))),(4,(C,(1,14))),(5,(C,(3,15)))}
    check aj(π₁, π₂, π₁, π₂ π₁, x, qt) ⟨π₁, π₂ [π₂ π₂, {(∗,0)}]⟩ = {(0,((B,5),0)),(1,((A,3),12)),(2,((B,5),0)),
      (3,((C,1),14)),(4,((A,7),13)),(5,((C,2),14)),(6,((B,1),0)),(7,((A,3),12))}
    -- pivot wide of (k, q, v): (A,a) 1+4, (B,a) 2, (A,b) 3, (C,b) 5; keys in first-occurrence order A B C, null as 0
    t3 : P ⟶ K×(S×N) ≜ {(0,(A,(a,1))),(1,(B,(a,2))),(2,(A,(b,3))),(3,(A,(a,4))),(4,(C,(b,5)))}
    pw : P ⟶ K×(N×N) ≜ pivotWide(π₁, π₂ π₁, {(∗,a)}, {(∗,b)}, F(t3 π₂ π₂) sum, t3) ⟨π₁, ⟨π₂ π₁ [𝟙, {(∗,0)}], π₂ π₂ [𝟙, {(∗,0)}]⟩⟩
    check pw = {(0,(A,(5,3))),(1,(B,(2,0))),(2,(C,(0,5)))}

#guard frameNullT.ok

end Rel.Lang.TestFrameNull
