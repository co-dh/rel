import Rel.Programs.FrameGroup

/-! The real-valued statistics of `frameStat` (`avg` `var` `svar` `dev` `sdev` `cov` `scov` `corr` `quantile`
    `skewness` `zScore` `valueProportions` `describe`), each in `F : f64` through `$` and the true quotient `%`, never an integer quotient.
    They cast the column's values to `Z : i64` first and read prim `sum`, which runs on `i64` only, so an `f64`
    column is refused at the cast (pinned below);
    its sum is the fold `⦇[{(∗,0)}, plus]⦈ʳ`. Expected rows worked by hand with values exact in binary. -/

namespace Rel.Lang.TestFrameStat

open Rel.Programs.prelude Rel.Programs.frame Rel.Programs.frameGroup Rel.Programs.frameStat in
rel_program frameStatT where
    obj K = {A,B}
    obj N
    f : N ⟶ F ≜ {(0,1.5),(1,0.25),(2,2.0)}
    w1 : N ⟶ F ≜ {(0,0.5)}
    e : N ⟶ F ≜ 𝟘
    v : N ⟶ N ≜ {(0,5),(1,3)}
    x : N ⟶ K×F ≜ {(0,(A,1.5)),(1,(B,0.25)),(2,(A,2.0))}
    -- 1.5 + 0.25 + 2 = 3.75; squares 2.25 + 0.0625 + 4 = 6.3125
    check summarize(F(f) ⦇[{(∗,0)}, plus]⦈ʳ, f) = {(∗,3.75)}
    check summarize(F(f ⟨𝟙, 𝟙⟩times) ⦇[{(∗,0)}, plus]⦈ʳ, f) = {(∗,6.3125)}
    -- one row: its value; no rows: `summarize` has no point to answer at
    check summarize(F(w1) ⦇[{(∗,0)}, plus]⦈ʳ, w1) = {(∗,0.5)}
    check summarize(F(e) ⦇[{(∗,0)}, plus]⦈ʳ, e) = 𝟘
    -- integers 5 3 cast to `f64`: 8; the count of `f` cast: 3
    check summarize(F(v $ F) ⦇[{(∗,0)}, plus]⦈ʳ, v $ F) = {(∗,8.0)}
    check count(f) $ F = {(∗,3.0)}
    -- groups A (rows 0, 2) and B (row 1): 1.5 + 2 = 3.5, 0.25
    check aggregate(π₁, F(x π₂) ⦇[{(∗,0)}, plus]⦈ʳ, x) = {(0,(A,3.5)),(1,(B,0.25))}
    -- prefix sums left to right: 1.5, 1.5 + 0.25 = 1.75, 1.75 + 2 = 3.75; per group A (rows 0, 2): 1.5, 3.5; B: 0.25
    check cumSum(f) = {(0,1.5),(1,1.75),(2,3.75)}
    gk : N ⟶ K ≜ {(0,A),(1,B),(2,A)}
    check sumsBy(gk, f) = {(0,1.5),(1,0.25),(2,3.5)}

    -- an integer column: q's `avg` of longs is a float
    t : N ⟶ N ≜ {(0,1),(1,4),(2,7)}
    -- 12/3 = 4; mean square 66/3 = 22, var 22 − 16 = 6, svar 6·3/2 = 9, sdev √9 = 3
    check summarize(F(t) avg, t) = {(∗,4.0)}
    check summarize(F(t) var, t) = {(∗,6.0)}
    check summarize(F(t) svar, t) = {(∗,9.0)}
    check summarize(F(t) sdev, t) = {(∗,3.0)}
    -- a = 1 3, b = 3 7: means 2 5, vars 1 4, devs 1 2; mean of ab (3 + 21)/2 = 12, cov 12 − 10 = 2, scov 2·2/1
    a : N ⟶ N ≜ {(0,1),(1,3)}
    b : N ⟶ N ≜ {(0,3),(1,7)}
    check summarize(F(a) dev, a) = {(∗,1.0)}
    check summarize(F(⟨a, b⟩) cov, a) = {(∗,2.0)}
    check summarize(F(⟨a, b⟩) scov, a) = {(∗,4.0)}
    -- 2/(1·2) = 1
    check summarize(F(⟨a, b⟩) corr, a) = {(∗,1.0)}
    -- the median is p = 0.5: odd, h = 0.5·2 = 1, row 1 of 1 4 7 is 4; even, 5 2 8 1 sorts to 1 2 5 8, h = 1.5: (2 + 5)/2
    m4 : N ⟶ N ≜ {(0,5),(1,2),(2,8),(3,1)}
    check quantile({(∗,0.5)}, t) = {(∗,4.0)}
    check quantile({(∗,0.5)}, m4) = {(∗,3.5)}
    -- p = 0, 1: the ends; 1 2 5 8 at p = 0.25: h = 0.75, 1 + 0.75·(2 − 1) = 1.75
    check quantile({(∗,0.0)}, m4) = {(∗,1.0)}
    check quantile({(∗,1.0)}, m4) = {(∗,8.0)}
    check quantile({(∗,0.25)}, m4) = {(∗,1.75)}
    -- 5 values 9 3 0 6 12 sort to 0 3 6 9 12: p = 0.25 gives h = 1 exactly, 3; p = 0.375, h = 1.5: (3 + 6)/2 = 4.5
    q5 : N ⟶ N ≜ {(0,9),(1,3),(2,0),(3,6),(4,12)}
    check quantile({(∗,0.25)}, q5) = {(∗,3.0)}
    check quantile({(∗,0.375)}, q5) = {(∗,4.5)}
    -- p outside [0, 1]: no answer
    check quantile({(∗,1.5)}, q5) = 𝟘
    -- 0 0 0 0 5: μ = 1, deviations −1 −1 −1 −1 4, m2 = 20/5 = 4, m3 = 60/5 = 12, 12/2³ = 1.5; 1 4 7 is symmetric: 0
    s5 : N ⟶ N ≜ {(0,0),(1,0),(2,5),(3,0),(4,0)}
    check summarize(F(s5) skewness, s5) = {(∗,1.5)}
    check summarize(F(t) skewness, t) = {(∗,0.0)}
    -- 1 4 7: mean 4, sample std 3, so −1 0 1
    check zScore(t) = {(0,-1.0),(1,0.0),(2,1.0)}
    -- per group, by composing with `aggregate`: A holds 1 3 (mean 2, svar 2), B holds 4 6 (mean 5, svar 2)
    g : N ⟶ K×N ≜ {(0,(A,1)),(1,(B,4)),(2,(A,3)),(3,(B,6))}
    check aggregate(π₁, F(g π₂) avg, g) = {(0,(A,2.0)),(1,(B,5.0))}
    check aggregate(π₁, F(g π₂) svar, g) = {(0,(A,2.0)),(1,(B,2.0))}
    -- skewness per group: B holds 1 4 7 (0, symmetric), A holds 0 0 5 0 0 (1.5, as `s5` below)
    gs : N ⟶ K×N ≜ {(0,(B,1)),(1,(A,0)),(2,(A,0)),(3,(B,4)),(4,(A,5)),(5,(A,0)),(6,(B,7)),(7,(A,0))}
    check aggregate(π₁, F(gs π₂) skewness, gs) = {(0,(B,0.0)),(1,(A,1.5))}
    -- one row: mean and median 7, var 0; svar 0·(1/0) is NaN, no row; describe's std null (a sum literal does not
    -- parse, so it is read back as -1)
    one : N ⟶ N ≜ {(0,7)}
    check summarize(F(one) avg, one) = {(∗,7.0)}
    check summarize(F(one) var, one) = {(∗,0.0)}
    check summarize(F(one) svar, one) = 𝟘
    check quantile({(∗,0.5)}, one) = {(∗,7.0)}
    -- zScore: no sample std at one row, so no rows
    check zScore(one) = 𝟘
    check describe(one) ⟨π₁, ⟨π₂ π₁, ⟨π₂ π₂ π₁ [𝟙, {(∗,-1.0)}], π₂ π₂ π₂⟩⟩⟩ = {(∗,(1,(7.0,(-1.0,(7,7)))))}
    -- no rows: no answer
    z : N ⟶ N ≜ 𝟘
    check summarize(F(z) avg, z) = 𝟘
    check quantile({(∗,0.5)}, z) = 𝟘
    check describe(z) = 𝟘
    -- count 3, mean 4, sample std 3, min 1, max 7
    check describe(t) ⟨π₁, ⟨π₂ π₁, ⟨π₂ π₂ π₁ [𝟙, {(∗,-1.0)}], π₂ π₂ π₂⟩⟩⟩ = {(∗,(3,(4.0,(3.0,(1,7)))))}
    -- A at 0 2 3, B at 1: 3/4, 1/4
    k : N ⟶ K ≜ {(0,A),(1,B),(2,A),(3,A)}
    check valueProportions(𝟙, k) = {(0,(A,0.75)),(1,(B,0.25))}

#guard frameStatT.failures.map toString == []

-- `avg` of an `f64` column: its entry cast to `Z` keeps values, and prim `sum`, which would take `F` instead, runs on
-- `i64` only (its `f64` row is not built; `sums` at `f64` is, `TestFrameTyped.sumsFloatT`)
/-- error: line 109, col 17: `summarize` at this call, where ν is N, δ is F, β is F: $ from F (f64) to Z (i64): not every f64 value is a i64 value, and $ keeps a number's value -/
#guard_msgs in
open Rel.Programs.prelude Rel.Programs.frame Rel.Programs.frameGroup Rel.Programs.frameStat in
rel_program avgFloatT where
    obj N
    f : N ⟶ F ≜ {(0,1.5),(1,0.25)}
    s : 1 ⟶ F ≜ summarize(F(f) avg, f)

-- a bounded object: 7³ = 343 and 40³ lie outside `N`, so the cubes, deviations and weights are computed in `F`
open Rel.Programs.prelude Rel.Programs.frame Rel.Programs.frameGroup Rel.Programs.frameStat in
rel_program frameStatBoundT where
    obj N = 0…40
    t : N ⟶ N ≜ {(0,7),(1,1),(2,4)}
    -- sorted 1 4 7: p = 0.75 gives h = 1.5, (4 + 7)/2 = 5.5; skewness 0 (symmetric); zScore (x − 4)/3
    check quantile({(∗,0.75)}, t) = {(∗,5.5)}
    check summarize(F(t) skewness, t) = {(∗,0.0)}
    check zScore(t) = {(0,1.0),(1,-1.0),(2,0.0)}
    -- 40 0 0 0 0: μ = 8, m2 = (32² + 4·8²)/5 = 256, m3 = (32³ − 4·8³)/5 = 6144, 6144/16³ = 1.5
    s5 : N ⟶ N ≜ {(0,40),(1,0),(2,0),(3,0),(4,0)}
    check summarize(F(s5) skewness, s5) = {(∗,1.5)}

#guard frameStatBoundT.failures.map toString == []

end Rel.Lang.TestFrameStat
