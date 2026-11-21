import Rel.Programs.FrameGroup

/-! The real-valued statistics of `frameStat` (`avg` `var` `svar` `dev` `sdev` `cov` `scov` `corr` `quantile`
    `skewness` `zScore` `valueProportions` `describe`), each generic over its result's float object `φ`, which each
    check fixes: its other side read at the program's own `F : f64`, or `𝟙(F)` where that side is `𝟘`. They cast the
    column's values to `φ` first and sum with prim `sum` there, so integer and `f64` columns both work.
    Expected rows worked by hand with values exact in binary. -/

namespace Rel.Lang.TestFrameStat

open Rel.Programs.prelude Rel.Programs.frame Rel.Programs.frameGroup Rel.Programs.frameStat in
rel_program frameStatT where
    obj K = {A,B}
    obj N
    obj F : f64
    obj D : date
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
    -- `genericPercentile`, no interpolation: the sorted row at ⌊h⌋. 1 4 7 at p = 0.5: h = 1, 4; 1 2 5 8 at p = 0.5:
    -- h = 1.5, row 1 is 2 (`quantile` gives 3.5); p = 0.75: h = 2.25, 5; p = 0, 1: the ends
    check genericPercentile({(∗,0.5)} 𝟙(F), t) = {(∗,4)}
    check genericPercentile({(∗,0.5)} 𝟙(F), m4) = {(∗,2)}
    check genericPercentile({(∗,0.75)} 𝟙(F), m4) = {(∗,5)}
    check genericPercentile({(∗,0.0)} 𝟙(F), m4) = {(∗,1)}
    check genericPercentile({(∗,1.0)} 𝟙(F), m4) = {(∗,8)}
    -- 5 values 0 3 6 9 12 at p = 0.375: h = 1.5, 3; p outside [0, 1]: no answer
    check genericPercentile({(∗,0.375)} 𝟙(F), q5) = {(∗,3)}
    check genericPercentile({(∗,1.5)} 𝟙(F), q5) 𝟙(N) = 𝟘
    check genericPercentile({(∗,-0.25)} 𝟙(F), q5) 𝟙(N) = 𝟘
    -- an `f64` column and a date column: sorted 0.25 1.5 2 and 2021.12.29 2022.01.08 2022.01.13, p = 0.5 gives h = 1
    check genericPercentile({(∗,0.5)} 𝟙(F), f) = {(∗,1.5)}
    dd : N ⟶ D ≜ {(0,2022.01.08),(1,2022.01.13),(2,2021.12.29)}
    check genericPercentile({(∗,0.5)} 𝟙(F), dd) = {(∗,2022.01.08)}
    check genericPercentile({(∗,1.0)} 𝟙(F), dd) = {(∗,2022.01.13)}
    -- a column at the enumerated `K`, in declaration order A B: B A B sorts to A B B, p = 0 gives A, p = 0.5 gives B
    kk : N ⟶ K ≜ {(0,B),(1,A),(2,B)}
    check genericPercentile({(∗,0.0)} 𝟙(F), kk) = {(∗,A)}
    check genericPercentile({(∗,0.5)} 𝟙(F), kk) = {(∗,B)}
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
    check summarize(F(one) svar, one) 𝟙(F) = 𝟘
    check quantile({(∗,0.5)}, one) = {(∗,7.0)}
    -- zScore: no sample std at one row, so no rows
    check zScore(one) 𝟙(F) = 𝟘
    check describe(one) ⟨π₁, ⟨π₂ π₁, ⟨π₂ π₂ π₁ [𝟙, {(∗,-1.0)}], π₂ π₂ π₂⟩⟩⟩ = {(∗,(1,(7.0,(-1.0,(7,7)))))}
    -- no rows: no answer (`𝟙(F)` fixes the result object, which `𝟘` does not)
    z : N ⟶ N ≜ 𝟘
    check summarize(F(z) avg, z) 𝟙(F) = 𝟘
    check quantile({(∗,0.5)}, z) = 𝟘
    check genericPercentile({(∗,0.0)} 𝟙(F), z) 𝟙(N) = 𝟘
    check describe(z) (𝟙 × (𝟙(F) × 𝟙)) = 𝟘
    -- count 3, mean 4, sample std 3, min 1, max 7
    check describe(t) ⟨π₁, ⟨π₂ π₁, ⟨π₂ π₂ π₁ [𝟙, {(∗,-1.0)}], π₂ π₂ π₂⟩⟩⟩ = {(∗,(3,(4.0,(3.0,(1,7)))))}
    -- A at 0 2 3, B at 1: 3/4, 1/4
    k : N ⟶ K ≜ {(0,A),(1,B),(2,A),(3,A)}
    check valueProportions(𝟙, k) = {(0,(A,0.75)),(1,(B,0.25))}

#guard frameStatT.failures.map toString == []

-- an `f64` column: the same definitions, the cast to `F` the identity
open Rel.Programs.prelude Rel.Programs.frame Rel.Programs.frameGroup Rel.Programs.frameStat in
rel_program frameStatFloatT where
    obj N
    obj F : f64
    -- 0.5 2 3.5: mean 2; mean square (0.25 + 4 + 12.25)/3 = 5.5, var 5.5 − 4 = 1.5, svar 1.5·3/2 = 2.25, sdev 1.5
    f : N ⟶ F ≜ {(0,0.5),(1,2.0),(2,3.5)}
    check summarize(F(f) avg, f) = {(∗,2.0)}
    check summarize(F(f) var, f) = {(∗,1.5)}
    check summarize(F(f) svar, f) = {(∗,2.25)}
    check summarize(F(f) sdev, f) = {(∗,1.5)}
    -- (x − 2)/1.5
    check zScore(f) = {(0,-1.0),(1,0.0),(2,1.0)}
    -- count 3, mean 2, sample std 1.5, min 0.5, max 3.5
    check describe(f) ⟨π₁, ⟨π₂ π₁, ⟨π₂ π₂ π₁ [𝟙, {(∗,-1.0)}], π₂ π₂ π₂⟩⟩⟩ = {(∗,(3,(2.0,(1.5,(0.5,3.5)))))}
    -- symmetric: E[x³] = (0.125 + 8 + 42.875)/3 = 17 = 2·(3·1.5 + 4), so 0
    check summarize(F(f) skewness, f) = {(∗,0.0)}
    -- 0 0 0 0 2.5 (`s5` of `frameStatT` halved): μ = 0.5, var 1.25 − 0.25 = 1, E[x³] = 3.125, m3 = 3.125 − 0.5·3.25 = 1.5
    s5 : N ⟶ F ≜ {(0,0.0),(1,0.0),(2,2.5),(3,0.0),(4,0.0)}
    check summarize(F(s5) skewness, s5) = {(∗,1.5)}
    -- a = 0.5 1.5, b = 2a: E[ab] = 2.5, cov 2.5 − 1·2 = 0.5, devs 0.5 1, corr 1
    a : N ⟶ F ≜ {(0,0.5),(1,1.5)}
    b : N ⟶ F ≜ {(0,1.0),(1,3.0)}
    check summarize(F(⟨a, b⟩) cov, a) = {(∗,0.5)}
    check summarize(F(⟨a, b⟩) corr, a) = {(∗,1.0)}
    -- 2.5 0.5 3.5 1 sorts to 0.5 1 2.5 3.5: p = 0.5, h = 1.5: (1 + 2.5)/2 = 1.75; p = 0.25, h = 0.75: 0.25·0.5 + 0.75·1
    m4 : N ⟶ F ≜ {(0,2.5),(1,0.5),(2,3.5),(3,1.0)}
    check quantile({(∗,0.5)}, m4) = {(∗,1.75)}
    check quantile({(∗,0.25)}, m4) = {(∗,0.875)}
    -- q's left fold: 1 + 1e16 = 1e16 (the tie rounds to the even 1e16), 1e16 − 1e16 = 0, so 0/3, where the exact mean
    -- is 1/3 and the right fold 1 + (1e16 − 1e16) would give it
    g : N ⟶ F ≜ {(0,1.0),(1,1e16),(2,-1e16)}
    check summarize(F(g) avg, g) = {(∗,0.0)}

#guard frameStatFloatT.failures.map toString == []

-- the result at an `f32` object: the typed definition fixes `φ` at `H`, and prim `sum` has no `f32` row
/-- error: line 168, col 32: `avg` at this call, where γ is N, φ is H: sum on H: H is an object of f32, and sum runs on objects of i64, f64 only; cast first, `x $ F` with `F` an object of f64 -/
#guard_msgs in
open Rel.Programs.prelude Rel.Programs.frame Rel.Programs.frameGroup Rel.Programs.frameStat in
rel_program frameStatF32T where
    obj N
    obj H : f32
    t : N ⟶ N ≜ {(0,1),(1,4),(2,7)}
    m : 1 ⟶ H ≜ summarize(F(t) avg, t)

-- a bounded object: 7³ = 343 and 40³ lie outside `N`, so the cubes, deviations and weights are computed in `F`
open Rel.Programs.prelude Rel.Programs.frame Rel.Programs.frameGroup Rel.Programs.frameStat in
rel_program frameStatBoundT where
    obj N = 0…40
    obj F : f64
    t : N ⟶ N ≜ {(0,7),(1,1),(2,4)}
    -- sorted 1 4 7: p = 0.75 gives h = 1.5, (4 + 7)/2 = 5.5; skewness 0 (symmetric); zScore (x − 4)/3
    check quantile({(∗,0.75)}, t) = {(∗,5.5)}
    -- at h = 1.5, ⌊h⌋ = 1: 4; the bounded positions cast to `Z`
    check genericPercentile({(∗,0.75)} 𝟙(F), t) = {(∗,4)}
    check summarize(F(t) skewness, t) = {(∗,0.0)}
    check zScore(t) = {(0,1.0),(1,-1.0),(2,0.0)}
    -- 40 0 0 0 0: μ = 8, m2 = (32² + 4·8²)/5 = 256, m3 = (32³ − 4·8³)/5 = 6144, 6144/16³ = 1.5
    s5 : N ⟶ N ≜ {(0,40),(1,0),(2,0),(3,0),(4,0)}
    check summarize(F(s5) skewness, s5) = {(∗,1.5)}

#guard frameStatBoundT.failures.map toString == []

end Rel.Lang.TestFrameStat
