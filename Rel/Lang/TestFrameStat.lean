import Rel.Programs.FrameGroup

/-! The real-valued statistics of `frameStat` (`avg` `var` `svar` `dev` `sdev` `cov` `scov` `corr` `med`
    `valueProportions` `describe`), each in `F : f64` through `$` and the true quotient `%`, never an integer quotient.
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
    -- odd: the middle of 1 4 7 is 4; even: 5 2 8 1 sorts to 1 2 5 8, (2 + 5)/2 = 3.5
    m4 : N ⟶ N ≜ {(0,5),(1,2),(2,8),(3,1)}
    check med(t) = {(∗,4.0)}
    check med(m4) = {(∗,3.5)}
    -- per group, by composing with `aggregate`: A holds 1 3 (mean 2, svar 2), B holds 4 6 (mean 5, svar 2)
    g : N ⟶ K×N ≜ {(0,(A,1)),(1,(B,4)),(2,(A,3)),(3,(B,6))}
    check aggregate(π₁, F(g π₂) avg, g) = {(0,(A,2.0)),(1,(B,5.0))}
    check aggregate(π₁, F(g π₂) svar, g) = {(0,(A,2.0)),(1,(B,2.0))}
    -- one row: mean and median 7, var 0; svar 0·(1/0) is NaN, no row; describe's std null (a sum literal does not
    -- parse, so it is read back as -1)
    one : N ⟶ N ≜ {(0,7)}
    check summarize(F(one) avg, one) = {(∗,7.0)}
    check summarize(F(one) var, one) = {(∗,0.0)}
    check summarize(F(one) svar, one) = 𝟘
    check med(one) = {(∗,7.0)}
    check describe(one) ⟨π₁, ⟨π₂ π₁, ⟨π₂ π₂ π₁ [𝟙, {(∗,-1.0)}], π₂ π₂ π₂⟩⟩⟩ = {(∗,(1,(7.0,(-1.0,(7,7)))))}
    -- no rows: no answer
    z : N ⟶ N ≜ 𝟘
    check summarize(F(z) avg, z) = 𝟘
    check med(z) = 𝟘
    check describe(z) = 𝟘
    -- count 3, mean 4, sample std 3, min 1, max 7
    check describe(t) ⟨π₁, ⟨π₂ π₁, ⟨π₂ π₂ π₁ [𝟙, {(∗,-1.0)}], π₂ π₂ π₂⟩⟩⟩ = {(∗,(3,(4.0,(3.0,(1,7)))))}
    -- A at 0 2 3, B at 1: 3/4, 1/4
    k : N ⟶ K ≜ {(0,A),(1,B),(2,A),(3,A)}
    check valueProportions(𝟙, k) = {(0,(A,0.75)),(1,(B,0.25))}

#guard frameStatT.failures.map toString == []

-- `avg` of an `f64` column: its entry cast to `Z` keeps values, and prim `sum`, which would take `F` instead, runs on
-- `i64` only (the float summation order is undecided, PLAN S4)
/-- error: line 84, col 5: $ from Rel.Programs.frameStat.F (f64) to Rel.Programs.frameStat.Z (i64): not every f64 value is a i64 value, and $ keeps a number's value -/
#guard_msgs in
open Rel.Programs.prelude Rel.Programs.frame Rel.Programs.frameGroup Rel.Programs.frameStat in
rel_program avgFloatT where
    obj N
    f : N ⟶ F ≜ {(0,1.5),(1,0.25)}
    s : 1 ⟶ F ≜ summarize(F(f) avg, f)

end Rel.Lang.TestFrameStat
