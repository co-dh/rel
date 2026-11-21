import Rel.Programs.FrameGroup

/-! The float statistics the library can state today on an `f64` column: the sum as the fold `⦇[{(∗,0)}, plus]⦈ʳ` (the
    prim `sum` runs on `i64` only), the sum of squares, per group through `aggregate`. A mean, a variance or a proportion
    needs a true float quotient, which no verb gives (`div` floors): `doc/dataframe-design.zh.typ` F4. Expected rows
    worked by hand with values exact in binary. -/

namespace Rel.Lang.TestFrameStat

open Rel.Programs.prelude Rel.Programs.frame Rel.Programs.frameGroup in
rel_program frameStatT where
    obj K = {A,B}
    obj N
    obj F : f64
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

#guard frameStatT.ok

end Rel.Lang.TestFrameStat
