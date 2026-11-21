import Rel.Programs.FrameGroup

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
    -- sum, count (`dimensions`), the integer quotient `sum div length` (by intent; not a mean), max, min, columnAsVector
    check summarize(F(x π₂) sum, x) = {(∗,27)}
    check count(x) = {(∗,8)}
    check summarize(F(x π₂) ⟨sum, length⟩div, x) = {(∗,3)}
    check summarize(F(x π₂) Λ(∋) last, x) = {(∗,7)}
    check summarize(F(x π₂) Λ(∋) head, x) = {(∗,1)}
    check summarize(F(x π₁), x) = {(∗,B A B C A C B A)}
    -- the pair: rows where both frames have one; `|||` (hstack): none unless the lengths agree
    check ⟨x, z⟩ = {(0,((B,5),1)),(1,((A,3),2)),(2,((B,5),3))}
    check hstack(x, z) = 𝟘
    check hstack(take({(∗,3)}, x), z) = {(0,((B,5),1)),(1,((A,3),2)),(2,((B,5),3))}
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
    -- arith verbs: `v div 2`, `v mod 2`; `and`, `or`, `not` of tests as `∩`, `∪`, `−` of coreflexives
    check x π₂ ⟨𝟙, ⊤ {(∗,2)}⟩div = {(0,2),(1,1),(2,2),(3,0),(4,3),(5,1),(6,0),(7,1)}
    check x π₂ ⟨𝟙, ⊤ {(∗,2)}⟩mod = {(0,1),(1,1),(2,1),(3,1),(4,1),(5,0),(6,1),(7,1)}
    check filterBy(dom(π₁ {(A,A)}) ∩ dom(π₂ big), x) = {(0,(A,3)),(1,(A,7)),(2,(A,3))}
    seven : N ⟶ N ≜ {(7,7)}
    check filterBy(dom(π₁ {(C,C)}) ∪ dom(π₂ seven), x) = {(0,(C,1)),(1,(A,7)),(2,(C,2))}
    check filterBy(𝟙 − dom(π₂ big), x) = {(0,(C,1)),(1,(C,2)),(2,(B,1))}

-- by hand from the fixture `k = B A B C A C B A`, `v = 5 3 5 1 7 2 1 3`: sum 27, quotient 27 div 8 = 3
#guard frameCols.ok

-- describe `v` (`frameStat`, a program of its own: its float objects would take part in reading the literals above):
-- count 8, mean 27/8 = 3.375, min 1, max 7; std √(255/56) ≈ 2.1339 is no float, so it is pinned in (2.125, 2.25):
-- 2.125² = 4.515625 < 255/56 < 5.0625 = 2.25²
open Rel.Programs.prelude Rel.Programs.frame Rel.Programs.frameStat frameData in
rel_program frameDescribe where
    obj F : f64
    check describe(x π₂) ⟨π₁, ⟨π₂ π₁, π₂ π₂ π₂⟩⟩ = {(∗,(8,(3.375,(1,7))))}
    check describe(x π₂) π₂ π₂ π₁ [𝟙, {(∗,-1.0)}] <° {(2.125,∗)} = {(∗,∗)}
    check describe(x π₂) π₂ π₂ π₁ [𝟙, {(∗,-1.0)}] < {(2.25,∗)} = {(∗,∗)}
    -- squares up to 49 and products v·2v up to 98 leave `N = 0…40`: mean square 123/8, var 123/8 − 3.375² = 255/64;
    -- cov(v, 2v) = 246/8 − 3.375·6.75 = 255/32
    check summarize(F(x π₂) var, x) = {(∗,3.984375)}
    check summarize(F(⟨x π₂, x π₂ ⟨𝟙,𝟙⟩plus⟩) cov, x) = {(∗,7.96875)}

#guard frameDescribe.failures.map toString == []

-- `pow` (DataHaskell `x ^ i`, `i` an `Int`): no definition, the column expression `⟨c $ F, i $ F⟩xexp`, the exponent a
-- literal or a column; libm `pow` is exact on these, a negative base with an integer exponent included
open Rel.Programs.prelude frameData in
rel_program framePow where
    obj F : f64
    obj L : i64
    a : P ⟶ L ≜ {(0,-2),(1,3),(2,0),(3,1)}
    e : P ⟶ L ≜ {(0,3),(1,2),(2,0),(3,5)}
    b : P ⟶ F ≜ {(0,1.5),(1,-0.5),(2,4.0)}
    three : P ⟶ L ≜ ⊤ {(∗,3)}
    check ⟨a $ F, three $ F⟩xexp = {(0,-8.0),(1,27.0),(2,0.0),(3,1.0)}
    check ⟨a $ F, e $ F⟩xexp = {(0,-8.0),(1,9.0),(2,1.0),(3,1.0)}
    check ⟨b, ⊤ {(∗,2.0)}⟩xexp = {(0,2.25),(1,0.25),(2,16.0)}
    check ⟨b, e $ F⟩xexp = {(0,3.375),(1,0.25),(2,1.0)}
    -- derive `v^v` on the fixture: `v = 5 3 5 1 7 2 1 3`
    check x ⟨𝟙, ⟨π₂ $ F, π₂ $ F⟩xexp⟩ = {(0,((B,5),3125.0)),(1,((A,3),27.0)),(2,((B,5),3125.0)),(3,((C,1),1.0)),
      (4,((A,7),823543.0)),(5,((C,2),4.0)),(6,((B,1),1.0)),(7,((A,3),27.0))}

-- by hand: `(-2)^3 = -8`, `3^3 = 27`, `0^3 = 0`; `3^2 = 9`, `0^0 = 1`, `1^5 = 1`; `1.5^2 = 2.25`, `(-0.5)^2 = 0.25`,
-- `1.5^3 = 3.375`, `4^0 = 1`; `5^5 = 3125`, `7^7 = 823543`
#guard framePow.failures.map toString == []

-- `fround` (DataHaskell, Haskell's `round`: half to even, float to integral): no definition, the row `round : F ⟶ L`
open Rel.Programs.prelude frameData in
rel_program frameRound where
    obj F : f64
    obj L : i64
    c : P ⟶ F ≜ {(0,0.5),(1,1.5),(2,2.5),(3,-0.5),(4,-1.5),(5,2.4),(6,2.6),(7,-2.6)}
    cr : P ⟶ L ≜ c round
    check cr = {(0,0),(1,2),(2,2),(3,0),(4,-2),(5,2),(6,3),(7,-3)}
    -- derive `round v` on a frame whose `v` is `f64`
    y : P ⟶ K×F ≜ {(0,(A,2.5)),(1,(B,-2.6)),(2,(C,3.5))}
    yr : P ⟶ (K×F)×L ≜ y ⟨𝟙, π₂ round⟩
    check yr = {(0,((A,2.5),2)),(1,((B,-2.6),-3)),(2,((C,3.5),4))}

-- by hand: ties `0.5 1.5 2.5 -0.5 -1.5` to the even `0 2 2 -0 -2` (`-0` is the `i64` `0`), `2.4 2.6 -2.6` to
-- `2 3 -3`; derive: `2.5 -2.6 3.5` to `2 -3 4`
#guard frameRound.failures.map toString == []

end Rel.Lang.TestFrameCols
