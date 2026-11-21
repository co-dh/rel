import Rel.Programs.FrameJoin

/-! The dataframe library on columns at declared typed objects (`obj D : date`, `obj F : f64`): the verbs that only
    compare, order and match values run unchanged; arithmetic at those atoms is refused (pinned below). Expected rows
    worked by hand. -/

namespace Rel.Lang.TestFrameTyped

open Rel.Programs.prelude Rel.Programs.frame Rel.Programs.frameGroup Rel.Programs.frameJoin in
rel_program frameTypedT where
    obj K = {A,B,C}
    obj N
    obj D : date
    obj F : f64
    x : N ⟶ D×F ≜ {(0,(19000,2.5)),(1,(18990,-1.5)),(2,(19000,-0.5)),(3,(19005,10))}
    -- by `f`: -1.5 at 1, -0.5 at 2, 2.5 at 0, 10 at 3 (negatives below zero: the order is the number's)
    check sortBy(π₂, x) = {(0,(18990,-1.5)),(1,(19000,-0.5)),(2,(19000,2.5)),(3,(19005,10))}
    check sortByDesc(π₂, x) = {(0,(19005,10)),(1,(19000,2.5)),(2,(19000,-0.5)),(3,(18990,-1.5))}
    -- by date, ties (19000 at 0 and 2) in position order
    check sortBy(π₁, x) = {(0,(18990,-1.5)),(1,(19000,2.5)),(2,(19000,-0.5)),(3,(19005,10))}
    check topK({(∗,2)}, π₂, x) = {(0,(19005,10)),(1,(19000,2.5))}
    -- dates by first occurrence: 19000 (0, 2), 18990 (1), 19005 (3)
    check distinct(x π₁) = {(0,19000),(1,18990),(2,19005)}
    vd : N ⟶ D×N ≜ valueCounts(π₁, x)
    check vd = {(0,(19000,2)),(1,(18990,1)),(2,(19005,1))}
    check aggregate(π₁, F(x π₂) Λ(∋) last, x) = {(0,(19000,2.5)),(1,(18990,-1.5)),(2,(19005,10))}
    check summarize(F(x π₂) Λ(∋) head, x) = {(∗,-1.5)}
    check summarize(F(x π₂) Λ(∋) last, x) = {(∗,10)}
    check summarize(F(x π₁) Λ(∋) last, x) = {(∗,19005)}
    -- join on a date (x's 0 2 meet y's 0, x's 3 meets y's 1) and on a float (x's 2 meets yf's 0, x's 3 yf's 1)
    y : N ⟶ D×K ≜ {(0,(19000,A)),(1,(19005,B))}
    ij : N ⟶ (D×F)×(D×K) ≜ innerJoin(π₁, π₁, x, y)
    check ij = {(0,((19000,2.5),(19000,A))),(1,((19000,-0.5),(19000,A))),(2,((19005,10),(19005,B)))}
    yf : N ⟶ F×K ≜ {(0,(-0.5,A)),(1,(10,B))}
    ijf : N ⟶ (D×F)×(F×K) ≜ innerJoin(π₂, π₁, x, yf)
    check ijf = {(0,((19000,-0.5),(-0.5,A))),(1,((19005,10),(10,B)))}
    -- an integer column cast to `f64`, then sorted: 5 3 7 → 3 5 7
    v : N ⟶ N ≜ {(0,5),(1,3),(2,7)}
    check sortBy(𝟙, v $ F) = {(0,3),(1,5),(2,7)}

#guard frameTypedT.ok

-- `aj` with a date time column: its `sums` runs along the time, which must be a number object
/-- error: line 53, col 31: `Rel.Lang.TestFrameTyped.ajDateT.Rel.Programs.frameJoin.aj.form.1.1.1.1.0.0.num.0.2.1.0.1.1`: an object variable is D here; its constant is not generic over it, a number object -/
#guard_msgs in
open Rel.Programs.prelude Rel.Programs.frame Rel.Programs.frameGroup Rel.Programs.frameJoin in
rel_program ajDateT where
    obj K = {A,B,C}
    obj N
    obj D : date
    q : N ⟶ K×(D×N) ≜ {(0,(A,(18990,1))),(1,(A,(19001,2))),(2,(B,(18000,3)))}
    xa : N ⟶ K×D ≜ {(0,(A,19000)),(1,(A,19010)),(2,(B,17000)),(3,(A,18000))}
    a : N ⟶ (K×D)×(K×(D×N)) ≜ aj(π₁, π₂, π₁, π₂ π₁, xa, q) ⟨π₁, π₂ [𝟙, {(∗,(C,(0,0)))}]⟩

-- `daysBetween`: `minus` at a date, or the date read as its day number
/-- error: line 62, col 23: minus on D: D is an object of date, and minus runs on objects of i64, f32, f64 only -/
#guard_msgs in
rel_program daysMinusT where
    obj N
    obj D : date
    d : N ⟶ D ≜ {(0,19000),(1,18990)}
    e : N ⟶ D ≜ ⟨d, d⟩minus

-- the days between two dates: the composition `⟨a $ N, b $ N⟩minus` of their day counts (`daysBetween`, S8)
rel_program daysCastT where
    obj N
    obj D : date
    d : N ⟶ D ≜ {(0,19000),(1,18990)}
    e : N ⟶ D ≜ {(0,18995),(1,19000)}
    check d $ N = {(0,19000),(1,18990)}
    -- by hand: 19000 − 18995 = 5, 18990 − 19000 = −10
    check ⟨d $ N, e $ N⟩minus = {(0,5),(1,-10)}

#guard daysCastT.failures.map toString == []

-- the orders and `max`/`min` at a `date` and an `f64` column: the integer order of the days, IEEE's order
open Rel.Programs.prelude Rel.Programs.frame in
rel_program frameOrderT where
    obj N
    obj D : date
    obj G : f64
    x : N ⟶ D×G ≜ {(0,(19000,2.5)),(1,(18990,-1.5)),(2,(19000,-0.5)),(3,(19005,10))}
    -- by hand: 18990 (1) is below the other three, 19000 (0, 2) below 19005 (3)
    check dom(x π₁ < (x π₁)°) = {(0,0),(1,1),(2,2)}
    check x π₂ ⟨𝟙, 𝟙⟩max = {(0,2.5),(1,-1.5),(2,-0.5),(3,10)}
    check x π₁ ⟨𝟙, 𝟙⟩max = {(0,19000),(1,18990),(2,19000),(3,19005)}
    check x π₁ ⟨𝟙, {(18990,18995),(19000,18995),(19005,18995)}⟩min = {(0,18995),(1,18990),(2,18995),(3,18995)}
    check x π₁ ⟨𝟙, {(18990,18995),(19000,18995),(19005,18995)}⟩max = {(0,19000),(1,18995),(2,19000),(3,19005)}

#guard frameOrderT.failures.map toString == []

-- `sums` with its positions at a `date` and at a `datetime`: each key's prefix sums in the order of the positions
rel_program sumsTimeT where
    obj K = {A,B}
    obj N
    obj D : date
    obj T : datetime
    x : K×D ⟶ N ≜ {((A,19000),3),((A,18990),4),((B,19000),5),((A,19005),-2)}
    -- by hand, A in day order: 18990 → 4, 19000 → 4+3 = 7, 19005 → 7−2 = 5; B has no earlier row: 19000 → 5; the
    -- day 19000 is a position of both keys
    check sums(x) = {((A,18990),4),((A,19000),7),((A,19005),5),((B,19000),5)}
    y : K×T ⟶ N ≜ {((A,1000000000),1),((A,-5),2),((B,7),10)}
    -- a negative datetime first: −5 → 2, 10^9 → 2+1 = 3; B: 10
    check sums(y) = {((A,-5),2),((A,1000000000),3),((B,7),10)}

#guard sumsTimeT.failures.map toString == []

-- positions at an `f64`: its canon order is its bits' until S5, so `sums` is refused by name
/-- error: -/
#guard_msgs in
rel_program sumsFloatPosT where
    obj K = {A}
    obj N
    obj G : f64
    x : K×G ⟶ N ≜ {((A,1.5),1)}
    s : K×G ⟶ N ≜ sums(x)

-- `sum` and `sums` at an `f64` column: refused by name (a float sum waits on the summation order, S4)
/-- error: line 100, col 5: sum on G: G is an object of f64, and sum runs on objects of i64 only -/
#guard_msgs in
open Rel.Programs.prelude Rel.Programs.frame in
rel_program sumFloatT where
    obj N
    obj G : f64
    f : N ⟶ G ≜ {(0,2.5),(1,-1.5)}
    s : 1 ⟶ G ≜ summarize(F(f) sum, f)

/-- error: line 109, col 17: `Rel.Lang.TestFrameTyped.cumSumFloatT.Rel.Programs.frame.cumSum.num.1.1`: an object variable is G here; its constant is not generic over it, a number object -/
#guard_msgs in
open Rel.Programs.prelude Rel.Programs.frame in
rel_program cumSumFloatT where
    obj N
    obj G : f64
    f : N ⟶ G ≜ {(0,2.5),(1,-1.5)}
    s : N ⟶ G ≜ cumSum(f)

end Rel.Lang.TestFrameTyped
