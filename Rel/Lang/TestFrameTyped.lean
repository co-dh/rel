import Rel.Programs.FrameJoin

/-! The dataframe library on columns at declared typed objects (`obj D : date`, `obj F : f64`): the verbs that only
    compare, order and match values run unchanged; `minus` at a date, `sum`/`sums` at `f64` and `aj` along a date
    are refused (pinned below), and `daysBetween` reads dates as day counts. Expected rows worked by hand. -/

namespace Rel.Lang.TestFrameTyped

open Rel.Programs.prelude Rel.Programs.frame Rel.Programs.frameGroup Rel.Programs.frameJoin in
rel_program frameTypedT where
    obj K = {A,B,C}
    obj N
    obj D : date
    obj F : f64
    x : N ⟶ D×F ≜ {(0,(2022.01.08,2.5)),(1,(2021.12.29,-1.5)),(2,(2022.01.08,-0.5)),(3,(2022.01.13,10))}
    -- by `f`: -1.5 at 1, -0.5 at 2, 2.5 at 0, 10 at 3 (negatives below zero: the order is the number's)
    check sortBy(π₂, x) = {(0,(2021.12.29,-1.5)),(1,(2022.01.08,-0.5)),(2,(2022.01.08,2.5)),(3,(2022.01.13,10))}
    check sortByDesc(π₂, x) = {(0,(2022.01.13,10)),(1,(2022.01.08,2.5)),(2,(2022.01.08,-0.5)),(3,(2021.12.29,-1.5))}
    -- by date, ties (2022.01.08 at 0 and 2) in position order
    check sortBy(π₁, x) = {(0,(2021.12.29,-1.5)),(1,(2022.01.08,2.5)),(2,(2022.01.08,-0.5)),(3,(2022.01.13,10))}
    check topK({(∗,2)}, π₂, x) = {(0,(2022.01.13,10)),(1,(2022.01.08,2.5))}
    -- dates by first occurrence: 2022.01.08 (0, 2), 2021.12.29 (1), 2022.01.13 (3)
    check distinct(x π₁) = {(0,2022.01.08),(1,2021.12.29),(2,2022.01.13)}
    vd : N ⟶ D×N ≜ valueCounts(π₁, x)
    check vd = {(0,(2022.01.08,2)),(1,(2021.12.29,1)),(2,(2022.01.13,1))}
    check aggregate(π₁, F(x π₂) Λ(∋) last, x) = {(0,(2022.01.08,2.5)),(1,(2021.12.29,-1.5)),(2,(2022.01.13,10))}
    check summarize(F(x π₂) Λ(∋) head, x) = {(∗,-1.5)}
    check summarize(F(x π₂) Λ(∋) last, x) = {(∗,10)}
    check summarize(F(x π₁) Λ(∋) last, x) = {(∗,2022.01.13)}
    -- join on a date (x's 0 2 meet y's 0, x's 3 meets y's 1) and on a float (x's 2 meets yf's 0, x's 3 yf's 1)
    y : N ⟶ D×K ≜ {(0,(2022.01.08,A)),(1,(2022.01.13,B))}
    ij : N ⟶ (D×F)×(D×K) ≜ innerJoin(π₁, π₁, x, y)
    check ij = {(0,((2022.01.08,2.5),(2022.01.08,A))),(1,((2022.01.08,-0.5),(2022.01.08,A))),(2,((2022.01.13,10),(2022.01.13,B)))}
    yf : N ⟶ F×K ≜ {(0,(-0.5,A)),(1,(10,B))}
    ijf : N ⟶ (D×F)×(F×K) ≜ innerJoin(π₂, π₁, x, yf)
    check ijf = {(0,((2022.01.08,-0.5),(-0.5,A))),(1,((2022.01.13,10),(10,B)))}
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
    q : N ⟶ K×(D×N) ≜ {(0,(A,(2021.12.29,1))),(1,(A,(2022.01.09,2))),(2,(B,(2019.04.14,3)))}
    xa : N ⟶ K×D ≜ {(0,(A,2022.01.08)),(1,(A,2022.01.18)),(2,(B,2016.07.18)),(3,(A,2019.04.14))}
    a : N ⟶ (K×D)×(K×(D×N)) ≜ aj(π₁, π₂, π₁, π₂ π₁, xa, q) ⟨π₁, π₂ [𝟙, {(∗,(C,(0,0)))}]⟩

-- `minus` at a date stays refused: a difference of days is no date; `daysBetween` reads each as its day count
/-- error: line 62, col 23: minus on D: D is an object of date, and minus runs on objects of i64, f32, f64 only -/
#guard_msgs in
rel_program daysMinusT where
    obj N
    obj D : date
    d : N ⟶ D ≜ {(0,2022.01.08),(1,2021.12.29)}
    e : N ⟶ D ≜ ⟨d, d⟩minus

-- `daysBetween(a, b) ≜ ⟨a $ Z, b $ Z⟩minus` at the library's `D : date`
open Rel.Programs.frameStat in
rel_program daysCastT where
    obj N
    d : N ⟶ D ≜ {(0,2022.01.08),(1,2021.12.29),(2,2024.03.01)}
    e : N ⟶ D ≜ {(0,2022.01.03),(1,2022.01.08),(2,2024.01.01)}
    -- 2022.01.08 is day 19000 since 1970.01.01, 2021.12.29 day 18990
    check d $ Z = {(0,19000),(1,18990),(2,19783)}
    -- by hand: 8 − 3 = 5; 29 Dec to 8 Jan is −10; January's 31 days and leap February's 29 give 60
    check daysBetween(d, e) = {(0,5),(1,-10),(2,60)}

#guard daysCastT.failures.map toString == []

-- the orders and `max`/`min` at a `date` and an `f64` column: the integer order of the days, IEEE's order
open Rel.Programs.prelude Rel.Programs.frame in
rel_program frameOrderT where
    obj N
    obj D : date
    obj G : f64
    x : N ⟶ D×G ≜ {(0,(2022.01.08,2.5)),(1,(2021.12.29,-1.5)),(2,(2022.01.08,-0.5)),(3,(2022.01.13,10))}
    -- by hand: 2021.12.29 (1) is below the other three, 2022.01.08 (0, 2) below 2022.01.13 (3)
    check dom(x π₁ < (x π₁)°) = {(0,0),(1,1),(2,2)}
    check x π₂ ⟨𝟙, 𝟙⟩max = {(0,2.5),(1,-1.5),(2,-0.5),(3,10)}
    check x π₁ ⟨𝟙, 𝟙⟩max = {(0,2022.01.08),(1,2021.12.29),(2,2022.01.08),(3,2022.01.13)}
    check x π₁ ⟨𝟙, {(2021.12.29,2022.01.03),(2022.01.08,2022.01.03),(2022.01.13,2022.01.03)}⟩min = {(0,2022.01.03),(1,2021.12.29),(2,2022.01.03),(3,2022.01.03)}
    check x π₁ ⟨𝟙, {(2021.12.29,2022.01.03),(2022.01.08,2022.01.03),(2022.01.13,2022.01.03)}⟩max = {(0,2022.01.08),(1,2022.01.03),(2,2022.01.08),(3,2022.01.13)}

#guard frameOrderT.failures.map toString == []

-- `sum` and `sums` at an `f64` column: refused by name (a float sum waits on the summation order, S4)
/-- error: line 101, col 5: sum on G: G is an object of f64, and sum runs on objects of i64 only -/
#guard_msgs in
open Rel.Programs.prelude Rel.Programs.frame in
rel_program sumFloatT where
    obj N
    obj G : f64
    f : N ⟶ G ≜ {(0,2.5),(1,-1.5)}
    s : 1 ⟶ G ≜ summarize(F(f) sum, f)

/-- error: line 110, col 17: `Rel.Lang.TestFrameTyped.cumSumFloatT.Rel.Programs.frame.cumSum.num.1.1`: an object variable is G here; its constant is not generic over it, a number object -/
#guard_msgs in
open Rel.Programs.prelude Rel.Programs.frame in
rel_program cumSumFloatT where
    obj N
    obj G : f64
    f : N ⟶ G ≜ {(0,2.5),(1,-1.5)}
    s : N ⟶ G ≜ cumSum(f)

end Rel.Lang.TestFrameTyped
