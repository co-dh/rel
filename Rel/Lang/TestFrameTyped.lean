import Rel.Programs.FrameJoin

/-! The dataframe library on columns at declared typed objects (`obj D : date`, `obj F : f64`): the verbs that only
    compare, order and match values run unchanged, as do `sums` at `f64` values and `aj` along a date; `minus` at a
    date and `sum` at `f64` are refused (pinned below), and `daysBetween` reads dates as day counts. Expected rows
    worked by hand. -/

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
    check aggregate(π₁, F(x π₂) ((𝟙÷∋)E(∋)) last, x) = {(0,(2022.01.08,2.5)),(1,(2021.12.29,-1.5)),(2,(2022.01.13,10))}
    check summarize(F(x π₂) ((𝟙÷∋)E(∋)) head, x) = {(∗,-1.5)}
    check summarize(F(x π₂) ((𝟙÷∋)E(∋)) last, x) = {(∗,10)}
    check summarize(F(x π₁) ((𝟙÷∋)E(∋)) last, x) = {(∗,2022.01.13)}
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

-- `aj` with a date time column: its `sums` runs along the days
open Rel.Programs.prelude Rel.Programs.frame Rel.Programs.frameGroup Rel.Programs.frameJoin in
rel_program ajDateT where
    obj K = {A,B,C}
    obj N
    obj D : date
    q : N ⟶ K×(D×N) ≜ {(0,(A,(2021.12.29,1))),(1,(A,(2022.01.09,2))),(2,(B,(2019.04.14,3)))}
    xa : N ⟶ K×D ≜ {(0,(A,2022.01.08)),(1,(A,2022.01.18)),(2,(B,2016.07.18)),(3,(A,2019.04.14))}
    a : N ⟶ (K×D)×(K×(D×N)) ≜ aj(π₁, π₂, π₁, π₂ π₁, xa, q) ⟨π₁, π₂ [{(∗,(C,(0,0)))}, 𝟙]⟩
    -- by hand, per `xa` row the last `q` row of its key at a day ≤ its own: 0 (A,2022.01.08) meets 2021.12.29
    -- (2022.01.09 is later); 1 (A,2022.01.18) meets 2022.01.09; 2 (B,2016.07.18) none (B's 2019.04.14 is later);
    -- 3 (A,2019.04.14) none; none reads (C,(0,0))
    check a = {(0,((A,2022.01.08),(A,(2021.12.29,1)))),(1,((A,2022.01.18),(A,(2022.01.09,2)))),(2,((B,2016.07.18),(C,(0,0)))),(3,((A,2019.04.14),(C,(0,0))))}

#guard ajDateT.failures.map toString == []

-- `minus` at a date stays refused: a difference of days is no date; `daysBetween` reads each as its day count
/-- error: line 67, col 23: minus on D: D is an object of date, and minus runs on objects of i64, f32, f64 only; cast first, `x $ F` with `F` an object of i64, f32, f64 -/
#guard_msgs in
rel_program daysMinusT where
    obj N
    obj D : date
    d : N ⟶ D ≜ {(0,2022.01.08),(1,2021.12.29)}
    e : N ⟶ D ≜ ⟨d, d⟩minus

-- `daysBetween(a, b) ≜ ⟨a $ Z, b $ Z⟩minus`, generic in the date object: here the program's own `D : date`
open Rel.Programs.frameStat in
rel_program daysCastT where
    obj N
    obj D : date
    d : N ⟶ D ≜ {(0,2022.01.08),(1,2021.12.29),(2,2024.03.01)}
    e : N ⟶ D ≜ {(0,2022.01.03),(1,2022.01.08),(2,2024.01.01)}
    -- 2022.01.08 is day 19000 since 1970.01.01; by hand 8 − 3 = 5, 29 Dec to 8 Jan −10, 31 days + leap Feb's 29 = 60
    check d $ Z = {(0,19000),(1,18990),(2,19783)}
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

-- `sums` with its positions at a `date` and at a `datetime`: each key's prefix sums in the order of the positions
rel_program sumsTimeT where
    obj K = {A,B}
    obj N
    obj D : date
    obj T : datetime
    x : K×D ⟶ N ≜ {((A,2022.01.08),3),((A,2021.12.29),4),((B,2022.01.08),5),((A,2022.01.13),-2)}
    -- by hand, A in day order: 2021.12.29 → 4, 2022.01.08 → 4+3 = 7, 2022.01.13 → 7−2 = 5; B has no earlier row:
    -- 2022.01.08 → 5; the day 2022.01.08 is a position of both keys
    check sums(x) = {((A,2021.12.29),4),((A,2022.01.08),7),((A,2022.01.13),5),((B,2022.01.08),5)}
    y : K×T ⟶ N ≜ {((A,1000000000),1),((A,-5),2),((B,7),10)}
    -- a negative datetime first: −5 → 2, 10^9 → 2+1 = 3; B: 10
    check sums(y) = {((A,-5),2),((A,1000000000),3),((B,7),10)}

#guard sumsTimeT.failures.map toString == []

-- positions at an `f64`: its canon order is its bits' until S5, so `sums` is refused by name
/-- error: line 122, col 5: sums' position object G is an object of f64; sums orders positions of u8, i16, i32, i64, char, i8, date, datetime -/
#guard_msgs in
rel_program sumsFloatPosT where
    obj K = {A}
    obj N
    obj G : f64
    x : K×G ⟶ N ≜ {((A,1.5),1)}
    s : K×G ⟶ N ≜ sums(x)

-- `sum` at an `f64` column: the left fold `⦇[0, plus]⦈` of the IEEE sums, from the first element (q's order)
open Rel.Programs.prelude Rel.Programs.frame in
rel_program sumFloatT where
    obj N
    obj G : f64
    -- by hand: 0 + 2.5 = 2.5, then 2.5 − 1.5 = 1
    f : N ⟶ G ≜ {(0,2.5),(1,-1.5)}
    check summarize(F(f) sum, f) = {(∗,1.0)}
    -- by hand, from the left: 0 + 1 = 1, 1 + 1e16 = 1e16 (the spacing there is 2 and the tie rounds to the even
    -- 1e16), 1e16 − 1e16 = 0; from the right it would be 1 + (1e16 − 1e16) = 1
    g : N ⟶ G ≜ {(0,1.0),(1,1e16),(2,-1e16)}
    check summarize(F(g) sum, g) = {(∗,0.0)}

#guard sumFloatT.failures.map toString == []

-- `sums` at `f64` values: one IEEE sum per row, left to right along the positions (q's order)
rel_program sumsFloatT where
    obj K = {A,B}
    obj N
    obj G : f64
    -- by hand, A: 1, then 1 + 1e16 = 1e16 (the spacing there is 2 and the tie rounds to the even 1e16), then
    -- 1e16 − 1e16 = 0, where the exact sum is 1; B: −1.5, then −1.5 + 1.5 = +0
    x : K×N ⟶ G ≜ {((A,0),1.0),((A,1),1e16),((A,2),-1e16),((B,0),-1.5),((B,1),1.5)}
    check sums(x) = {((A,0),1.0),((A,1),1e16),((A,2),0.0),((B,0),-1.5),((B,1),0.0)}
    -- `0 % 0` (NaN) is no row, so position 1 has no value and no sum: 1, then 1 + 3 = 4 at position 2
    z : N ⟶ G ≜ {(0,0.0)}
    nn : N ⟶ G ≜ ⟨z, z⟩%
    p : K×N ⟶ N ≜ {((A,1),0)}
    y : K×N ⟶ G ≜ {((A,0),1.0),((A,2),3.0)} ∪ (p nn)
    check sums(y) = {((A,0),1.0),((A,2),4.0)}
    -- a −0 value: +0 + −0 = +0
    m : K×N ⟶ G ≜ {((A,0),-0.0)}
    check sums(m) = {((A,0),0.0)}

#guard sumsFloatT.failures.map toString == []

-- `sums` at `f32` values (`Lang.sumDen`): each prefix the `f64` sum rounded once to `f32`; `2^24 + 1` is a tie and
-- rounds to the even `2^24`, `2^24 + 2` is exact, where rounding each step would stay at `2^24`
rel_program sumsF32T where
    obj K = {A}
    obj N
    obj H : f32
    x : K×N ⟶ H ≜ {((A,0),16777216.0),((A,1),1.0),((A,2),1.0)}
    check sums(x) = {((A,0),16777216.0),((A,1),16777216.0),((A,2),16777218.0)}

-- `sum` at an `f32` column: added in `f64`, rounded once: `2^24 + 1 + 1` is `2^24 + 2`
open Rel.Programs.prelude Rel.Programs.frame in
rel_program sumF32T where
    obj N
    obj H : f32
    f : N ⟶ H ≜ {(0,16777216.0),(1,1.0),(2,1.0)}
    check summarize(F(f) sum, f) = {(∗,16777218.0)}

-- `0.1 + 0.2` at `f32`: the word `0x3e99999a`, the `f32` nearest `0.3`
open Rel.Programs.prelude Rel.Programs.frame in
rel_program sumF32T2 where
    obj N
    obj H : f32
    f : N ⟶ H ≜ {(0,0.1),(1,0.2)}
    check summarize(F(f) sum, f) = {(∗,0.3)}
-- the word itself: `0.1f`, `0.2f` widened, added in `f64`, rounded once
#guard (Rel.Kernel.Op.eval .fadd (Rel.Kernel.Op.widen32 0x3dcccccd) (Rel.Kernel.Op.widen32 0x3e4ccccd)).toOption.map
  (Rel.Kernel.Op.ftoWord .f32) == some 0x3e99999a

end Rel.Lang.TestFrameTyped
