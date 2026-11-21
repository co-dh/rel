import Rel.Programs.FrameJoin

/-! Five queries of TPC-H shape (Q1, Q3, Q4, Q6, Q13) over a generated star schema at the unbounded `N`, each a
    frame-verb composition over named columns, checked against closed forms at 10³ and 10⁴ lineitem rows.
    Lineitem row `i` has digits `d0 = i mod 10`, `d1 = (i div 10) mod 10`, `d2 = (i div 100) mod 10` and `H = n/1000`
    blocks of 1000; order `o = i div 10 = 10a + b`, customer `c = 5a + b div 3`. Money is integer cents, dates day
    numbers: `price = i+1`, `discount = d0` (%), `quantity = 1 + 5·d1`, `orderdate = 20·d2`, `shipdate = 20·d2 + d0 + 1`. -/

namespace Rel.Lang.TestFrameBench

open Rel.Programs.prelude Rel.Programs.frame Rel.Programs.frameGroup Rel.Programs.frameJoin in
rel_program benchN where
    obj N
    schema LI = {orderkey : N, partkey : N, quantity : N, price : N, discount : N, shipdate : N, returnflag : N, linestatus : N}
    schema Ord = {orderkey : N, custkey : N, orderdate : N, priority : N}
    schema Cust = {custkey : N, segment : N}
    D : 1 ⟶ N ≜ {(∗,0),(∗,1),(∗,2),(∗,3),(∗,4),(∗,5),(∗,6),(∗,7),(∗,8),(∗,9)}
    F5 : 1 ⟶ N ≜ {(∗,0),(∗,1),(∗,2),(∗,3),(∗,4)}
    -- each `p` of `P` with each digit `d` as `10p + d`: `ext` applied k times to `D` is `0…10^(k+1)−1`
    ext(P : 1 ⟶ N) : 1 ⟶ N ≜ ⟨P, D⟩ ⟨⟨π₁, ⊤ {(∗,10)}⟩times, π₂⟩plus
    tenth : N ⟶ N ≜ ⟨𝟙, ⊤ {(∗,10)}⟩div
    d0 : N ⟶ N ≜ ⟨𝟙, ⊤ {(∗,10)}⟩mod

    lineitem(P : 1 ⟶ N) : N ⟶ LI ≜ ran(P) ⟨⟨⟨⟨⟨⟨⟨tenth, ⟨𝟙, ⊤ {(∗,200)}⟩mod⟩, tenth d0 ⟨⟨𝟙, ⊤ {(∗,5)}⟩times, ⊤ {(∗,1)}⟩plus⟩, succ⟩, d0⟩, ⟨tenth tenth d0 ⟨𝟙, ⊤ {(∗,20)}⟩times, d0 succ⟩plus⟩, d0 ⟨𝟙, ⊤ {(∗,3)}⟩mod⟩, tenth d0 ⟨𝟙, ⊤ {(∗,2)}⟩mod⟩
    orders(P : 1 ⟶ N) : N ⟶ Ord ≜ ran(P) ⟨⟨⟨𝟙, ⟨tenth ⟨𝟙, ⊤ {(∗,5)}⟩times, d0 ⟨𝟙, ⊤ {(∗,3)}⟩div⟩plus⟩, tenth d0 ⟨𝟙, ⊤ {(∗,20)}⟩times⟩, ⟨𝟙, ⊤ {(∗,5)}⟩mod⟩
    customer(P : 1 ⟶ N) : N ⟶ Cust ≜ ran(P) ⟨𝟙, ⟨𝟙, ⊤ {(∗,5)}⟩mod⟩
    -- price·(100 − discount), the discounted price in cents·%
    rev : LI ⟶ N ≜ ⟨col LI "price", ⟨⊤ {(∗,100)}, col LI "discount"⟩minus⟩times

    -- B1 (Q1): shipdate ≤ 100 keeps d2 < 5; per (returnflag, linestatus): Σ quantity, Σ price, Σ rev, count, by key
    b1(x : N ⟶ LI) : N ⟶ (N×N)×(N×(N×(N×N))) ≜ sortBy(π₁, aggregate(⟨col LI "returnflag", col LI "linestatus"⟩, ⟨F(f col LI "quantity") sum, ⟨F(f col LI "price") sum, ⟨F(f rev) sum, length⟩⟩⟩, f)) where f ≜ filterBy(dom(col LI "shipdate" ≤ {(100,∗)}), x)
    -- B3 (Q3): segment 1, orderdate < 85, shipdate > 85; Σ rev per order, the 10 largest
    -- a join's position object is free: the inner join of the two is a definition so its frame is at `N`
    co(c : N ⟶ Cust, o : N ⟶ Ord) : N ⟶ Cust×Ord ≜ innerJoin(col Cust "custkey", col Ord "custkey", filterBy(dom(col Cust "segment" {(1,1)}), c), filterBy(dom(col Ord "orderdate" < {(85,∗)}), o))
    b3(c : N ⟶ Cust, o : N ⟶ Ord, l : N ⟶ LI) : N ⟶ N×N ≜ topK({(∗,10)}, π₂, aggregate(π₂ col LI "orderkey", F(j π₂ rev) sum, j)) where j ≜ innerJoin(π₂ col Ord "orderkey", col LI "orderkey", co(c, o), filterBy(dom(col LI "shipdate" > {(85,∗)}), l))
    -- B4 (Q4): orders with 20 ≤ orderdate < 60 having a line of quantity < 20; count per priority, by priority
    b4(o : N ⟶ Ord, l : N ⟶ LI) : N ⟶ N×N ≜ sortBy(π₁, valueCounts(col Ord "priority", semiJoin(col Ord "orderkey", col LI "orderkey", of, lf))) where of ≜ filterBy(dom(col Ord "orderdate" ≥ {(20,∗)}) dom(col Ord "orderdate" < {(60,∗)}), o), lf ≜ filterBy(dom(col LI "quantity" < {(20,∗)}), l)
    -- B6 (Q6): 20 ≤ shipdate < 60, 5 ≤ discount ≤ 7, quantity < 24; Σ price·discount
    b6(x : N ⟶ LI) : 1 ⟶ N ≜ summarize(F(f ⟨col LI "price", col LI "discount"⟩times) sum, f) where f ≜ filterBy(dom(col LI "shipdate" ≥ {(20,∗)}) dom(col LI "shipdate" < {(60,∗)}) dom(col LI "discount" ≥ {(5,∗)}) dom(col LI "discount" ≤ {(7,∗)}) dom(col LI "quantity" < {(24,∗)}), x)
    -- B13 (Q13): orders per customer, 0 for none (the null side counts 0), then customers per order count
    b13(c : N ⟶ Cust, o : N ⟶ Ord) : N ⟶ N×N ≜ sortByDesc(π₂, valueCounts(π₂, aggregate(π₁ col Cust "custkey", F(lj π₂ [⊤ {(∗,1)}, {(∗,0)}]) sum, lj))) where lj ≜ leftJoin(col Cust "custkey", col Ord "custkey", c, o)

-- n = 10³ lineitem rows, 10² orders, 50 customers: H = 1, A = n/100 = 10
open Rel.Programs.prelude benchN in
rel_program bench3 where
    li : N ⟶ LI ≜ lineitem(ext(ext(D)))
    od : N ⟶ Ord ≜ orders(ext(D))
    cu : N ⟶ Cust ≜ customer(ext(F5))
    -- group (r,s): d0 ∈ G_r (g of them), d1 ∈ B_s, d2 < 5: count 25gH, Σ qty 5gH(5 + 5ΣB_s),
    -- Σ price 12500gH(H−1) + 5000gH + 50gHΣB + 25HΣG + 25gH, Σ rev Σ_{G}(100−d0)(12500H(H−1) + 5000H + 50HΣB + 25H(d0+1))
    check b1(li) = {(0,((0,0),(2100,(24550,(2343400,100))))),(1,((0,1),(2600,(25550,(2438900,100))))),
      (2,((1,0),(1575,(18375,(1763550,75))))),(3,((1,1),(1950,(19125,(1835550,75))))),
      (4,((2,0),(1575,(18450,(1752300,75))))),(5,((2,1),(1950,(19200,(1823550,75)))))}
    -- orders 10a + b, a ≡ 4 (10), b ∈ {3,4,5}, lines d0 ≥ 5: Σ_{l=5..9}(10o + l + 1)(100 − l) = 4650o + 3710
    check b3(cu, od, li) = {(0,(45,212960)),(1,(44,208310)),(2,(43,203660))}
    -- d2 ∈ {1,2}, b ≤ 3: priority b, 2·A/10 = 2H orders each
    check b4(od, li) = {(0,(0,2)),(1,(1,2)),(2,(2,2)),(3,(3,2))}
    -- Σ_{d0=5..7} d0·Σ_{h,d2∈{1,2},d1≤4}(i+1) = 90000H(H−1) + 31880H
    check b6(li) = {(∗,31880)}
    -- c = 5a + r: r ≤ 2 has 3 orders (b = 3r…3r+2), r = 3 one (b = 9), r = 4 none: 3A, A, A customers
    check b13(cu, od) = {(0,(3,30)),(1,(1,10)),(2,(0,10))}

#guard bench3.failures.map toString == []

-- n = 10⁴: H = 10, A = 100, the same closed forms
open Rel.Programs.prelude benchN in
rel_program bench4 where
    li : N ⟶ LI ≜ lineitem(ext(ext(ext(D))))
    od : N ⟶ Ord ≜ orders(ext(ext(D)))
    cu : N ⟶ Cust ≜ customer(ext(ext(F5)))
    check b1(li) = {(0,((0,0),(21000,(4745500,(453184000,1000))))),(1,((0,1),(26000,(4755500,(454139000,1000))))),
      (2,((1,0),(15750,(3558750,(341635500,750))))),(3,((1,1),(19500,(3566250,(342355500,750))))),
      (4,((2,0),(15750,(3559500,(338148000,750))))),(5,((2,1),(19500,(3567000,(338860500,750)))))}
    -- the 10 largest o: a = 94, 84, 74 with b = 5, 4, 3, then a = 64, b = 5
    check b3(cu, od, li) = {(0,(945,4397960)),(1,(944,4393310)),(2,(943,4388660)),(3,(845,3932960)),(4,(844,3928310)),
      (5,(843,3923660)),(6,(745,3467960)),(7,(744,3463310)),(8,(743,3458660)),(9,(645,3002960))}
    check b4(od, li) = {(0,(0,20)),(1,(1,20)),(2,(2,20)),(3,(3,20))}
    check b6(li) = {(∗,8418800)}
    check b13(cu, od) = {(0,(3,300)),(1,(1,100)),(2,(0,100))}

#guard bench4.failures.map toString == []

-- n = 10⁵: orders 10⁴, customers 5000; B3's revenue is 4650o + 3710 whatever n, and the survivors are a ≡ 4 (10), b ∈ {3,4,5}
-- as above, so the 10 largest o are a = 994, 984, 974 with b = 5, 4, 3, then a = 964, b = 5 (each a step of 465000)
open Rel.Programs.prelude benchN in
rel_program bench5 where
    li : N ⟶ LI ≜ lineitem(ext(ext(ext(ext(D)))))
    od : N ⟶ Ord ≜ orders(ext(ext(ext(D))))
    cu : N ⟶ Cust ≜ customer(ext(ext(ext(F5))))
    check b3(cu, od, li) = {(0,(9945,46247960)),(1,(9944,46243310)),(2,(9943,46238660)),(3,(9845,45782960)),(4,(9844,45778310)),
      (5,(9843,45773660)),(6,(9745,45317960)),(7,(9744,45313310)),(8,(9743,45308660)),(9,(9645,44852960))}

#guard bench5.failures.map toString == []

-- `joinOn`'s `x × y` at 1500 · 55001 pairs (below the pair bound): read only on the 1500 pairs `J` selects (`i = j`
-- for `i < 1500`), never built whole; the pair spelling `⟨π₁ x, π₂ y⟩` runs the same plan
open Rel.Programs.prelude Rel.Programs.frame Rel.Programs.frameGroup Rel.Programs.frameJoin benchN in
rel_program joinBig where
    x : N ⟶ N ≜ ran(ext(ext(ext(D)))) dom(𝟙 < {(1500,∗)})
    y : N ⟶ N ≜ ran(ext(ext(ext(ext(D))))) dom(𝟙 ≤ {(55000,∗)})
    check count(innerJoin(𝟙, 𝟙, x, y)) = {(∗,1500)}
    check count(asc(ran(⟨𝟙, J(𝟙, 𝟙, x, y)⟩)) ⟨π₁ x, π₂ y⟩) = {(∗,1500)}

#guard joinBig.failures.map toString == []

end Rel.Lang.TestFrameBench
