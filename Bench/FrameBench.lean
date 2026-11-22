import Rel.Lang.TestFrameBench

/-! `TestFrameBench`'s queries at 10³, 10⁴ and 10⁵ lineitem rows, over what a program may cost the gate (`gateMs`). -/

namespace Rel.Lang.TestFrameBench

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

end Rel.Lang.TestFrameBench
