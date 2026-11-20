import Rel.Programs.FrameJoin

/-! Five analytics queries, each a pipeline of frame verbs, on GENERATED frames at the unbounded `N` (the generator
    of `TestFrameScale`: `n` rows `0…n−1` as decimal digit strings), checked against closed forms in `T`, the rows per
    key. `queryN` holds the queries once; a sized program feeds them `n` rows. -/

namespace Rel.Lang.TestFrameQuery

open Rel.Programs.prelude Rel.Programs.frame Rel.Programs.frameGroup Rel.Programs.frameJoin in
rel_program queryN where
    obj N
    D : 1 ⟶ N ≜ {(∗,0),(∗,1),(∗,2),(∗,3),(∗,4),(∗,5),(∗,6),(∗,7),(∗,8),(∗,9)}
    -- each number `p` of `P` with each digit `d` as `10p + d`: `ext` applied k times to `D` is `0…10^(k+1)−1`
    ext(P : 1 ⟶ N) : 1 ⟶ N ≜ ⟨P, D⟩ ⟨⟨π₁, ⊤ {(∗,10)}⟩times, π₂⟩plus
    k50 : N ⟶ N ≜ ran(ext({(∗,0),(∗,1),(∗,2),(∗,3),(∗,4)}))

    -- row i = (i mod 100, i): key and value
    sales(P : 1 ⟶ N) : N ⟶ N×N ≜ ran(P) ⟨⟨𝟙, ⊤ {(∗,100)}⟩mod, 𝟙⟩
    -- Q1: keys < 50, per key (sum, count), the 3 keys of largest integer mean, as (key, mean)
    q1(x : N ⟶ N×N) : N ⟶ N×N ≜ topK({(∗,3)}, π₂ div, aggregate(π₁, F(f π₂) ⟨sum, length⟩, f)) ⟨π₁, π₂ div⟩ where f ≜ filterBy(dom(π₁ k50), x)

    -- row i = (i mod 4, ((i div 4) mod 5, i)): two key columns and a value
    cells(P : 1 ⟶ N) : N ⟶ N×(N×N) ≜ ran(P) ⟨⟨𝟙, ⊤ {(∗,4)}⟩mod, ⟨⟨𝟙, ⊤ {(∗,4)}⟩div ⟨𝟙, ⊤ {(∗,5)}⟩mod, 𝟙⟩⟩
    -- Q2: sum per (a, b), largest sum first
    q2(x : N ⟶ N×(N×N)) : N ⟶ (N×N)×N ≜ sortByDesc(π₂, aggregate(⟨π₁, π₂ π₁⟩, F(x π₂ π₂) sum, x))

    -- dimension row p < 100 = (p, (p mod 4, p div 50)): product, region, flag
    dim : N ⟶ N×(N×N) ≜ ran(ext(D)) ⟨𝟙, ⟨⟨𝟙, ⊤ {(∗,4)}⟩mod, ⟨𝟙, ⊤ {(∗,50)}⟩div⟩⟩
    -- Q3: sales joined to products, flag 0 only, sum of value per region
    q3(x : N ⟶ N×N) : N ⟶ N×N ≜ aggregate(π₂ π₂ π₁, F(f π₁ π₂) sum, f) where f ≜ filterBy(dom(π₂ π₂ π₂ {(0,0)}), innerJoin(π₁, π₁, x, dim))

    -- row i = (i mod 10, i div 10)
    ticks(P : 1 ⟶ N) : N ⟶ N×N ≜ ran(P) ⟨⟨𝟙, ⊤ {(∗,10)}⟩mod, ⟨𝟙, ⊤ {(∗,10)}⟩div⟩
    -- cumAgg within each key `a` (polars cum_sum().over(a)): `cumAgg`'s `≥` cut to the pairs of equal key
    cumAggBy(a : β ⟶ γ, f : [ν] ⟶ δ, x : ν ⟶ β) : ν ⟶ δ ≜ agg((dom(x) ≥ dom(x)) ∩ (x a (x a)°), f)
    -- Q4: sorted by key, (key, running sum of the value within the key)
    q4(x : N ⟶ N×N) : N ⟶ N×N ≜ ⟨s π₁, cumAggBy(π₁, F(s π₂) sum, s)⟩ where s ≜ sortBy(π₁, x)
    -- Q4': the last running sum of each key is the key's total
    q4t(x : N ⟶ N×N) : N ⟶ N×N ≜ aggregate(π₁, F(q4(x) π₂) last, q4(x))

    -- dimension keys 0…49 only: (p, p+1)
    dim50 : N ⟶ N×N ≜ k50 ⟨𝟙, succ⟩
    lj5(x : N ⟶ N×N) : N ⟶ (N×N)×((N×N)+1) ≜ leftJoin(π₁, π₁, x, dim50)
    -- Q5: (unmatched rows, sum of the dimension value over the matched rows)
    q5(x : N ⟶ N×N) : 1 ⟶ N×N ≜ ⟨nulls(π₂, lj5(x)), summarize(F(m π₂ inl° π₂) sum, m)⟩ where m ≜ filterJust(π₂, lj5(x))

-- n = 10³
open Rel.Programs.prelude queryN in
rel_program query3 where
    P : 1 ⟶ N ≜ ext(ext(D))
    -- T = 10: key k sums Tk + 50T(T−1) over T rows, mean k + 50(T−1)
    check q1(sales(P)) = {(0,(49,499)),(1,(48,498)),(2,(47,497))}
    -- T = 50 rows per r = i mod 20 = a + 4b, sum Tr + 10T(T−1); group r is position r, sorted r = 19…0
    check q2(cells(P)) = ran(ext({(∗,0),(∗,1)})) ⟨⊤ {(∗,19)}, 𝟙⟩minus ⟨⟨⟨𝟙, ⊤ {(∗,4)}⟩mod, ⟨𝟙, ⊤ {(∗,4)}⟩div⟩, ⟨⟨𝟙, ⊤ {(∗,50)}⟩times, ⊤ {(∗,24500)}⟩plus⟩
    -- region g: products p < 50, p ≡ g (4): 13,13,12,12 of them summing 312,325,288,300; T·Σp + |S|·50T(T−1)
    check q3(sales(P)) = {(0,(0,61620)),(1,(1,61750)),(2,(2,56880)),(3,(3,57000))}
    -- T = 100 rows per key; sorted row p is (p div T, t = p mod T), running sum 0+…+t
    check q4(ticks(P)) = ran(P) ⟨⟨𝟙, ⊤ {(∗,100)}⟩div, ⟨𝟙, ⊤ {(∗,100)}⟩mod ⟨⟨𝟙, succ⟩times, ⊤ {(∗,2)}⟩div⟩
    check q4t(ticks(P)) = ran(D) ⟨𝟙, ⊤ {(∗,4950)}⟩
    -- keys ≥ 50 unmatched: 50T rows; matched rows sum T(1+…+50)
    check q5(sales(P)) = {(∗,(500,12750))}

#guard query3.failures.map toString == []

end Rel.Lang.TestFrameQuery
