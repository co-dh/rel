import Rel.Programs.FrameJoin

/-! Plan M3: the frame verbs on a GENERATED frame of `n` rows, row `i` = (`i mod 100`, `i`), built from `𝟙` and
    `mod` at a declared object, checked against closed forms. With `T = n/100` rows per key, the rows of key `k < 50`
    are `i = k + 100t`, `t < T`, so the filter keeps `50T` rows, key `k`'s sum is `Tk + 100·T(T−1)/2`, and the join
    with `y : k ↦ (k, k+1)` keeps every kept row and sums its `k+1` to `T·(1+…+50) = 1275T`. Here `n = 1000`: at `n = 10⁴`, `M` must hold 499900 (at 10⁵, 49999000).
    At 8cf4a7f `Λ` at a declared object still grows with |M|: at |M| = 5·10⁵ the list `Λ` of 1000 rows takes
    39.5 s, `count` of it 78.5 s, `summarize(sum)` 58.9 s, so the pipeline at 10⁴ did not finish in 4 minutes (measured). -/

namespace Rel.Lang.TestFrameScale

open Rel.Programs.prelude Rel.Programs.frame Rel.Programs.frameGroup Rel.Programs.frameJoin in
rel_program frameScaleT where
    -- one object for positions, keys and values, holding the largest sum: 49T + 50T(T−1) = 4990, 1275T = 12750
    obj M = 0…19999
    -- `i < b` as `i div b = 0`: `dom(< b̂°)` reads `<` on M×M, |M|² pairs
    below(b : 1 ⟶ M) : M ⟶ M ≜ dom(⟨𝟙, ⊤ b⟩div {(0,0)})
    x : M ⟶ M×M ≜ below({(∗,1000)}) ⟨⟨𝟙, ⊤ {(∗,100)}⟩mod, 𝟙⟩
    y : M ⟶ M×M ≜ below({(∗,100)}) ⟨𝟙, succ⟩
    -- each relation argument is cut to the rows of its frame, `ran(x)`: bare, the three cost this module 15 s and
    -- 6.4 GB against 7.4 s and 1.4 GB (measured), though arguments are passed on demand
    xf : M ⟶ M×M ≜ filterBy(ran(x) dom(π₁ below({(∗,50)})), x)
    check count(xf) = {(∗,500)}
    -- group `j` is key `j` (keys 0…49 first occur at positions 0…49): `(j, 10j + 4500)`
    check aggregate(ran(xf) π₁, F(xf π₂) sum, xf) = below({(∗,50)}) ⟨𝟙, ⟨𝟙, ⊤ {(∗,10)}⟩times ⟨𝟙, ⊤ {(∗,4500)}⟩plus⟩
    j : M ⟶ (M×M)×(M×M) ≜ innerJoin(ran(xf) π₁, ran(y) π₁, xf, y)
    check count(j) = {(∗,500)}
    check summarize(F(j π₂ π₂) sum, j) = {(∗,12750)}

#guard frameScaleT.ok

-- The same pipeline at the unbounded `N`: the positions
-- `0…n−1` as decimal digit strings, `⟨P, D⟩` pairing each number of `P` with each digit `d` into `10p + d`.
-- At `N` no row reads a universe, so `n = 10⁵` runs where `M` stops below 10⁴; this module builds in 7.5 s with the
-- three joins, 6.4 s without (measured).
open Rel.Programs.prelude in
rel_program scaleN where
    obj N
    D : 1 ⟶ N ≜ {(∗,0),(∗,1),(∗,2),(∗,3),(∗,4),(∗,5),(∗,6),(∗,7),(∗,8),(∗,9)}
    d2 : 1 ⟶ N ≜ ⟨D, D⟩ ⟨⟨π₁, ⊤ {(∗,10)}⟩times, π₂⟩plus
    d3 : 1 ⟶ N ≜ ⟨d2, D⟩ ⟨⟨π₁, ⊤ {(∗,10)}⟩times, π₂⟩plus
    k50 : N ⟶ N ≜ ran(⟨{(∗,0),(∗,1),(∗,2),(∗,3),(∗,4)}, D⟩ ⟨⟨π₁, ⊤ {(∗,10)}⟩times, π₂⟩plus)
    y : N ⟶ N×N ≜ ran(d2) ⟨𝟙, succ⟩

-- n = 10³, T = 10
open Rel.Programs.prelude Rel.Programs.frame Rel.Programs.frameGroup Rel.Programs.frameJoin scaleN in
rel_program frameScaleN3 where
    x : N ⟶ N×N ≜ ran(d3) ⟨⟨𝟙, ⊤ {(∗,100)}⟩mod, 𝟙⟩
    xf : N ⟶ N×N ≜ filterBy(dom(π₁ k50), x)
    check count(xf) = {(∗,500)}
    j : N ⟶ (N×N)×(N×N) ≜ innerJoin(π₁, π₁, xf, y)
    check count(j) = {(∗,500)}
    check summarize(F(j π₂ π₂) sum, j) = {(∗,12750)}
    check aggregate(π₁, F(xf π₂) sum, xf) = k50 ⟨𝟙, ⟨⟨𝟙, ⊤ {(∗,10)}⟩times, ⊤ {(∗,4500)}⟩plus⟩
    -- the comparison rows, `x π₂ = i`: `take`/`drop` of n/2 sum to h(h−1)/2 and the rest of n(n−1)/2; the window of
    -- 3 ending at `i` sums all three times but rows 0, 1, n−2, n−1: 3n(n−1)/2 − 3n + 4
    t : N ⟶ N×N ≜ take({(∗,500)}, x)
    check summarize(F(t π₂) sum, t) = {(∗,124750)}
    dr : N ⟶ N×N ≜ drop({(∗,500)}, x)
    check summarize(F(dr π₂) sum, dr) = {(∗,374750)}
    r : N ⟶ N ≜ rolling({(∗,3)}, F(x π₂) sum, x)
    check summarize(F(r) sum, r) = {(∗,1495504)}
    check cumAgg(F(x π₂) sum, x) = ran(d3) ⟨⟨𝟙, succ⟩times, ⊤ {(∗,2)}⟩div
    -- `c` holds a value at key 0, i.e. at multiples of 100: `fills` reads `100·(i div 100)`
    c : N ⟶ N+1 ≜ dom(x) tot(dom(x π₁ {(0,0)}) x π₂)
    check fills(c) [𝟙, {(∗,0)}] = ran(d3) ⟨⟨𝟙, ⊤ {(∗,100)}⟩div, ⊤ {(∗,100)}⟩times
    -- `q` is `x` one step later: row `i ≥ 100` meets `i − 99` of its key, so Σ (i − 99) = (n−100)(n−99)/2
    q : N ⟶ N×N ≜ x ⟨π₁, π₂ succ⟩
    a : N ⟶ (N×N)×((N×N)+1) ≜ aj(π₁, π₂, π₁, π₂, x, q)
    check summarize(F(a π₂ [π₂, {(∗,0)}]) sum, a) = {(∗,405450)}
    check median(π₂, x) = {(∗,499)}
    check topK({(∗,3)}, π₂, x) = {(0,(99,999)),(1,(98,998)),(2,(97,997))}
    -- sorted position `p` holds key `p div T`, row `p div T + 100·(p mod T)`
    check sortBy(π₁, x) = ran(d3) ⟨⟨𝟙, ⊤ {(∗,10)}⟩div, ⟨⟨⟨𝟙, ⊤ {(∗,10)}⟩mod, ⊤ {(∗,100)}⟩times, ⟨𝟙, ⊤ {(∗,10)}⟩div⟩plus⟩

#guard frameScaleN3.ok

-- n = 10⁴, T = 100: key `k` sums to `100k + 50·100·99`
open Rel.Programs.prelude Rel.Programs.frame Rel.Programs.frameGroup Rel.Programs.frameJoin scaleN in
rel_program frameScaleN4 where
    d4 : 1 ⟶ N ≜ ⟨d3, D⟩ ⟨⟨π₁, ⊤ {(∗,10)}⟩times, π₂⟩plus
    x : N ⟶ N×N ≜ ran(d4) ⟨⟨𝟙, ⊤ {(∗,100)}⟩mod, 𝟙⟩
    xf : N ⟶ N×N ≜ filterBy(dom(π₁ k50), x)
    check count(xf) = {(∗,5000)}
    j : N ⟶ (N×N)×(N×N) ≜ innerJoin(π₁, π₁, xf, y)
    check count(j) = {(∗,5000)}
    check summarize(F(j π₂ π₂) sum, j) = {(∗,127500)}
    check aggregate(π₁, F(xf π₂) sum, xf) = k50 ⟨𝟙, ⟨⟨𝟙, ⊤ {(∗,100)}⟩times, ⊤ {(∗,495000)}⟩plus⟩
    -- the comparison rows as at 10³; `cumAgg` (271 s) and `aj` (214 s) are left out (measured)
    t : N ⟶ N×N ≜ take({(∗,5000)}, x)
    check summarize(F(t π₂) sum, t) = {(∗,12497500)}
    dr : N ⟶ N×N ≜ drop({(∗,5000)}, x)
    check summarize(F(dr π₂) sum, dr) = {(∗,37497500)}
    r : N ⟶ N ≜ rolling({(∗,3)}, F(x π₂) sum, x)
    check summarize(F(r) sum, r) = {(∗,149955004)}
    c : N ⟶ N+1 ≜ dom(x) tot(dom(x π₁ {(0,0)}) x π₂)
    check fills(c) [𝟙, {(∗,0)}] = ran(d4) ⟨⟨𝟙, ⊤ {(∗,100)}⟩div, ⊤ {(∗,100)}⟩times
    check median(π₂, x) = {(∗,4999)}
    check topK({(∗,3)}, π₂, x) = {(0,(99,9999)),(1,(98,9998)),(2,(97,9997))}
    check sortBy(π₁, x) = ran(d4) ⟨⟨𝟙, ⊤ {(∗,100)}⟩div, ⟨⟨⟨𝟙, ⊤ {(∗,100)}⟩mod, ⊤ {(∗,100)}⟩times, ⟨𝟙, ⊤ {(∗,100)}⟩div⟩plus⟩

#guard frameScaleN4.ok

-- n = 10⁵, T = 1000: key `k` sums to `1000k + 50·1000·999`
open Rel.Programs.prelude Rel.Programs.frame Rel.Programs.frameGroup Rel.Programs.frameJoin scaleN in
rel_program frameScaleN5 where
    d4 : 1 ⟶ N ≜ ⟨d3, D⟩ ⟨⟨π₁, ⊤ {(∗,10)}⟩times, π₂⟩plus
    d5 : 1 ⟶ N ≜ ⟨d4, D⟩ ⟨⟨π₁, ⊤ {(∗,10)}⟩times, π₂⟩plus
    x : N ⟶ N×N ≜ ran(d5) ⟨⟨𝟙, ⊤ {(∗,100)}⟩mod, 𝟙⟩
    xf : N ⟶ N×N ≜ filterBy(dom(π₁ k50), x)
    check count(xf) = {(∗,50000)}
    j : N ⟶ (N×N)×(N×N) ≜ innerJoin(π₁, π₁, xf, y)
    check count(j) = {(∗,50000)}
    check summarize(F(j π₂ π₂) sum, j) = {(∗,1275000)}
    check aggregate(π₁, F(xf π₂) sum, xf) = k50 ⟨𝟙, ⟨⟨𝟙, ⊤ {(∗,1000)}⟩times, ⊤ {(∗,49950000)}⟩plus⟩
    -- the comparison rows as at 10³ that finish within a minute; `fills` takes 81 s and 6.9 GB (measured)
    t : N ⟶ N×N ≜ take({(∗,50000)}, x)
    check summarize(F(t π₂) sum, t) = {(∗,1249975000)}
    dr : N ⟶ N×N ≜ drop({(∗,50000)}, x)
    check summarize(F(dr π₂) sum, dr) = {(∗,3749975000)}
    r : N ⟶ N ≜ rolling({(∗,3)}, F(x π₂) sum, x)
    check summarize(F(r) sum, r) = {(∗,14999550004)}
    check median(π₂, x) = {(∗,49999)}
    check topK({(∗,3)}, π₂, x) = {(0,(99,99999)),(1,(98,99998)),(2,(97,99997))}
    check sortBy(π₁, x) = ran(d5) ⟨⟨𝟙, ⊤ {(∗,1000)}⟩div, ⟨⟨⟨𝟙, ⊤ {(∗,1000)}⟩mod, ⊤ {(∗,100)}⟩times, ⟨𝟙, ⊤ {(∗,1000)}⟩div⟩plus⟩

#guard frameScaleN5.ok

end Rel.Lang.TestFrameScale
