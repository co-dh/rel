import Rel.Programs.FrameJoin

/-! Plan M3: the frame verbs on a GENERATED frame of `n` rows, row `i` = (`i mod 100`, `i`), built from `𝟙` and
    `mod` at a declared object, checked against closed forms. With `T = n/100` rows per key, the rows of key `k < 50`
    are `i = k + 100t`, `t < T`, so the filter keeps `50T` rows, key `k`'s sum is `Tk + 100·T(T−1)/2`, and the join
    with `y : k ↦ (k, k+1)` keeps every kept row and sums its `k+1` to `T·(1+…+50) = 1275T`. Here `n = 1000`: at `n = 10⁴`, `M` must hold 499900, and `length`/`sum`
    at a declared object cost (list length)·|M| (measured: `count` of 1000 rows takes 1.5 s, 11 s, 22 s at
    |M| = 4·10³, 10⁵, 2·10⁵), so one `count` of 5000 rows would take minutes; 10⁴ did not finish in 4 minutes. -/

namespace Rel.Lang.TestFrameScale

open Rel.Programs.prelude Rel.Programs.frame Rel.Programs.frameGroup Rel.Programs.frameJoin in
rel_program frameScaleT where
    -- one object for positions, keys and values, holding the largest sum: 49T + 50T(T−1) = 4990, 1275T = 12750
    obj M = 0…19999
    -- `i < b` as `i div b = 0`: `dom(< b̂°)` reads `<` on M×M, |M|² pairs
    below(b : 1 ⟶ M) : M ⟶ M ≜ dom(⟨𝟙, ⊤ b⟩div {(0,0)})
    x : M ⟶ M×M ≜ below({(∗,1000)}) ⟨⟨𝟙, ⊤ {(∗,100)}⟩mod, 𝟙⟩
    y : M ⟶ M×M ≜ below({(∗,100)}) ⟨𝟙, succ⟩
    -- a relation argument of a generic constant is read on its whole source, here M×M (|M|² rows): each argument
    -- below is cut to the rows of its frame first, `ran(x)`
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
-- At `N` no row reads a universe, so `n = 10⁵` runs where `M` stops below 10⁴; this module builds in 35 s with the
-- three joins, 6.9 s without (measured).
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

#guard frameScaleN5.ok

end Rel.Lang.TestFrameScale
