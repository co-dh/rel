import Rel.Programs.Prelude

/-! `⊤` between two bounded neighbours and `×` beside a sum's `𝟙`, at an unbounded `obj N`: `⊤`'s value side runs on
    the range its right neighbour bounds (`GenK.top`, `GenK.id` on either side), and the universe of `N+1` runs on the
    values in demand (`uniPart`). The same rows at a declared finite `N`. Expected rows worked by hand. -/

namespace Rel.Lang.TestTopProd

open Rel.Programs.prelude in
rel_program topProdN where
    obj N
    x : N ⟶ N ≜ {(0,30),(1,10),(2,40),(3,20)}
    y : N ⟶ N ≜ {(5,1),(7,2)}
    J : N ⟶ N ≜ {(0,5),(2,6)}
    tt : N ⟶ N+1 ≜ (J inl) ∪ ((𝟙 − dom(J)) ⊤(N,1) inr)
    check dom(x) ⊤ dom(y) = {(0,5),(0,7),(1,5),(1,7),(2,5),(2,7),(3,5),(3,7)}
    check dom(x) ⊤(N,1) ⊤(1,N) dom(y) = {(0,5),(0,7),(1,5),(1,7),(2,5),(2,7),(3,5),(3,7)}
    check asc(ran(⟨𝟙, x⟩)) (x × 𝟙) = {(0,(30,30)),(1,(10,10)),(2,(40,40)),(3,(20,20))}
    check asc(ran(⟨𝟙, dom(x) tt⟩)) (x × 𝟙) (𝟙 × inl°) = {(0,(30,5)),(2,(40,6))}

open Rel.Programs.prelude in
rel_program topProdFin where
    obj N = 0…99
    x : N ⟶ N ≜ {(0,30),(1,10),(2,40),(3,20)}
    y : N ⟶ N ≜ {(5,1),(7,2)}
    J : N ⟶ N ≜ {(0,5),(2,6)}
    tt : N ⟶ N+1 ≜ (J inl) ∪ ((𝟙 − dom(J)) ⊤(N,1) inr)
    check dom(x) ⊤ dom(y) = {(0,5),(0,7),(1,5),(1,7),(2,5),(2,7),(3,5),(3,7)}
    check dom(x) ⊤(N,1) ⊤(1,N) dom(y) = {(0,5),(0,7),(1,5),(1,7),(2,5),(2,7),(3,5),(3,7)}
    check asc(ran(⟨𝟙, x⟩)) (x × 𝟙) = {(0,(30,30)),(1,(10,10)),(2,(40,40)),(3,(20,20))}
    check asc(ran(⟨𝟙, dom(x) tt⟩)) (x × 𝟙) (𝟙 × inl°) = {(0,(30,5)),(2,(40,6))}

-- by hand: `dom(x) ⊤ dom(y)` is every key of `x` (0…3) to every key of `y` (5, 7), eight pairs; through the unit
-- `⊤(N,1) ⊤(1,N)` is the same product. `ran⟨𝟙, x⟩` is `(0,30) (1,10) (2,40) (3,20)`, in value order by the distinct
-- first sides, so `asc` numbers them 0…3 and `x × 𝟙` maps `(i, x(i))` to `(x(i), x(i))`. `tt` sends `0 ↦ inl 5`,
-- `2 ↦ inl 6` and the other keys of `x` to `inr`; `asc` numbers `(0,inl 5) (1,inr) (2,inl 6) (3,inr)` 0…3 by the
-- first side, `x × 𝟙` maps the first side by `x`, and `𝟙 × inl°` keeps the `inl` rows: `0 ↦ (30,5)`, `2 ↦ (40,6)`.
#guard topProdN.ok
#guard topProdFin.ok

end Rel.Lang.TestTopProd
