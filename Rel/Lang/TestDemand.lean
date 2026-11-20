import Rel.Programs.Prelude

/-! An operand beside a table runs on that table's sides: `∩` and `−` hand a table's `dom` and `ran` to the lazy
    operand (`GenK.bound`), and `R × S` in a context whose domain is known runs as `⟨π₁ R, π₂ S⟩` on those pairs.
    Expected rows worked by hand. -/

namespace Rel.Lang.TestDemand

open Rel.Programs.prelude in
rel_program demandT where
    obj N = 0…99
    x : N ⟶ N ≜ {(0,30),(1,10),(2,40),(3,20)}
    q : N ⟶ N ≜ {(10,20),(30,10),(20,20),(40,30)}
    t : N ⟶ N ≜ {(0,1),(1,2),(2,3),(0,3)}
    p : N ⟶ N×N ≜ {(5,(0,1)),(6,(2,3))}
    check q ∩ < = {(10,20)}
    check < ∩ q = {(10,20)}
    check q ∩ ≤ = {(10,20),(20,20)}
    check q − < = {(30,10),(20,20),(40,30)}
    check t ∩ (x < x°) = {(1,2)}
    check (x < x°) ∩ t = {(1,2)}
    check t − (x < x°) = {(0,1),(2,3),(0,3)}
    check p (x×x) = {(5,(30,10)),(6,(40,20))}
    p₂ : N ⟶ N×N ≜ {(5,(0,10)),(6,(2,30))}
    check p₂ (x×q) = {(5,(30,20)),(6,(40,10))}

-- by hand: `q ∩ <` keeps the pairs `a < b` of `q`: `(10,20)` only (`30 > 10`, `20 = 20`, `40 > 30`); `≤` adds
-- `(20,20)`; `q − <` is the other three. `x < x°` relates `i` to `j` where `x(i) < x(j)`: of `t`'s pairs only
-- `(1,2)` (`10 < 40`); `(0,1)` is `30 < 10`, `(2,3)` is `40 < 20`, `(0,3)` is `30 < 20`, all false.
-- `p(x×x)`: `(0,1) ↦ (x(0),x(1)) = (30,10)`, `(2,3) ↦ (40,20)`. `p₂(x×q)`: `(0,10) ↦ (x(0),q(10)) = (30,20)`,
-- `(2,30) ↦ (40,10)`.
#guard demandT.ok

/-! `⟨R, S⟩` relates `a` only where both do, so a table operand (`K`, `c`) runs first and its domain bounds the lazy
    `𝟙` (`GenK.pairK`): the same rows at the unbounded `obj N` as at a declared finite one. -/

open Rel.Programs.prelude in
rel_program pairN where
    obj N
    K : N ⟶ N ≜ {(1,7),(3,5),(3,8)}
    c : N ⟶ N ≜ {(0,30),(1,10),(2,40),(3,20)}
    check ran(⟨𝟙, K⟩) = {((1,7),(1,7)),((3,5),(3,5)),((3,8),(3,8))}
    check ⟨K, 𝟙⟩ = {(1,(7,1)),(3,(5,3)),(3,(8,3))}
    check K ⟨𝟙, 𝟙⟩ = {(1,(7,7)),(3,(5,5)),(3,(8,8))}
    check asc(ran(⟨c, 𝟙⟩)) π₂ = {(0,1),(1,3),(2,0),(3,2)}
    bad : N ⟶ N×N ≜ ⟨𝟙, 𝟙⟩

open Rel.Programs.prelude in
rel_program pairFin where
    obj N = 0…49
    K : N ⟶ N ≜ {(1,7),(3,5),(3,8)}
    c : N ⟶ N ≜ {(0,30),(1,10),(2,40),(3,20)}
    check ran(⟨𝟙, K⟩) = {((1,7),(1,7)),((3,5),(3,5)),((3,8),(3,8))}
    check ⟨K, 𝟙⟩ = {(1,(7,1)),(3,(5,3)),(3,(8,3))}
    check K ⟨𝟙, 𝟙⟩ = {(1,(7,7)),(3,(5,5)),(3,(8,8))}
    check asc(ran(⟨c, 𝟙⟩)) π₂ = {(0,1),(1,3),(2,0),(3,2)}

-- by hand: `⟨𝟙, K⟩` relates `a` to `(a, b)` for each `(a, b)` of `K`, so its range is `K`'s three pairs, each to
-- itself; `⟨K, 𝟙⟩` puts `K`'s value first. `K ⟨𝟙, 𝟙⟩` doubles each value of `K`. `ran⟨c, 𝟙⟩` is the pairs
-- `(c(i), i)`: in value order `(10,1) (20,3) (30,0) (40,2)`, so `asc` numbers them 0…3 and `π₂` reads the positions
-- `1 3 0 2` (q's `iasc 30 10 40 20`). `bad` pairs two lazy `𝟙` with nothing to bound either: its one failure.
#eval pairN.failures.map toString
#guard pairFin.ok

end Rel.Lang.TestDemand
