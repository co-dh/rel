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

end Rel.Lang.TestDemand
