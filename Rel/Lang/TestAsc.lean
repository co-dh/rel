import Rel.Programs.Prelude

/-! The row `asc(P)` (q's `asc` of a set: `j ↦` the `j`-th smallest element of `dom P`) and the prelude's `iasc(c)`
    (q's `iasc` of a column: `asc(ran⟨c,dom(c)⟩)π₂`, the positions of `c` in stable ascending order), at a declared
    object and at the unbounded `obj N`. Expected rows worked by hand. -/

namespace Rel.Lang.TestAsc

open Rel.Programs.prelude in
rel_program ascT where
    obj N = 0…9
    obj Z = -5…5
    obj K = {A,B}
    s : N ⟶ N ≜ {(7,7),(3,3),(9,9),(2,2)}
    a : N ⟶ N ≜ {(0,7),(1,3),(2,7)}
    b : N ⟶ N ≜ {(0,4),(1,1),(2,4),(3,1),(4,0)}
    c : N ⟶ Z ≜ {(0,2),(1,-3),(2,0),(3,-5),(4,2)}
    k : N ⟶ K ≜ {(0,B),(1,A)}
    as : N ⟶ N ≜ asc(s)
    ia : N ⟶ N ≜ iasc(a)
    ib : N ⟶ N ≜ iasc(b)
    ic : N ⟶ N ≜ iasc(c)
    ik : N ⟶ N ≜ iasc(k)
    check as = {(0,2),(1,3),(2,7),(3,9)}
    check ia = {(0,1),(1,0),(2,2)}
    check ib = {(0,4),(1,1),(2,3),(3,0),(4,2)}
    check ic = {(0,3),(1,1),(2,2),(3,0),(4,4)}
    check ik = {(0,1),(1,0)}

-- by hand: `as`: {7,3,9,2} ascending is 2 3 7 9. `ia`: `7 3 7`, pairs (7,0) (3,1) (7,2) ascending (3,1) (7,0) (7,2),
-- so 1 0 2. `ib`: `4 1 4 1 0`, pairs ascending (0,4) (1,1) (1,3) (4,0) (4,2), so 4 1 3 0 2. `ic`: `2 -3 0 -5 2`,
-- (-5,3) (-3,1) (0,2) (2,0) (2,4), so 3 1 2 0 4. `ik`: `B A`, `K`'s elements in declared order A < B, so 1 0.
#guard ascT.failures.isEmpty

-- At the unbounded object a row runs on demand (§a), so each is read at a frame's positions: `as` at `dom(b)`'s
-- 0…4, of which `asc(s)` has 0…3; `iasc(x)` at `dom(x)`, its own domain.
open Rel.Programs.prelude in
rel_program ascU where
    obj N
    s : N ⟶ N ≜ {(7,7),(3,3),(9,9),(2,2)}
    a : N ⟶ N ≜ {(0,7),(1,3),(2,7)}
    b : N ⟶ N ≜ {(0,4),(1,1),(2,4),(3,1),(4,0)}
    c : N ⟶ N ≜ {(0,2),(1,-3),(2,0),(3,-5),(4,2)}
    as : N ⟶ N ≜ dom(b) asc(s)
    ia : N ⟶ N ≜ dom(a) iasc(a)
    ib : N ⟶ N ≜ dom(b) iasc(b)
    ic : N ⟶ N ≜ dom(c) iasc(c)
    check as = {(0,2),(1,3),(2,7),(3,9)}
    check ia = {(0,1),(1,0),(2,2)}
    check ib = {(0,4),(1,1),(2,3),(3,0),(4,2)}
    check ic = {(0,3),(1,1),(2,2),(3,0),(4,4)}

#guard ascU.failures.isEmpty

end Rel.Lang.TestAsc
