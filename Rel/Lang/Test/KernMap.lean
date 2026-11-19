import Rel.Lang.Test.Common

namespace Rel.Lang.Test

open Tab Rel.Lang Rel.Alg Rel

/-! The kernel path's row `F` (`Tab.map`): `kernMap` runs it, `kernMapOld` is the same definitions on the old layer.
    `x` holds an empty cell (2), a singleton (7), equal elements (4, 6) and an element `r` relates to nothing (9, in 8);
    `z` is empty (an empty demand). `f1` maps by a function (`succ`, one pass); `f2` by `r`, which gives `1` two images
    and `9` none (the fold); `sz` is a hylo over the list functor (`kids`'s target `[E]`), the size of each subtree. -/
open Rel.Programs.prelude in
rel_program kernMap where
    obj N = 0…10
    obj E = 0…6
    x : N ⟶ [N] ≜ {(1,3 1 2),(2,[]),(3,1 2),(4,2 2),(5,4 4),(6,5 1 1 3),(7,[3]),(8,2 9)}
    z : N ⟶ N ≜ x 𝟘
    r : N ⟶ N ≜ {(1,1),(1,7),(2,2),(3,3),(4,4),(5,5)}
    f1 : N ⟶ [N] ≜ x F(succ)
    f2 : N ⟶ [N] ≜ x F(r)
    f3 : N ⟶ [N] ≜ z x F(succ)
    boss : E ⟶ E ≜ {(1,0),(2,0),(3,1),(4,3),(5,3)}
    kids : E ⟶ [E] ≜ Λ(boss°)
    S : E×[N] ⟶ N ≜ π₂ sum succ
    sz : E ⟶ N ≜ hylo(⟨𝟙, kids⟩, S)

open Rel.Programs.prelude in
set_option rel.kernel false in
rel_program kernMapOld where
    obj N = 0…10
    obj E = 0…6
    x : N ⟶ [N] ≜ {(1,3 1 2),(2,[]),(3,1 2),(4,2 2),(5,4 4),(6,5 1 1 3),(7,[3]),(8,2 9)}
    z : N ⟶ N ≜ x 𝟘
    r : N ⟶ N ≜ {(1,1),(1,7),(2,2),(3,3),(4,4),(5,5)}
    f1 : N ⟶ [N] ≜ x F(succ)
    f2 : N ⟶ [N] ≜ x F(r)
    f3 : N ⟶ [N] ≜ z x F(succ)
    boss : E ⟶ E ≜ {(1,0),(2,0),(3,1),(4,3),(5,3)}
    kids : E ⟶ [E] ≜ Λ(boss°)
    S : E×[N] ⟶ N ≜ π₂ sum succ
    sz : E ⟶ N ≜ hylo(⟨𝟙, kids⟩, S)

-- A cyclic coalgebra over the list functor on the kernel path (`TestHylo.hyloCycle` on the old layer): it fails,
-- never a silent `𝟘`.
open Rel.Programs.prelude in
rel_program kernMapCycle where
    obj E = {a,b,m}
    obj N = 0…40
    next : E ⟶ E ≜ {(a,b),(b,a)}
    S : E×[N] ⟶ N ≜ π₂ sum
    bad : E ⟶ N ≜ hylo(⟨𝟙, Λ(next)⟩, S)

#guard kernMapCycle.kernel && kernMapCycle.failures.map (·.msg) == [s!"bad: the coalgebra c at line " ++
  s!"{decl_line% kernMapCycle + 5}, col 24 reaches a node from itself, so it is not well-founded there (2 of 3 nodes)"]

#guard kernMap.kernel && !kernMapOld.kernel && kernMap.ok && kernMapOld.ok
#guard ["f1", "f2", "f3"].all (sameK kernMap.expanded kernMapOld.expanded · .long (.arr .long))
#guard ["sz"].all (sameK kernMap.expanded kernMapOld.expanded · .long .long)
-- not vacuous: the kernel tables have rows where the input does, none on the empty demand
#guard ["f1", "f2"].all fun d => ((get kernMap.expanded d .long (.arr .long)).map (·.n.toNat != 0)) == some true
#guard ((get kernMap.expanded "f3" .long (.arr .long)).map (·.n.toNat)) == some 0
#guard ((get kernMap.expanded "sz" .long .long).map (·.n.toNat != 0)) == some true

end Rel.Lang.Test
