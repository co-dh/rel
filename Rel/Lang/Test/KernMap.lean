import Rel.Lang.Test.Common

namespace Rel.Lang.Test

open Tab Rel.Lang Rel.Alg Rel

/-! The kernel path's row `F` (`Tab.map`): `kernMap` runs it.
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

#guard kernMap.ok
-- not vacuous: the kernel tables have rows where the input does, none on the empty demand
#guard ["f1", "f2"].all fun d => ((get kernMap.expanded d .long (.arr .long)).map (·.n.toNat != 0)) == some true
#guard ((get kernMap.expanded "f3" .long (.arr .long)).map (·.n.toNat)) == some 0
#guard ((get kernMap.expanded "sz" .long .long).map (·.n.toNat != 0)) == some true

end Rel.Lang.Test
