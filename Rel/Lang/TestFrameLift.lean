import Rel.Lang.TestFrameCols

/-! The function lifts of `Rel.Programs.frame` (dataframe gap F7) on the fixture of `TestFrameCols`
    (`k = B A B C A C B A`, `v = 5 3 5 1 7 2 1 3`): each element function is a definition of this program, passed to
    `lift`, `lift2`, `apply`, `bind`, `nullLift`, `nullLift2` as a relation; expected rows worked by hand. -/

namespace Rel.Lang.TestFrameLift

open Rel.Programs.prelude Rel.Programs.frame Rel.Lang.TestFrameCols.frameData in
rel_program frameLiftT where
    -- the user's element functions: `2n`, `max(n, m)`, `a + 2b`, and `n` below 6 or else the null
    dbl : N ⟶ N ≜ ⟨𝟙, 𝟙⟩plus
    atLeast(m : 1 ⟶ N) : N ⟶ N ≜ ⟨𝟙, ⊤ m⟩max
    wsum : N×N ⟶ N ≜ ⟨π₁, π₂ dbl⟩plus
    low : N ⟶ 1+N ≜ tot(dom(< {(6,∗)}))
    check x lift(dbl, π₂) = {(0,10),(1,6),(2,10),(3,2),(4,14),(5,4),(6,2),(7,6)}
    -- a definition with a parameter, applied before it is passed
    check x lift(atLeast({(∗,3)}), π₂) = {(0,5),(1,3),(2,5),(3,3),(4,7),(5,3),(6,3),(7,3)}
    -- a partial `f` (`v > 2`): rows 3 5 6 have no image
    check x lift(big, π₂) = {(0,5),(1,3),(2,5),(4,7),(7,3)}
    -- `a + 2b` on the pairs (1,2) (3,0) (4,5)
    y : P ⟶ N×N ≜ {(0,(1,2)),(1,(3,0)),(2,(4,5))}
    check y lift2(wsum, π₁, π₂) = {(0,5),(1,3),(2,14)}
    -- `v` doubled, moved in front of `k`
    check apply(dbl, π₂, π₁, x) = {(0,(10,B)),(1,(6,A)),(2,(10,B)),(3,(2,C)),(4,(14,A)),(5,(4,C)),(6,(2,B)),(7,(6,A))}
    -- nullable `nc`: 5 · 5 · 7 · · 3; `n2`: · · 4 · · · · 1; the null read as 40
    nc : P ⟶ 1+N ≜ dom(x) tot({(0,5),(2,5),(4,7),(7,3)})
    n2 : P ⟶ 1+N ≜ dom(x) tot({(2,4),(7,1)})
    check nullLift(dbl, nc) [{(∗,40)}, 𝟙] = {(0,10),(1,40),(2,10),(3,40),(4,14),(5,40),(6,40),(7,6)}
    -- `low` sends 7 to the null as well
    check bind(low, nc) [{(∗,40)}, 𝟙] = {(0,5),(1,40),(2,5),(3,40),(4,40),(5,40),(6,40),(7,3)}
    -- both present only at 2 (5 + 2·4) and 7 (3 + 2·1)
    check nullLift2(wsum, nc, n2) [{(∗,40)}, 𝟙] = {(0,40),(1,40),(2,13),(3,40),(4,40),(5,40),(6,40),(7,5)}

#guard frameLiftT.ok

end Rel.Lang.TestFrameLift
