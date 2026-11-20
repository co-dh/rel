import Rel.Lang.TestFrameCols
import Rel.Programs.FrameJoin

/-! The null rows of `Rel.Programs.frame`/`frameJoin` (plan M4) on the fixture of `TestFrameCols`, against rows
    worked by hand. A sum literal does not parse, so a null is built with `tot` and read back through an impute. -/

namespace Rel.Lang.TestFrameNull

open Rel.Programs.prelude Rel.Programs.frame Rel.Programs.frameGroup Rel.Programs.frameJoin
  Rel.Lang.TestFrameCols.frameData in
rel_program frameNullT where
    obj Z = -10…40
    -- a nullable column beside `k`: a value at positions 0 2 4 7, null at 1 3 5 6
    nc : P ⟶ N+1 ≜ dom(x) tot({(0,5),(2,5),(4,7),(7,3)})
    xn : P ⟶ K×(N+1) ≜ ⟨x π₁, nc⟩
    check filterJust(π₂, xn) ⟨π₁, π₂ inl°⟩ = {(0,(B,5)),(1,(B,5)),(2,(A,7)),(3,(A,3))}
    check filterNothing(π₂, xn) π₁ = {(0,A),(1,C),(2,C),(3,B)}
    -- `v = 5 3 5 1 7 2 1 3` moved down one and two rows; the null reads as 40
    check shift({(∗,1)}, x π₂) [𝟙, {(∗,40)}] = {(0,40),(1,5),(2,3),(3,5),(4,1),(5,7),(6,2),(7,1)}
    check shift({(∗,2)}, x π₂) [𝟙, {(∗,40)}] = {(0,40),(1,40),(2,5),(3,3),(4,5),(5,1),(6,7),(7,2)}
    -- `v` in `Z`, so a difference may be negative: 3−5, 5−3, 1−5, 7−1, 2−7, 1−2, 3−1
    v : P ⟶ Z ≜ {(0,5),(1,3),(2,5),(3,1),(4,7),(5,2),(6,1),(7,3)}
    check diff({(∗,1)}, v) [𝟙, {(∗,40)}] = {(0,40),(1,-2),(2,2),(3,-4),(4,6),(5,-5),(6,-1),(7,2)}
    -- `y` has keys A C: x's A rows 1 4 7 meet (A,9), its C rows 3 5 meet (C,8), its B rows 0 2 6 the null,
    -- read as (B,0); one row per x row since each key occurs once in `y`
    y : P ⟶ K×N ≜ {(0,(A,9)),(1,(C,8))}
    lj : P ⟶ (K×N)×(K×N) ≜ leftJoin(π₁, π₁, x, y) ⟨π₁, π₂ [𝟙, {(∗,(B,0))}]⟩
    check lj = {(0,((B,5),(B,0))),(1,((A,3),(A,9))),(2,((B,5),(B,0))),(3,((C,1),(C,8))),(4,((A,7),(A,9))),
      (5,((C,2),(C,8))),(6,((B,1),(B,0))),(7,((A,3),(A,9)))}

#guard frameNullT.ok

end Rel.Lang.TestFrameNull
