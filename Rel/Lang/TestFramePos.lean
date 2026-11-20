import Rel.Lang.TestFrameCols

/-! The position rows of `Rel.Programs.frame` (plan M1) on the fixture of `TestFrameCols`, against rows worked by
    hand. -/

namespace Rel.Lang.TestFramePos

open Rel.Programs.prelude Rel.Programs.frame Rel.Lang.TestFrameCols.frameData in
rel_program framePos where
    check take({(∗,3)}, x) = {(0,(B,5)),(1,(A,3)),(2,(B,5))}
    check drop({(∗,3)}, x) = {(0,(C,1)),(1,(A,7)),(2,(C,2)),(3,(B,1)),(4,(A,3))}
    check range({(∗,2)}, {(∗,5)}, x) = {(0,(B,5)),(1,(C,1)),(2,(A,7))}
    -- `v > 2` holds at positions 0 1 2 4 7: `nth` numbers them, `filterBy` reads the rows
    pz : P ⟶ P ≜ nth(>, dom(x π₂ big))
    check pz = {(0,0),(1,1),(2,2),(3,4),(4,7)}
    check filterBy(dom(π₂ big), x) = {(0,(B,5)),(1,(A,3)),(2,(B,5)),(3,(A,7)),(4,(A,3))}
    -- the earlier rows with the same key: B A B C A C B A gives 0 0 1 0 1 1 2 2
    rk : P ⟶ P ≜ dom(x) rank((x π₁ (x π₁)°) ∩ >)
    check rk = {(0,0),(1,0),(2,1),(3,0),(4,1),(5,1),(6,2),(7,2)}

#guard framePos.ok

end Rel.Lang.TestFramePos
