import Rel.Programs.FrameGroup

/-! The random source of the frame library (`frameRand`, dataframe F8), against splitmix64 worked by hand. -/

namespace Rel.Lang.TestFrameRand

open Rel.Programs.prelude Rel.Programs.frame Rel.Programs.frameRand in
rel_program frameRandT where
    obj P = 0…15
    obj K = {A,B,C,D,E,F,G,H}
    x : P ⟶ K ≜ {(0,A),(1,B),(2,C)}
    y : P ⟶ K ≜ {(0,A),(1,B),(2,C),(3,D),(4,E),(5,F),(6,G),(7,H)}
    s0 : 1 ⟶ R ≜ {(∗,0)}
    s42 : 1 ⟶ R ≜ {(∗,42)}
    half : 1 ⟶ Q ≜ {(∗,0.5)}
    two : 1 ⟶ P ≜ {(∗,2)}
    three : 1 ⟶ R ≜ {(∗,3)}
    -- seed 0: splitmix64's first three outputs halved
    check rand(s0, x) = {(0,8147104208329303767),(1,3980143261097177850),(2,243808509735772839)}
    check shuffle(s0, x) = {(0,C),(1,B),(2,A)}
    check sample(s0, two, x) = {(0,C),(1,B)}
    -- same seed, same answer: the draws at seed 42 are those at seed 0 shifted by 42 counters
    check rand(s42, x) = {(0,283244664701664340),(1,675551852842775707),(2,7350826267122727452)}
    check randomSplit(s42, half, y) = {(0,A),(1,B),(4,E),(5,F),(6,G),(7,H)}
    check randomRest(s42, half, y) = {(2,C),(3,D)}
    check count(randomSplit(s42, half, y)) = {(∗,6)}
    check kFolds(s42, three, y) = {(0,1),(1,1),(2,0),(3,0),(4,0),(5,1),(6,1),(7,2)}

#guard frameRandT.failures.map toString == []

end Rel.Lang.TestFrameRand
