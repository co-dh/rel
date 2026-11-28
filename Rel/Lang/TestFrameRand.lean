import Rel.Programs.FrameGroup

/-! The random source of the frame library (`frameRand`, dataframe F8), against splitmix64 worked by hand. -/

namespace Rel.Lang.TestFrameRand

open Rel.Programs.prelude Rel.Programs.frame Rel.Programs.frameRand in
rel_program frameRandT where
    obj P = 0…15
    obj K = {A,B,C,D,E,F,G,H}
    obj G = {u,v}
    g : K ⟶ G ≜ {(A,u),(B,u),(C,u),(D,u),(E,v),(F,v),(G,v),(H,v)}
    x : P ⟶ K ≜ {(0,A),(1,B),(2,C)}
    y : P ⟶ K ≜ {(0,A),(1,B),(2,C),(3,D),(4,E),(5,F),(6,G),(7,H)}
    s0 : 1 ⟶ R ≜ {(∗,0)}
    s42 : 1 ⟶ R ≜ {(∗,42)}
    half : 1 ⟶ Q ≜ {(∗,0.5)}
    two : 1 ⟶ P ≜ {(∗,2)}
    three : 1 ⟶ R ≜ {(∗,3)}
    -- seed 0: splitmix64's first three outputs halved
    test rand(s0, x) = {(0,8147104208329303767),(1,3980143261097177850),(2,243808509735772839)}
    test shuffle(s0, x) = {(0,C),(1,B),(2,A)}
    test sample(s0, two, x) = {(0,C),(1,B)}
    -- same seed, same answer: the draws at seed 42 are those at seed 0 shifted by 42 counters
    test rand(s42, x) = {(0,283244664701664340),(1,675551852842775707),(2,7350826267122727452)}
    test randomSplit(s42, half, y) = {(0,A),(1,B),(4,E),(5,F),(6,G),(7,H)}
    test randomRest(s42, half, y) = {(2,C),(3,D)}
    test count(randomSplit(s42, half, y)) = {(∗,6)}
    test kFolds(s42, three, y) = {(0,1),(1,1),(2,0),(3,0),(4,0),(5,1),(6,1),(7,2)}
    -- the stream's first two draws: splitmix64 at counters 0, 1 and at 42, 43
    test take(two, mkRandom(s0)) = {(0,8147104208329303767),(1,3980143261097177850)}
    test take(two, mkRandom(s42)) = {(0,283244664701664340),(1,675551852842775707)}
    -- groups u = A…D, v = E…H; seed 0 shuffles `y` to C E G F B H A D, so the first two of u are C B, of v E G;
    -- seed 42 to A B H E F G C D: A B of u, H E of v
    test stratifiedSample(s0, two, g, y) = {(0,C),(1,E),(2,G),(3,B)}
    test stratifiedSample(s42, two, g, y) = {(0,A),(1,B),(2,H),(3,E)}
    -- one group: `sample`
    test stratifiedSample(s0, two, ⊤ {(∗,u)}, x) = sample(s0, two, x)



end Rel.Lang.TestFrameRand
