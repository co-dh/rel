import Rel.Programs.FrameJoin

/-! A comparison met with a table, `T ∩ ≥`: the meet hands the comparison `T`'s pairs (`Known.pairs`), so it tests
    those `n` pairs one by one instead of the `dom T × ran T` box. Expected rows worked by hand. -/

namespace Rel.Lang.TestCmpMeet

open Rel.Programs.prelude in
rel_program cmpMeetT where
    obj N
    t : N ⟶ N ≜ {(1,0),(1,1),(1,2),(3,5),(4,4)}
    ge : N ⟶ N ≜ t ∩ ≥
    lt : N ⟶ N ≜ t ∩ <
    gt : N ⟶ N ≜ t ∩ >
    le : N ⟶ N ≜ t ∩ ≤
    eq : N ⟶ N ≜ t ∩ 𝟙
    gel : N ⟶ N ≜ ≥ ∩ t
    either : N ⟶ N ≜ t ∩ (< ∪ >)
    test ge = {(1,0),(1,1),(4,4)}
    test lt = {(1,2),(3,5)}
    test gt = {(1,0)}
    test le = {(1,1),(1,2),(3,5),(4,4)}
    test eq = {(1,1),(4,4)}
    test gel = {(1,0),(1,1),(4,4)}
    test either = {(1,0),(1,2),(3,5)}


-- `Bench/CmpMeet.lean`'s `cmpMeetBig` at 10³ rows over `M` of 10⁵ values: `P` the positions 0…999, `R0` each to its
-- successor and to its half, so `R0 ∩ ≥` has range 0…499, `R0 ∩ <` range 1…1000, `R0 ∩ 𝟙` is `(0,0)`. `bad` reads
-- `⊤` on two whole objects of 10⁵ values: 10¹⁰ pairs, past `crossMax`, its one failure.
open Rel.Programs.prelude Rel.Programs.frame in
rel_program cmpMeet3 where
    obj M = 0…99999
    D : 1 ⟶ M ≜ {(∗,0),(∗,1),(∗,2),(∗,3),(∗,4),(∗,5),(∗,6),(∗,7),(∗,8),(∗,9)}
    d2 : 1 ⟶ M ≜ ⟨D, D⟩ ⟨⟨π₁, ⊤ {(∗,10)}⟩times, π₂⟩plus
    d3 : 1 ⟶ M ≜ ⟨d2, D⟩ ⟨⟨π₁, ⊤ {(∗,10)}⟩times, π₂⟩plus
    P : M ⟶ M ≜ ran(d3)
    R0 : M ⟶ M ≜ (P succ) ∪ (P ⟨𝟙, ⊤ {(∗,2)}⟩div)
    test count(R0) = {(∗,1000)}
    test count(ran(R0 ∩ ≥)) = {(∗,500)}
    test count(ran(R0 ∩ <)) = {(∗,1000)}
    test R0 ∩ 𝟙 = {(0,0)}

/-- error: rel_program Rel.Lang.TestCmpMeet.cmpMeetBad: bad: cross: 100000 values of the left object by 100000 of the right is 10000000000 pairs, past the bound 268435456: a relation on two whole objects (`≤`, `<`, `⊤`) read where nothing bounds it to fewer pairs; meet it with a table (`T ∩ ≤` tests T's pairs only) or compose a smaller table on each side (`K ≤ L`) -/
#guard_msgs in
open Rel.Programs.prelude Rel.Programs.frame in
rel_program cmpMeetBad where
    obj M = 0…99999
    bad : M ⟶ M ≜ ⊤(M,M)

end Rel.Lang.TestCmpMeet
