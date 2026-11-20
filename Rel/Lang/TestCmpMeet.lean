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
    check ge = {(1,0),(1,1),(4,4)}
    check lt = {(1,2),(3,5)}
    check gt = {(1,0)}
    check le = {(1,1),(1,2),(3,5),(4,4)}
    check eq = {(1,1),(4,4)}
    check gel = {(1,0),(1,1),(4,4)}
    check either = {(1,0),(1,2),(3,5)}

#guard cmpMeetT.ok

-- 10⁵ rows over the object `M` of 10⁶ values: `P` the positions 0…99999 (five digits), `R0` each position to its
-- successor and to its half, 2·10⁵ distinct rows (`i+1 = i div 2` has no solution). By hand: `i ≥ i div 2` always
-- and `i ≥ i+1` never, so `R0 ∩ ≥` is the 10⁵ half rows; `i < i+1` always and `i < i div 2` never, so `R0 ∩ <` is
-- the 10⁵ successor rows; `R0 ∩ 𝟙` is `(0,0)` alone. `bad` is `≤` between two sets of 10⁵ values with no table to meet: past `crossMax`.
open Rel.Programs.prelude Rel.Programs.frame in
rel_program cmpMeetBig where
    obj M = 0…999999
    D : 1 ⟶ M ≜ {(∗,0),(∗,1),(∗,2),(∗,3),(∗,4),(∗,5),(∗,6),(∗,7),(∗,8),(∗,9)}
    d2 : 1 ⟶ M ≜ ⟨D, D⟩ ⟨⟨π₁, ⊤ {(∗,10)}⟩times, π₂⟩plus
    d4 : 1 ⟶ M ≜ ⟨d2, d2⟩ ⟨⟨π₁, ⊤ {(∗,100)}⟩times, π₂⟩plus
    d5 : 1 ⟶ M ≜ ⟨d4, D⟩ ⟨⟨π₁, ⊤ {(∗,10)}⟩times, π₂⟩plus
    P : M ⟶ M ≜ ran(d5)
    R0 : M ⟶ M ≜ P succ ∪ P ⟨𝟙, ⊤ {(∗,2)}⟩div
    check count(R0) = {(∗,100000)}
    check count(ran(R0 ∩ ≥)) = {(∗,50000)}
    check count(ran(R0 ∩ <)) = {(∗,100000)}
    check R0 ∩ 𝟙 = {(0,0)}
    bad : M ⟶ M ≜ P ≤ P

#eval cmpMeetBig.failures.map toString

end Rel.Lang.TestCmpMeet
