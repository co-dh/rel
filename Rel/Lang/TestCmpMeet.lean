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
-- successor and to its half, 2·10⁵ distinct rows on 10⁵ positions (`count` counts positions). By hand: `i ≥ i div 2`
-- always and `i ≥ i+1` never, so `R0 ∩ ≥` is the half rows, its range 0…49999; `i < i+1` always and `i < i div 2`
-- never, so `R0 ∩ <` is the successor rows, its range 1…100000; `R0 ∩ 𝟙` is `(0,0)` alone. `bad` is `≤` between two
-- sets of 10⁵ values with no table to meet: 10¹⁰ pairs, past `crossMax`, its one failure.
open Rel.Programs.prelude Rel.Programs.frame in
rel_program cmpMeetBig where
    obj M = 0…999999
    D : 1 ⟶ M ≜ {(∗,0),(∗,1),(∗,2),(∗,3),(∗,4),(∗,5),(∗,6),(∗,7),(∗,8),(∗,9)}
    d2 : 1 ⟶ M ≜ ⟨D, D⟩ ⟨⟨π₁, ⊤ {(∗,10)}⟩times, π₂⟩plus
    d4 : 1 ⟶ M ≜ ⟨d2, d2⟩ ⟨⟨π₁, ⊤ {(∗,100)}⟩times, π₂⟩plus
    d5 : 1 ⟶ M ≜ ⟨d4, D⟩ ⟨⟨π₁, ⊤ {(∗,10)}⟩times, π₂⟩plus
    P : M ⟶ M ≜ ran(d5)
    R0 : M ⟶ M ≜ (P succ) ∪ (P ⟨𝟙, ⊤ {(∗,2)}⟩div)
    check count(R0) = {(∗,100000)}
    check count(ran(R0 ∩ ≥)) = {(∗,50000)}
    check count(ran(R0 ∩ <)) = {(∗,100000)}
    check R0 ∩ 𝟙 = {(0,0)}
    bad : M ⟶ M ≜ P ≤ P

#guard cmpMeetBig.failures.map toString == ["bad: cross: 100000 values of the left object by 100000 of the right " ++
  "is 10000000000 pairs, past the bound 268435456: a relation on two whole objects (`≤`, `<`, `⊤`) read where " ++
  "nothing bounds it to fewer pairs; meet it with a table (`T ∩ ≤` tests T's pairs only) or compose a smaller " ++
  "table on each side (`K ≤ L`)"]

end Rel.Lang.TestCmpMeet
