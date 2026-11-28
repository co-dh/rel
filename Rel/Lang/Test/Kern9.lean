import Rel.Lang.Test.Common

namespace Rel.Lang.Test

open Tab Rel.Lang Rel.Alg Rel

/-! The kernel path, step T9: `kernT9` uses `hylo(c, S)` and the rows `loop`, `merge`, `thinL`.
    `x` holds an empty cell, a cell of one element, and cells with equal elements (so
    `thinL(≤)` keeps both choices: a relation, not a function); `z` is empty (an empty demand).
    `hylo`: `sub` is the depth under `boss` (3 at most; 6 has no root, so no value), `dbl` doubles by the sum functor
    `1 + X` (`succ°` the coalgebra), `ch` has a relation as coalgebra (each node stops or goes up: every depth up
    to its own). -/
open Rel.Programs.prelude in
rel_program kernT9 where
    obj N = 0…10
    obj E = 0…6
    x : N ⟶ [N] ≜ {(1,3 1 2),(2,[]),(3,1 2),(4,2 2),(5,4 4),(6,5 1 1 3)}
    xs : N ⟶ [N] ≜ {(1,1 2 3),(2,[]),(3,1 2),(4,2 2),(5,4 4),(6,1 1 3 5)}
    y : N ⟶ [N] ≜ {(1,2 4),(2,1 1),(3,[]),(4,1 2 3),(5,[]),(6,3 3)}
    z : N ⟶ N ≜ x 𝟘
    zr : 1 ⟶ N ≜ {(∗,0)}
    l1 : N ⟶ N ≜ ⟨𝟙,x⟩loop(plus)
    l2 : N ⟶ N ≜ ⟨𝟙,x⟩loop(plus ∪ π₁)
    l3 : N ⟶ N ≜ z ⟨𝟙,x⟩loop(plus)
    m1 : N ⟶ [N] ≜ ⟨xs, y⟩merge(≤)
    m2 : N ⟶ [N] ≜ ⟨x, y⟩merge(<)
    m3 : N ⟶ [N] ≜ z ⟨x, y⟩merge(≤)
    p : N ⟶ [N×N] ≜ {(1,(1,5) (2,3)),(2,[(3,1)]),(3,[]),(4,(2,2) (2,2) (5,0))}
    q : N ⟶ [N×N] ≜ {(1,(1,7) (2,9) (2,0)),(2,(3,1) (3,1)),(3,[(4,4)]),(4,(2,2) (5,0) (5,0))}
    m4 : N ⟶ [N×N] ≜ ⟨p, q⟩merge(π₁ ≤ π₁°)
    m5 : N ⟶ [N×N] ≜ ⟨q, q⟩merge(π₁ ≤ π₁°)
    m6 : N ⟶ [N×N] ≜ ⟨q, p⟩merge(π₁ < π₁°)
    t1 : N ⟶ [N] ≜ x thinL(≤)
    t2 : N ⟶ [N] ≜ x thinL(<)
    t3 : N ⟶ [N] ≜ z x thinL(≤)
    boss : E ⟶ E ≜ {(1,0),(2,0),(3,1),(4,3),(5,3)}
    rt : E ⟶ 1 ≜ {(0,∗)}
    ee : E ⟶ 1 ≜ {(0,∗),(1,∗),(2,∗),(3,∗),(4,∗),(5,∗),(6,∗)}
    sub : E ⟶ N ≜ hylo((rt inl) ∪ (boss inr), [zr, succ])
    lf : E ⟶ E ≜ {(2,2),(4,4),(6,6)}
    leaf : E ⟶ N ≜ lf sub
    ze : E ⟶ E ≜ boss 𝟘
    sube : E ⟶ N ≜ ze sub
    ch : E ⟶ N ≜ hylo((ee inl) ∪ (boss inr), [zr, succ])
    z1 : N ⟶ 1 ≜ {(0,∗)}
    dd : N ⟶ N ≜ {(0,0),(1,1),(3,3),(5,5)}
    dbl : N ⟶ N ≜ dd hylo((z1 inl) ∪ (succ° inr), [zr, succ succ])
    -- the rows worked by hand from each definition's relations, not read from a run
    test x = {(1,3 1 2),(2,[]),(3,1 2),(4,2 2),(5,4 4),(6,5 1 1 3)}
    test xs = {(1,1 2 3),(2,[]),(3,1 2),(4,2 2),(5,4 4),(6,1 1 3 5)}
    test y = {(1,2 4),(2,1 1),(3,[]),(4,1 2 3),(5,[]),(6,3 3)}
    test z = 𝟘
    test zr = {(∗,0)}
    -- `n` plus the sum of `x(n)`, every partial sum in `N = 0…10` (`5`: 13, `6`: 11 are not)
    test l1 = {(1,7),(2,2),(3,6),(4,8)}
    -- `n` plus the sum of any subsequence of `x(n)`, at most 10
    test l2 = {(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(2,2),(3,3),(3,4),(3,5),(3,6),(4,4),(4,6),(4,8),(5,5),(5,9),(6,6),(6,7),(6,8),(6,9),(6,10)}
    test l3 = 𝟘
    -- the head of the first array is taken where it is `Q` the other's head, or the other is empty
    test m1 = {(1,1 2 2 3 4),(2,1 1),(3,1 2),(4,1 2 2 2 3),(5,4 4),(6,1 1 3 3 3 5)}
    test m2 = {(1,2 3 1 2 4),(2,1 1),(3,1 2),(4,1 2 2 2 3),(5,4 4),(6,3 3 5 1 1 3)}
    test m3 = 𝟘
    test p = {(1,(1,5) (2,3)),(2,[(3,1)]),(3,[]),(4,(2,2) (2,2) (5,0))}
    test q = {(1,(1,7) (2,9) (2,0)),(2,(3,1) (3,1)),(3,[(4,4)]),(4,(2,2) (5,0) (5,0))}
    test m4 = {(1,(1,5) (1,7) (2,3) (2,9) (2,0)),(2,(3,1) (3,1) (3,1)),(3,[(4,4)]),(4,(2,2) (2,2) (2,2) (5,0) (5,0) (5,0))}
    test m5 = {(1,(1,7) (1,7) (2,9) (2,0) (2,9) (2,0)),(2,(3,1) (3,1) (3,1) (3,1)),(3,(4,4) (4,4)),(4,(2,2) (2,2) (5,0) (5,0) (5,0) (5,0))}
    test m6 = {(1,(1,5) (1,7) (2,3) (2,9) (2,0)),(2,(3,1) (3,1) (3,1)),(3,[(4,4)]),(4,(2,2) (2,2) (2,2) (5,0) (5,0) (5,0))}
    -- from the right: an element `Q` the chain's head replaces it, one the head is `Q` to is dropped, else pushed
    test t1 = {(1,[1]),(2,[]),(3,[1]),(4,[2]),(5,[4]),(6,[1])}
    test t2 = {(1,[1]),(2,[]),(3,[1]),(4,2 2),(5,4 4),(6,1 1)}
    test t3 = 𝟘
    test boss = {(1,0),(2,0),(3,1),(4,3),(5,3)}
    test rt = {(0,∗)}
    test ee = {(0,∗),(1,∗),(2,∗),(3,∗),(4,∗),(5,∗),(6,∗)}
    -- the depth under `boss`; `6` reaches no root
    test sub = {(0,0),(1,1),(2,1),(3,2),(4,3),(5,3)}
    test lf = {(2,2),(4,4),(6,6)}
    test leaf = {(2,1),(4,3)}
    test ze = 𝟘
    test sube = 𝟘
    -- `0`, or one more than a value of the boss: every depth up to the node's own
    test ch = {(0,0),(1,0),(1,1),(2,0),(2,1),(3,0),(3,1),(3,2),(4,0),(4,1),(4,2),(4,3),(5,0),(5,1),(5,2),(5,3),(6,0)}
    test z1 = {(0,∗)}
    test dd = {(0,0),(1,1),(3,3),(5,5)}
    test dbl = {(0,0),(1,2),(3,6),(5,10)}


-- not vacuous: the kernel tables have rows where the input does, none on the empty demand
#guard ["l1", "l2", "dbl", "sub", "leaf", "ch"].all fun d => ((get kernT9.expanded d .long .long).map (·.n.toNat != 0)) == some true
#guard ["m1", "m2", "t1", "t2"].all fun d =>
  ((get kernT9.expanded d .long (.arr .long)).map (·.n.toNat != 0)) == some true
-- `merge` with ties under a preorder (`π₁ ≤ π₁°`: equal first, different second) and duplicates in both inputs: one
-- merged list per key (`List.merge`), each round's state carrying one copy of `x`'s payload (`Tab.pack`)
#guard ["m4", "m5", "m6"].all fun d =>
  ((get kernT9.expanded d .long (.arr (.prod .long .long))).map (·.n.toNat)) == some 4
#guard ["l3", "sube"].all fun d => ((get kernT9.expanded d .long .long).map (·.n.toNat)) == some 0
#guard ["m3", "t3"].all fun d => ((get kernT9.expanded d .long (.arr .long)).map (·.n.toNat)) == some 0

end Rel.Lang.Test
