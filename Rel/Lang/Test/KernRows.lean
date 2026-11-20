import Rel.Lang.Test.Common

namespace Rel.Lang.Test

open Rel.Lang

/-! The kernel path for the rows `inits`, `tails`, `concat`, `filter`, `takewhile` (their `Tab` definitions in
    `Rel/Run/List.lean`): `kernRows5` closed (on `x`, `L`) and given a family (`hF`; `filter`, `takewhile` given a
    family are refused by the expander on both paths: a left fold is not liftable on its own).
    `x` holds an empty cell, a singleton, a repeated element and one array twice;
    `L` an empty outer cell, an empty inner cell and one inner array twice; `p`'s keys are `2 4 5`, `z` has none. -/
open Rel.Programs.prelude in
rel_program kernRows5 where
    obj N = 0…5
    obj K = 0…2
    x : N ⟶ [N] ≜ {(1,3 1 2),(2,[]),(3,2 2),(4,2 2),(5,[4])}
    L : N ⟶ [[N]] ≜ {(1,[1 2] [] [1 2]),(2,[]),(3,[[4]]),(4,[] [])}
    p : N ⟶ N ≜ {(2,2),(4,1),(5,5)}
    z : N ⟶ N ≜ p 𝟘
    i1 : N ⟶ [[N]] ≜ x inits
    t1 : N ⟶ [[N]] ≜ x tails
    c1 : N ⟶ [N] ≜ L concat
    c2 : N ⟶ [N] ≜ x inits concat
    c3 : N ⟶ [N] ≜ x tails concat
    a1 : N ⟶ [N] ≜ x filter(p)
    a2 : N ⟶ [N] ≜ x filter(z)
    q : [N] ⟶ [N] ≜ dom(x° p)
    a3 : N ⟶ [[N]] ≜ L filter(q)
    w1 : N ⟶ [N] ≜ x takewhile(p)
    w2 : N ⟶ [N] ≜ x takewhile(z)
    w3 : N ⟶ [[N]] ≜ L takewhile(q)
    Fm : K ⟶ N×N ≜ {(0,(2,2)),(0,(4,4)),(1,(3,3)),(2,(1,1)),(2,(2,2))}
    h(R : N ⟶ N) : N ⟶ [[N]] ≜ R x tails
    hF : K ⟶ N×[[N]] ≜ h(Fm)
    -- the rows worked by hand from each definition's relations, not read from a run
    check x = {(1,3 1 2),(2,[]),(3,2 2),(4,2 2),(5,[4])}
    check L = {(1,[1 2] [] [1 2]),(2,[]),(3,[[4]]),(4,[] [])}
    check p = {(2,2),(4,1),(5,5)}
    check z = 𝟘
    -- `Λ(prefix)`: the prefixes by increasing length, `[]` first
    check i1 = {(1,[] [3] [3 1] [3 1 2]),(2,[[]]),(3,[] [2] [2 2]),(4,[] [2] [2 2]),(5,[] [4])}
    -- the suffixes by decreasing length, `[]` last
    check t1 = {(1,[3 1 2] [1 2] [2] []),(2,[[]]),(3,[2 2] [2] []),(4,[2 2] [2] []),(5,[4] [])}
    check c1 = {(1,1 2 1 2),(2,[]),(3,[4]),(4,[])}
    check c2 = {(1,3 3 1 3 1 2),(2,[]),(3,2 2 2),(4,2 2 2),(5,[4])}
    check c3 = {(1,3 1 2 1 2 2),(2,[]),(3,2 2 2),(4,2 2 2),(5,[4])}
    -- `filter(p)` keeps the elements in `dom(p) = {2,4,5}`; `filter(z)` keeps none
    check a1 = {(1,[2]),(2,[]),(3,2 2),(4,2 2),(5,[4])}
    check a2 = {(1,[]),(2,[]),(3,[]),(4,[]),(5,[])}
    -- `x°` then `dom(p)`: the cells of `x` at the keys `2 4 5`
    check q = {([],[]),(2 2,2 2),([4],[4])}
    check a3 = {(1,[[]]),(2,[]),(3,[[4]]),(4,[] [])}
    -- the longest prefix whose elements are all in `dom(p)`
    check w1 = {(1,[]),(2,[]),(3,2 2),(4,2 2),(5,[4])}
    check w2 = {(1,[]),(2,[]),(3,[]),(4,[]),(5,[])}
    check w3 = {(1,[]),(2,[]),(3,[[4]]),(4,[] [])}
    check Fm = {(0,(2,2)),(0,(4,4)),(1,(3,3)),(2,(1,1)),(2,(2,2))}
    -- each `k` with `(n, tails(x(m)))` for `(n, m)` in `Fm(k)`
    check hF = {(0,(2,[[]])),(0,(4,[2 2] [2] [])),(1,(3,[2 2] [2] [])),(2,(1,[3 1 2] [1 2] [2] [])),(2,(2,[[]]))}

#guard kernRows5.ok
-- not vacuous: the kernel tables have rows
#guard ["c1", "c2", "c3", "a1", "a2", "w1", "w2"].all fun d =>
  ((get kernRows5.expanded d .long (.arr .long)).map (·.n.toNat != 0)) == some true
#guard ["i1", "t1", "a3", "w3"].all fun d =>
  ((get kernRows5.expanded d .long (.arr (.arr .long))).map (·.n.toNat != 0)) == some true
#guard ((get kernRows5.expanded "hF" .long (.prod .long (.arr (.arr .long)))).map (·.n.toNat != 0)) == some true

end Rel.Lang.Test
