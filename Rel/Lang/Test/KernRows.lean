import Rel.Lang.Test.Common

namespace Rel.Lang.Test

open Rel.Lang

/-! The kernel path for the rows `inits`, `tails`, `concat`, `filter`, `takewhile` (their `Tab` definitions in
    `Rel/Run/List.lean`): `kernRows5` closed (on `x`, `L`) and given a family (`fF`, `gF`, `hF`); `kernRows5Old` the
    same definitions on the old layer. `x` holds an empty cell, a singleton, a repeated element and one array twice;
    `L` an empty outer cell, an empty inner cell and one inner array twice; `p`'s keys are `2 4 5`, `z` has none. -/
rel_program kernRows5 where
    obj N = 0…5
    obj K = 0…2
    x : N ⟶ [N] ≜ {(1,3 1 2),(2,[]),(3,2 2),(4,2 2),(5,4)}
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
    a3 : N ⟶ [[N]] ≜ L filter(dom(length{(2,2)}))
    w1 : N ⟶ [N] ≜ x takewhile(p)
    w2 : N ⟶ [N] ≜ x takewhile(z)
    w3 : N ⟶ [[N]] ≜ L takewhile(dom(length{(2,2)}))
    Fm : K ⟶ N×N ≜ {(0,(2,2)),(0,(4,4)),(1,(3,3)),(2,(1,1)),(2,(2,2))}
    f(R : N ⟶ N) : N ⟶ [N] ≜ x filter(R)
    g(R : N ⟶ N) : N ⟶ [N] ≜ x takewhile(R)
    h(R : N ⟶ N) : N ⟶ [[N]] ≜ R x tails
    fF : K ⟶ N×[N] ≜ f(Fm)
    gF : K ⟶ N×[N] ≜ g(Fm)
    hF : K ⟶ N×[[N]] ≜ h(Fm)

set_option rel.kernel false in
rel_program kernRows5Old where
    obj N = 0…5
    obj K = 0…2
    x : N ⟶ [N] ≜ {(1,3 1 2),(2,[]),(3,2 2),(4,2 2),(5,4)}
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
    a3 : N ⟶ [[N]] ≜ L filter(dom(length{(2,2)}))
    w1 : N ⟶ [N] ≜ x takewhile(p)
    w2 : N ⟶ [N] ≜ x takewhile(z)
    w3 : N ⟶ [[N]] ≜ L takewhile(dom(length{(2,2)}))
    Fm : K ⟶ N×N ≜ {(0,(2,2)),(0,(4,4)),(1,(3,3)),(2,(1,1)),(2,(2,2))}
    f(R : N ⟶ N) : N ⟶ [N] ≜ x filter(R)
    g(R : N ⟶ N) : N ⟶ [N] ≜ x takewhile(R)
    h(R : N ⟶ N) : N ⟶ [[N]] ≜ R x tails
    fF : K ⟶ N×[N] ≜ f(Fm)
    gF : K ⟶ N×[N] ≜ g(Fm)
    hF : K ⟶ N×[[N]] ≜ h(Fm)

#guard kernRows5.kernel && !kernRows5Old.kernel && kernRows5.ok && kernRows5Old.ok
#guard ["x", "c1", "c2", "c3", "a1", "a2", "w1", "w2"].all
  (sameK kernRows5.expanded kernRows5Old.expanded · .long (.arr .long))
#guard ["L", "i1", "t1", "a3", "w3"].all (sameK kernRows5.expanded kernRows5Old.expanded · .long (.arr (.arr .long)))
#guard ["fF", "gF"].all (sameK kernRows5.expanded kernRows5Old.expanded · .long (.prod .long (.arr .long)))
#guard ["hF"].all (sameK kernRows5.expanded kernRows5Old.expanded · .long (.prod .long (.arr (.arr .long))))
-- not vacuous: the kernel tables have rows
#guard ["c1", "c2", "c3", "a1", "a2", "w1", "w2"].all fun d =>
  ((get kernRows5.expanded d .long (.arr .long)).map (·.n.toNat != 0)) == some true
#guard ["i1", "t1", "a3", "w3"].all fun d =>
  ((get kernRows5.expanded d .long (.arr (.arr .long))).map (·.n.toNat != 0)) == some true
#guard ["fF", "gF"].all fun d =>
  ((get kernRows5.expanded d .long (.prod .long (.arr .long))).map (·.n.toNat != 0)) == some true

end Rel.Lang.Test
