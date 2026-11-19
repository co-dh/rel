import Rel.Lang.Test.Common

namespace Rel.Lang.Test

open Rel.Lang

/-! The kernel path for the rows `inits`, `tails`, `concat`, `filter`, `takewhile` (their `Tab` definitions in
    `Rel/Run/List.lean`): `kernRows5` closed (on `x`, `L`) and given a family (`hF`; `filter`, `takewhile` given a
    family are refused by the expander on both paths: a left fold is not liftable on its own); `kernRows5Old` the
    same definitions on the old layer. `x` holds an empty cell, a singleton, a repeated element and one array twice;
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

open Rel.Programs.prelude in
set_option rel.kernel false in
rel_program kernRows5Old where
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

#guard kernRows5.kernel && !kernRows5Old.kernel && kernRows5.ok && kernRows5Old.ok
#guard ["x", "c1", "c2", "c3", "a1", "a2", "w1", "w2"].all
  (sameK kernRows5.expanded kernRows5Old.expanded · .long (.arr .long))
#guard ["L", "i1", "t1", "a3", "w3"].all (sameK kernRows5.expanded kernRows5Old.expanded · .long (.arr (.arr .long)))
#guard ["hF"].all (sameK kernRows5.expanded kernRows5Old.expanded · .long (.prod .long (.arr (.arr .long))))
-- not vacuous: the kernel tables have rows
#guard ["c1", "c2", "c3", "a1", "a2", "w1", "w2"].all fun d =>
  ((get kernRows5.expanded d .long (.arr .long)).map (·.n.toNat != 0)) == some true
#guard ["i1", "t1", "a3", "w3"].all fun d =>
  ((get kernRows5.expanded d .long (.arr (.arr .long))).map (·.n.toNat != 0)) == some true
#guard ((get kernRows5.expanded "hF" .long (.prod .long (.arr (.arr .long)))).map (·.n.toNat != 0)) == some true

end Rel.Lang.Test
