import Rel.Lang.Test.Common

namespace Rel.Lang.Test

open Tab Rel.Lang Rel.Alg Rel

open Rel.Programs.prelude in
/-- The base of a fold is the relation literal `{(∗,0)} : 1 ⟶ V` (B10c: `length`, `sum` as prelude text): the object
    variable `β` is a number object, its universe the constant's argument, so `sm` at `0…5` is cut to it. -/
rel_program foldBase where
    len : [α] ⟶ β ≜ ⦇[{(∗,0)}, π₁ succ]⦈
    sm : [β] ⟶ β ≜ ⦇[{(∗,0)}, plus]⦈
    obj N
    obj P = 0…5
    obj M = -3…3
    obj F : f64
    x : N ⟶ [N] ≜ {(0,[1 2 3]),(1,[5 -7])}
    z : N ⟶ [P] ≜ {(0,[1 2]),(1,[4 3])}
    m : N ⟶ [M] ≜ {(0,[3 3 -3]),(1,[1 2])}
    f : N ⟶ [F] ≜ {(0,[1.5 2.5])}
    a1 : N ⟶ N ≜ x len
    a2 : N ⟶ N ≜ x sm
    a3 : N ⟶ P ≜ z sm
    a4 : N ⟶ P ≜ z len
    a6 : N ⟶ M ≜ m sm
    a7 : N ⟶ F ≜ f sm
    check a1 = {(0,3),(1,2)}
    check a2 = {(0,6),(1,-2)}
    check a3 = {(0,3)}
    check a4 = {(0,2),(1,2)}
    check a6 = {(1,3)}
    check a7 = {(0,4.0)}
    b1 : N ⟶ M ≜ m sum
    check b1 = a6

#guard foldBase.failures.isEmpty

end Rel.Lang.Test
