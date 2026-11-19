import Rel.Lang.Test.Common

namespace Rel.Lang.Test

open Tab Rel.Lang Rel.Alg Rel

/-! Fixed points `μX : φ`, `νX : φ`: printed as read, run against their rounds written out, and refused where the
    body is not monotonic in `X` or the rounds have no bound. -/

#eval trips ["νZ : R ∩ Z", "(μZ : 𝟙 ∪ (R Z)) S", "R° ∪ (νZ : R ∩ (S \\ (Z R)))", "⟨νZ : R ∩ Z, S⟩"]
-- `R*`, the least `X` with `𝟙 ∪ RX ⊑ X`, against the closure written out
open Rel.Programs.prelude in
rel_program closure where
    obj N = 0…4
    R : N ⟶ N ≜ {(0,1),(1,2),(2,3)}
    c : N ⟶ N ≜ μX : 𝟙 ∪ (R X)
    check c = {(0,0),(1,1),(2,2),(3,3),(4,4),(0,1),(0,2),(0,3),(1,2),(1,3),(2,3)}
#guard closure.ok
-- postfix `*`, at the level of `°`: `R*` reads as that `μ`, its variable primed past every name in scope (the object
-- `X` here) and in its operand (`X'` here); `°` and `*` chain either way
#eval readsAll [("R*", "(μX' : (𝟙 ∪ (R X')))"), ("R°*", "(μX' : (𝟙 ∪ (R° X')))"), ("R*°", "(μX' : (𝟙 ∪ (R X')))°"),
  ("R S*", "(R (μX' : (𝟙 ∪ (S X'))))"), ("(R X')*", "(μX'' : (𝟙 ∪ ((R X') X'')))")]
-- `R*` against the hand-written `μ` and its value; `R°*` and `R*°` against its converse; `X`, a name of the
-- program, is not captured by the `μ` of `(R X)*`
open Rel.Programs.prelude in
rel_program star where
    obj N = 0…4
    R : N ⟶ N ≜ {(0,1),(1,2),(2,3)}
    X : N ⟶ N ≜ {(3,4)}
    c : N ⟶ N ≜ μZ : 𝟙 ∪ (R Z)
    check R* = c
    check R* = {(0,0),(1,1),(2,2),(3,3),(4,4),(0,1),(0,2),(0,3),(1,2),(1,3),(2,3)}
    check R°* = c°
    check R*° = c°
    check (R X)* = μZ : 𝟙 ∪ (R X Z)
    check (R X)* = {(0,0),(1,1),(2,2),(3,3),(4,4),(2,4)}
#guard star.ok
-- `*` is no name
#eval errAt "obj B = 0…1\n* : B ⟶ B ≜ 𝟙(B)\n" 0 "expected"
-- the points with an infinite `R`-path: the rounds from `𝟙` written out, which stop changing at the second
open Rel.Programs.prelude in
rel_program infPath where
    obj N = 0…5
    R : N ⟶ N ≜ {(0,1),(1,2),(2,0),(3,4)}
    v : N ⟶ N ≜ νX : 𝟙(N) ∩ dom(R X)
    x₁ : N ⟶ N ≜ 𝟙(N) ∩ dom(R 𝟙(N))
    x₂ : N ⟶ N ≜ 𝟙(N) ∩ dom(R x₁)
    x₃ : N ⟶ N ≜ 𝟙(N) ∩ dom(R x₂)
    check v = x₂
    check x₃ = x₂
    check v = {(0,0),(1,1),(2,2)}
#guard infPath.ok

-- `μ` on an array target, its values duplicate-free lists: the unions of the singletons `s`, which stop growing
-- once every set of three is reached; against the two levels of union written out
open Rel.Programs.prelude in
rel_program muArr where
    obj B = 0…2
    s : B ⟶ [B] ≜ Λ({(0,0)}) ∪ Λ({(0,1)}) ∪ Λ({(0,2)})
    f : B ⟶ [B] ≜ μX : s ∪ (⟨X, X⟩ cat setify)
    d : B ⟶ [B] ≜ ⟨s, s⟩ cat setify
    e : B ⟶ [B] ≜ ⟨d, s⟩ cat setify
    check f = s ∪ d ∪ e
    print f
#guard muArr.ok
#guard muArr.prints == ["f = {(0, [0]), (0, 0 1), (0, 0 1 2), (0, 0 2), (0, [1]), (0, 1 2), (0, [2]), (1, []), (2, [])}"]

-- `X` under an operator not monotonic in its argument, or in an antitone place; `ν` with no bound
#eval errAt "obj B = 0…1\nf : B ⟶ B ≜ νX : ⊤(B,B) ∩ (Λ(X)∋)\n" 2
  "νX: X occurs under Λ at 2:30; Λ is not monotonic in its argument, so the fixed point need not exist"
#eval errAt "obj B = 0…1\nr : B ⟶ B ≜ {(0,1)}\nf : B ⟶ B ≜ μX : r ∪ X\\r\n" 3
  "μX: X occurs in the left operand of \\ at 3:22 (antitone); X must occur only in monotonic positions"
-- `X` under two antitone places reads positively to `Pre.polarity`, but `\`'s left operand is read on both sides
-- (`ldivDen`'s `∀` and `∃`), so `Tm.pol` refuses it
#eval errAt "obj B = 0…1\nr : B ⟶ B ≜ {(0,1)}\nf : B ⟶ B ≜ μX : r ∪ ((X\\r)\\r)\n" 3
  "μX at 3:13: X first occurs at 3:24, and the body does not use X positively (it reads X on both sides, or holds it whole)"
#eval errAt "obj B = 0…1\nr : B ⟶ B ≜ {(0,1)}\nf : B ⟶ B ≜ νX : r X\n" 3
  "νX needs a bound: write S ∩ φ with S not mentioning X (⊤(A,B) for the whole object)"
#eval errAt "obj X = {A,B,C}\nobj St = [X×X]\nL(S : X ⟶ X) : X ⟶ X ≜ νZ : S ∩ Z\nf : St ⟶ X×X ≜ L(∋)\n" 3
  "νZ given a family is not liftable"
#eval errAt "obj B = 0…1\nνx : B ⟶ B ≜ 𝟙(B)\n" 2 "the name 'νx' reads as a fixed point"


end Rel.Lang.Test
