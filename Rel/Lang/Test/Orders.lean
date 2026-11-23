import Rel.Lang.Test.Common

namespace Rel.Lang.Test

open Tab Rel.Lang Rel.Alg Rel

open Rel.Programs.prelude Programs.blocks in
/-- `Λ(S)est(P)`, `Λ(S)front(P)` with the order `P` a family (the rows of §e on `S∋`) against the order closed
    (the closed row), on the reachable states — `est` of a map is the map — and on their complements, where a
    block has two values. -/
rel_program orders where
    O : X ⟶ X ≜ {(A,A),(A,B),(A,C),(B,B),(B,C),(C,C)}
    Of : [X×X] ⟶ X×X ≜ Q⊤(St,X)⟨𝟙,O⟩
    lc(S : X ⟶ X) : X ⟶ X ≜ Λ(S)est(O)
    lf(S : X ⟶ X, V : X ⟶ X) : X ⟶ X ≜ Λ(S)est(V)
    tc(S : X ⟶ X) : X ⟶ [X] ≜ Λ(S)front(O)
    tf(S : X ⟶ X, V : X ⟶ X) : X ⟶ [X] ≜ Λ(S)front(V)
    Y(S : X ⟶ X) : X ⟶ X ≜ ∼S
    check Qlc(∋) = Q∋
    check Qlf(∋,Of) = Qlc(∋)
    check Qlf(Y(∋),Of) = Qlc(Y(∋))
    check Qtf(∋,Of) = Qtc(∋)
    check Qtf(Y(∋),Of) = Qtc(Y(∋))
    print s₀lf(Y(∋),Of)
    print s₀tf(Y(∋),Of)

-- at `S₀`, `∼S₀` gives `A` the values `B C`, `B` the values `A C`, `C` the values `B C`: the least of each
#guard orders.ok && orders.prints == [
  "s₀ lf(Y(∋), Of) = {((A, A) (B, B) (C, A), (A, B)), ((A, A) (B, B) (C, A), (B, A)), " ++
    "((A, A) (B, B) (C, A), (C, B))}",
  "s₀ tf(Y(∋), Of) = {((A, A) (B, B) (C, A), (A, [B])), ((A, A) (B, B) (C, A), (B, [A])), " ++
    "((A, A) (B, B) (C, A), (C, [B]))}"]

/-! `lt`, `le` at objects no atom of `cmpRow`'s `num` stores (O2): the text runs, `Obj.lt` at that object, never the
    row. Each strict order is checked as one: on every pair exactly one of `lt`, `lt` swapped, `=` holds. -/

open Rel.Programs.prelude in
rel_program ltObjs where
    obj N = 0…4
    obj C : char
    p : N ⟶ (N×N)×(N×N) ≜ {(0,((0,1),(1,0))),(1,((1,0),(0,1))),(2,((1,1),(1,1)))}
    s : N ⟶ [C]×[C] ≜ {(0,("ab","b")),(1,("b","ab")),(2,("a","ab")),(3,("ab","ab")),(4,("","a"))}
    -- `inl ∗ < inr n` (null below every value), `inr` in N's order
    v : N ⟶ (1+N)×(1+N) ≜ ⟨⊤(N,1) inl, inr⟩ ∪ ⟨inr, < inr⟩ ∪ ⟨inr, inr⟩
    check v lt = ⟨⊤(N,1) inl, inr⟩ ∪ ⟨inr, < inr⟩
    check v le = v
    check dom(p lt) ∪ dom(p ⟨π₂,π₁⟩ lt) ∪ dom(p dom(π₁ ∩ π₂)) = dom(p)
    check dom(p lt) ∩ dom(p ⟨π₂,π₁⟩ lt) = 𝟘
    check dom(p lt) ∩ dom(p dom(π₁ ∩ π₂)) = 𝟘
    check dom(s lt) ∪ dom(s ⟨π₂,π₁⟩ lt) ∪ dom(s dom(π₁ ∩ π₂)) = dom(s)
    check dom(s lt) ∩ dom(s ⟨π₂,π₁⟩ lt) = 𝟘
    check dom(s lt) ∩ dom(s dom(π₁ ∩ π₂)) = 𝟘
    check p le = (p lt) ∪ (p dom(π₁ ∩ π₂))
    check s le = (s lt) ∪ (s dom(π₁ ∩ π₂))

#guard ltObjs.ok && ltObjs.failures.map toString == []

/-! The operators `<`, `≤`, `>` at an object that is no atom (`Tm.cmpDef`): the pairs of `dom U` the prelude's test
    holds at, `Obj.lt` of the object. `(0,2) < (1,0)` at `N×N` (first component first), null below every value at
    `1+N`, no universe at `[C]` (reported). -/

open Rel.Programs.prelude in
rel_program cmpObjs where
    obj N = 0…2
    obj C : char
    lo : N ⟶ N×N ≜ {(0,(0,2))}
    hi : N ⟶ N×N ≜ {(0,(1,0))}
    check lo < ∩ hi = hi
    check hi < ∩ lo = 𝟘
    check lo ≤ ∩ lo = lo
    check hi > ∩ lo = lo
    nl : N ⟶ 1+N ≜ ⊤(N,1) inl
    check nl < ∩ inr = inr
    check inr < ∩ nl = 𝟘
    check nl ≤ ∩ nl = nl

#guard cmpObjs.ok && cmpObjs.failures.map toString == []

/-! `asc(P)` at an object that is no atom runs its prelude text `(dom(P) Λ(> dom(P)) length)°`: number `j` is the `j`-th
    smallest pair of `dom P` in `Obj.lt` order. -/

open Rel.Programs.prelude in
rel_program ascObjs where
    obj N = 0…2
    P : N×N ⟶ N×N ≜ {((1,0),(1,0)), ((0,2),(0,2))}
    check asc(P) = {(0,(0,2)), (1,(1,0))}

#guard ascObjs.ok && ascObjs.failures.map toString == []

-- an object with no universe, and an atom with no order code
#eval errAt "obj N = 0…2\nobj C : char\ng : [C] ⟶ [C] ≜ <\n" 3 "has no universe"
#eval errAt "obj N = 0…2\nobj S : sym\ng : S×N ⟶ S×N ≜ <\n" 3 "has no order code"

end Rel.Lang.Test
