import Rel.Programs.Prelude

/-! A numeral literal in the body of a generic definition: its object is the object variable the context puts it
    at, so each call decides it (`litTy`, `Env.gdef`). The constant takes the numeral as the number; each call checks
    that its object holds it (`build`'s `.call`): at the unbounded `obj N` every numeral, at a declared range the
    ones in it. `quantile` stands in for the frame library's, with its parameter shape. Expected rows by hand. -/

namespace Rel.Lang.TestGenericLit

open Rel.Programs.prelude in
rel_program genLitG where
    inc(x : 1 ⟶ ν) : 1 ⟶ ν ≜ ⟨x, {(∗,1)}⟩ plus
    quantile(p : 1 ⟶ ν, d : 1 ⟶ ν, a : ν ⟶ ν, x : ν ⟶ ν) : 1 ⟶ ν ≜ ⟨p, d⟩ plus a x
    percentile(p : 1 ⟶ ν, a : ν ⟶ ν, x : ν ⟶ ν) : 1 ⟶ ν ≜ quantile(p, {(∗,100)}, a, x)

open Rel.Programs.prelude genLitG in
rel_program genLitNT where
    obj N
    x : 1 ⟶ N ≜ {(∗,5)}
    a : N ⟶ N ≜ {(105,7),(6,9)}
    s : N ⟶ N ≜ {(7,3)}
    check inc(x) = {(∗,6)}
    check percentile(x, a, s) = {(∗,3)}

open Rel.Programs.prelude genLitG in
rel_program genLitQT where
    obj Q = 0…200
    x : 1 ⟶ Q ≜ {(∗,5)}
    a : Q ⟶ Q ≜ {(105,7),(6,9)}
    s : Q ⟶ Q ≜ {(7,3)}
    check inc(x) = {(∗,6)}
    check percentile(x, a, s) = {(∗,3)}

-- by hand: `inc` adds 1 to 5; `percentile` adds 100 to 5, `a` takes 105 to 7, `s` takes 7 to 3
#guard genLitNT.failures.map toString == []
#guard genLitQT.failures.map toString == []

/-- error: line 46, col 11: `percentile` at the objects of this call: 100 is not in P = 0…15 -/
#guard_msgs in
open Rel.Programs.prelude genLitG in
rel_program genLitPT where
    obj P = 0…15
    x : 1 ⟶ P ≜ {(∗,5)}
    a : P ⟶ P ≜ {(7,7)}
    s : P ⟶ P ≜ {(7,3)}
    check percentile(x, a, s) = 𝟘

end Rel.Lang.TestGenericLit
