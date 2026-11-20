import Rel.Programs.Frame

/-! Generic constants whose bodies hold a row with a `dfn` (`length`, `sum`), directly, through another generic
    constant, and inside `F(…)`, `Λ(…)`, `agg`, instantiated at the unbounded number object `obj N` and at the
    bounded `obj P = 0…15`: the row runs fused where the call's object is unbounded (universe `𝟙`), its definition
    (each step kept in the object) where it is bounded. Expected rows worked by hand. -/

namespace Rel.Lang.TestGenericN

open Rel.Programs.prelude Rel.Programs.frame in
rel_program genericG where
    lenL(x : 1 ⟶ [α]) : 1 ⟶ ν ≜ x length
    lenL2(x : 1 ⟶ [α]) : 1 ⟶ ν ≜ lenL(x)
    sm(x : ν ⟶ ν) : 1 ⟶ ν ≜ summarize(F(x) sum, x)
    len2(x : ν ⟶ β) : 1 ⟶ ν ≜ agg((dom(x) ⊤)°, length)
    cnt(x : ν ⟶ β) : 1 ⟶ ν ≜ count(x)
    rk(p : ν ⟶ ν) : ν ⟶ ν ≜ p Λ(> p) length

open Rel.Programs.prelude Rel.Programs.frame genericG in
rel_program genericNT where
    obj N
    xs : 1 ⟶ [N] ≜ {(∗,5 0 7 0)}
    x : N ⟶ N ≜ {(0,5),(1,0),(2,7),(3,0)}
    y : N ⟶ N ≜ {(0,9),(1,9)}
    p : N ⟶ N ≜ {(2,2),(5,5),(7,7),(9,9)}
    t4 : 1 ⟶ N ≜ lenL(xs)
    check t4 = {(∗,4)}
    check lenL2(xs) = {(∗,4)}
    check sm(x) = {(∗,12)}
    check sm(y) = {(∗,18)}
    check len2(x) = {(∗,4)}
    check cnt(x) = {(∗,4)}
    check rk(p) = {(2,0),(5,1),(7,2),(9,3)}

open Rel.Programs.prelude Rel.Programs.frame genericG in
rel_program genericPT where
    obj P = 0…15
    xs : 1 ⟶ [P] ≜ {(∗,5 0 7 0)}
    x : P ⟶ P ≜ {(0,5),(1,0),(2,7),(3,0)}
    y : P ⟶ P ≜ {(0,9),(1,9)}
    p : P ⟶ P ≜ {(2,2),(5,5),(7,7),(9,9)}
    t4 : 1 ⟶ P ≜ lenL(xs)
    check t4 = {(∗,4)}
    check lenL2(xs) = {(∗,4)}
    check sm(x) = {(∗,12)}
    check sm(y) = 𝟘
    check len2(x) = {(∗,4)}
    check cnt(x) = {(∗,4)}
    check rk(p) = {(2,0),(5,1),(7,2),(9,3)}

-- by hand: `5 0 7 0` has 4 elements; `x`'s values sum to 5+0+7+0 = 12, `y`'s to 9+9 = 18, which `P = 0…15` does not
-- hold, so at `P` the fold's last step leaves the object and `sm(y)` has no value; `x` has 4 rows; `rk` each element
-- of `p` to the count of elements below it (2 has none, 9 has 2 5 7).
#guard genericNT.failures.map toString == []
#guard genericPT.failures.map toString == []

end Rel.Lang.TestGenericN
