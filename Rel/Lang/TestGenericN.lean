import Rel.Programs.FrameJoin

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
    rk(p : ν ⟶ ν) : ν ⟶ ν ≜ p ^(> p) length

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

/-! A relation argument that needs keys (`π₁`, `π₂`, `𝟙`) is passed on demand (`Expand.callDef`), so it runs bounded
    by what the constant's body composes it with, as the inlined body runs it, not on its source's whole universe:
    at `N` that universe is `𝟙`, which nothing bounds, at a declared `M` it is `M×M`. `R ∩ S` and `R − S` beside a
    table `R` need no keys (`Tm.dem`), so `ran` reads them. -/
open Rel.Programs.prelude Rel.Programs.frame Rel.Programs.frameGroup Rel.Programs.frameJoin in
rel_program paramNT where
    obj N
    obj K = {A,B,C}
    x : N ⟶ K×N ≜ {(0,(B,5)),(1,(A,3)),(2,(B,5)),(3,(C,1))}
    xn : N ⟶ K×(1+N) ≜ ⟨x π₁, dom(x) tot({(0,5),(2,5)})⟩
    y : N ⟶ K×N ≜ {(0,(A,9)),(1,(C,8))}
    check filterJust(π₂, xn) ⟨π₁, π₂ inr°⟩ = {(0,(B,5)),(1,(B,5))}
    check filterNothing(π₂, xn) π₁ = {(0,A),(1,C)}
    check filterBy(dom(π₂ {(3,3),(5,5)}), x) = {(0,(B,5)),(1,(A,3)),(2,(B,5))}
    check innerJoin(π₁, π₁, x, y) = {(0,((A,3),(A,9))),(1,((C,1),(C,8)))}
    q : N ⟶ N ≜ {(1,5),(2,2)}
    check ran(q ∩ 𝟙) = {(2,2)}
    check ran(q − 𝟙) = {(5,5)}

open Rel.Programs.prelude Rel.Programs.frame Rel.Programs.frameGroup Rel.Programs.frameJoin in
rel_program paramPT where
    obj P = 0…15
    obj K = {A,B,C}
    x : P ⟶ K×P ≜ {(0,(B,5)),(1,(A,3)),(2,(B,5)),(3,(C,1))}
    xn : P ⟶ K×(1+P) ≜ ⟨x π₁, dom(x) tot({(0,5),(2,5)})⟩
    y : P ⟶ K×P ≜ {(0,(A,9)),(1,(C,8))}
    check filterJust(π₂, xn) ⟨π₁, π₂ inr°⟩ = {(0,(B,5)),(1,(B,5))}
    check filterNothing(π₂, xn) π₁ = {(0,A),(1,C)}
    check filterBy(dom(π₂ {(3,3),(5,5)}), x) = {(0,(B,5)),(1,(A,3)),(2,(B,5))}
    check innerJoin(π₁, π₁, x, y) = {(0,((A,3),(A,9))),(1,((C,1),(C,8)))}
    q : P ⟶ P ≜ {(1,5),(2,2)}
    check ran(q ∩ 𝟙) = {(2,2)}
    check ran(q − 𝟙) = {(5,5)}

-- a 1000-row frame `j ↦ (i,i)`, `i = j + 19000`, in `M×M`, `|M×M| = 4·10⁸`: the argument `π₁` read on its universe
-- does not fit memory
open Rel.Programs.prelude Rel.Programs.frame Rel.Programs.frameGroup Rel.Programs.frameJoin in
rel_program paramBigT where
    obj M = 0…19999
    -- `x`: the positions `j` with `j + a` in `M`, `j = 0…999`, numbered from 0 as a frame's are (`filterBy`'s `dom(x)`
    -- keeps the new positions among `x`'s); `<` would be stored whole: `GenK.memo`
    a : 1 ⟶ M ≜ {(∗,19000)}
    b : 1 ⟶ M ≜ {(∗,19950)}
    x : M ⟶ M×M ≜ dom(⟨𝟙, ⊤ a⟩plus) ⟨𝟙, ⊤ a⟩plus ⟨𝟙, 𝟙⟩
    check filterBy(dom(π₁ dom(⟨𝟙, ⊤ b⟩minus)), x) = dom(⟨𝟙, ⊤ b⟩plus) ⟨𝟙, ⊤ b⟩plus ⟨𝟙, 𝟙⟩
    check innerJoin(π₁, π₁, x, x) = dom(⟨𝟙, ⊤ a⟩plus) ⟨𝟙, ⊤ a⟩plus ⟨⟨𝟙, 𝟙⟩, ⟨𝟙, 𝟙⟩⟩

-- by hand: `xn` holds a value at rows 0 2 (B,5), the null at 1 3 (A),(C), renumbered 0 1; the values 3 5 are at
-- rows 0 1 2; `x`'s keys B A B C meet `y`'s A C at (1,0), (3,1); `q ∩ 𝟙` keeps (2,2), `q − 𝟙` keeps (1,5); at `M`
-- the rows with `i ≥ 19950` renumbered `j = i − 19950` (`j + 19950` in `M`: `j < 50`), and `x` joined with itself on
-- `π₁` matches each row with itself, pair `j` the row `j`.
#guard paramNT.failures.map toString == []
#guard paramPT.failures.map toString == []
#guard paramBigT.failures.map toString == []

-- the universe of `M×M` is built when a term reads it, so `paramBigT` declares `M×M` and runs; `whole` reads it
-- (`𝟙` on demand, closed on its source's universe), 4·10⁸ pairs past `crossMax`: the program's error
/-- error: line 119, col 5: the universe of M × M: cross: 20000 values of the left object by 20000 of the right is 400000000 pairs, past the bound 268435456: a relation on two whole objects (`≤`, `<`, `⊤`) read where nothing bounds it to fewer pairs; meet it with a table (`T ∩ ≤` tests T's pairs only) or compose a smaller table on each side (`K ≤ L`) -/
#guard_msgs in
rel_program bigUniT where
    obj M = 0…19999
    whole : M×M ⟶ M×M ≜ 𝟙
    check whole = whole

end Rel.Lang.TestGenericN
