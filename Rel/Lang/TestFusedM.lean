import Rel.Programs.Prelude

/-! The rows with a fused form and a definition (`Prim.dfn`: `length`, `sum`) on lists over a declared bounded object
    `M = 0…19999`, large enough that enumerating `M` per list element shows in the build time. Expected rows worked
    by hand. -/

namespace Rel.Lang.TestFusedM

open Rel.Programs.prelude in
rel_program fusedMT where
    obj M = 0…19999
    obj K = 0…2
    xs : 1 ⟶ [M] ≜ {(∗,1 2 3 4 5 6 7 8 9 10 1 2 3 4 5 6 7 8 9 10 1 2 3 4 5 6 7 8 9 10 1 2 3 4 5 6 7 8 9 10 1 2 3 4 5 6 7 8 9 10 1 2 3 4 5 6 7 8 9 10 1 2 3 4 5 6 7 8 9 10 1 2 3 4 5 6 7 8 9 10 1 2 3 4 5 6 7 8 9 10 1 2 3 4 5 6 7 8 9 10 1 2 3 4 5 6 7 8 9 10 1 2 3 4 5 6 7 8 9 10 1 2 3 4 5 6 7 8 9 10 1 2 3 4 5 6 7 8 9 10 1 2 3 4 5 6 7 8 9 10 1 2 3 4 5 6 7 8 9 10 1 2 3 4 5 6 7 8 9 10 1 2 3 4 5 6 7 8 9 10 1 2 3 4 5 6 7 8 9 10 1 2 3 4 5 6 7 8 9 10 1 2 3 4 5 6 7 8 9 10 1 2 3 4 5 6 7 8 9 10 1 2 3 4 5 6 7 8 9 10 1 2 3 4 5 6 7 8 9 10 1 2 3 4 5 6 7 8 9 10 1 2 3 4 5 6 7 8 9 10 1 2 3 4 5 6 7 8 9 10 1 2 3 4 5 6 7 8 9 10 1 2 3 4 5 6 7 8 9 10 1 2 3 4 5 6 7 8 9 10)}
    ys : K ⟶ [M] ≜ {(0,19999 1),(1,19999 0),(2,5 0)}
    x2 : 1 ⟶ [M] ≜ ⟨xs, xs⟩ cat
    x4 : 1 ⟶ [M] ≜ ⟨x2, x2⟩ cat
    x8 : 1 ⟶ [M] ≜ ⟨x4, x4⟩ cat
    xn : 1 ⟶ M ≜ xs length
    zn : 1 ⟶ M ≜ x8 length
    zsm : 1 ⟶ M ≜ x8 sum
    xsm : 1 ⟶ M ≜ xs sum
    yn : K ⟶ M ≜ ys length
    ysm : K ⟶ M ≜ ys sum
    check xn = {(∗,300)}
    check xsm = {(∗,1650)}
    check zn = {(∗,2400)}
    check zsm = {(∗,13200)}
    check yn = {(0,2),(1,2),(2,2)}
    check ysm = {(1,19999),(2,5)}

-- by hand: `xs` is `1 2 … 10` thirty times: 300 elements, sum 30 × 55 = 1650; `x8` is `xs` eight times: 2400 elements, sum 13200. `ys`: every row has two elements,
-- row 2 sums to 5 + 0 = 5; row 0 sums to 19999 + 1 = 20000, which `M` does not hold, so it has no sum; row 1
-- sums to 19999 + 0 = 19999.
#guard fusedMT.failures.map toString == []

open Rel.Programs.prelude in
rel_program fusedG where
    lenG(x : 1 ⟶ [α]) : 1 ⟶ ν ≜ x length
    sumG(x : 1 ⟶ [ν]) : 1 ⟶ ν ≜ x sum

/-! The same rows inside constants generic over their target `ν`, called at `M` (the constant built with `ν` an
    initial segment, `formKey`'s `seg`), and at `Q = 1…5`, not one: there the definition runs, and its fold's base
    `0` is not in `Q`, so it has no value. -/
open Rel.Programs.prelude fusedG in
rel_program fusedGT where
    obj M = 0…19999
    obj Q = 1…5
    xs : 1 ⟶ [M] ≜ {(∗,1 2 3 4 5 6 7 8 9 10)}
    x2 : 1 ⟶ [M] ≜ ⟨xs, xs⟩ cat
    x4 : 1 ⟶ [M] ≜ ⟨x2, x2⟩ cat
    zs : 1 ⟶ [M] ≜ {(∗,19999 1)}
    qs : 1 ⟶ [Q] ≜ {(∗,1 2)}
    gn : 1 ⟶ M ≜ lenG(x4)
    gs : 1 ⟶ M ≜ sumG(x4)
    gz : 1 ⟶ M ≜ sumG(zs)
    qn : 1 ⟶ Q ≜ qs length
    qsm : 1 ⟶ Q ≜ qs sum
    check gn = {(∗,40)}
    check gs = {(∗,220)}
    check gz = 𝟘
    check qn = 𝟘
    check qsm = 𝟘

-- by hand: `x4` is `1 2 … 10` four times: 40 elements, sum 4 × 55 = 220; `zs` sums to 20000, not in `M`; at `Q` the
-- definitions' folds start at `0 ∉ Q`, so `length` and `sum` of `1 2` have no value.
#guard fusedGT.failures.map toString == []

end Rel.Lang.TestFusedM
