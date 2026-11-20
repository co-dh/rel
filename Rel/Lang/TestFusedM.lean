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

end Rel.Lang.TestFusedM
