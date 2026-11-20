import Rel.Programs.Prelude

/-! The row `asc` (dataframe §3.1's `σ`): each list to its positions in the stable ascending order of their elements,
    new position `j` to old position `σ[j]`. Expected rows worked by hand from `ascL`. -/

namespace Rel.Lang.TestAsc

open Rel.Programs.prelude in
rel_program ascT where
    obj N = 0…9
    obj Z = -5…5
    obj K = {A,B}
    bab : 1 ⟶ [N] ≜ {(∗,7 3 7)}
    ties : 1 ⟶ [N] ≜ {(∗,4 1 4 1 0)}
    neg : 1 ⟶ [Z] ≜ {(∗,2 -3 0 -5 2)}
    sym : 1 ⟶ [K] ≜ {(∗,B A B)}
    sbab : 1 ⟶ [N] ≜ bab asc
    sties : 1 ⟶ [N] ≜ ties asc
    sneg : 1 ⟶ [N] ≜ neg asc
    ssym : 1 ⟶ [N] ≜ sym asc
    check sbab = {(∗,1 0 2)}
    check sties = {(∗,4 1 3 0 2)}
    check sneg = {(∗,3 1 2 0 4)}
    check ssym = {(∗,1 0 2)}

-- by hand: `7 3 7`: the `3` (position 1) first, then the two `7`s in input order, 0 before 2. `4 1 4 1 0`: `0` at 4,
-- the `1`s at 1 and 3, the `4`s at 0 and 2. `2 -3 0 -5 2`: `-5` at 3, `-3` at 1, `0` at 2, the `2`s at 0 and 4.
#guard ascT.ok

end Rel.Lang.TestAsc
