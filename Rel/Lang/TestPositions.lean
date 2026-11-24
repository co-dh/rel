import Rel.Programs.Prelude

/-! The row `positions(p)` (dataframe §3.1's `where(dom(xs ≫ p))`): each list to the positions, ascending, of its
    elements in `dom(p)`. Expected rows worked by hand from `positionsL`. -/

namespace Rel.Lang.TestPositions

open Rel.Programs.prelude in
rel_program positionsT where
    obj N = 0…9
    big : N ⟶ N ≜ dom(<°{(2,∗)})
    dup : 1 ⟶ [N] ≜ {(∗,5 0 7 0 3 3)}
    all : 1 ⟶ [N] ≜ {(∗,3 4 5)}
    none : 1 ⟶ [N] ≜ {(∗,1 2 1)}
    pdup : 1 ⟶ [N] ≜ dup positions(big)
    pall : 1 ⟶ [N] ≜ all positions(big)
    pnone : 1 ⟶ [N] ≜ none positions(big)
    nnone : 1 ⟶ N ≜ pnone length
    pempty : 1 ⟶ [N] ≜ pnone positions(big)
    nempty : 1 ⟶ N ≜ pempty length
    twelve : 1 ⟶ [N] ≜ {(∗,3 4 5 6 7 8 9 3 4 5 6 7)}
    ptwelve : 1 ⟶ [N] ≜ twelve positions(big)
    check pdup = {(∗,0 2 4 5)}
    check ptwelve = 𝟘
    check pall = {(∗,0 1 2)}
    check nnone = {(∗,0)}
    check nempty = {(∗,0)}

-- by hand: `big` keeps 3…9. `5 0 7 0 3 3` keeps positions 0 2 4 5 (the two `3`s each count: positions, not values);
-- `3 4 5` keeps every position; `1 2 1` none, so `pnone` is the empty list (checked by its length: a literal list
-- cannot be empty), and `positions` of that empty input is empty again. `twelve` passes everywhere, but its positions
-- 10 and 11 lie outside `N = 0…9`, so `positions` cut to `N` gives it no list at all (`Tm.positionsDef_den`).
#guard positionsT.ok

end Rel.Lang.TestPositions
