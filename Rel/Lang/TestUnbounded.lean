import Rel.Programs.Prelude

/-! The unbounded number object `obj N` (no elements, no range: every `Int64` is an element and `𝟙` its universe,
    so nothing of it is materialised): `succ`, `plus`, `<` and the rows on it read only what their context bounds.
    Expected rows worked by hand, on the 4-row frame `x` (position ↦ value) and the set `p` = {2,5,7,9}. -/

namespace Rel.Lang.TestUnbounded

open Rel.Programs.prelude in
rel_program unboundedT where
    obj N
    x : N ⟶ N ≜ {(0,30),(1,10),(2,40),(3,20)}
    p : N ⟶ N ≜ {(2,2),(5,5),(7,7),(9,9)}
    xs : 1 ⟶ [N] ≜ {(∗,5 0 7 0)}
    big : N ⟶ N ≜ {(3,3),(5,5),(7,7)}
    sp : N ⟶ N ≜ dom(x) succ
    dbl : N ⟶ N ≜ x ⟨𝟙,𝟙⟩plus
    tk : N ⟶ N ≜ dom(<{(2,2)}) x
    ps : 1 ⟶ [N] ≜ xs positions(big)
    pss : 1 ⟶ [N] ≜ ps E(succ)
    lt2 : N ⟶ N ≜ dom(x) < dom(x)
    gt : N ⟶ N ≜ p > p
    ge : N ⟶ N ≜ p ≥ p
    pl : N ⟶ N ≜ p (p + p)
    len : 1 ⟶ N ≜ xs length
    rank : N ⟶ N ≜ p Λ(> p) length
    wh : N ⟶ N ≜ rank°
    bad : N ⟶ N ≜ <
    check sp = {(0,1),(1,2),(2,3),(3,4)}
    check dbl = {(0,60),(1,20),(2,80),(3,40)}
    check tk = {(0,30),(1,10)}
    check ps = {(∗,0 2)}
    check pss = {(∗,1 3)}
    check lt2 = {(0,1),(0,2),(0,3),(1,2),(1,3),(2,3)}
    check gt = {(5,2),(7,2),(7,5),(9,2),(9,5),(9,7)}
    check ge = {(2,2),(5,2),(5,5),(7,2),(7,5),(7,7),(9,2),(9,5),(9,7),(9,9)}
    check pl = {(2,4),(5,10),(7,14),(9,18)}
    check len = {(∗,4)}
    check rank = {(2,0),(5,1),(7,2),(9,3)}
    check wh = {(0,2),(1,5),(2,7),(3,9)}

-- by hand: `sp` each position to the next; `dbl` each value doubled; `tk` (take 2, dataframe §3 `(<n) ≫ x`) the
-- positions below 2; `5 0 7 0` has its elements of {3,5,7} at positions 0 and 2, `pss` those plus one; `lt2` the
-- pairs of positions in order; `gt`, `ge` the pairs of `p` in descending (or equal) order; `pl` each element doubled;
-- `len` 4 elements; `rank` each element of `p` to the count of elements below it (2 has none, 9 has 2 5 7), `wh` its
-- converse. `bad` is `<` with nothing on either side: its one failure, the left side named.
#guard unboundedT.failures.map toString == ["bad: < on an unbounded object: nothing bounds its left side; compose it " ++
  "with a table on that side (a leaf on demand ran with its domain unknown)"]

end Rel.Lang.TestUnbounded
