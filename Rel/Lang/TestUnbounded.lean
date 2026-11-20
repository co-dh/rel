import Rel.Programs.Prelude

/-! The unbounded number object `obj N` (no elements, no range: every `Int64` is an element and `𝟙` its universe,
    so nothing of it is materialised): `succ`, `plus`, `<` and the rows on it read only what their context bounds.
    Expected rows worked by hand, on the 4-row frame `x` (position ↦ value). -/

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
    bad : N ⟶ N ≜ <
    check sp = {(0,1),(1,2),(2,3),(3,4)}
    check dbl = {(0,60),(1,20),(2,80),(3,40)}
    check tk = {(0,30),(1,10)}
    check ps = {(∗,0 2)}
    check pss = {(∗,1 3)}
    check lt2 = {(0,1),(0,2),(0,3),(1,2),(1,3),(2,3)}

-- by hand: `sp` each position to the next; `dbl` each value doubled; `tk` (take 2, dataframe §3 `(<n) ≫ x`) the
-- positions below 2; `5 0 7 0` has its elements of {3,5,7} at positions 0 and 2, `pss` those plus one; `lt2` the
-- pairs of positions in order. `sp dbl ps pss` hold. `tk`, `lt2` do NOT yet: `GenK.comp` runs a lazy `<` before
-- the table on its right, so nothing bounds that side (the hand values above stay the expectation); `bad` is `<`
-- run closed. All five failures are the unbounded-side message, and only those.
#guard unboundedT.failures.length == 5
#guard (unboundedT.failures.map toString).all fun s =>
  (s.splitOn "< on an unbounded object: nothing bounds its").length == 2

end Rel.Lang.TestUnbounded
