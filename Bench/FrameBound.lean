import Rel.Programs.FrameJoin

/-! The aggregates `count`, `summarize`, `agg` at a large DECLARED object `M = 0…499999` on a frame of few rows: each
    reads `length` or `sum` of a list, whose definition (a fold, one round per element, each round on all of `M`)
    `build` runs as the row cut to `M` (`Prim.cut`, the `.prim` rule), one pass. When the definition ran instead,
    `count` of 1000 rows took 6.3 s at |M| = 5·10⁴ and 35 s at 5·10⁵ (measured); of the 5000 rows here, minutes.
    Expected rows by hand: `x` is `0…4999`, `i mod 10` sums to `500·45 = 22500`, and each residue holds 500
    positions. -/

namespace Rel.Lang.TestFrameBound

open Rel.Programs.prelude Rel.Programs.frame in
rel_program frameBoundT where
    obj M = 0…499999
    below(b : 1 ⟶ M) : M ⟶ M ≜ dom(⟨𝟙, ⊤ b⟩div {(0,0)})
    x : M ⟶ M ≜ below({(∗,5000)})
    check count(x) = {(∗,5000)}
    check summarize(F(x ⟨𝟙, ⊤ {(∗,10)}⟩mod) sum, x) = {(∗,22500)}
    check agg((x ⟨𝟙, ⊤ {(∗,10)}⟩mod)°, length) = below({(∗,10)}) ⊤ {(∗,500)}

#guard frameBoundT.failures.map toString == []

end Rel.Lang.TestFrameBound
