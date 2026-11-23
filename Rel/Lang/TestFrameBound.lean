import Rel.Programs.FrameJoin

/-! The aggregates `count`, `summarize`, `agg` at a large DECLARED object `M = 0…49999` on a frame of few rows: each
    reads `length` or `sum` of a list, whose definition (a fold, one round per element, each round on all of `M`)
    `build` runs as the row cut to `M` (`Prim.cut`, the `.prim` rule), one pass. When the definition ran instead,
    `count` of 1000 rows took 6.3 s at |M| = 5·10⁴ and 35 s at 5·10⁵ (measured); of 5000 rows at 5·10⁵ (`Bench/FrameBound.lean`), minutes.
    Expected rows by hand: `x` is `0…499`, `i mod 10` sums to `50·45 = 2250`, and each residue holds 50
    positions. -/

namespace Rel.Lang.TestFrameBound

open Rel.Programs.prelude Rel.Programs.frame in
rel_program frameBoundT where
    obj M = 0…49999
    below(b : 1 ⟶ M) : M ⟶ M ≜ dom(⟨𝟙, ⊤ b⟩div {(0,0)})
    x : M ⟶ M ≜ below({(∗,500)})
    check count(x) = {(∗,500)}
    check summarize(F(x ⟨𝟙, ⊤ {(∗,10)}⟩mod) sum, x) = {(∗,2250)}
    check agg((x ⟨𝟙, ⊤ {(∗,10)}⟩mod)°, length) = below({(∗,10)}) ⊤ {(∗,50)}

#guard frameBoundT.failures.map toString == []

end Rel.Lang.TestFrameBound
