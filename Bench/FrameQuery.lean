import Rel.Lang.TestFrameQuery

namespace Rel.Lang.TestFrameQuery

-- n = 10⁵, Q4 alone: T = 10⁴ rows per key, each key's total 0+…+9999
open Rel.Programs.prelude queryN in
rel_program query5 where
    P : 1 ⟶ N ≜ ext(ext(ext(ext(D))))
    check q4(ticks(P)) = ran(P) ⟨⟨𝟙, ⊤ {(∗,10000)}⟩div, ⟨𝟙, ⊤ {(∗,10000)}⟩mod ⟨⟨𝟙, succ⟩times, ⊤ {(∗,2)}⟩div⟩
    r4 : N ⟶ N×N ≜ q4(ticks(P))
    check q4t(r4) = ran(D) ⟨𝟙, ⊤ {(∗,49995000)}⟩

#guard query5.failures.map toString == []

end Rel.Lang.TestFrameQuery
