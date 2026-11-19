import Rel.Lang.Test.Common

namespace Rel.Lang.Test

open Tab Rel.Lang Rel.Alg Rel

-- a `μ` whose arrays grow every round: no fixed point, so its rounds reach `muCap` and the program reports it
-- pinned to the old layer, whose text this pins: the kernel path (about 40 s) reports the μ alone,
-- "g: the μ at line …, col 19 ran its cap of 1024 rounds without reaching a fixed point", where the old layer's
-- ok bit cannot tell the cap from a capacity overflow and names both
open Rel.Programs.prelude in
set_option rel.kernel false in
rel_program muGrow where
    obj B = 0…1
    r : B ⟶ [B] ≜ {(0,[1])}
    g : B ⟶ [B] ≜ μX : r ∪ (⟨X, r⟩ cat)
#guard !muGrow.ok
#guard muGrow.failures.map (·.msg) == ["an op ran out of capacity (its twin's ok bit is false); in g, or the μ at " ++
  s!"line {decl_line% muGrow + 3}, col 19 ran its cap of 1024 rounds without reaching a fixed point"]

end Rel.Lang.Test
