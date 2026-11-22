import Rel.Lang.Test.Common

namespace Rel.Lang.Test

open Tab Rel.Lang Rel.Alg Rel

-- a `μ` whose arrays grow every round: no fixed point, so its rounds reach `muCap` and the program reports it
open Rel.Programs.prelude in
rel_program muGrow where
    obj B = 0…1
    r : B ⟶ [B] ≜ {(0,[1])}
    g : B ⟶ [B] ≜ μX : r ∪ (⟨X, r⟩ cat)
#guard !muGrow.ok
#guard muGrow.failures.map (·.msg) ==
  [s!"g: the μ at line {decl_line% muGrow + 3}, col 19 ran its cap of 1024 rounds without reaching a fixed point"]

end Rel.Lang.Test
