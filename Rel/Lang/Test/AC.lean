import Rel.Lang.Test.Common

namespace Rel.Lang.Test

open Tab Rel.Lang Rel.Alg Rel

-- arc consistency on `y = x²` with both arcs, `x → y` by `sq` and `y → x` by `sq°`
open Rel.Programs.prelude in
rel_program square where
    obj V = {x,y}
    obj D = 0…9
    A : V ⟶ V ≜ {(x,y)}
    Ac : V ⟶ V ≜ A°
    sq : D ⟶ D ≜ {(0,0),(1,1),(2,4),(3,9)}
    sqc : D ⟶ D ≜ sq°
    uV : V ⟶ V ≜ 𝟙(V)
    uD : D ⟶ D ≜ 𝟙(D)
    s : V ⟶ D ≜ ⊤(V,D)
    z : V ⟶ D ≜ νZ : s ∩ (A\(Z sq)) ∩ (A°\(Z sq°))
    check z = {(x,0),(x,1),(x,2),(x,3),(y,0),(y,1),(y,4),(y,9)}
#guard square.ok


end Rel.Lang.Test
