import Rel.Programs.Prelude

/-! Symmetric division `R/S ∩ (S/R)°` (`Pre.symDiv`, `Tm.symDiv_den`): `x` to `y` when `R x` and `S y` are one image,
    within the universe of `N`. Expected rows worked by hand. -/

namespace Rel.Lang.TestSymDiv

rel_program symDiv where
    obj N = 0…3
    R : N ⟶ N ≜ {(0,1),(0,2),(1,1)}
    S : N ⟶ N ≜ {(2,1),(2,2),(3,1)}
    check (R/S) ∩ (S/R)° = {(0,2),(1,3),(2,0),(2,1),(3,0),(3,1)}

-- by hand: the images are `R 0 = {1,2}`, `R 1 = {1}`, `R 2 = R 3 = ∅` and `S 0 = S 1 = ∅`, `S 2 = {1,2}`, `S 3 = {1}`;
-- equal images pair `0 ↦ 2`, `1 ↦ 3`, and each of `2`, `3` (empty under `R`) with each of `0`, `1` (empty under `S`).
#guard symDiv.ok

end Rel.Lang.TestSymDiv
