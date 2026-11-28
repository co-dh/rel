import Rel.Programs.Prelude
import Rel.Lang.Laws.AopS2_40

/-! # Power-allegory laws of freyd §2.4 (`Freyd/S2_40.lean`), in Rel

Each theorem is named after the last component of its freyd declaration, with the declaration and the companion
position (chapter file : line) beside it. The power object `[β]` holds the lists of `β` and `Λ(R)` the ascending list of
the images of `R`, so a law freyd states for every `R` (`UnguardedPowerAllegory`) carries the premise `dom(Λ(R)) = 𝟙`
where it needs an array at every point (`Rel/Lang/Laws/AopS2_40.lean`). -/

namespace Rel.Programs

open Rel.Programs.prelude in
rel_program aopS2_40 where
    -- only the simple half of `Map(Λ(R))`: the entire half is the premise `dom(Λ(R)) = 𝟙` of the laws below
    theorem lamSimple(R : α ⟶ β) : Λ(R)°Λ(R) ⊑ 𝟙 by Rel.Lang.Tm.lam_simple_den  -- Freyd.Alg.Λ_is_map', 00-laws.typ:375
    theorem lamEpsEq(R : α ⟶ β) if dom(Λ(R)) = 𝟙 : Λ(R)∋ = R by Rel.Lang.Tm.lam_eps_eq_den  -- Freyd.Alg.Λ_eps_eq', 00-laws.typ:378, 05-datatypes.typ:513, 07-optimisation.typ:714
    theorem singletonMapMonic : Λ(𝟙)Λ(𝟙)° ⊑ 𝟙 by Rel.Lang.Tm.lam_id_monic_den  -- Freyd.Alg.singletonMap_monic, 00-laws.typ:385
    theorem lamOfMap(f : α ⟶ β) if dom(f) = 𝟙, f°f ⊑ 𝟙 : Λ(f) = f Λ(𝟙) by Rel.Lang.Tm.lam_of_map_den  -- Freyd.Alg.Λ_of_map, 00-laws.typ:400, 05-datatypes.typ:694

-- not ported: Λ_is_map' (entire half): `dom(Λ(R)) = 𝟙` holds only for a flat target `β` (finite, ordered by `Obj.key`), and `β` is a type variable here; as a premise it would restate the conclusion
-- not ported: simple_le_Λ_eps: `[β]` holds every list, `Λ` only strictly ascending ones, so a simple `F : α ⟶ [β]` returning an unsorted list is not below `Λ(F∋)`
-- not ported: symm_div_eq_Λ_comp: `÷` is the division bounded by the universes `UB`, `UC` of the objects (§3.5), whose side conditions have no counterpart in the allegory identity; the elaborator fixes them per type, so the law has no statement over type variables
-- not ported: subset_eq_recip_supset: the Prelude defines no `⊆`, `⊇` (the freyd `subset`, `supset`), so the law has nothing to state

end Rel.Programs
