import Rel.Programs.Prelude
import Rel.Lang.Laws.AopA5_1

/-! # Rows of freyd `AOP/A5_1.lean` (B&dM §5.1 Relators), in Rel (laws: `Rel/Lang/Laws/AopA5_1.lean`) -/

namespace Rel.Programs

-- the list instance: freyd's relator parameter `F` is the list relator `F(R)`, whose relator axioms are `mapDen_id/comp/recip/mono`
open Rel.Programs.prelude in
rel_program aopA5_1 where
    -- Relator.map_is_map (05-datatypes:19) at F(R) = list relator: `Map f` is the two halves, entire and simple
    theorem mapIsMapEntire(f : α ⟶ β) if 𝟙 ⊑ f f° : 𝟙 ⊑ F(f) F(f)° by Rel.Lang.Tm.map_is_map_entire_den
    theorem mapIsMapSimple(f : α ⟶ β) if f° f ⊑ 𝟙 : F(f)° F(f) ⊑ 𝟙 by Rel.Lang.Tm.map_is_map_simple_den
    -- Relator.map_inter_le (05-datatypes:37) at the list relator
    theorem mapInterLe(R : α ⟶ β, S : α ⟶ β) : F(R ∩ S) ⊑ F(R) ∩ F(S) by Rel.Lang.Tm.map_inter_le_den
    -- Relator.map_inter_coreflexive (05-datatypes:34) at the list relator; stated for any R, S (stronger: no coreflexivity needed)
    theorem mapInterCoreflexive(R : α ⟶ β, S : α ⟶ β) : F(R ∩ S) = F(R) ∩ F(S) by Rel.Lang.Tm.map_inter_coreflexive_den
    -- Relator.map_dom (05-datatypes:39) at the list relator
    theorem mapDom(R : α ⟶ β) : F(dom(R)) = dom(F(R)) by Rel.Lang.Tm.map_dom_den

-- not ported: Relator.map_recip_map (05-datatypes:19): the converse of a map; at F(R) it is fmapRecip (A5_5_TypeFunctor) for every R, not only maps
-- not ported: Relator.map_recip, Relator.preservesRecip_of_tabular (05-datatypes:29, :26): at F(R) both are fmapRecip (A5_5_TypeFunctor), cited not restated
-- not ported: Relator.map_laxNatural (05-datatypes:808): needs a second relator and a family φ, elements quantified over R (laxNatural_* are not portable)

end Rel.Programs
