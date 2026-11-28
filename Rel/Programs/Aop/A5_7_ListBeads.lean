import Rel.Programs.Prelude
import Rel.Lang.Laws.AopA5_7_ListBeads

namespace Rel.Programs

open Rel.Programs.prelude in
rel_program aopA5_7_ListBeads where
    -- list(R) is F(R); the prelude's `prefix` row is freyd's `prefix`. A parameter relation R : α ⟶ β (as freyd's R)
    theorem prefixLaxNatural(R : α ⟶ β) : F(R) prefix ⊑ prefix F(R) by Rel.Lang.Tm.prefixLaxNatural_den  -- Freyd.Alg.RelSet.ListRel.prefix_lax_natural, 07-optimisation.typ:512

-- not ported: prefix_not_strict (07-optimisation.typ:513): a negative existential (∃ R, ¬ (list(R) prefix ⊑ …)), not an equation or inclusion of relations

end Rel.Programs
