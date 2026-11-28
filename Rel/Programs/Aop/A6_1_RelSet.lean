import Rel.Programs.Prelude
import Rel.Lang.Laws.AopA6_1_RelSet

/-! # Laws of freyd §6.1 (`AOP/A6_1_RelSet.lean`), in Rel (laws: `Rel/Lang/Laws/AopA6_1_RelSet.lean`) -/

namespace Rel.Programs

open Rel.Programs.prelude in
rel_program aopA6_1_RelSet where
    -- Freyd.Alg.RelSet.rprodMap_id_snd, 07-optimisation.typ:1319: `(𝟙×Q) π₂ = π₂ Q` for any relation `Q`
    theorem rprodIdSnd(Q : β ⟶ γ) : (𝟙×Q) π₂ = π₂ Q by Rel.Lang.Tm.rprodIdSnd_den

end Rel.Programs
