import Rel.Programs.Prelude
import Rel.Lang.Laws.AopA4_1

/-! # Laws of freyd §4.1 (`AOP/A4_1.lean`), in Rel (laws: `Rel/Lang/Laws/AopA4_1.lean`) -/

namespace Rel.Programs

open Rel.Programs.prelude in
rel_program aopA4_1 where
    theorem compInterLe(R : α ⟶ β, S : β ⟶ γ, T : β ⟶ γ) : R (S ∩ T) ⊑ (R S) ∩ (R T) by Rel.Lang.Tm.comp_inter_le_den  -- Freyd.Alg.comp_inter_le, 00-laws.typ:253

end Rel.Programs
