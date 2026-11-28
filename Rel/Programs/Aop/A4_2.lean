import Rel.Programs.Prelude
import Rel.Lang.Laws.AopA4_2

/-! # Laws of freyd §4.2 (`AOP/A4_2.lean`), in Rel (laws: `Rel/Lang/Laws/AopA4_2.lean`) -/

namespace Rel.Programs

open Rel.Programs.prelude in
rel_program aopA4_2 where
    -- `S = R° ∧ Map R` is three theorems: `S = R°`, `dom(R) = 𝟙`, `R°R ⊑ 𝟙`
    theorem recipOfCompId(R : α ⟶ β, S : β ⟶ α) if 𝟙 ⊑ R S, S R ⊑ 𝟙 : S = R° by Rel.Lang.Tm.recip_of_comp_id_den  -- Freyd.Alg.recip_of_comp_id, 04-relations.typ:16
    theorem entireOfCompId(R : α ⟶ β, S : β ⟶ α) if 𝟙 ⊑ R S : dom(R) = 𝟙 by Rel.Lang.Tm.entire_of_comp_id_den  -- Freyd.Alg.recip_of_comp_id (Map R, entire), 04-relations.typ:16
    theorem simpleOfCompId(R : α ⟶ β, S : β ⟶ α) if 𝟙 ⊑ R S, S R ⊑ 𝟙 : R°R ⊑ 𝟙 by Rel.Lang.Tm.simple_of_comp_id_den  -- Freyd.Alg.recip_of_comp_id (Map R, simple), 04-relations.typ:16
    theorem simpleDistInterRecip(g : γ ⟶ β, X : α ⟶ β, Y : α ⟶ β) if g°g ⊑ 𝟙 : (X ∩ Y) g° = (X g°) ∩ (Y g°) by Rel.Lang.Tm.simple_dist_inter_recip_den  -- Freyd.Alg.simple_dist_inter_recip, 00-laws.typ:79

end Rel.Programs
