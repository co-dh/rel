import Rel.Programs.Prelude
import Rel.Lang.Laws.AopA4_4

/-! # Laws of freyd §4.4 (`AOP/A4_4.lean`), in Rel (laws: `Rel/Lang/Laws/AopA4_4.lean`)

Freyd's `R ⇨ S` is the prelude's `R ⇒ S` (`∼R ∪ S`: the Boolean allegory `Rel` is its own Heyting one). A map is
`dom(f) = 𝟙` with `f°f ⊑ 𝟙`. -/

namespace Rel.Programs

open Rel.Programs.prelude in
rel_program aopA4_4 where
    theorem implInter(R : α ⟶ β, S : α ⟶ β, T : α ⟶ β) : (R ⇒ (S ∩ T)) = (R ⇒ S) ∩ (R ⇒ T) by Rel.Lang.Tm.impl_inter_den  -- Freyd.Alg.impl_inter, 00-laws.typ:67
    theorem implCurry(R : α ⟶ β, S : α ⟶ β, T : α ⟶ β) : (R ⇒ (S ⇒ T)) = ((R ∩ S) ⇒ T) by Rel.Lang.Tm.impl_curry_den  -- Freyd.Alg.impl_curry, 00-laws.typ:144
    theorem mapCompDiv(f : δ ⟶ α, R : α ⟶ γ, S : β ⟶ γ) if dom(f) = 𝟙, f°f ⊑ 𝟙 : f (R/S) = (f R)/S by Rel.Lang.Tm.map_comp_div_den  -- Freyd.Alg.map_comp_div, 00-laws.typ:109
    theorem divCompRecipMap(f : δ ⟶ β, R : α ⟶ γ, S : β ⟶ γ) if dom(f) = 𝟙, f°f ⊑ 𝟙 : R/(f S) = (R/S) f° by Rel.Lang.Tm.div_comp_recip_map_den  -- Freyd.Alg.div_comp_recip_map, 00-laws.typ:124

end Rel.Programs
