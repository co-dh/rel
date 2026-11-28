import Rel.Programs.Prelude
import Rel.Lang.Laws.AopS2_10

/-! # Allegory laws of freyd §2.10 (`Freyd/S2_10.lean`), in Rel

Each theorem is named after the last component of its freyd declaration, with the declaration and the companion
position (chapter file : line) beside it. Premises `Entire R`, `Simple f` are `dom(R) = 𝟙`, `f°f ⊑ 𝟙`
(`Rel/Lang/Laws/AopS2_10.lean`). -/

namespace Rel.Programs

open Rel.Programs.prelude in
rel_program aopS2_10 where
    theorem recipInter(R : α ⟶ β, S : α ⟶ β) : (R ∩ S)° = R° ∩ S° by Rel.Lang.Tm.recip_inter_den  -- Freyd.Alg.Allegory.recip_inter, 00-laws.typ:20
    theorem recipMono(R : α ⟶ β, S : α ⟶ β) if R ⊑ S : R° ⊑ S° by Rel.Lang.Tm.recip_mono_den  -- Freyd.Alg.recip_mono, 00-laws.typ:240
    theorem domInter(R : α ⟶ β, S : α ⟶ β) : dom(R ∩ S) = 𝟙 ∩ (S R°) by Rel.Lang.Tm.dom_inter_den  -- Freyd.Alg.dom_inter, 00-laws.typ:267
    theorem domCompLe(R : α ⟶ β, S : β ⟶ γ) : dom(R S) ⊑ dom(R) by Rel.Lang.Tm.dom_comp_le_den  -- Freyd.Alg.dom_comp_le, 00-laws.typ:265
    theorem entireComp(R : α ⟶ β, S : β ⟶ γ) if dom(R) = 𝟙, dom(S) = 𝟙 : dom(R S) = 𝟙 by Rel.Lang.Tm.entire_comp_den  -- Freyd.Alg.entire_comp, 00-laws.typ:275
    theorem entireOfCompEntire(R : α ⟶ β, S : β ⟶ γ) if dom(R S) = 𝟙 : dom(R) = 𝟙 by Rel.Lang.Tm.entire_of_comp_entire_den  -- Freyd.Alg.entire_of_comp_entire, 00-laws.typ:280
    theorem simpleComp(f : α ⟶ β, g : β ⟶ γ) if f°f ⊑ 𝟙, g°g ⊑ 𝟙 : (f g)°(f g) ⊑ 𝟙 by Rel.Lang.Tm.simple_comp_den  -- Freyd.Alg.simple_comp, 00-laws.typ:276
    -- only the entire half of `Map f` is used, so the premise is `dom(f) = 𝟙`
    theorem mapEntireLe(f : α ⟶ β) if dom(f) = 𝟙 : 𝟙 ⊑ f f° by Rel.Lang.Tm.map_entire_le_den  -- Freyd.Alg.map_entire_le, 00-laws.typ:75
    theorem eqOfLeEntireSimple(X : α ⟶ β, Y : α ⟶ β) if dom(X) = 𝟙, Y°Y ⊑ 𝟙, X ⊑ Y : X = Y by Rel.Lang.Tm.eq_of_le_entire_simple_den  -- Freyd.Alg.eq_of_le_entire_simple, 07-optimisation.typ:679

-- not ported: recipId (Freyd.Alg.recip_id): the elaborator reduces `𝟙°` to `𝟙` (`Elab.convs`), so the statement is `𝟙 = 𝟙`, a syntactic identity
-- not ported: mapComp (map_comp): `Map (f ≫ g)` concludes entire ∧ simple, and a theorem here states one relation law; it is `entire_comp` with `simple_comp`

end Rel.Programs
