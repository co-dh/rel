import Rel.Programs.Prelude
import Rel.Lang.Laws.AopA5_2

/-! # Product laws of freyd `AOP/A5_2.lean` (chapter 05-datatypes), in Rel

Each theorem is named after the last component of its freyd declaration, with the declaration and the companion
position beside it. `⟨R,S⟩` is `RelProd.pair`, `π₁`/`π₂` its projections, `⟨π₁R,π₂S⟩` is `prodMap` (`R × S` elaborates with a domain guard, so it is not used)
(`Rel/Lang/Laws/AopA5_2.lean`). -/

namespace Rel.Programs

open Rel.Programs.prelude in
rel_program aopA5_2 where
    theorem pairOutlLe(R : α ⟶ β, S : α ⟶ γ) : ⟨R,S⟩π₁ ⊑ R by Rel.Lang.Tm.pair_outl_le_den  -- Freyd.Alg.RelProd.pair_outl_le, 05-datatypes.typ:63
    theorem pairOutrLe(R : α ⟶ β, S : α ⟶ γ) : ⟨R,S⟩π₂ ⊑ S by Rel.Lang.Tm.pair_outr_le_den  -- Freyd.Alg.RelProd.pair_outr_le, 05-datatypes.typ:63
    theorem pairOutl(R : α ⟶ β, S : α ⟶ γ) : ⟨R,S⟩π₁ = dom(S) R by Rel.Lang.Tm.pair_outl_den  -- Freyd.Alg.RelProd.pair_outl, 05-datatypes.typ:56
    theorem pairOutr(R : α ⟶ β, S : α ⟶ γ) : ⟨R,S⟩π₂ = dom(R) S by Rel.Lang.Tm.pair_outr_den  -- Freyd.Alg.RelProd.pair_outr, 05-datatypes.typ:58
    theorem pairProdMap(X : α ⟶ β, Y : α ⟶ γ, R : β ⟶ δ, S : γ ⟶ ε) : ⟨X,Y⟩⟨π₁R,π₂S⟩ = ⟨X R, Y S⟩ by Rel.Lang.Tm.pair_prodMap_den  -- Freyd.Alg.RelProd.pair_prodMap, 05-datatypes.typ:100
    theorem pairRecipPair(X : α ⟶ β, Y : α ⟶ γ, R : δ ⟶ β, S : δ ⟶ γ) : ⟨X,Y⟩⟨R,S⟩° = (X R°) ∩ (Y S°) by Rel.Lang.Tm.pair_recip_pair_den  -- Freyd.Alg.RelProd.pair_recip_pair, 05-datatypes.typ:116
    theorem recipPairPairLe(R : α ⟶ β, S : α ⟶ γ, U : α ⟶ δ, V : α ⟶ ε) : ⟨R,S⟩°⟨U,V⟩ ⊑ ⟨π₁|(R° U),π₂|(S° V)⟩ by Rel.Lang.Tm.recip_pair_pair_le_den  -- Freyd.Alg.RelProd.recip_pair_pair_le, 05-datatypes.typ:120
    theorem compPairLe(X : α ⟶ β, R : β ⟶ γ, S : β ⟶ δ) : X ⟨R,S⟩ ⊑ ⟨X R, X S⟩ by Rel.Lang.Tm.comp_pair_le_den  -- Freyd.Alg.RelProd.comp_pair_le, 05-datatypes.typ:129
    -- only the simple half of `Map f` is used, so the premise is `f°f ⊑ 𝟙`
    theorem mapCompPair(f : α ⟶ β, R : β ⟶ γ, S : β ⟶ δ) if f°f ⊑ 𝟙 : f ⟨R,S⟩ = ⟨f R, f S⟩ by Rel.Lang.Tm.map_comp_pair_den  -- Freyd.Alg.RelProd.map_comp_pair, 05-datatypes.typ:124
    theorem prodMapOutlLe(R : α ⟶ γ, S : β ⟶ δ) : ⟨π₁R,π₂S⟩π₁ ⊑ π₁ R by Rel.Lang.Tm.prodMap_outl_le_den  -- Freyd.Alg.prodMap_outl_le, 05-datatypes.typ:87
    theorem prodMapOutrLe(R : α ⟶ γ, S : β ⟶ δ) : ⟨π₁R,π₂S⟩π₂ ⊑ π₂ S by Rel.Lang.Tm.prodMap_outr_le_den  -- Freyd.Alg.prodMap_outr_le, 05-datatypes.typ:87

-- not ported: prodMap_out_le (Freyd.Alg.prodMap_out_le): a conjunction, ported as prodMapOutlLe and prodMapOutrLe
-- not ported: unzip_lax (Freyd.Alg.unzip_lax): states a law of an arbitrary relator `F` over `unzip F`; rel has no relator variable, only functors `F(R)` of a fixed shape

end Rel.Programs
