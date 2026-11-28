import Rel.Programs.Prelude
import Rel.Lang.Laws.AopS2_10
import Rel.Lang.Laws.AopA5_5_Leaf

namespace Rel.Programs

open Rel.Programs.prelude in
rel_program aopA5_5_Leaf where
    -- Freyd.Alg.pair_relCata_eq_relCata_pair, 03-applications.typ:37
    theorem pairRelCataEqRelCataPair(e : 1 ⟶ α, S : α×γ ⟶ α, e2 : 1 ⟶ β, S2 : β×γ ⟶ β) : ⟨⦇[e,S]⦈,⦇[e2,S2]⦈⟩ = ⦇[⟨e,e2⟩, ⟨⟨π₁π₁,π₂⟩S, ⟨π₁π₂,π₂⟩S2⟩]⦈ by Rel.Lang.Tm.pair_relCata_eq_relCata_pair_den
    -- Freyd.Alg.relCata_mapAlg_cancel, 05-datatypes.typ:471 (stated at the list functor 1+X×E)
    theorem relCataMapAlgCancel(e : 1 ⟶ α, S : α×γ ⟶ α) : [nil, snoc] ⦇[e,S]⦈ = [e, (⦇[e,S]⦈ × 𝟙) S] by Rel.Lang.Tm.relCata_mapAlg_cancel_den
    -- Freyd.Alg.relCata_pair_beta, 03-applications.typ:63
    theorem relCataPairBeta(R : α ⟶ β, S : α ⟶ γ) if dom(S) = 𝟙 : ⟨R,S⟩ π₁ = R by Rel.Lang.Tm.relCata_pair_beta_den
    -- helper for relCata_pair_beta (no Freyd row): Λ(T) ∋ = T when Λ(T) is entire
    theorem lamMem(T : α ⟶ β) if dom(Λ(T)) = 𝟙 : Λ(T) ∋ = T by Rel.Lang.Tm.lam_mem_den
    -- Freyd.Alg.pair_relCata_hom, 03-applications.typ:43 (stated at the list functor 1+X×E)
    theorem pairRelCataHom(e : 1 ⟶ α, S : α×γ ⟶ α, e2 : 1 ⟶ β, S2 : β×γ ⟶ β) : [nil, snoc] ⟨⦇[e,S]⦈,⦇[e2,S2]⦈⟩ = [⟨e,e2⟩, (⟨⦇[e,S]⦈,⦇[e2,S2]⦈⟩ × 𝟙) ⟨⟨π₁π₁,π₂⟩S, ⟨π₁π₂,π₂⟩S2⟩] by Rel.Lang.Tm.pair_relCata_hom_den

-- not ported: Freyd.Alg.pair_eq_relCata_pair_iff (03-applications.typ:92): ↔ conclusion over an arbitrary relator F

end Rel.Programs
