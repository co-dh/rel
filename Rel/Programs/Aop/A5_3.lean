import Rel.Programs.Prelude
import Rel.Lang.Laws.AopA5_3

/-! # Sum laws of B&dM §5.3 (`AOP/A5_3.lean`), in Rel

Each theorem is named after the last component of its freyd declaration, with the declaration and the companion
position (chapter file : line) beside it. `[R,S]` is `inl°R ∪ inr°S`, `R ⊕ S` is `[R inl, S inr]` (prelude `_⊕_`);
`C.u₁`, `C.u₂` are `inl`, `inr` (`Rel/Lang/Laws/AopA5_3.lean`). -/

namespace Rel.Programs

open Rel.Programs.prelude in
rel_program aopA5_3 where
    theorem juncComp(R : α ⟶ γ, S : β ⟶ γ, Z : γ ⟶ δ) : [R, S] Z = [R Z, S Z] by Rel.Lang.Tm.junc_comp_den  -- Freyd.Alg.junc_comp, 05-datatypes.typ:166 and 07-optimisation.typ:822
    theorem u1Junc(R : α ⟶ γ, S : β ⟶ γ) : inl [R, S] = R by Rel.Lang.Tm.u1_junc_den  -- Freyd.Alg.u₁_junc, 05-datatypes.typ:159
    theorem u2Junc(R : α ⟶ γ, S : β ⟶ γ) : inr [R, S] = S by Rel.Lang.Tm.u2_junc_den  -- Freyd.Alg.u₂_junc, 05-datatypes.typ:159
    theorem juncUnique(R : α ⟶ γ, S : β ⟶ γ, T : α+β ⟶ γ) if inl T = R, inr T = S : T = [R, S] by Rel.Lang.Tm.junc_unique_den  -- Freyd.Alg.junc_unique, 05-datatypes.typ:159
    theorem juncRecipJunc(U : α ⟶ δ, V : β ⟶ δ, R : α ⟶ γ, S : β ⟶ γ) : [U, V]° [R, S] = (U° R) ∪ (V° S) by Rel.Lang.Tm.junc_recip_junc_den  -- Freyd.Alg.junc_recip_junc, 05-datatypes.typ:165
    theorem lamJunc(R : α ⟶ γ, S : β ⟶ γ) : Λ([R, S]) = [Λ(R), Λ(S)] by Rel.Lang.Tm.Λ_junc_den  -- Freyd.Alg.Λ_junc, 05-datatypes.typ:219
    -- `R = Λ(R)∋` needs an array of images at every point, so the premises are `dom(Λ(R)) = 𝟙`, `dom(Λ(S)) = 𝟙`
    theorem juncEqLamJuncEps(R : α ⟶ γ, S : β ⟶ γ) if dom(Λ(R)) = 𝟙, dom(Λ(S)) = 𝟙 : [R, S] = [Λ(R), Λ(S)] ∋ by Rel.Lang.Tm.junc_eq_Λ_junc_eps_den  -- Freyd.Alg.junc_eq_Λ_junc_eps, 05-datatypes.typ:157
    theorem u1JuncLamEps(R : α ⟶ γ, S : β ⟶ γ) if dom(Λ(R)) = 𝟙 : inl [Λ(R), Λ(S)] ∋ = R by Rel.Lang.Tm.u1_junc_Λ_eps_den  -- Freyd.Alg.u_junc_Λ_eps (first conjunct), 05-datatypes.typ:222
    theorem u2JuncLamEps(R : α ⟶ γ, S : β ⟶ γ) if dom(Λ(S)) = 𝟙 : inr [Λ(R), Λ(S)] ∋ = S by Rel.Lang.Tm.u2_junc_Λ_eps_den  -- Freyd.Alg.u_junc_Λ_eps (second conjunct), 05-datatypes.typ:222
    theorem sumMapInterJuncRecip(R : α ⟶ β, S : α' ⟶ β', P : α ⟶ γ, Q : α' ⟶ γ, U : β ⟶ γ, V : β' ⟶ γ) : [R inl, S inr] ∩ ([P, Q] [U, V]°) = [(R ∩ (P U°)) inl, (S ∩ (Q V°)) inr] by Rel.Lang.Tm.sumMap_inter_junc_recip_den  -- Freyd.Alg.sumMap_inter_junc_recip, 05-datatypes.typ:246

end Rel.Programs
