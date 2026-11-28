import Rel.Programs.Prelude
import Rel.Lang.Laws.AopS2_20

/-! # Distributive-allegory laws of freyd §2.2 (`Freyd/S2_20.lean`), in Rel

Each theorem is named after the last component of its freyd declaration, with the declaration and the companion
position (chapter file : line) beside it. The five equations of the freyd `Coproduct` structure (§2.214) are laws of
`inl`, `inr` here (`Rel/Lang/Laws/AopS2_20.lean`). -/

namespace Rel.Programs

open Rel.Programs.prelude in
rel_program aopS2_20 where
    theorem recipUnion(R : α ⟶ β, S : α ⟶ β) : (R ∪ S)° = S° ∪ R° by Rel.Lang.Tm.recip_union_den  -- Freyd.Alg.recip_union, 00-laws.typ:18
    theorem recipZero : 𝟘° = 𝟘 by Rel.Lang.Tm.recip_zero_den  -- Freyd.Alg.recip_zero, 00-laws.typ:182
    theorem u1SelfCompRecip : inl inl° = 𝟙 by Rel.Lang.Tm.inl_inl_conv_den  -- Freyd.Alg.Coproduct.u₁_self_comp_recip, 05-datatypes.typ:180
    theorem u2SelfCompRecip : inr inr° = 𝟙 by Rel.Lang.Tm.inr_inr_conv_den  -- Freyd.Alg.Coproduct.u₂_self_comp_recip, 05-datatypes.typ:180
    theorem u1U2Recip : inl inr° = 𝟘 by Rel.Lang.Tm.inl_inr_conv_den  -- Freyd.Alg.Coproduct.u₁_u₂_recip, 05-datatypes.typ:187
    theorem u2U1Recip : inr inl° = 𝟘 by Rel.Lang.Tm.inr_inl_conv_den  -- Freyd.Alg.Coproduct.u₂_u₁_recip, 05-datatypes.typ:187
    theorem recipUnionEqId : (inl°inl) ∪ (inr°inr) = 𝟙 by Rel.Lang.Tm.inl_conv_inl_union_den  -- Freyd.Alg.Coproduct.recip_union_eq_id, 05-datatypes.typ:191

end Rel.Programs
