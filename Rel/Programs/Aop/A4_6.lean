import Rel.Programs.Prelude
import Rel.Lang.Laws.AopA4_6

/-! # Laws of freyd §4.6 (`AOP/A4_6.lean`), in Rel (laws: `Rel/Lang/Laws/AopA4_6.lean`)

`Λ(R)` is a list, so a law that reads `Λ(R)` at every point carries `dom(Λ(R)) = 𝟙` (an array exists). `E(R)` is
`Λ(∋ R)`; `Λ(𝟙)` is freyd's `singletonMap`. -/

namespace Rel.Programs

open Rel.Programs.prelude in
rel_program aopA4_6 where
    theorem lamCompEps(R : α ⟶ β) if dom(Λ(R)) = 𝟙 : Λ(R) ∋ = R by Rel.Lang.Tm.lam_comp_mem_den  -- Freyd.Alg.Λ_comp_eps, 00-laws.typ:438
    theorem lamFusion(f : δ ⟶ α, R : α ⟶ β) if dom(f) = 𝟙, f°f ⊑ 𝟙 : Λ(f R) = f Λ(R) by Rel.Lang.Tm.lam_fusion_den  -- Freyd.Alg.Λ_fusion, 00-laws.typ:394 / 05-datatypes.typ:512
    theorem lamAbsorption(S : γ ⟶ α, R : α ⟶ β) if dom(Λ(S)) = 𝟙 : Λ(S) E(R) = Λ(S R) by Rel.Lang.Tm.absorption_den  -- Freyd.Alg.Λ_absorption, 00-laws.typ:413 / 07-optimisation.typ:711 / 05-datatypes.typ:730 (the prelude's `absorption`)
    theorem existsImageEqLamBigUnion(R : α ⟶ β) if dom(Λ(R)) = 𝟙 : E(R) = E(Λ(R)) E(∋) by Rel.Lang.Tm.Eunion_den  -- Freyd.Alg.existsImage_eq_Λ_bigUnion, 00-laws.typ:418 (the prelude's `Eunion`)
    theorem singletonMapNatural(f : α ⟶ β) if dom(f) = 𝟙, f°f ⊑ 𝟙 : f Λ(𝟙) = Λ(f) by Rel.Lang.Tm.singleton_natural_den  -- Freyd.Alg.singletonMap_natural, 00-laws.typ:395 (`Λ(𝟙) E(f)` is fused to `Λ(f)` by the elaborator)

-- not ported: Λ_eps_reflection (00-laws.typ:390, 08-thinning.typ:79): `Λ(∋) = 𝟙` is the prelude's `setify`, which sorts and drops repeats, so it is not `𝟙` on an array that is not a set
-- not ported: Λ_eq_singleton_existsImage (00-laws.typ:410, 07-optimisation.typ:621, 10-appendix.typ:267): `Λ(R) = Λ(𝟙) E(R)`; the elaborator fuses `Λ(𝟙) E(R)` to `Λ(R)` (`Tm.fuseLam`), so the statement is `Λ(R) = Λ(R)`, a syntactic identity

end Rel.Programs
