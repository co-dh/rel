import Rel.Programs.Prelude
import Rel.Lang.Laws.AopA5_5_TypeFunctor

namespace Rel.Programs

-- list reading of freyd's generic F: F(R) is the list relator, cata is the left fold, alpha is nil / snoc
open Rel.Programs.prelude in
rel_program aopA5_5_TypeFunctor where
    -- typeMap_id (02-categories:177)
    theorem fmapId(R : α ⟶ β) : F(𝟙) = 𝟙 by Rel.Lang.Tm.fmap_id_den
    -- typeMap_comp (02-categories:177)
    theorem fmapComp(R : α ⟶ β, S : β ⟶ γ) : F(R) F(S) = F(R S) by Rel.Lang.Tm.fmap_comp_den
    -- typeMap_recip (05-datatypes:387)
    theorem fmapRecip(R : α ⟶ β) : F(R)° = F(R°) by Rel.Lang.Tm.fmap_recip_den
    -- typeMap_fusion (02-categories:163)
    theorem fmapFusion(f : α ⟶ β, e : 1 ⟶ γ, S : γ×β ⟶ γ) : F(f) ⦇[e,S]⦈ = ⦇[e, (𝟙×f) S]⦈ by Rel.Lang.Tm.fmap_fold_den
    -- alpha_natural (02-categories:144), snoc component
    theorem alphaNatSnoc(f : α ⟶ β) : snoc F(f) = (F(f)×f) snoc by Rel.Lang.Tm.fmap_snoc_den

-- not ported: typeMap_defn: F is the primitive row mapRow in rel; its unfolding is the definition, no law
-- not ported: typeMap_fusion_cancel: conjunction of typeMap_fusion and the cata cancel law (foldCancel, Laws/AopA5_5)
-- not ported: alphaT_natural: same statement as alpha_natural at the list reading
-- not ported: alpha_natural_split: wrapper over alpha_natural (nil/snoc split), already the two theorems above
-- not ported: alpha_natural nil component: nil elaborates as a cast prelude prim with a universe guard; fmap_nil_den (Laws) does not match it
-- not ported: tri_defn: definitional unfolding of tri, no law
-- not ported: tri_cata_fusion: Horner rule with relational f; not attempted

end Rel.Programs
