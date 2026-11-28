import Rel.Programs.Prelude
import Rel.Lang.Laws.AopA4_5

/-! # Laws of freyd §4.5 (`AOP/A4_5.lean`, subtraction), in Rel (laws: `Rel/Lang/Laws/AopA4_5.lean`) -/

namespace Rel.Programs

open Rel.Programs.prelude in
rel_program aopA4_5 where
    theorem subZero(R : α ⟶ β) : R − 𝟘 = R by Rel.Lang.Tm.sub_zero_den  -- Freyd.Alg.sub_zero, 06-recursive.typ:552
    theorem unionSubAbsorb(R : α ⟶ β, S : α ⟶ β) : R ∪ (S − R) = R ∪ S by Rel.Lang.Tm.union_sub_absorb_den  -- Freyd.Alg.union_sub_absorb, 06-recursive.typ:554
    theorem subUnion(R : α ⟶ β, S : α ⟶ β, T : α ⟶ β) : R − (S ∪ T) = (R − S) − T by Rel.Lang.Tm.sub_union_den  -- Freyd.Alg.sub_union, 06-recursive.typ:557
    theorem unionSubDistrib(R : α ⟶ β, S : α ⟶ β, T : α ⟶ β) : (R ∪ S) − T = (R − T) ∪ (S − T) by Rel.Lang.Tm.union_sub_distrib_den  -- Freyd.Alg.union_sub_distrib, 06-recursive.typ:560

end Rel.Programs
