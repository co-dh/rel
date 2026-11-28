import Rel.Lang.Laws.AopS2_10

/-! # Laws of `Freyd/A4_1.lean` (B&dM §4.1), on the concrete core: `Rel/Programs/Aop/A4_1.lean` states each as
`theorem <name> … by Rel.Lang.Tm.<name>_den`. -/

namespace Rel.Lang
open Tab Rel.Rep
open scoped Rel.Core.Rel
open Rel.Core.Rel hiding id comp recip inter union zero le inl inr junc

theorem Tm.comp_inter_le_den {A B C : Obj} {R : Tm A B} {S T : Tm B C} (ρ : Val) :
    (Tm.comp R (Tm.meet S T)).den ρ ⊑ (Tm.meet (Tm.comp R S) (Tm.comp R T)).den ρ :=
  Core.Rel.le_iff.2 fun _ _ ⟨b, hr, hs, ht⟩ => ⟨⟨b, hr, hs⟩, ⟨b, hr, ht⟩⟩

end Rel.Lang
