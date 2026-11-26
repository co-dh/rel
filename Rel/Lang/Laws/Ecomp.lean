import Rel.Lang.Den

namespace Rel.Lang
open Rel.Kernel Tab Rel.Rep
open scoped Rel.Core.Rel
open Rel.Core.Rel hiding id comp recip inter union zero le inl inr junc

/-- `E(S T) = E(S) E(T)` (Prelude `Ecomp`): `E` is a functor, on arrays. The premise says `E(S)` has an array at every
    array, i.e. every image of `S` is finite in the declared object `B`; without it the right side has no `ys`. -/
theorem EDen_comp (S : Core.Rel (Obj.El A) (Obj.El B)) (T : Core.Rel (Obj.El B) (Obj.El C))
    (h : ∀ xs, ∃ ys, EDen S xs ys) : EDen (S ≫ T) = EDen S ≫ EDen T := by
  funext xs zs
  refine propext ⟨fun hh => ?_, fun ⟨ys, h1, h2⟩ => ?_⟩
  · obtain ⟨ys, h1⟩ := h xs
    obtain ⟨hp, hy⟩ := (lamDen_iff _ xs ys).1 h1
    obtain ⟨hq, hz⟩ := (lamDen_iff _ xs zs).1 hh
    exact ⟨ys, h1, (lamDen_iff _ ys zs).2 ⟨hq, fun c => (hz c).trans
      ⟨fun ⟨a, ha, b, hS, hT⟩ => ⟨b, (hy b).2 ⟨a, ha, hS⟩, hT⟩,
       fun ⟨b, hb, hT⟩ => by obtain ⟨a, ha, hS⟩ := (hy b).1 hb; exact ⟨a, ha, b, hS, hT⟩⟩⟩⟩
  · obtain ⟨hp, hy⟩ := (lamDen_iff _ xs ys).1 h1
    obtain ⟨hq, hz⟩ := (lamDen_iff _ ys zs).1 h2
    exact (lamDen_iff _ xs zs).2 ⟨hq, fun c => (hz c).trans
      ⟨fun ⟨b, hb, hT⟩ => by obtain ⟨a, ha, hS⟩ := (hy b).1 hb; exact ⟨a, ha, b, hS, hT⟩,
       fun ⟨a, ha, b, hS, hT⟩ => ⟨b, (hy b).2 ⟨a, ha, hS⟩, hT⟩⟩⟩

#print axioms EDen_comp

end Rel.Lang
