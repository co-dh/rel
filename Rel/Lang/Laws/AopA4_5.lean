import Rel.Lang.Laws.AopS2_10

/-! # Laws of `Freyd/A4_5.lean` (B&dM §4.5, subtraction), on the concrete core: `Rel/Programs/Aop/A4_5.lean` states each
as `theorem <name> … by Rel.Lang.Tm.<name>_den`. `R − S` is `Core.Rel.diff`, `R a b ∧ ¬ S a b`. -/

namespace Rel.Lang
open Tab Rel.Rep
open scoped Rel.Core.Rel
open Rel.Core.Rel hiding id comp recip inter union zero le inl inr junc

theorem Tm.sub_zero_den {A B : Obj} {R : Tm A B} (ρ : Val) : (Tm.diff R Tm.zero).den ρ = R.den ρ :=
  Core.Rel.ext fun _ _ => ⟨fun ⟨h, _⟩ => h, fun h => ⟨h, fun x => x⟩⟩

theorem Tm.union_sub_absorb_den {A B : Obj} {R S : Tm A B} (ρ : Val) :
    (Tm.join R (Tm.diff S R)).den ρ = (Tm.join R S).den ρ :=
  Core.Rel.ext fun a b => ⟨fun h => h.elim Or.inl fun h => Or.inr h.1, fun h =>
    h.elim Or.inl fun hs => (Classical.em (R.den ρ a b)).elim Or.inl fun hr => Or.inr ⟨hs, hr⟩⟩

theorem Tm.sub_union_den {A B : Obj} {R S T : Tm A B} (ρ : Val) :
    (Tm.diff R (Tm.join S T)).den ρ = (Tm.diff (Tm.diff R S) T).den ρ :=
  Core.Rel.ext fun _ _ => ⟨fun ⟨hr, h⟩ => ⟨⟨hr, fun hs => h (Or.inl hs)⟩, fun ht => h (Or.inr ht)⟩,
    fun ⟨⟨hr, hs⟩, ht⟩ => ⟨hr, fun h => h.elim hs ht⟩⟩

theorem Tm.union_sub_distrib_den {A B : Obj} {R S T : Tm A B} (ρ : Val) :
    (Tm.diff (Tm.join R S) T).den ρ = (Tm.join (Tm.diff R T) (Tm.diff S T)).den ρ :=
  Core.Rel.ext fun _ _ => ⟨fun ⟨h, ht⟩ => h.elim (fun hr => Or.inl ⟨hr, ht⟩) fun hs => Or.inr ⟨hs, ht⟩,
    fun h => h.elim (fun ⟨hr, ht⟩ => ⟨Or.inl hr, ht⟩) fun ⟨hs, ht⟩ => ⟨Or.inr hs, ht⟩⟩

end Rel.Lang
