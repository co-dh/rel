import Rel.Lang.Laws.Eunion
import Rel.Lang.Laws.AopS2_10

/-! # Laws of `AOP/A8_3.lean` (B&dM §8.3), on the concrete core

`Rel/Programs/Aop/A8_3.lean` states each as `theorem <name> … by Rel.Lang.Tm.<name>_den`. `Λ(∋)` is the prelude's `setify`
on arrays (sorted, repeat-free); `sort(≼) = setify° ordered(≼)`. -/

namespace Rel.Lang
open Tab Rel.Rep
open scoped Rel.Core.Rel
open Rel.Core.Rel hiding id comp recip inter union zero le inl inr junc

/-- (8.7) `sort(≼) minL(R) ⊑ est(R)`, with `ordered(≼)` any coreflexive `C`: `Λ(∋)` is single-valued, so
`Λ(∋)° C Λ(∋)` is below `𝟙`. -/
theorem Tm.sortCompMinLLe_den {A : Obj} {C : Tm A.arr A.arr} {E : Tm A.arr A} (ρ : Val)
    (hC : C.den ρ ⊑ (Tm.id (A := A.arr)).den ρ) :
    (Tm.comp (Tm.comp (Tm.comp (Tm.comp Tm.id Tm.mem.lam).conv C) Tm.mem.lam) E).den ρ ⊑ E.den ρ := by
  refine le_iff.mpr fun xs b h => ?_
  simp only [Tm.den, Core.Rel.comp] at h
  obtain ⟨w, ⟨z, ⟨y, ⟨u, hu, hL⟩, hC'⟩, hL'⟩, hE⟩ := h
  obtain rfl : y = u := hu
  obtain rfl : y = z := le_iff.mp hC y z hC'
  obtain rfl := lamDen_unique _ hL hL'
  exact hE

/-- (8.6) `sort(≼) thinL(Q) ⊑ thin(Q) sort(≼)` with `thinL(Q) = (Λ(∋) T Λ(∋)°) ∩ S` for any `T` (`thin(Q)`), any `S`
(`subseq`) and `ordered(≼)` any coreflexive `C` with `C S ⊑ S C`, after any `X`: `Λ(∋)` is single-valued, so
`Λ(∋)° (Λ(∋) T Λ(∋)°)` is below `T Λ(∋)°`, and `C` moves across `S` by its hypothesis. -/
theorem Tm.sortCompThinLLe_den {B A : Obj} {X : Tm B A.arr} {C S T : Tm A.arr A.arr} (ρ : Val)
    (hC : C.den ρ ⊑ (Tm.id (A := A.arr)).den ρ) (hCS : (Tm.comp C S).den ρ ⊑ (Tm.comp S C).den ρ) :
    (Tm.comp (Tm.comp (Tm.comp X (Tm.comp Tm.id Tm.mem.lam).conv) C)
        (Tm.meet (Tm.comp (Tm.comp Tm.mem.lam T) (Tm.comp Tm.id Tm.mem.lam).conv) S)).den ρ ⊑
      (Tm.comp (Tm.comp (Tm.comp X T) (Tm.comp Tm.id Tm.mem.lam).conv) C).den ρ := by
  refine le_iff.mpr fun x z h => ?_
  simp only [Tm.den, Core.Rel.comp] at h ⊢
  obtain ⟨w, ⟨v, ⟨y, hxy, u, hu, hL⟩, hCv⟩, ⟨t', ⟨t, hLw, hT⟩, u', hu', hLz⟩, hS⟩ := h
  obtain rfl : v = u := hu
  obtain rfl : z = u' := hu'
  obtain rfl : v = w := le_iff.mp hC v w hCv
  obtain rfl := lamDen_unique _ hL hLw
  obtain ⟨z', hSz, hCz⟩ := le_iff.mp hCS v z ⟨v, hCv, hS⟩
  obtain rfl : z' = z := le_iff.mp hC z' z hCz
  exact ⟨_, ⟨_, ⟨_, hxy, hT⟩, _, rfl, hLz⟩, hCz⟩
end Rel.Lang
