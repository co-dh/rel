/-
  `(μX : φX)` and `(νX : φX)` on a hom-set of relations (B&dM Theorem 6.1), defined for every `φ`: a fixed point
  when `φ` is monotonic. The one copy of the fixed points Rel proper uses; `Gen.mu`, `Gen.nu` compute them.
-/
import Rel.Core.Rel

namespace Rel.Core.Rel

open Rel.Core

variable {α β : Type} {φ ψ : Rel α β → Rel α β} {Y : Rel α β}

/-- A monotonic map on a hom-set ("not necessarily a functor", Theorem 6.1). -/
def Monotonic (φ : Rel α β → Rel α β) : Prop := ∀ X Y : Rel α β, X ⊑ Y → φ X ⊑ φ Y

/-- `(μX : φX)`: the pairs in every prefixed point. -/
def mu (φ : Rel α β → Rel α β) : Rel α β := fun a b => ∀ Y : Rel α β, φ Y ⊑ Y → Y a b

/-- `(νX : φX)`: the pairs in some postfixed point. -/
def nu (φ : Rel α β → Rel α β) : Rel α β := fun a b => ∃ Y : Rel α β, Y ⊑ φ Y ∧ Y a b

theorem mu_le (h : φ Y ⊑ Y) : mu φ ⊑ Y := le_iff.2 fun _ _ hx => hx Y h

theorem le_nu (h : Y ⊑ φ Y) : Y ⊑ nu φ := le_iff.2 fun _ _ hy => ⟨Y, h, hy⟩

theorem mu_prefixed (hφ : Monotonic φ) : φ (mu φ) ⊑ mu φ :=
  le_iff.2 fun a b hx _ hY => le_iff.1 hY a b (le_iff.1 (hφ _ _ (mu_le hY)) a b hx)

theorem mu_fix (hφ : Monotonic φ) : φ (mu φ) = mu φ :=
  le_antisymm (mu_prefixed hφ) (mu_le (hφ _ _ (mu_prefixed hφ)))

theorem nu_fix (hφ : Monotonic φ) : φ (nu φ) = nu φ := by
  have h1 : nu φ ⊑ φ (nu φ) :=
    le_iff.2 fun a b ⟨Y, hY, hy⟩ => le_iff.1 (hφ _ _ (le_nu hY)) a b (le_iff.1 hY a b hy)
  exact le_antisymm (le_nu (hφ _ _ h1)) h1

/-- `mu` is monotone in its body, pointwise: no monotonicity of either body is needed. -/
theorem mu_mono (h : ∀ X, φ X ⊑ ψ X) : mu φ ⊑ mu ψ :=
  le_iff.2 fun _ _ hx Y hY => hx Y (le_trans (h Y) hY)

theorem nu_mono (h : ∀ X, φ X ⊑ ψ X) : nu φ ⊑ nu ψ :=
  le_iff.2 fun _ _ ⟨Y, hY, hy⟩ => ⟨Y, le_trans hY (h Y), hy⟩

/-- `starLinear` (the prelude's `star(R) ≜ μX : 𝟙 ∪ R X`): `μX : S ∪ R X = star(R) S`, so a linear recursion runs
    as the row `star` (`Tab.star`, semi-naive) on `S`. -/
theorem starLinear (R : Rel α α) (S : Rel α β) :
    mu (fun X => S ∪ R ≫ X) = mu (fun X => 𝟙 α ∪ R ≫ X) ≫ S := by
  apply le_antisymm
  · -- `star(R) S` is a prefixed point of `S ∪ R X`
    refine mu_le (le_iff.2 fun a c h => ?_)
    rcases h with h | ⟨b, hR, d, hs, hS⟩
    · exact ⟨a, fun Y hY => le_iff.1 hY a a (Or.inl rfl), h⟩
    · exact ⟨d, fun Y hY => le_iff.1 hY a d (Or.inr ⟨b, hR, hs Y hY⟩), hS⟩
  · -- `star(R)` is below the pairs `(a,b)` with `S b c ⟹ M a c`, `M` the left side: a prefixed point of `𝟙 ∪ R X`
    refine le_iff.2 fun a c h => ?_
    obtain ⟨b, hs, hS⟩ := h
    refine hs (fun a b => ∀ c, S b c → mu (fun X => S ∪ R ≫ X) a c) (le_iff.2 fun a b h c hc Z hZ => ?_) c hS
    rcases h with rfl | ⟨d, hR, hd⟩
    · exact le_iff.1 hZ a c (Or.inl hc)
    · exact le_iff.1 hZ a c (Or.inr ⟨d, hR, hd c hc Z hZ⟩)

end Rel.Core.Rel
