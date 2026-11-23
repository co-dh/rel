/-
  Division on the concrete core (Freyd §2.31, §2.312): `rdiv R S` is the body of the `div` field of freyd's
  `RelSet` `DivisionAllegory` instance and `ldiv` is freyd's `leftDiv`, so the bridge ties both by `rfl`.
-/
module

public import Rel.Core.Rel

-- exposed: the bodies are unfolded by the denotation proofs and by freyd's `rfl` bridge
@[expose] public section

namespace Rel.Core.Rel

universe u v w

variable {α : Type u} {β : Type v} {γ : Type w}

/-- Right division `R / S`: the largest `X` with `X ≫ S ⊑ R` (`le_rdiv_iff`). -/
def rdiv (R : Rel α γ) (S : Rel β γ) : Rel α β := fun a b => ∀ c, S b c → R a c

/-- Left division `R \ S = (S° / R°)°`: the largest `X` with `R ≫ X ⊑ S` (`le_ldiv_iff`). -/
def ldiv (R : Rel α β) (S : Rel α γ) : Rel β γ := (rdiv S° R°)°

@[simp] theorem rdiv_apply (R : Rel α γ) (S : Rel β γ) (a : α) (b : β) : rdiv R S a b = ∀ c, S b c → R a c := rfl

@[simp] theorem ldiv_apply (R : Rel α β) (S : Rel α γ) (b : β) (c : γ) : ldiv R S b c = ∀ a, R a b → S a c := rfl

/-- The Galois law of right division (Freyd §2.31). -/
theorem le_rdiv_iff {R : Rel α γ} {S : Rel β γ} {X : Rel α β} : X ⊑ rdiv R S ↔ X ≫ S ⊑ R :=
  ⟨fun h => le_iff.2 fun a c ⟨b, hX, hS⟩ => le_iff.1 h a b hX c hS,
   fun h => le_iff.2 fun a b hX c hS => le_iff.1 h a c ⟨b, hX, hS⟩⟩

/-- The Galois law of left division (Freyd §2.312). -/
theorem le_ldiv_iff {R : Rel α β} {S : Rel α γ} {X : Rel β γ} : X ⊑ ldiv R S ↔ R ≫ X ⊑ S :=
  ⟨fun h => le_iff.2 fun a c ⟨b, hR, hX⟩ => le_iff.1 h b c hX a hR,
   fun h => le_iff.2 fun b c hX a hR => le_iff.1 h a c ⟨b, hR, hX⟩⟩

end Rel.Core.Rel

end
