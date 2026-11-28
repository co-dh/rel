module

public import Rel.Lang.Den
public import Rel.Programs.Prelude

@[expose] public section

/-! `_⊕_(R : α ⟶ β, S : γ ⟶ δ) : α+γ ⟶ β+δ ≜ [R inl, S inr]` (`Programs/Prelude.lean`): the sum of relations relates
    `inl a` to `inl b` when `R a b` and `inr a` to `inr b` when `S a b`, nothing across. -/

namespace Rel.Lang

open Rel.Core.Rel hiding id comp recip inter union zero le inl inr junc

/-- The body of `⊕` at a call: `[R inl, S inr]` with the call's parameters `R`, `S` bound to the variables `k`, `l`. -/
abbrev Tm.oplusDef (k l : Nat) (A B C D : Obj) : Tm (.sum A C) (.sum B D) :=
  .join (.comp Tm.inl.conv (.comp (.var k : Tm A B) .inl)) (.comp Tm.inr.conv (.comp (.var l : Tm C D) .inr))

/-- **A call of `⊕` is the sum of its arguments**: `inl a` goes to `inl b` when `R a b`, `inr a` to `inr b` when `S a b`.
    The node is stated with its body written out, as the elaborator builds it: a call renumbers its body's parameters
    to fresh variables `k`, `l` per call site, so a body fixed at `prelude.«⊕».body` (variables 4, 5) would not match. -/
theorem Tm.oplusCall_den {A B C D : Obj} {k l : Nat} (hkl : l ≠ k) {cv : Option Lean.Name} {os : List Obj} (ρ : Val)
    (R : Tm A B) (S : Core.Rel (Obj.El C) (Obj.El D)) (p : (Obj.sum A C).El) (q : (Obj.sum B D).El) :
    Tm.argDen ρ (Tm.arg (Tm.call [k, l] `«_⊕_» cv os (Tm.oplusDef k l A B C D)) R) [⟨C, D, S⟩] p q ↔
      (∃ a b, p = Sum.inl a ∧ q = Sum.inl b ∧ R.den ρ a b) ∨ ∃ a b, p = Sum.inr a ∧ q = Sum.inr b ∧ S a b := by
  have h2 : (Val.args [k, l] [⟨_, _, R.den ρ⟩, ⟨_, _, S⟩]) k A B = R.den ρ := Val.bind_apply _ _ _ rfl rfl
  have h3 : (Val.args [k, l] [⟨_, _, R.den ρ⟩, ⟨_, _, S⟩]) l C D = S := by
    rw [Val.args, Val.bind_ne hkl]
    exact Val.bind_apply _ _ _ rfl rfl
  simp only [Tm.den, Tm.argDen, h2, h3, Core.Rel.union, Core.Rel.comp, Core.Rel.recip, Core.Rel.inl,
    Core.Rel.inr, Core.Rel.graph]
  constructor
  · rintro (⟨a, rfl, b, h, rfl⟩ | ⟨a, rfl, b, h, rfl⟩)
    · exact Or.inl ⟨a, b, rfl, rfl, h⟩
    · exact Or.inr ⟨a, b, rfl, rfl, h⟩
  · rintro (⟨a, b, rfl, rfl, h⟩ | ⟨a, b, rfl, rfl, h⟩)
    · exact Or.inl ⟨a, rfl, b, h, rfl⟩
    · exact Or.inr ⟨a, rfl, b, h, rfl⟩

end Rel.Lang
