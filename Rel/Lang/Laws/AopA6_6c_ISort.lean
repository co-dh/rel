import Rel.Lang.Laws.PermConv
import Rel.Lang.Laws.AopA6_2

/-! # Laws of AOP `A6_6c_ISort` (Exercise 6.30, insertion sort) on the concrete core, read off `Tm.den`

`insertion_sort` is `⦇[nil, ins]⦈ ⊑ perm O` for any `ins` with `(O×𝟙) ins ⊑ add O`: fusion (6.4) of the fold `⦇[nil, add]⦈ = perm`
with `O`. Stated for any `O` (stronger than freyd's `ordered R`), under `nil ⊑ nil O`; freyd discharges that premise for
`ordered R` by `wrap_ordered`, here it stays a premise. -/

namespace Rel.Lang
open scoped Rel.Core.Rel
open Rel.Core.Rel hiding id comp recip inter union zero le inl inr junc

/-- The prelude's `perm` call node: its body is `permConv_den`'s forward term. -/
abbrev Tm.permCall (B : Obj) (n : Lean.Name) (cv : Option Lean.Name) (os0 : List Obj) (k : Nat) (c : Lean.Name)
    (os : List Obj) : Tm (.arr B) (.arr B) :=
  .call [] n cv os0 ((Tm.call [k] c none os (.fold (Tm.ran (Tm.closedNil B)) (.var k))).arg (Tm.permStep B))

/-- **Ex 6.30**: `⦇[nil, ins]⦈ ⊑ perm O` for any `ins` with `(O×𝟙) ins ⊑ add O`, given `nil ⊑ nil O`. -/
theorem Tm.insertionSort_den {B : Obj} {ins : Tm (.prod (.arr B) B) (.arr B)} {O : Tm (.arr B) (.arr B)}
    {n : Lean.Name} {cv : Option Lean.Name} {os0 : List Obj} {k : Nat} {c : Lean.Name} {os : List Obj} (ρ : Val)
    (h1 : (Tm.closedNil B).den ρ ⊑ (Tm.comp (.uni (Gen.oneV false 1).1) (Tm.comp .nil O)).den ρ)
    (h2 : (Tm.comp (Tm.pair (Tm.comp .outl O) (Tm.comp .outr .id)) ins).den ρ ⊑ ((Tm.permStep B).comp O).den ρ) :
    (Tm.fold (Tm.ran (Tm.closedNil B)) ins).den ρ ⊑ ((Tm.permCall B n cv os0 k c os).comp O).den ρ := by
  change foldDen _ _ ⊑ (Tm.permCall B n cv os0 k c os).den ρ ≫ O.den ρ
  rw [show (Tm.permCall B n cv os0 k c os).den ρ = permDen from Tm.permCall_den (k := k) (c := c) (os := os) ρ]
  rw [← Tm.permFold_den ρ]
  refine foldDen_le_comp ?_ ?_
  · intro w hw
    obtain ⟨m, hm⟩ := (ranSeed_iff ρ _ w).1 hw
    obtain ⟨s, hs, v, hv, hO⟩ := Core.Rel.le_iff.1 h1 m w hm
    exact ⟨v, (ranSeed_iff ρ _ v).2 ⟨m, s, hs, hv⟩, hO⟩
  · intro v u x w hS hG
    obtain ⟨v', hF, hO⟩ := Core.Rel.le_iff.1 h2 (v, x) w ⟨(u, x), ⟨⟨v, rfl, hS⟩, ⟨x, rfl, rfl⟩⟩, hG⟩
    exact ⟨v', hF, hO⟩

end Rel.Lang
