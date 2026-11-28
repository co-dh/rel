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

/-- The prelude's insertion fold is `permDen` (the lemma inside `Tm.permConv_den`). -/
theorem Tm.permFold_den {B : Obj} (ρ : Val) :
    foldDen ((Tm.ran (Tm.closedNil B)).den ρ) ((Tm.permStep B).den ρ) = permDen := by
  have hseed (v : List B.El) : (∃ a, (Tm.ran (Tm.closedNil B)).den ρ a v) ↔ v = [] := by
    simp [Tm.ran_den, Tm.closedNil_den, Core.Rel.id, Core.Rel.inter, Core.Rel.comp, Core.Rel.recip, Core.Rel.graph]
  apply Core.Rel.ext
  intro xs ys
  unfold permDen
  rw [foldDen_iff, foldDen_iff]
  simp only [hseed, Tm.den, Tm.prod_den, Prim.den_uncat, Prim.den_snoc, Prim.den_cat,
    nilDen, Core.Rel.graph, Core.Rel.comp_assoc, exists_const]

theorem Tm.permCall_den {B : Obj} {n : Lean.Name} {cv : Option Lean.Name} {os0 : List Obj} {k : Nat} {c : Lean.Name}
    {os : List Obj} (ρ : Val) : (Tm.permCall B n cv os0 k c os).den ρ = permDen := by
  have hfold := Tm.permFold_den (B := B) (Val.args [] [])
  have h := Tm.permConv_den (B := B) (k := k) (c := c) (os := os) (Val.args [] [])
  change (Tm.arg (Tm.call [k] c none os (.fold (Tm.ran (Tm.closedNil B)) (.var k))) (Tm.permStep B)).den (Val.args [] [])
    = _
  rw [← h]
  change (𝟙 _ ≫ foldDen ((Tm.ran (Tm.closedNil B)).den (Val.args [] [])) ((Tm.permStep B).den (Val.args [] [])))° = _
  rw [Core.Rel.id_comp, hfold]
  exact permDen_conv

/-- **Ex 6.30**: `⦇[nil, ins]⦈ ⊑ perm O` for any `ins` with `(O×𝟙) ins ⊑ add O`, given `nil ⊑ nil O`. -/
theorem Tm.insertionSort_den {B : Obj} {ins : Tm (.prod (.arr B) B) (.arr B)} {O : Tm (.arr B) (.arr B)}
    {n : Lean.Name} {cv : Option Lean.Name} {os0 : List Obj} {k : Nat} {c : Lean.Name} {os : List Obj} (ρ : Val)
    (h1 : (Tm.closedNil B).den ρ ⊑ (Tm.comp (.uni (Gen.oneV false 1).1) (Tm.comp .nil O)).den ρ)
    (h2 : (Tm.comp (Tm.pair (Tm.comp .outl O) (Tm.comp .outr .id)) ins).den ρ ⊑ ((Tm.permStep B).comp O).den ρ) :
    (Tm.fold (Tm.ran (Tm.closedNil B)) ins).den ρ ⊑ ((Tm.permCall B n cv os0 k c os).comp O).den ρ := by
  change foldDen _ _ ⊑ (Tm.permCall B n cv os0 k c os).den ρ ≫ O.den ρ
  rw [Tm.permCall_den]
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
