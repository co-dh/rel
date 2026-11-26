import Rel.Lang.PreludePrefix

/-! Denotation of the prefix fold, reusable by programs that derive it. -/

namespace Rel.Lang

open Rel.Core.Rel hiding id comp recip inter union zero le inl inr junc

/-- **The fold of `nil ∪ cons` means the prefixes**, whatever its seed `e` whose values are `[]` alone. -/
theorem Tm.prefixFold_iff (ρ : Val) {B : Obj} (e : Tm (.arr B) (.arr B)) (he : ∀ v, (∃ a, e.den ρ a v) ↔ v = [])
    (xs ys : List B.El) :
    (Tm.foldr e (.join .nil (.prim (rowOf "cons")))).den ρ xs ys ↔ ys <+: xs := by
  simp only [Tm.den, Tm.nil, Prim.den_nilRow, Prim.den_cons]
  induction xs generalizing ys with
  | nil => rw [foldrDen_empty]; simp [he]
  | cons x xs ih =>
    rw [foldrDen_cons]
    simp only [ih, Core.Rel.union, nilDen, Core.Rel.graph]
    constructor
    · rintro ⟨u, hu, h | h⟩
      · subst h; exact List.nil_prefix
      · subst h; exact List.cons_prefix_cons.2 ⟨rfl, hu⟩
    · intro h
      rcases ys with _ | ⟨y, ys⟩
      · exact ⟨[], List.nil_prefix, .inl rfl⟩
      · obtain ⟨rfl, h'⟩ := List.cons_prefix_cons.1 h
        exact ⟨ys, h', .inr rfl⟩

/-- **`⦇[nil, nil ∪ cons]⦈ʳ` and `cat° π₁` are one relation** at every object `B`, under any variables (neither
    term reads one), whatever the fold's seed `e` whose values are `[]` alone. -/
theorem Tm.prefixFold_prefixDef (ρ ρ' : Val) {B : Obj} (e : Tm (.arr B) (.arr B))
    (he : ∀ v, (∃ a, e.den ρ a v) ↔ v = []) :
    (Tm.foldr e (.join .nil (.prim (rowOf "cons")))).den ρ = (Tm.prefixDef B).den ρ' := by
  funext xs ys; apply propext
  rw [Tm.prefixFold_iff ρ e he]
  simp only [Tm.prefixDef, Tm.den, Prim.den_uncat, Core.Rel.comp, Core.Rel.graph]
  constructor
  · rintro ⟨t, ht⟩; exact ⟨(ys, t), ht.symm, rfl⟩
  · rintro ⟨p, hp, rfl⟩; exact ⟨p.2, hp.symm⟩

/-- The prefix fold can replace the prelude row in any denotation. -/
theorem Tm.prefixFold_row (ρ : Val) {B : Obj} (e : Tm (.arr B) (.arr B))
    (he : ∀ v, (∃ a, e.den ρ a v) ↔ v = []) :
    (Tm.foldr e (.join .nil (.prim (rowOf "cons")))).den ρ =
      (Tm.prim (rowOf "prefix") : Tm (.arr B) (.arr B)).den ρ := by
  rw [Tm.prefixFold_prefixDef ρ ρ e he]
  funext xs ys
  exact propext (Tm.prefixDef_row ρ xs ys)

/-- The seed of the right fold, at the declared one-point universe. -/
def Tm.prefixSeed (B : Obj) : Tm B.arr B.arr :=
  (Tm.prim (rowOf "ran")).arg
    ((Tm.uni (Gen.oneV false (USize.ofNat 1)).fst : Tm .one .one).comp
      (Tm.nil : Tm .one B.arr))

/-- The range of nil on the declared one-point universe has the empty array as its sole value. -/
theorem Tm.prefixFold_seed (ρ : Val) {B : Obj} (v : B.arr.El) :
    (∃ a, (Tm.prefixSeed B).den ρ a v) ↔ v = [] := by
  simp only [Tm.prefixSeed, Tm.den, Tm.argDen, Tm.nil]
  erw [Prim.den_ranRow, Prim.den_nilRow]
  simp only [Core.Rel.inter, Core.Rel.id, Core.Rel.comp, Core.Rel.recip, Core.Rel.graph, nilDen]
  have i : Fin (USize.ofNat 1).toNat := ⟨0, by simp [USize.toNat_ofNat]⟩
  constructor
  · rintro ⟨_, rfl, -, -, _, -, rfl⟩
    rfl
  · rintro rfl
    exact ⟨_, rfl, (), ⟨(), ⟨i, by trivial, by trivial⟩, rfl⟩, (), ⟨i, by trivial, by trivial⟩, rfl⟩

/-- The prefix fold and row agree after any preceding relation. -/
theorem Tm.prefixFold_input {A B : Obj} {X : Tm A B.arr} (ρ : Val) :
    (X.comp (Tm.foldr (Tm.prefixSeed B) (.join .nil (.prim (rowOf "cons"))))).den ρ =
    (X.comp (Tm.prim (rowOf "prefix") : Tm B.arr B.arr)).den ρ := by
  have compDen {C D E : Obj} (R : Tm C D) (S : Tm D E) :
      (R.comp S).den ρ = R.den ρ ≫ S.den ρ := by
    simp only [Tm.den]
  rw [compDen, compDen]
  rw [Tm.prefixFold_row ρ _ (Tm.prefixFold_seed ρ)]

end Rel.Lang
