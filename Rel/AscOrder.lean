import Rel.ObjOrder

/-! The row `asc`'s meaning: `asc(P) : ℕ ⟶ B` numbers the set `dom P` in `Obj.lt` order, and the law that makes the
numbering one: a list strictly ascending in `Obj.lt` is fixed by its elements. -/

namespace Rel

/-- **A strictly ascending list is fixed by its elements**: two lists ascending strictly in `Obj.lt` with one set of
elements are one list. -/
theorem lt_sorted_unique {B : Obj} : ∀ {l l' : List B.El}, l.Pairwise B.lt → l'.Pairwise B.lt →
    (∀ b, b ∈ l ↔ b ∈ l') → l = l'
  | [], [], _, _, _ => rfl
  | [], b :: _, _, _, hm => absurd ((hm b).2 List.mem_cons_self) List.not_mem_nil
  | a :: _, [], _, _, hm => absurd ((hm a).1 List.mem_cons_self) List.not_mem_nil
  | a :: l, b :: l', h, h', hm => by
    rw [List.pairwise_cons] at h h'
    -- the heads: each is in the other list, so neither is below the other
    have hab : a = b := by
      rcases List.mem_cons.1 ((hm a).1 List.mem_cons_self) with e | ha
      · exact e
      rcases List.mem_cons.1 ((hm b).2 List.mem_cons_self) with e | hb
      · exact e.symm
      exact absurd (h.1 b hb) (Obj.lt_asymm B (h'.1 a ha))
    subst hab
    have ne : ∀ {l : List B.El}, (∀ x ∈ l, B.lt a x) → a ∉ l := fun hl ha => Obj.lt_irrefl B a (hl a ha)
    refine congrArg _ (lt_sorted_unique h.2 h'.2 fun x => ⟨fun hx => ?_, fun hx => ?_⟩)
    · rcases List.mem_cons.1 ((hm x).1 (List.mem_cons_of_mem _ hx)) with rfl | h2
      · exact absurd hx (ne h.1)
      · exact h2
    · rcases List.mem_cons.1 ((hm x).2 (List.mem_cons_of_mem _ hx)) with rfl | h2
      · exact absurd hx (ne h'.1)
      · exact h2

/-- **`asc(P)`'s meaning**, `p` the set `dom P`: `j` to the `j`-th element (from 0) of the list holding exactly `p`,
strictly ascending in `Obj.lt` (`Lang.lamDen`'s list), so `a` to the number of elements of `p` below it. -/
def ascDen (B : Obj) (p : B.El → Prop) (j : Int64) (a : B.El) : Prop :=
  ∃ ys : List B.El, ys.Pairwise B.lt ∧ (∀ b, b ∈ ys ↔ p b) ∧ ∃ k, ys[k]? = some a ∧ j = Int64.ofNat k

end Rel
