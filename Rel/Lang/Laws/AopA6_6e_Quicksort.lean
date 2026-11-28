import Rel.Lang.Laws.PermConv

/-! # Laws of freyd §6.6 `AOP/A6_6e_Quicksort.lean`, on the concrete core

List cores of `join_perm` (`join perm = F(perm) join perm`): `perm` is `List.Perm` (`permDen_iff`). -/

namespace Rel.Lang

/-- `x a y` joins to a permutation of `z` iff some permuted parts join to it: `⊇` by `refl` parts, `⊆` by `Perm.append`. -/
theorem joinPerm_core {α : Type} (x y z : List α) (a : α) :
    (x ++ a :: y).Perm z ↔ ∃ x' y', x.Perm x' ∧ y.Perm y' ∧ (x' ++ a :: y').Perm z :=
  ⟨fun h => ⟨x, y, List.Perm.refl _, List.Perm.refl _, h⟩,
    fun ⟨_, _, hx, hy, h⟩ => (List.Perm.append hx (List.Perm.cons a hy)).trans h⟩

end Rel.Lang
