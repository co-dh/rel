import Rel.Lang.Laws.PermConv
import Rel.Programs.Prelude

/-! # Laws of freyd §6.6 `AOP/A6_6e_Quicksort.lean`, on the concrete core

List cores of `join_perm` (`join perm = F(perm) join perm`): `perm` is `List.Perm` (`permDen_iff`). -/

namespace Rel.Lang

/-- `x a y` joins to a permutation of `z` iff some permuted parts join to it: `⊇` by `refl` parts, `⊆` by `Perm.append`. -/
theorem joinPerm_core {α : Type} (x y z : List α) (a : α) :
    (x ++ a :: y).Perm z ↔ ∃ x' y', x.Perm x' ∧ y.Perm y' ∧ (x' ++ a :: y').Perm z :=
  ⟨fun h => ⟨x, y, List.Perm.refl _, List.Perm.refl _, h⟩,
    fun ⟨_, _, hx, hy, h⟩ => (List.Perm.append hx (List.Perm.cons a hy)).trans h⟩

open Rel.Kernel Tab Rel.Rep

/-- **`perm`'s text relates an array to its permutations**: the body the prelude elaborates, `prelude.perm.body`, at
    any objects `σ` (`Tm.instObj`). A law about a call of `perm` takes
    `(ht : prelude.perm.body.instObj [.general] [B] = .ok t' := by rfl)` and states the node `Tm.call ks c cv os t'`. -/
theorem Tm.permDef_den (ph : List QAtomicType) (σ : List Obj) (ρ : Val)
    {t' : Tm ((Obj.atom .general).arr.inst ph σ) ((Obj.atom .general).arr.inst ph σ)}
    (ht : Rel.Programs.prelude.perm.body.instObj ph σ = .ok t') (xs ys : Obj.El ((Obj.atom .general).inst ph σ).arr) :
    t'.den ρ xs ys ↔ xs.Perm ys := by
  obtain rfl := Except.ok.inj ht
  exact (Iff.of_eq (congrFun (congrFun (Tm.permCall_den (k := 31) (c := `add) (os := []) ρ) xs) ys)).trans
    (permDen_iff xs ys)

/-- `join(x,a,y) = x ⧺ [a] ⧺ y` on the left-nested triple, `(snoc×𝟙)cat` as the program elaborates it. -/
abbrev Tm.joinT (B : Obj) : Tm (.prod (.prod (.arr B) B) (.arr B)) (.arr B) :=
  ((Tm.outl.comp (Tm.prim (rowOf "snoc") : Tm (.prod (.arr B) B) (.arr B))).pair (Tm.outr.comp Tm.id : Tm (.prod (.prod (.arr B) B) (.arr B)) (.arr B))).comp
    (Tm.prim (rowOf "cat"))

/-- `join perm = (perm×𝟙)×perm join perm`: `perm` calls of the prelude at the one object `B`. -/
theorem Tm.joinPerm_den {B : Obj} {t' : Tm (.arr B) (.arr B)}
    (ht : Rel.Programs.prelude.perm.body.instObj [.general] [B] = .ok t' := by rfl) (ρ : Val) :
    Tm.den ρ ((Tm.joinT B).comp (Tm.call [] `Rel.Programs.prelude.perm (some `Rel.Programs.prelude.perm) [B] t')) =
    Tm.den ρ ((((Tm.outl.comp ((Tm.outl.comp (Tm.call [] `Rel.Programs.prelude.perm (some `Rel.Programs.prelude.perm) [B] t')).pair
        (Tm.outr.comp Tm.id))).pair (Tm.outr.comp (Tm.call [] `Rel.Programs.prelude.perm (some `Rel.Programs.prelude.perm) [B] t'))).comp
      (Tm.joinT B)).comp (Tm.call [] `Rel.Programs.prelude.perm (some `Rel.Programs.prelude.perm) [B] t')) := by
  have hP : ∀ xs ys, t'.den (Val.args [] []) xs ys ↔ xs.Perm ys := fun xs ys =>
    Tm.permDef_den [.general] [B] _ ht xs ys
  apply Core.Rel.ext
  rintro ⟨⟨x, a⟩, y⟩ z
  simp only [Tm.den, Core.Rel.comp, Core.Rel.rpair, Core.Rel.graph, hP, Prim.den_snoc, Prim.den_cat, Core.Rel.id]
  simp only [Prod.exists, exists_eq_left, exists_eq_right, exists_and_left, exists_and_right, and_assoc,
    exists_eq_left', exists_eq_right', Prod.mk.injEq]
  rw [show x ++ [a] ++ y = x ++ a :: y by simp, joinPerm_core]
  constructor
  · rintro ⟨x', y', hx, hy, h⟩
    exact ⟨x' ++ a :: y', ⟨x', hx, y', hy, by simp⟩, h⟩
  · rintro ⟨b, ⟨x', hx, y', hy, rfl⟩, h⟩
    exact ⟨x', y', hx, hy, by simpa using h⟩

end Rel.Lang
