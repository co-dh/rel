import Rel.Lang.Laws.AopA5_5_TypeFunctor
import Rel.Lang.PrefixFold

/-! # Laws of freyd `AOP/A5_7_ListBeads.lean` (B&dM §5.7), at the list relator `F(R) = mapDen R`

`Rel/Programs/Aop/A5_7_ListBeads.lean` states each law as `theorem <name> … by Rel.Lang.Tm.<name>_den`. -/

namespace Rel.Lang
open Tab Rel.Rep
open scoped Rel.Core.Rel
open Rel.Core.Rel hiding id comp recip inter union zero le inl inr junc

/-- The row `prefix` relates `xs` to its list prefixes. -/
theorem Tm.prefixRow_iff (ρ : Val) {B : Obj} (xs ys : List B.El) :
    (Tm.prim (rowOf "prefix") : Tm B.arr B.arr).den ρ xs ys ↔ ys <+: xs := by
  rw [← Tm.prefixFold_row ρ (Tm.prefixSeed B) (Tm.prefixFold_seed ρ)]
  exact Tm.prefixFold_iff ρ _ (Tm.prefixFold_seed ρ) xs ys

/-- `list(R) prefix ⊑ prefix list(R)`: a prefix `w` of an `R`-image `ys` of `xs` is the `R`-image of the prefix of `xs`
    of the same length. -/
theorem mapDen_prefix_lax {A B : Obj} (T : Core.Rel (Obj.El A) (Obj.El B)) (xs : List A.El) (ys w : List B.El)
    (h : mapDen T xs ys) (hw : w <+: ys) : ∃ v, v <+: xs ∧ mapDen T v w := by
  obtain ⟨t, rfl⟩ := hw
  obtain ⟨hl, h⟩ := (mapDen_iff _ _ _).1 h
  have hl : w.length + t.length = xs.length := by simpa using hl
  refine ⟨xs.take w.length, List.take_prefix _ _, (mapDen_iff _ _ _).2 ⟨?_, fun i hi hi' => ?_⟩⟩
  · simp; omega
  · have hi2 : i < w.length := by simpa using hi'
    have e := h i (by omega) (by simp; omega)
    rw [List.getElem_append_left hi2] at e
    simpa using e

/-- `F(R) prefix ⊑ prefix F(R)` (freyd `prefix_lax_natural` at the list relator). -/
theorem Tm.prefixLaxNatural_den {A B : Obj} {R : Tm A B} (ρ : Val) :
    (Tm.comp (Tm.arg (Tm.prim mapRow : Tm (.arr A) (.arr B)) R) (Tm.prim (rowOf "prefix") : Tm (.arr B) (.arr B))).den ρ ⊑
      (Tm.comp (Tm.prim (rowOf "prefix") : Tm (.arr A) (.arr A)) (Tm.arg (Tm.prim mapRow : Tm (.arr A) (.arr B)) R)).den ρ := by
  refine Core.Rel.le_iff.2 fun xs w => ?_
  rintro ⟨ys, hy, hw⟩
  rw [Tm.fmap_den] at hy
  obtain ⟨v, hv, hv'⟩ := mapDen_prefix_lax _ xs ys w hy ((Tm.prefixRow_iff ρ ys w).1 hw)
  refine ⟨v, (Tm.prefixRow_iff ρ xs v).2 hv, ?_⟩
  rw [Tm.fmap_den]; exact hv'

end Rel.Lang
