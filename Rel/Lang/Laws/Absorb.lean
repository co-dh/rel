module

public import Rel.Lang.Laws.Eunion

@[expose] public section

/-! The Prelude law `absorption` (`Programs/Prelude.lean`): `Λ(𝟙) E(S) E(R) = Λ(𝟙) E(S R)`. `Λ(𝟙)` is the singleton
    `a ↦ [a]`, so `Λ(𝟙) E(T)` is `Λ(T)`, and absorption is `lamDen_absorb` on arrays. -/

namespace Rel.Lang

open scoped Rel.Core.Rel
open Rel.Core.Rel hiding id comp recip inter union zero le inl inr junc

variable {A B C : Obj}

/-- `Λ(𝟙)` sends `a` to the one list `[a]`. -/
theorem lamDen_id_iff (a : Obj.El A) (xs : Obj.El (.arr A)) : lamDen (𝟙 _) a xs ↔ xs = [a] := by
  refine (lamDen_iff _ a xs).trans ⟨fun ⟨hp, h⟩ => pw_eq hp (List.pairwise_singleton _ _) fun c =>
    (h c).trans (by simp [Core.Rel.id, eq_comm]), fun e => e ▸ ⟨List.pairwise_singleton _ _, fun c => ?_⟩⟩
  simp [Core.Rel.id, eq_comm]

theorem lamDen_id_EDen (T : Core.Rel (Obj.El A) (Obj.El B)) : lamDen (𝟙 _) ≫ EDen T = lamDen T := by
  funext a zs
  refine propext ⟨fun ⟨ys, h1, h2⟩ => ?_, fun h => ⟨[a], (lamDen_id_iff a _).2 rfl, ?_⟩⟩
  · rw [(lamDen_id_iff a ys).1 h1] at h2
    obtain ⟨hp, hz⟩ := (EDen_iff T _ zs).1 h2
    exact (lamDen_iff T a zs).2 ⟨hp, fun c => (hz c).trans (by simp)⟩
  · obtain ⟨hp, hz⟩ := (lamDen_iff T a zs).1 h
    exact (EDen_iff T _ zs).2 ⟨hp, fun c => (hz c).trans (by simp)⟩

theorem EDen_absorb (S : Core.Rel (Obj.El A) (Obj.El B)) (R : Core.Rel (Obj.El B) (Obj.El C))
    (hS : ∀ a, ∃ ys, lamDen S a ys) : (lamDen (𝟙 _) ≫ EDen S) ≫ EDen R = lamDen (𝟙 _) ≫ EDen (S ≫ R) := by
  rw [lamDen_id_EDen, lamDen_id_EDen]
  exact lamDen_absorb S R hS
end Rel.Lang
