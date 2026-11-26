import Rel.Lang.Den

/-! The Prelude law `estMap`: `(𝟙÷∋)E(f) est(R) = f` — the `R`-extreme of a singleton is itself.

`(𝟙÷∋)` is `lamDen (𝟙 _)`, `est(R)` is `estDen TQ` with `R = qtDen TQ`. Only `simple(f)` is used: where `f a` is empty
both sides are empty, and `dom(f) = 𝟙` and `𝟙 ⊑ R` (the extreme of a one-element list needs no comparison) are not
needed, so the theorem is stated with `simple(f)` alone, which gives the Prelude law at every `R` and every `f` with
`dom(f) = 𝟙`. -/
namespace Rel.Lang
open scoped Rel.Core.Rel

theorem estMap_den {A B : Obj} (f : Core.Rel (Obj.El A) (Obj.El B))
    (TQ : Core.Rel (Obj.El (.prod B B)) (Obj.El (.prod B B)))
    (hsimple : f° ≫ f ⊑ 𝟙 _) : lamDen (𝟙 _) ≫ EDen f ≫ estDen TQ = f := by
  have hs : ∀ a b b', f a b → f a b' → b = b' := fun a b b' h h' => Core.Rel.le_iff.1 hsimple b b' ⟨a, h, h'⟩
  funext a c
  refine propext ⟨fun ⟨xs, hx, ys, hy, he⟩ => ?_, fun h => ?_⟩
  · obtain ⟨-, hxs⟩ := (lamDen_iff _ a xs).1 hx
    obtain ⟨-, hys⟩ := (lamDen_iff _ xs ys).1 hy
    obtain ⟨hc, hn⟩ := (estDen_iff _ ys c).1 he
    obtain ⟨x, hxm, hfx⟩ := (hys c).1 hc
    have hxa : x = a := ((hxs x).1 hxm).symm
    subst hxa
    exact hfx
  · refine ⟨[a], (lamDen_iff _ a _).2 ⟨by simp, fun b => by simp [eq_comm, Core.Rel.id]⟩, [c],
      (lamDen_iff _ _ _).2 ⟨by simp, fun b => ?_⟩, (estDen_iff _ _ _).2 ⟨by simp, ?_⟩⟩
    · simp only [List.mem_singleton]
      exact ⟨fun hb => ⟨a, by simp, by subst hb; exact h⟩, fun ⟨x, hx, hf⟩ => by
        obtain rfl := List.mem_singleton.1 hx
        exact hs _ _ _ hf h⟩
    · rintro ⟨c', hc', hne, -⟩
      exact hne (List.mem_singleton.1 hc')

#print axioms estMap_den

end Rel.Lang
