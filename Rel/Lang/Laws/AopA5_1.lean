import Rel.Lang.Laws.AopA7_2
import Rel.Lang.Laws.AopA5_5_TypeFunctor

/-! # Relator laws of `AOP/A5_1.lean` (B&dM §5.1) at the list relator `F(R)`, on the concrete core

freyd states each row over a relator parameter; here it is the list instance `F(R) = mapDen R`, whose laws
(`mapDen_id/comp/recip`, `mapDen_mono`) are exactly the relator axioms, so each row is those axioms composed.
`Rel/Programs/Aop/A5_1.lean` states each as `theorem <name> … by Rel.Lang.Tm.<name>_den`. -/

namespace Rel.Lang
open Tab Rel.Rep
open scoped Rel.Core.Rel
open Rel.Core.Rel hiding id comp recip inter union zero le inl inr junc

/-- The list relator preserves `∩` of ANY two relations (elementwise, equal lengths), which subsumes
    freyd's coreflexive case. -/
theorem mapDen_inter {A B : Obj} (R S : Core.Rel (Obj.El A) (Obj.El B)) :
    mapDen (R ∩ S) = mapDen R ∩ mapDen S :=
  Core.Rel.ext fun xs ys => by
    constructor
    · intro h
      obtain ⟨hl, h⟩ := (mapDen_iff _ _ _).1 h
      exact ⟨(mapDen_iff _ _ _).2 ⟨hl, fun t a b => (h t a b).1⟩, (mapDen_iff _ _ _).2 ⟨hl, fun t a b => (h t a b).2⟩⟩
    · rintro ⟨h1, h2⟩
      obtain ⟨hl, h1⟩ := (mapDen_iff _ _ _).1 h1
      obtain ⟨-, h2⟩ := (mapDen_iff _ _ _).1 h2
      exact (mapDen_iff _ _ _).2 ⟨hl, fun t a b => ⟨h1 t a b, h2 t a b⟩⟩

theorem mapDen_entire {A B : Obj} {T : Core.Rel (Obj.El A) (Obj.El B)} (h : 𝟙 _ ⊑ T ≫ T°) :
    𝟙 (Obj.El (.arr A)) ⊑ mapDen T ≫ (mapDen T)° := by
  have := mapDen_mono h
  rwa [mapDen_id _, ← mapDen_comp, ← mapDen_recip] at this

theorem mapDen_simple {A B : Obj} {T : Core.Rel (Obj.El A) (Obj.El B)} (h : T° ≫ T ⊑ 𝟙 _) :
    (mapDen T)° ≫ mapDen T ⊑ 𝟙 (Obj.El (.arr B)) := by
  have := mapDen_mono h
  rwa [mapDen_id _, ← mapDen_comp, ← mapDen_recip] at this

theorem mapDen_dom {A B : Obj} (T : Core.Rel (Obj.El A) (Obj.El B)) :
    mapDen (𝟙 _ ∩ T ≫ T°) = 𝟙 (Obj.El (.arr A)) ∩ mapDen T ≫ (mapDen T)° := by
  rw [mapDen_inter, mapDen_id, ← mapDen_comp, ← mapDen_recip]

/-- `map_is_map`, entire half, at `F(R)`: `𝟙 ⊑ f f°` gives `𝟙 ⊑ F(f) F(f)°`. -/
theorem Tm.map_is_map_entire_den {A B : Obj} {f : Tm A B} (ρ : Val)
    (h : (Tm.id (A := A)).den ρ ⊑ (Tm.comp f (Tm.conv f)).den ρ) :
    (Tm.id (A := .arr A)).den ρ ⊑
      (Tm.comp (Tm.arg (Tm.prim mapRow : Tm (.arr A) (.arr B)) f)
        (Tm.conv (Tm.comp Tm.id (Tm.arg (Tm.prim mapRow : Tm (.arr A) (.arr B)) f)))).den ρ := by
  simp only [Tm.den, Tm.argDen, Prim.den_mapRow, Core.Rel.id_comp] at h ⊢
  exact mapDen_entire h

/-- `map_is_map`, simple half, at `F(R)`: `f° f ⊑ 𝟙` gives `F(f)° F(f) ⊑ 𝟙`. -/
theorem Tm.map_is_map_simple_den {A B : Obj} {f : Tm A B} (ρ : Val)
    (h : (Tm.comp (Tm.conv f) f).den ρ ⊑ (Tm.id (A := B)).den ρ) :
    (Tm.comp (Tm.conv (Tm.comp Tm.id (Tm.arg (Tm.prim mapRow : Tm (.arr A) (.arr B)) f)))
        (Tm.arg (Tm.prim mapRow : Tm (.arr A) (.arr B)) f)).den ρ ⊑ (Tm.id (A := .arr B)).den ρ := by
  simp only [Tm.den, Tm.argDen, Prim.den_mapRow, Core.Rel.id_comp] at h ⊢
  exact mapDen_simple h

/-- `map_inter_le` at `F(R)`: `F(R ∩ S) ⊑ F(R) ∩ F(S)`. -/
theorem Tm.map_inter_le_den {A B : Obj} {R S : Tm A B} (ρ : Val) :
    (Tm.arg (Tm.prim mapRow : Tm (.arr A) (.arr B)) (Tm.meet R S)).den ρ ⊑
      (Tm.meet (Tm.arg (Tm.prim mapRow : Tm (.arr A) (.arr B)) R)
        (Tm.arg (Tm.prim mapRow : Tm (.arr A) (.arr B)) S)).den ρ := by
  simp only [Tm.den, Tm.argDen, Prim.den_mapRow]
  rw [mapDen_inter]; exact Core.Rel.le_iff.2 fun _ _ h => h

/-- `map_inter_coreflexive` at `F(R)`: the equation `F(X ∩ Y) = F(X) ∩ F(Y)` holds for any `X`, `Y` (not only
    coreflexives), because `F(R)` relates lists elementwise. -/
theorem Tm.map_inter_coreflexive_den {A B : Obj} {R S : Tm A B} (ρ : Val) :
    (Tm.arg (Tm.prim mapRow : Tm (.arr A) (.arr B)) (Tm.meet R S)).den ρ =
      (Tm.meet (Tm.arg (Tm.prim mapRow : Tm (.arr A) (.arr B)) R)
        (Tm.arg (Tm.prim mapRow : Tm (.arr A) (.arr B)) S)).den ρ := by
  simp only [Tm.den, Tm.argDen, Prim.den_mapRow]
  exact mapDen_inter _ _

/-- `map_dom` at `F(R)`: `F(dom R) = dom(F(R))`. -/
theorem Tm.map_dom_den {A B : Obj} {R : Tm A B} (ρ : Val) :
    (Tm.arg (Tm.prim mapRow : Tm (.arr A) (.arr A)) (Tm.dom R)).den ρ =
      (Tm.dom (Tm.arg (Tm.prim mapRow : Tm (.arr A) (.arr B)) R)).den ρ := by
  rw [Tm.fmap_den, Tm.dom_den, Tm.dom_den, Tm.fmap_den]
  exact mapDen_dom _

end Rel.Lang
