import Rel.Lang.Laws.Map
import Rel.Lang.PreludeRows

/-! # Laws of AOP `A7_1` on the concrete core, read off `Tm.den`

`∋°\R` is `Tm.ldiv (id ≫ mem)° R id id`: at a type variable the universes are `𝟙`, so the division's guard is
vacuous. Each lemma is `Rel/Programs/Aop/A7_1.lean`'s theorem of that name. -/

namespace Rel.Lang
open Tab Rel.Rep
open scoped Rel.Core.Rel
open Rel.Core.Rel hiding id comp recip inter union zero le inl inr junc

/-- `τ (∋°\R) = R`: the singleton `[a]` has the one element `a`. -/
theorem Tm.singletonMapCompLb_den {A : Obj} {R : Tm A A} (ρ : Val) :
    (Tm.comp (Tm.prim (rowOf "τ")) (Tm.ldiv (Tm.comp Tm.id Tm.mem).conv R Tm.id Tm.id)).den ρ = R.den ρ := by
  refine Core.Rel.ext fun a c => ?_
  simp only [Tm.den, Prim.den_tau, Core.Rel.comp, exists_eq_left]
  have hm : ((𝟙 A.arr.El ≫ memDen)° : Core.Rel _ _) a [a] := ⟨[a], rfl, List.mem_singleton_self a⟩
  refine ⟨fun h => (ldivDen_iff.1 h).1 a hm, fun h => ldivDen_iff.2 ⟨?_, .inl ⟨a, hm⟩⟩⟩
  rintro a' ⟨y, rfl, hm⟩
  obtain rfl := List.mem_singleton.1 hm
  exact h

/-- `Λ(S) (∋°\R) = S°\R`, where `Λ(S)` has a list at every point. -/
theorem Tm.lamCompLb_den {A B C : Obj} {S : Tm B A} {R : Tm A C} (ρ : Val)
    (h : (Tm.dom (Tm.lam S)).den ρ = (Tm.id (A := B)).den ρ) :
    (Tm.comp (Tm.lam S) (Tm.ldiv (Tm.comp Tm.id Tm.mem).conv R Tm.id Tm.id)).den ρ =
      (Tm.ldiv S.conv R Tm.id Tm.id).den ρ := by
  have e := Tm.entire_of_dom h
  refine Core.Rel.ext fun b c => ?_
  simp only [Tm.den, Core.Rel.comp]
  refine ⟨fun ⟨ys, hl, hd⟩ => ?_, fun hd => ?_⟩
  · obtain ⟨-, hm⟩ := (lamDen_iff _ _ _).1 hl
    exact ldivDen_iff.2 ⟨fun a ha => (ldivDen_iff.1 hd).1 a ⟨ys, rfl, (hm a).2 ha⟩, .inr ⟨⟨b, rfl⟩, ⟨c, rfl⟩⟩⟩
  · obtain ⟨ys, hl⟩ := e b
    obtain ⟨-, hm⟩ := (lamDen_iff _ _ _).1 hl
    refine ⟨ys, hl, ldivDen_iff.2 ⟨?_, .inr ⟨⟨ys, rfl⟩, ⟨c, rfl⟩⟩⟩⟩
    rintro a ⟨y, rfl, hma⟩
    exact (ldivDen_iff.1 hd).1 a ((hm a).1 hma)

/-- `∋°\Z = (∋°\∋°) Λ(Z°)°`: `xs` lies in `Z`'s column at `c` iff it is inside the list of `c`'s `Z`-preimages. -/
theorem Tm.memLeftDivEq_den {A C : Obj} {Z : Tm A C} (ρ : Val)
    (h : (Tm.dom (Tm.lam Z.conv)).den ρ = (Tm.id (A := C)).den ρ) :
    (Tm.ldiv (Tm.comp Tm.id Tm.mem).conv Z Tm.id Tm.id).den ρ =
      (Tm.comp (Tm.ldiv (Tm.comp Tm.id Tm.mem).conv (Tm.comp Tm.id Tm.mem).conv Tm.id Tm.id)
        (Tm.comp Tm.id Z.conv.lam).conv).den ρ := by
  have e := Tm.entire_of_dom h
  refine Core.Rel.ext fun xs c => ?_
  simp only [Tm.den, Core.Rel.comp]
  refine ⟨fun hd => ?_, fun ⟨ys, hs, b, hb, hl⟩ => ?_⟩
  · obtain ⟨ys, hl⟩ := e c
    obtain ⟨-, hm⟩ := (lamDen_iff _ _ _).1 hl
    refine ⟨ys, ldivDen_iff.2 ⟨?_, .inr ⟨⟨xs, rfl⟩, ⟨ys, rfl⟩⟩⟩, c, (rfl : c = c), hl⟩
    rintro a ⟨y, rfl, hma⟩
    exact ⟨ys, rfl, (hm a).2 ((ldivDen_iff.1 hd).1 a ⟨xs, rfl, hma⟩)⟩
  · obtain rfl : c = b := hb
    obtain ⟨-, hm⟩ := (lamDen_iff _ _ _).1 hl
    refine ldivDen_iff.2 ⟨?_, .inr ⟨⟨xs, rfl⟩, ⟨c, rfl⟩⟩⟩
    rintro a ⟨y, rfl, hma⟩
    obtain ⟨y', rfl, hmy⟩ := (ldivDen_iff.1 hs).1 a ⟨xs, rfl, hma⟩
    exact (hm a).1 hmy

end Rel.Lang
