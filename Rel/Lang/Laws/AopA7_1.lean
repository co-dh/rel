import Rel.Lang.PreludeDfn
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

/-- The prelude's `est(Q)` is freyd's `est(Q ∪ 𝟙) = ∋ ∩ (∈ \ (Q ∪ 𝟙)°)`: the extreme under `Q ∪ 𝟙`, no reflexivity needed. -/
theorem Tm.estPairTest_den {B : Obj} (Q : Tm B B) (ρ : Val) :
    (Tm.est (pairTest Q)).den ρ =
      (memDen : Core.Rel (Obj.El (.arr B)) (Obj.El B)) ∩ Core.Rel.ldiv memDen° ((Q.den ρ ∪ 𝟙 _)°) := by
  refine Core.Rel.ext fun xs c => ?_
  rw [Tm.est_den]
  refine (estDen_iff _ xs c).trans ?_
  simp only [Tm.pairTest_den, Core.Rel.inter, Core.Rel.ldiv_apply, Core.Rel.recip, Core.Rel.union, Core.Rel.id]
  refine and_congr_right fun _ => ?_
  refine ⟨fun h a ha => ?_, fun h ⟨a, ha, hne, hq⟩ => ?_⟩
  · by_cases hq : Q.den ρ c a
    · exact .inl hq
    · by_cases he : c = a
      · exact .inr he
      · exact absurd ⟨a, ha, fun e => he e.symm, hq⟩ h
  · rcases h a ha with h | h
    · exact hq h
    · exact hne h.symm

/-- `Λ(S) est(Q) = S ∩ (S°\(Q ∪ 𝟙)°)` (freyd `Λ_comp_est`); `𝟙` under `\` is `ran(S)`, which agrees with it on
    every pair the division reads (`a' ∈ S b`), because a closed `𝟙` is no operand of `\`. -/
theorem Tm.lamCompEst_den {A B : Obj} {S : Tm B A} {Q : Tm A A} (ρ : Val)
    (h : (Tm.dom (Tm.lam S)).den ρ = (Tm.id (A := B)).den ρ) :
    (Tm.comp (Tm.lam S) (Tm.est (pairTest Q))).den ρ =
      (Tm.meet S (Tm.ldiv S.conv (Tm.join Q.conv (Tm.ran S)) Tm.id Tm.id)).den ρ := by
  have e := Tm.entire_of_dom h
  refine Core.Rel.ext fun b c => ?_
  change (Core.Rel.comp (Tm.den ρ (Tm.lam S)) (Tm.den ρ (Tm.est (pairTest Q)))) b c ↔ _
  rw [Tm.estPairTest_den]
  simp only [Tm.den, Tm.ran_den, Core.Rel.inter, Core.Rel.comp]
  refine ⟨fun ⟨ys, hl, hm, hn⟩ => ?_, fun ⟨hs, hd⟩ => ?_⟩
  · obtain ⟨-, hy⟩ := (lamDen_iff _ _ _).1 hl
    refine ⟨(hy c).1 hm, ldivDen_iff.2 ⟨fun a ha => ?_, .inr ⟨⟨b, rfl⟩, ⟨c, rfl⟩⟩⟩⟩
    rcases hn a ((hy a).2 ha) with hq | heq
    · exact .inl hq
    · subst heq
      exact .inr ⟨rfl, b, ha, ha⟩
  · obtain ⟨ys, hl⟩ := e b
    obtain ⟨-, hy⟩ := (lamDen_iff _ _ _).1 hl
    refine ⟨ys, hl, (hy c).2 hs, fun a ha => ?_⟩
    rcases (ldivDen_iff.1 hd).1 a ((hy a).1 ha) with hq | ⟨heq, -⟩
    · exact .inl hq
    · exact .inr heq.symm

/-- freyd `Λ_comp_est_context`: `Λ(S) est(R ∩ S°S) = Λ(S) est(R)` at `R ≜ Q ∪ 𝟙`; no totality of `Λ(S)` is used. -/
theorem Tm.lamCompEstContext_den {A B : Obj} {S : Tm B A} {Q : Tm A A} (ρ : Val)
    (_ : (Tm.dom (Tm.lam S)).den ρ = (Tm.id (A := B)).den ρ) :
    (Tm.comp (Tm.lam S) (Tm.est (pairTest (Tm.meet (Tm.join Q Tm.id) (Tm.comp S.conv S))))).den ρ =
      (Tm.comp (Tm.lam S) (Tm.est (pairTest Q))).den ρ := by
  refine Core.Rel.ext fun b c => ?_
  change (Core.Rel.comp (Tm.den ρ (Tm.lam S)) (Tm.den ρ (Tm.est (pairTest _)))) b c ↔
    (Core.Rel.comp (Tm.den ρ (Tm.lam S)) (Tm.den ρ (Tm.est (pairTest Q)))) b c
  rw [Tm.estPairTest_den, Tm.estPairTest_den]
  simp only [Tm.den, Core.Rel.inter, Core.Rel.comp]
  refine ⟨fun ⟨ys, hl, hm, hn⟩ => ?_, fun ⟨ys, hl, hm, hn⟩ => ?_⟩
  · refine ⟨ys, hl, hm, fun a ha => ?_⟩
    rcases hn a ha with ⟨hq, -⟩ | heq
    · exact hq
    · exact .inr heq
  · obtain ⟨-, hy⟩ := (lamDen_iff _ _ _).1 hl
    refine ⟨ys, hl, hm, fun a ha => ?_⟩
    rcases hn a ha with hq | heq
    · by_cases hca : c = a
      · exact .inr hca
      · exact .inl ⟨.inl hq, b, (hy c).1 hm, (hy a).1 ha⟩
    · exact .inr heq

/-- freyd `singletonMap_comp_est`: `τ est(Q) = 𝟙 ∩ (Q ∪ 𝟙)°`. -/
theorem Tm.singletonMapCompEst_den {A : Obj} {Q : Tm A A} (ρ : Val) :
    (Tm.comp (Tm.prim (rowOf "τ")) (Tm.est (pairTest Q))).den ρ =
      (Tm.meet Tm.id (Tm.join Q.conv Tm.id)).den ρ := by
  refine Core.Rel.ext fun a c => ?_
  change (Core.Rel.comp (Tm.den ρ (Tm.prim (rowOf "τ"))) (Tm.den ρ (Tm.est (pairTest Q)))) a c ↔ _
  rw [Tm.estPairTest_den]
  simp only [Tm.den, Prim.den_tau, Core.Rel.inter, Core.Rel.comp, exists_eq_left]
  refine ⟨fun ⟨hm, hn⟩ => ?_, fun h => ?_⟩
  · obtain rfl := List.mem_singleton.1 hm
    exact ⟨rfl, .inr rfl⟩
  · obtain ⟨hac, -⟩ := h
    subst hac
    exact ⟨List.mem_singleton_self _, fun x hx => .inr (List.mem_singleton.1 hx).symm⟩

/-- freyd `powerRel_map_comp_est` at `P(f) = E(f)` (`powerRel_map`): `E(f) est(Q) = est(f (Q ∪ 𝟙) f°) f`. -/
theorem Tm.powerRelMapCompEst_den {A B : Obj} {f : Tm A B} {Q : Tm B B} (ρ : Val)
    (h1 : (Tm.dom f).den ρ = (Tm.id (A := A)).den ρ)
    (h2 : (Tm.comp f.conv f).den ρ ⊑ (Tm.id (A := B)).den ρ)
    (h3 : (Tm.dom (Tm.lam (Tm.comp Tm.mem f))).den ρ = (Tm.id (A := .arr A)).den ρ) :
    (Tm.comp (Tm.lam (Tm.comp Tm.mem f)) (Tm.est (pairTest Q))).den ρ =
      (Tm.comp (Tm.est (pairTest (Tm.comp (Tm.comp f (Tm.join Q Tm.id)) f.conv))) f).den ρ := by
  have e1 := Tm.entire_of_dom h1
  have e3 := Tm.entire_of_dom h3
  have hs : ∀ a b b', f.den ρ a b → f.den ρ a b' → b = b' := fun a b b' h h' =>
    Core.Rel.le_iff.1 h2 b b' ⟨a, h, h'⟩
  refine Core.Rel.ext fun xs d => ?_
  change (Core.Rel.comp (Tm.den ρ (Tm.lam (Tm.comp Tm.mem f))) (Tm.den ρ (Tm.est (pairTest Q)))) xs d ↔
    (Core.Rel.comp (Tm.den ρ (Tm.est (pairTest (Tm.comp (Tm.comp f (Tm.join Q Tm.id)) f.conv)))) (Tm.den ρ f)) xs d
  rw [Tm.E_den, Tm.estPairTest_den, Tm.estPairTest_den]
  simp only [Tm.den, Core.Rel.inter, Core.Rel.comp]
  refine ⟨fun ⟨ys, hy, hm, hn⟩ => ?_, fun ⟨a, ⟨ha, hl⟩, hF⟩ => ?_⟩
  · obtain ⟨-, hys⟩ := (EDen_iff _ _ _).1 hy
    obtain ⟨a, ha, hF⟩ := (hys d).1 hm
    refine ⟨a, ⟨ha, fun a' ha' => ?_⟩, hF⟩
    obtain ⟨c', hc'⟩ := e1 a'
    rcases hn c' ((hys c').2 ⟨a', ha', hc'⟩) with hq | heq
    · exact .inl ⟨c', ⟨d, hF, .inl hq⟩, hc'⟩
    · exact .inl ⟨c', ⟨d, hF, .inr heq⟩, hc'⟩
  · obtain ⟨ys, hy⟩ := e3 xs
    obtain ⟨-, hys⟩ := (EDen_iff _ _ _).1 hy
    refine ⟨ys, hy, (hys d).2 ⟨a, ha, hF⟩, fun c' hc' => ?_⟩
    obtain ⟨a', ha', hc'F⟩ := (hys c').1 hc'
    rcases hl a' ha' with ⟨b', ⟨b, hb, hq⟩, hb'⟩ | heq
    · obtain rfl := hs _ _ _ hF hb
      obtain rfl := hs _ _ _ hc'F hb'
      exact hq
    · subst heq
      exact .inr (hs _ _ _ hF hc'F)

end Rel.Lang
