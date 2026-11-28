import Rel.Lang.Laws.AopA7_1
import Rel.Lang.Laws.AopA7_2
import Rel.Lang.Laws.AopA4_6
import Rel.Lang.Laws.AopA5_5_TypeFunctor
import Rel.Lang.PreludeDfn

/-! # Laws of freyd `AOP/A7_3_Party.lean` (B&dM §7.3, the company party), on the concrete core

The rose tree and the rating sum are not in rel, so `R` is any relation on `[α]` and the list-level premises
`(𝟙×R°)cons ⊑ cons R°`, `F(R°)C ⊑ C R°` (`C` any `[[α]] ⟶ [α]`, in the book `concat`) stand in for `cons_monotonic` and
`concat_monotonic`; the product `R×R` is written `⟨π₁R, π₂R⟩`, the product without the elaborator's definedness guard.
`Rel/Programs/Aop/A7_3_Party.lean` states each law as `theorem <name> … by Rel.Lang.Tm.<name>_den`. -/

namespace Rel.Lang
open Tab Rel.Rep
open scoped Rel.Core.Rel
open Rel.Core.Rel hiding id comp recip inter union zero le inl inr junc

/-- `⟨π₁R, π₂R⟩`, the product `R×R` without a guard. -/
abbrev Tm.prodR {B : Obj} (R : Tm B B) : Tm (.prod B B) (.prod B B) := Tm.pair (Tm.comp Tm.outl R) (Tm.comp Tm.outr R)

/-- `⟨π₁R, π₂R⟩°` as the elaborator writes it: the converse goes into the product, `R°` beside an `id`. -/
def Tm.prodC {B : Obj} (R : Tm B B) : Tm (.prod B B) (.prod B B) :=
  Tm.pair (Tm.comp Tm.outl (Tm.comp (Tm.conv R) Tm.id)) (Tm.comp Tm.outr (Tm.comp (Tm.conv R) Tm.id))

theorem Tm.prodC_den {B : Obj} {R : Tm B B} (ρ : Val) : (Tm.prodC R).den ρ = (Tm.conv (Tm.prodR R)).den ρ := by
  refine Core.Rel.ext fun p q => ?_
  simp only [Tm.prodC, Tm.den, Core.Rel.comp_apply, Core.Rel.recip_apply, Core.Rel.rpair, Core.Rel.graph, Core.Rel.id]
  constructor
  · rintro ⟨⟨_, rfl, _, h1, rfl⟩, ⟨_, rfl, _, h2, rfl⟩⟩
    exact ⟨⟨_, rfl, h1⟩, ⟨_, rfl, h2⟩⟩
  · rintro ⟨⟨_, rfl, h1⟩, ⟨_, rfl, h2⟩⟩
    exact ⟨⟨_, rfl, _, h1, rfl⟩, ⟨_, rfl, _, h2, rfl⟩⟩

/-- `𝟙×X` as the elaborator writes it. -/
abbrev Tm.crossId {A B C : Obj} (X : Tm B C) : Tm (.prod A B) (.prod A C) :=
  Tm.pair (Tm.comp Tm.outl Tm.id) (Tm.comp Tm.outr X)

/-- `choose = π₁ ∪ π₂`. -/
abbrev Tm.chooseT {B : Obj} : Tm (.prod B B) B := Tm.join Tm.outl Tm.outr

/-- B&dM §7.3, first monotonicity claim: `(R×R)° choose ⊑ choose R°`, for any `R`. -/
theorem Tm.chooseRMonotonic_den {B : Obj} {R : Tm B B} (ρ : Val) :
    (Tm.comp (Tm.prodC R) Tm.chooseT).den ρ ⊑ (Tm.comp Tm.chooseT (Tm.conv R)).den ρ := by
  refine Core.Rel.le_iff.2 fun p y => ?_
  simp only [Tm.prodC_den, Tm.den, Core.Rel.comp_apply, Core.Rel.recip_apply, Core.Rel.rpair, Core.Rel.graph, Core.Rel.union_apply]
  rintro ⟨b, ⟨⟨_, rfl, h1⟩, ⟨_, rfl, h2⟩⟩, rfl | rfl⟩
  · exact ⟨p.1, .inl rfl, h1⟩
  · exact ⟨p.2, .inr rfl, h2⟩

/-- `F(X)`, the list relator, as the elaborator writes it. -/
abbrev Tm.fmapT {A B : Obj} (X : Tm A B) : Tm (.arr A) (.arr B) := Tm.arg (Tm.prim mapRow : Tm (.arr A) (.arr B)) X

/-- **party-mono-branch**: a branch `(𝟙×(F(g) C)) h` is monotonic on `(R×R)°` given its `g` row, its `h` row and
    `F(R°) C ⊑ C R°` (stronger form: `C` is any `[[α]] ⟶ [α]`, in the book `concat`, whose row the sum makes a leaf). -/
theorem Tm.branchMonotonic_den {A : Obj} {R : Tm (.arr A) (.arr A)} {g : Tm (.prod (.arr A) (.arr A)) (.arr A)}
    {h : Tm (.prod A (.arr A)) (.arr A)} {C : Tm (.arr (.arr A)) (.arr A)} (ρ : Val)
    (hg : (Tm.comp (Tm.prodC R) g).den ρ ⊑ (Tm.comp g (Tm.conv R)).den ρ)
    (hh : (Tm.comp (Tm.crossId (Tm.conv R)) h).den ρ ⊑ (Tm.comp h (Tm.conv R)).den ρ)
    (hC : (Tm.comp (Tm.fmapT (Tm.conv R)) C).den ρ ⊑ (Tm.comp C (Tm.conv R)).den ρ) :
    (Tm.comp (Tm.crossId (Tm.fmapT (Tm.prodC R))) (Tm.comp (Tm.crossId (Tm.comp (Tm.fmapT g) C)) h)).den ρ ⊑
      (Tm.comp (Tm.comp (Tm.crossId (Tm.comp (Tm.fmapT g) C)) h) (Tm.conv R)).den ρ := by
  have hg' := Core.Rel.le_iff.1 hg
  have hh' := Core.Rel.le_iff.1 hh
  have hC' := Core.Rel.le_iff.1 hC
  refine Core.Rel.le_iff.2 fun u y => ?_
  simp only [Tm.prodC_den, Tm.den, Core.Rel.comp_apply, Core.Rel.recip_apply, Core.Rel.rpair, Core.Rel.graph, Tm.argDen, Prim.den_mapRow] at hg' hh' hC' ⊢
  rintro ⟨b, ⟨⟨_, rfl, hid⟩, ⟨_, rfl, hmap⟩⟩, b1, ⟨⟨_, rfl, hid2⟩, ⟨_, rfl, qs, hF, hC1⟩⟩, hh1⟩
  obtain ⟨hl, hp⟩ := (mapDen_iff _ _ _).1 hmap
  obtain ⟨hl2, hq⟩ := (mapDen_iff _ _ _).1 hF
  have hgl : mapDen (den ρ g ≫ (den ρ R)°) u.2 qs := (mapDen_iff _ _ _).2 ⟨by omega, fun t h1 h2 => by
    obtain ⟨hp1, hp2⟩ := hp t h1 (by omega)
    exact hg' u.2[t] qs[t] ⟨b.2[t]'(by omega), ⟨hp1, hp2⟩, hq t (by omega) h2⟩⟩
  rw [← mapDen_comp] at hgl
  obtain ⟨qs', hg1, hg2⟩ := hgl
  obtain ⟨w', hC2, hw⟩ := hC' qs' b1.2 ⟨qs, hg2, hC1⟩
  obtain ⟨y', hh2, hy⟩ := hh' (u.1, w') y ⟨b1, ⟨⟨_, rfl, (show u.1 = b1.1 from (show u.1 = b.1 from hid).trans (show b.1 = b1.1 from hid2))⟩, ⟨_, rfl, hw⟩⟩, hh1⟩
  exact ⟨y', ⟨(u.1, w'), ⟨⟨_, rfl, rfl⟩, ⟨_, rfl, qs', hg1, hC2⟩⟩, hh2⟩, hy⟩

/-- `(R×R)° π₂ ⊑ π₂ R°` (law 4 of the product calculus), the `g := π₂` row of `include`. -/
theorem Tm.prodRConvOutr_den {B : Obj} {R : Tm B B} (ρ : Val) :
    (Tm.comp (Tm.prodC R) Tm.outr).den ρ ⊑ (Tm.comp Tm.outr (Tm.conv R)).den ρ := by
  refine Core.Rel.le_iff.2 fun p y => ?_
  simp only [Tm.prodC_den, Tm.den, Core.Rel.comp_apply, Core.Rel.recip_apply, Core.Rel.rpair, Core.Rel.graph]
  rintro ⟨b, ⟨⟨_, rfl, h1⟩, ⟨_, rfl, h2⟩⟩, rfl⟩
  exact ⟨p.2, rfl, h2⟩

/-- **party-mono-branch, `include` row**: `(𝟙×F((R×R)°)) ((𝟙×(F(π₂) C)) h) ⊑ ((𝟙×(F(π₂) C)) h) R°` — `g := π₂`, and `h`
    is any `α×[α] ⟶ [α]` with `(𝟙×R°)h ⊑ h R°` (in the book `cons`). -/
theorem Tm.includeMonotonic_den {A : Obj} {R : Tm (.arr A) (.arr A)} {h : Tm (.prod A (.arr A)) (.arr A)}
    {C : Tm (.arr (.arr A)) (.arr A)} (ρ : Val)
    (hh : (Tm.comp (Tm.crossId (Tm.conv R)) h).den ρ ⊑ (Tm.comp h (Tm.conv R)).den ρ)
    (hC : (Tm.comp (Tm.fmapT (Tm.conv R)) C).den ρ ⊑ (Tm.comp C (Tm.conv R)).den ρ) :
    (Tm.comp (Tm.crossId (Tm.fmapT (Tm.prodC R))) (Tm.comp (Tm.crossId (Tm.comp (Tm.fmapT Tm.outr) C)) h)).den ρ ⊑
      (Tm.comp (Tm.comp (Tm.crossId (Tm.comp (Tm.fmapT Tm.outr) C)) h) (Tm.conv R)).den ρ :=
  Tm.branchMonotonic_den ρ (Tm.prodRConvOutr_den ρ) hh hC

/-- **party-mono-branch, `exclude` row**: `(𝟙×F((R×R)°)) (π₂ F(g) C) ⊑ (π₂ F(g) C) R°` given the `g` row
    `(R×R)° g ⊑ g R°` (stronger form: `g` is any `[α]×[α] ⟶ [α]`; `g = choose` by `chooseRMonotonic`) and
    `F(R°) C ⊑ C R°`. -/
theorem Tm.excludeMonotonic_den {A S : Obj} {R : Tm (.arr A) (.arr A)} {g : Tm (.prod (.arr A) (.arr A)) (.arr A)}
    {C : Tm (.arr (.arr A)) (.arr A)} (ρ : Val)
    (hg : (Tm.comp (Tm.prodC R) g).den ρ ⊑ (Tm.comp g (Tm.conv R)).den ρ)
    (hC : (Tm.comp (Tm.fmapT (Tm.conv R)) C).den ρ ⊑ (Tm.comp C (Tm.conv R)).den ρ) :
    (Tm.comp (Tm.crossId (Tm.fmapT (Tm.prodC R))) (Tm.comp (Tm.comp (Tm.outr (A := S)) (Tm.fmapT g)) C)).den ρ ⊑
      (Tm.comp (Tm.comp (Tm.comp (Tm.outr (A := S)) (Tm.fmapT g)) C) (Tm.conv R)).den ρ := by
  have hg' := Core.Rel.le_iff.1 hg
  have hC' := Core.Rel.le_iff.1 hC
  refine Core.Rel.le_iff.2 fun u y => ?_
  simp only [Tm.prodC_den, Tm.den, Core.Rel.comp_apply, Core.Rel.recip_apply, Core.Rel.rpair, Core.Rel.graph, Tm.argDen,
    Prim.den_mapRow] at hg' hC' ⊢
  rintro ⟨b, ⟨⟨_, rfl, hid⟩, ⟨_, rfl, hmap⟩⟩, qs, ⟨_, rfl, hF⟩, hC1⟩
  obtain ⟨hl, hp⟩ := (mapDen_iff _ _ _).1 hmap
  obtain ⟨hl2, hq⟩ := (mapDen_iff _ _ _).1 hF
  have hgl : mapDen (den ρ g ≫ (den ρ R)°) u.2 qs := (mapDen_iff _ _ _).2 ⟨by omega, fun t h1 h2 => by
    obtain ⟨hp1, hp2⟩ := hp t h1 (by omega)
    exact hg' u.2[t] qs[t] ⟨b.2[t]'(by omega), ⟨hp1, hp2⟩, hq t (by omega) h2⟩⟩
  rw [← mapDen_comp] at hgl
  obtain ⟨qs', hg1, hg2⟩ := hgl
  obtain ⟨w', hC2, hw⟩ := hC' qs' y ⟨qs, hg2, hC1⟩
  exact ⟨w', ⟨qs', ⟨_, rfl, hg1⟩, hC2⟩, hw⟩

/-- **party-mono** (B&dM §7.3's headline): `(𝟙×F((R×R)°)) ⟨X, Y⟩ ⊑ ⟨X, Y⟩ (R×R)°` from the two component rows
    `(𝟙×F((R×R)°)) X ⊑ X R°` and the same for `Y` (the `include` and `exclude` rows). -/
theorem Tm.pairMonotonic_den {A : Obj} {R : Tm (.arr A) (.arr A)} {X Y : Tm (.prod A (.arr (.prod (.arr A) (.arr A)))) (.arr A)}
    (ρ : Val)
    (hX : (Tm.comp (Tm.crossId (Tm.fmapT (Tm.prodC R))) X).den ρ ⊑ (Tm.comp X (Tm.conv R)).den ρ)
    (hY : (Tm.comp (Tm.crossId (Tm.fmapT (Tm.prodC R))) Y).den ρ ⊑ (Tm.comp Y (Tm.conv R)).den ρ) :
    (Tm.comp (Tm.crossId (Tm.fmapT (Tm.prodC R))) (Tm.pair X Y)).den ρ ⊑
      (Tm.comp (Tm.pair X Y) (Tm.prodC R)).den ρ := by
  have hX' := Core.Rel.le_iff.1 hX
  have hY' := Core.Rel.le_iff.1 hY
  refine Core.Rel.le_iff.2 fun u q => ?_
  simp only [Tm.prodC_den, Tm.den, Core.Rel.comp_apply, Core.Rel.recip_apply, Core.Rel.rpair, Core.Rel.graph, Tm.argDen,
    Prim.den_mapRow] at hX' hY' ⊢
  rintro ⟨b, hb, hXb, hYb⟩
  obtain ⟨p1, hp1, hq1⟩ := hX' u q.1 ⟨b, hb, hXb⟩
  obtain ⟨p2, hp2, hq2⟩ := hY' u q.2 ⟨b, hb, hYb⟩
  exact ⟨(p1, p2), ⟨hp1, hp2⟩, ⟨_, rfl, hq1⟩, ⟨_, rfl, hq2⟩⟩

/-- **party-mono**: the book's `S = ⟨include, exclude⟩` with `include = (𝟙×(F(π₂) C)) h` and `exclude = π₂ F(choose) C`,
    for `h` with `(𝟙×R°)h ⊑ h R°` and `C` with `F(R°)C ⊑ C R°` (stronger form: `h`, `C` any, `R` any). -/
theorem Tm.partyMono_den {A : Obj} {R : Tm (.arr A) (.arr A)} {h : Tm (.prod A (.arr A)) (.arr A)}
    {C : Tm (.arr (.arr A)) (.arr A)} (ρ : Val)
    (hh : (Tm.comp (Tm.crossId (Tm.conv R)) h).den ρ ⊑ (Tm.comp h (Tm.conv R)).den ρ)
    (hC : (Tm.comp (Tm.fmapT (Tm.conv R)) C).den ρ ⊑ (Tm.comp C (Tm.conv R)).den ρ) :
    (Tm.comp (Tm.crossId (Tm.fmapT (Tm.prodC R)))
      (Tm.pair (Tm.comp (Tm.crossId (Tm.comp (Tm.fmapT Tm.outr) C)) h)
        (Tm.comp (Tm.comp (Tm.outr (A := A)) (Tm.fmapT Tm.chooseT)) C))).den ρ ⊑
    (Tm.comp (Tm.pair (Tm.comp (Tm.crossId (Tm.comp (Tm.fmapT Tm.outr) C)) h)
        (Tm.comp (Tm.comp (Tm.outr (A := A)) (Tm.fmapT Tm.chooseT)) C)) (Tm.prodC R)).den ρ :=
  Tm.pairMonotonic_den ρ (Tm.includeMonotonic_den ρ hh hC) (Tm.excludeMonotonic_den ρ (Tm.chooseRMonotonic_den ρ) hC)

/-- `f ⊑ Λ(f) est(Q)` for a simple `f` (freyd `graph_le_Λ_est`: a map is its own best output; `est(Q)` is `est(Q ∪ 𝟙)`, so no
    reflexivity of `Q` is needed). -/
theorem Tm.graphLeLamEst_den {A B : Obj} {f : Tm B A} {Q : Tm A A} (ρ : Val)
    (hs : (Tm.comp (Tm.conv f) f).den ρ ⊑ (Tm.id (A := A)).den ρ)
    (h : (Tm.dom (Tm.lam f)).den ρ = (Tm.id (A := B)).den ρ) :
    f.den ρ ⊑ (Tm.comp (Tm.lam f) (Tm.est (pairTest Q))).den ρ := by
  have e := Tm.entire_of_dom h
  have hs' := Core.Rel.le_iff.1 hs
  refine Core.Rel.le_iff.2 fun b c hbc => ?_
  obtain ⟨ys, hl⟩ := e b
  obtain ⟨-, hy⟩ := (lamDen_iff _ _ _).1 hl
  change (Core.Rel.comp (Tm.den ρ (Tm.lam f)) (Tm.den ρ (Tm.est (pairTest Q)))) b c
  rw [Tm.estPairTest_den]
  simp only [Tm.den, Core.Rel.inter, Core.Rel.comp, Core.Rel.comp_apply, Core.Rel.recip_apply, Core.Rel.id] at hs' ⊢
  refine ⟨ys, hl, (hy c).2 hbc, fun a ha => ?_⟩
  exact .inr (hs' c a ⟨b, hbc, (hy a).1 ha⟩)

end Rel.Lang
