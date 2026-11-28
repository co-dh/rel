import Rel.Programs.Prelude
import Rel.Lang.Laws.AopA7_3_Party

/-! # Laws of AOP `A7_3_Party.lean` (companion `07-optimisation.typ`), in Rel

B&dM §7.3, planning a company party. The rose tree and the rating sum are not in rel, so every law is at a relation `R`
on `[α]` (in the book `R = cost ≤ cost°`) with the list-level premises `(𝟙×R°)cons ⊑ cons R°` and `F(R°)C ⊑ C R°`
(`C = concat`) standing in for `cons_monotonic` and `concat_monotonic`; `R×R` is written `⟨π₁ R, π₂ R⟩`, the product without
the elaborator's definedness guard. -/

namespace Rel.Programs

open Rel.Programs.prelude in
rel_program aopA7_3_Party where
    -- B&dM p.177, first monotonicity claim (`choose = π₁ ∪ π₂`); stronger form: `R` is any relation on `β`
    theorem chooseRMonotonic(R : β ⟶ β) : ⟨π₁ R, π₂ R⟩° (π₁ ∪ π₂) ⊑ (π₁ ∪ π₂) R° by Rel.Lang.Tm.chooseRMonotonic_den  -- Freyd.Alg.RelSet.Party.chooseR_monotonic, 07-optimisation.typ:1306
    -- stronger form: `R` is any relation on `[α]` and `C` any `[[α]] ⟶ [α]`; `g`, `h` rows and `F(R°) C ⊑ C R°` are premises
    theorem branchMonotonic(R : [α] ⟶ [α], g : [α]×[α] ⟶ [α], h : α×[α] ⟶ [α], C : [[α]] ⟶ [α]) if ⟨π₁ R, π₂ R⟩° g ⊑ g R°, (𝟙×R°) h ⊑ h R°, F(R°) C ⊑ C R° : (𝟙×F(⟨π₁ R, π₂ R⟩°)) ((𝟙×(F(g) C)) h) ⊑ ((𝟙×(F(g) C)) h) R° by Rel.Lang.Tm.branchMonotonic_den  -- Freyd.Alg.RelSet.Party.branch_monotonic, 07-optimisation.typ:1271
    -- stronger form: `R` is any relation, `C` any `[[α]] ⟶ [α]`; `cons_monotonic` and `concat_monotonic` are the premises
    theorem includeMonotonic(R : [α] ⟶ [α], C : [[α]] ⟶ [α]) if (𝟙×R°) cons ⊑ cons R°, F(R°) C ⊑ C R° : (𝟙×F(⟨π₁ R, π₂ R⟩°)) ((𝟙×(F(π₂) C)) cons) ⊑ ((𝟙×(F(π₂) C)) cons) R° by Rel.Lang.Tm.includeMonotonic_den  -- Freyd.Alg.RelSet.Party.include_monotonic, 07-optimisation.typ:1279
    -- stronger form: `g` is any `[α]×[α] ⟶ [α]` with the `g` row as premise (`g = π₁ ∪ π₂` by `chooseRMonotonic`); `exclude = π₂ F(g) C`
    theorem excludeMonotonic(R : [α] ⟶ [α], g : [α]×[α] ⟶ [α], C : [[α]] ⟶ [α]) if ⟨π₁ R, π₂ R⟩° g ⊑ g R°, F(R°) C ⊑ C R° : (𝟙×F(⟨π₁ R, π₂ R⟩°)) (π₂ F(g) C) ⊑ (π₂ F(g) C) R° by Rel.Lang.Tm.excludeMonotonic_den  -- Freyd.Alg.RelSet.Party.exclude_monotonic, 07-optimisation.typ:1281
    -- `party-mono` at the base functor `𝟙×F(-)` of the rose tree, `S = ⟨include, exclude⟩`, `g = π₁ ∪ π₂`
    theorem partyMono(R : [α] ⟶ [α], C : [[α]] ⟶ [α]) if (𝟙×R°) cons ⊑ cons R°, F(R°) C ⊑ C R° : (𝟙×F(⟨π₁ R, π₂ R⟩°)) ⟨(𝟙×(F(π₂) C)) cons, π₂ F(π₁ ∪ π₂) C⟩ ⊑ ⟨(𝟙×(F(π₂) C)) cons, π₂ F(π₁ ∪ π₂) C⟩ ⟨π₁ R, π₂ R⟩° by Rel.Lang.Tm.partyMono_den  -- Freyd.Alg.RelSet.Party.party_mono, 07-optimisation.typ:1230
    -- `party_absorb` at `⦇S⦈ choose`: stronger form, `X` is any `α ⟶ [α]×[α]` (the fold `⦇S⦈`); the premise is the book's totality of `Λ`
    theorem partyAbsorb(X : α ⟶ β×β) if dom(Λ(X)) = 𝟙 : Λ(X) E(π₁ ∪ π₂) = Λ(X (π₁ ∪ π₂)) by Rel.Lang.Tm.absorption_den  -- Freyd.Alg.RelSet.Party.party_absorb, 07-optimisation.typ:1243
    -- `f` is any simple relation (the book's map `f`); `est(Q)` is `est(Q ∪ 𝟙)`, so no `𝟙 ⊑ Q`
    theorem graphLeLamEst(f : α ⟶ β, Q : β ⟶ β) if f°f ⊑ 𝟙, dom(Λ(f)) = 𝟙 : f ⊑ Λ(f) est(Q) by Rel.Lang.Tm.graphLeLamEst_den  -- Freyd.Alg.RelSet.graph_le_Λ_est, 07-optimisation.typ:1391

-- not ported: cost_eq (07-optimisation.typ:1083), R_eq (:1088), include_eq (:1097), exclude_eq (:1101), party_eq (:1109): the point-free form is the definition itself (`cost ≜ F(r) sum`, `R ≜ cost ≤ cost°`, `include ≜ (𝟙×(F(π₂)concat))cons`, `exclude ≜ π₂F(choose)concat`; Rel/Programs/Party.lean states them as definitions), a syntactic identity here
-- not ported: concat_monotonic (07-optimisation.typ:1312), cons_monotonic (:1316): `cost` is a sum, and rel has no additive law for `sum`/`plus` over fixed-width atoms (an addition wraps); both appear as the premises `F(R°) C ⊑ C R°`, `(𝟙×R°) cons ⊑ cons R°` of the theorems above
-- not ported: party_laws (07-optimisation.typ:1115): the fold `⦇S⦈` runs over the rose tree, a recursive datatype rel does not have (Rel/Programs/Party.lean replaces it by `hylo(⟨𝟙, kids⟩, S)` at one concrete forest), and its greedy step has no hylo form proved; the rows it consumes (`party_mono`, `party_absorb`, `graph_le_Λ_est`) are above
-- not ported: exStaff_ratings (07-optimisation.typ:1122): `tree(snd)` over a `Rose (Char × Int)` literal, host data and no rose tree
-- not ported: party_example_costs (07-optimisation.typ:1149), party_listrr_example (:1197): `decide` on `Int` list literals through the host `costFn`; the same totals are the `check`s of Rel/Programs/Party.lean (`check root c max = {(a,17)}`)
-- not ported: party_list_choose_example (07-optimisation.typ:1172), run_best (:1145), run_kept (:1129), run_kept_b (:1133), run_kept_c (:1137): element quantifiers and host `List`/`Rose` values (`kept`, `best` are Lean functions), see Rel/Programs/Party.lean for the relational run

end Rel.Programs
