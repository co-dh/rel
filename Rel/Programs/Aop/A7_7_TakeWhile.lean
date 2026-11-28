import Rel.Programs.Prelude
import Rel.Lang.Laws.AopA7_7_TakeWhile

namespace Rel.Programs

open Rel.Programs.prelude in
rel_program aopA7_7_TakeWhile where
    discNil : α×[α] ⟶ [α] ≜ nil   -- freyd's `⊸ nil`, typed so the mono rows state it at `α×[α]`
    prefC : [α] ⟶ [α] ≜ ⦇[nil, nil ∪ cons]⦈ʳ   -- freyd's `prefix` on cons lists (the prelude's `prefix` is the same relation, `cat° π₁`)
    -- Stronger form of takewhile_alg_comm / takewhile_alg: `p` is any relation, not only a coreflexive (`⊸ nil` is `nil` at `α×[α]`)
    theorem takewhileAlgComm(p : α ⟶ α) : prefC F(p) = nil°nil ∪ (cons°(𝟙×(prefC F(p)))(⟨π₁ p, π₂⟩cons ∪ nil)) by Rel.Lang.Tm.takewhileAlgComm_den  -- Freyd.Alg.RelSet.GCTakeWhile.takewhile_alg_comm, 07-optimisation.typ:534
    theorem takewhileAlg(p : α ⟶ α) : prefC F(p) = ⦇[nil, ⟨π₁ p, π₂⟩cons ∪ nil]⦈ʳ by Rel.Lang.Tm.takewhileAlg_den  -- Freyd.Alg.RelSet.GCTakeWhile.takewhile_alg, 07-optimisation.typ:528
    -- takewhile-mono at a generic `Q` for `R°` (stronger form; `Q = R°`, `R = length ≤ length°`, is an instance): premises are what `R°` provides
    theorem takewhileMonoDisc(Q : [α] ⟶ [α]) : ⟨π₁, π₂ Q⟩ discNil ⊑ discNil by Rel.Lang.Tm.takewhileMonoDisc_den  -- Freyd.Alg.RelSet.GCTakeWhile.takewhile_mono_disc, 07-optimisation.typ:592
    theorem takewhileMonoFork(p : α ⟶ α, Q : [α] ⟶ [α]) : ⟨π₁, π₂ Q⟩(⟨π₁ p, π₂⟩cons ∪ discNil) = (⟨π₁ p, π₂ Q⟩cons) ∪ (⟨π₁, π₂ Q⟩discNil) by Rel.Lang.Tm.takewhileMonoFork_den  -- Freyd.Alg.RelSet.GCTakeWhile.takewhile_mono_fork, 07-optimisation.typ:585
    theorem takewhileMonoSlide(p : α ⟶ α, Q : [α] ⟶ [α]) if ⟨π₁, π₂ Q⟩cons ⊑ cons Q : ⟨π₁ p, π₂ Q⟩cons ⊑ ⟨π₁ p, π₂⟩cons Q by Rel.Lang.Tm.takewhileMonoSlide_den  -- Freyd.Alg.RelSet.GCTakeWhile.takewhile_mono_slide, 07-optimisation.typ:596
    -- not ported: takewhile_mono_nil (07-optimisation.typ:470): `nil R° = nil` is the order fact of `R = length ≤ length°` (no universe at `[α]`); at a generic `Q` it is the premise `nil ⊑ nil Q` of takewhileMonoCons
    theorem takewhileMonoCons(p : α ⟶ α, Q : [α] ⟶ [α]) if ⟨π₁, π₂ Q⟩cons ⊑ cons Q, discNil ⊑ discNil Q : ⟨π₁, π₂ Q⟩(⟨π₁ p, π₂⟩cons ∪ discNil) ⊑ (⟨π₁ p, π₂⟩cons ∪ discNil) Q by Rel.Lang.Tm.takewhileMonoCons_den  -- Freyd.Alg.RelSet.GCTakeWhile.takewhile_mono_cons, 07-optimisation.typ:576
    -- F(Q) = [𝟙(1) inl, ⟨π₁𝟙, π₂Q⟩ inr] (A9_4's spelling); `nil°nil ⊑ Q` (Q keeps `[]`) is the nil arm (stronger form of takewhile_mono: `Pres S R°` at any `Q`)
    theorem takewhileMono(p : α ⟶ α, Q : [α] ⟶ [α]) if ⟨π₁, π₂ Q⟩cons ⊑ cons Q, nil°nil ⊑ Q : [𝟙(1) inl, ⟨π₁𝟙, π₂ Q⟩ inr] [nil, ⟨π₁ p, π₂⟩cons ∪ discNil] ⊑ [nil, ⟨π₁ p, π₂⟩cons ∪ discNil] Q by Rel.Lang.Tm.takewhileMono_den  -- Freyd.Alg.RelSet.GCTakeWhile.takewhile_mono, 07-optimisation.typ:590
    -- takewhile_simple at a generic `Q` for `R°`: the prefixes of one list that `Q ∪ 𝟙` orders both ways are equal (`R = length ≤ length°` gives it, no coreflexive `p` needed)
    theorem takewhileSimple(p : α ⟶ α, Q : [α] ⟶ [α]) if ((prefC F(p))° (prefC F(p))) ∩ ((Q ∪ 𝟙) ∩ (Q ∪ 𝟙)°) ⊑ 𝟙 : (Λ(prefC F(p)) est(Q))° (Λ(prefC F(p)) est(Q)) ⊑ 𝟙 by Rel.Lang.Tm.takewhileSimple_den  -- Freyd.Alg.RelSet.GCTakeWhile.takewhile_simple, 07-optimisation.typ:672
    -- not ported: discNil_apply (454): host-level pointwise fact about `⊸ nil` on a pair, no relation statement
    -- not ported: takewhile_cata_le (655): needs `R = length ≤ length°` on `[α]` (no universe at `[α]`)
    -- not ported: takewhile_entire (675): needs `dom` of the takewhile catamorphism over host list types
    -- not ported: takewhile_eq_cata (422): host `List.takeWhile` function equality, no relation form
    -- not ported: takewhile_step (616): needs `R = length ≤ length°` and host list recursion

end Rel.Programs
