import Rel.Programs.Prelude
import Rel.Lang.Laws.AopA5_5

namespace Rel.Programs

open Rel.Programs.prelude in
rel_program aopA5_5 where
    theorem foldCancel(e : 1 ⟶ β, S : β×α ⟶ β) : ⦇[e, S]⦈ = nil°e ∪ (snoc°(⦇[e, S]⦈×𝟙)S) by Rel.Lang.Tm.fold_cancel_den  -- Freyd.Alg.relCata_cancel, 02-categories.typ:42
    theorem foldFusion(e : 1 ⟶ β, f : β×α ⟶ β, e' : 1 ⟶ γ, g : γ×α ⟶ γ, T : β ⟶ γ) if e T = e', f T = (T×𝟙) g : ⦇[e, f]⦈ T = ⦇[e', g]⦈ by Rel.Lang.Tm.fold_fusion_den  -- Freyd.Alg.relCata_fusion, 02-categories.typ:96


-- the list instance: `α = [nil, snoc]`, `⦇[e,S]⦈` the prelude fold; `relCata_UP` (iff) is `foldCancel` (←) with the prelude's `foldUP` (→)
-- not ported: relCata_UP (Freyd.Alg.relCata_UP, 05-datatypes.typ:410): an iff; its two halves are the prelude `foldUP` and `foldCancel` above
-- not ported: InitialAlgebra.cata_comm (02-categories.typ:24): a class field with no statement of its own; its list instance is `foldCancel`
-- not ported: relCata_unfold (05-datatypes.typ:461): `rfl` of freyd's definition `⦇R⦈ = cata(Λ(F∋ R)) ≫ ∋`; the language's fold is not defined through `Λ`
-- not ported: Λ_relCata (05-datatypes.typ:467): Eilenberg-Wright `Λ(⦇R⦈) = cata(Λ(F∋ R))` needs a map-restricted cata over power objects, which has no Rel term
-- not ported: InitialAlgebra.recip_alpha_alpha (06-recursive.typ:127, 05-datatypes.typ:511): `[nil,snoc]°[nil,snoc] = 𝟙` has `nil°nil` at an unconstrained source `α`; `nil°` runs on demand over `α`'s universe, so it is the coreflexive of `[]` only where `α` is inhabited (needs `closedNil`); no equation to cite
end Rel.Programs
