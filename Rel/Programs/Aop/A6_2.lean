import Rel.Programs.Prelude
import Rel.Lang.Laws.AopA6_2

/-! # Fixed-point laws of freyd §6.2 (`AOP/A6_2.lean`), in Rel

freyd's `relCata R` over its initial algebra is, at the list datatype `α = [nil, snoc]`, the prelude's left fold `⦇[e, S]⦈`,
and its recursion body `α° ≫ F(X) ≫ R` is `nil°e ∪ (snoc°(X×𝟙)S)` (as `foldCancel` in `A5_5`). The algebra `R = [e, S]`
and `T = [e', g]` are stated by their seeds and steps, so each row holds for every pair of algebras on the list datatype
(`F(S) T = [e', (S×𝟙) g]` after `S`). -/

namespace Rel.Programs

open Rel.Programs.prelude in
rel_program aopA6_2 where
    theorem relCataLeOfPrefixed(e : 1 ⟶ β, S : β×α ⟶ β, X : [α] ⟶ β) if nil°e ∪ (snoc°(X×𝟙)S) ⊑ X : ⦇[e, S]⦈ ⊑ X by Rel.Lang.Tm.relCata_le_of_prefixed_den  -- Freyd.Alg.relCata_le_of_prefixed, 06-recursive.typ:68
    theorem leRelCataOfPostfixed(e : 1 ⟶ β, S : β×α ⟶ β, X : [α] ⟶ β) if X ⊑ nil°e ∪ (snoc°(X×𝟙)S) : X ⊑ ⦇[e, S]⦈ by Rel.Lang.Tm.le_relCata_of_postfixed_den  -- Freyd.Alg.le_relCata_of_postfixed, 06-recursive.typ:71
    theorem relCataCompPrefixed(e : 1 ⟶ β, f : β×α ⟶ β, e' : 1 ⟶ γ, g : γ×α ⟶ γ, S : β ⟶ γ) if e' ⊑ e S, (S×𝟙) g ⊑ f S : nil°e' ∪ (snoc°((⦇[e, f]⦈ S)×𝟙)g) ⊑ ⦇[e, f]⦈ S by Rel.Lang.Tm.relCata_comp_prefixed_den  -- Freyd.Alg.relCata_comp_prefixed, 06-recursive.typ:90
    theorem relCataLeComp(e : 1 ⟶ β, f : β×α ⟶ β, e' : 1 ⟶ γ, g : γ×α ⟶ γ, S : β ⟶ γ) if e' ⊑ e S, (S×𝟙) g ⊑ f S : ⦇[e', g]⦈ ⊑ ⦇[e, f]⦈ S by Rel.Lang.Tm.relCata_le_comp_den  -- Freyd.Alg.relCata_le_comp, 06-recursive.typ:81
    theorem relCataCompPostfixed(e : 1 ⟶ β, f : β×α ⟶ β, e' : 1 ⟶ γ, g : γ×α ⟶ γ, S : β ⟶ γ) if e S ⊑ e', f S ⊑ (S×𝟙) g : (⦇[e, f]⦈ S) ⊑ nil°e' ∪ (snoc°((⦇[e, f]⦈ S)×𝟙)g) by Rel.Lang.Tm.relCata_comp_postfixed_den  -- Freyd.Alg.relCata_comp_postfixed, 06-recursive.typ:100
    theorem compLeRelCata(e : 1 ⟶ β, f : β×α ⟶ β, e' : 1 ⟶ γ, g : γ×α ⟶ γ, S : β ⟶ γ) if e S ⊑ e', f S ⊑ (S×𝟙) g : (⦇[e, f]⦈ S) ⊑ ⦇[e', g]⦈ by Rel.Lang.Tm.comp_le_relCata_den  -- Freyd.Alg.comp_le_relCata, 06-recursive.typ:82

-- not ported: mu_le (Freyd.Alg.mu_le, 06-recursive.typ:60): the core has it, `Rel.Core.Rel.mu_le`
-- not ported: mu_fixed (Freyd.Alg.mu_fixed, 06-recursive.typ:64): the core has it, `Rel.Core.Rel.mu_fix`
-- not ported: mu_rolling (Freyd.Alg.mu_rolling, 06-recursive.typ:567): rolling needs a mapping between hom-sets as a Lean function `fun`, which is not a relation (needs a rel primitive or prelude definition)
-- not ported: relCata_eq_mu (Freyd.Alg.relCata_eq_mu, 06-recursive.typ:77): `μ` of a Lean function `fun X => α° ≫ F(X) ≫ R`, which the language does not state
-- not ported: relCata_eq_nu (Freyd.Alg.relCata_eq_nu, 06-recursive.typ:78): `ν` of a Lean function `fun X => α° ≫ F(X) ≫ R`, which the language does not state
end Rel.Programs
