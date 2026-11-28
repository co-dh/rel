import Rel.Programs.Prelude
import Rel.Lang.Laws.AopA6_3

/-! # Hylomorphisms of freyd §6.3 (`AOP/A6_3.lean`), in Rel

At the list datatype `α = [nil, snoc]` the algebras are `T = [e, S]` and `h = [e', S']`, `⦇T⦈` is the prelude's `⦇[e, S]⦈`,
`H = ⦇T⦈°⦇h⦈`, and the body `T° F(X) h` is `e°e' ∪ (S°(X×𝟙)S')`. Each row holds for every pair of algebras on the list. -/

namespace Rel.Programs

open Rel.Programs.prelude in
rel_program aopA6_3 where
    theorem hyloFixed(e : 1 ⟶ β, S : β×α ⟶ β, e' : 1 ⟶ γ, S' : γ×α ⟶ γ) : e°e' ∪ (S°((⦇[e, S]⦈° ⦇[e', S']⦈)×𝟙)S') = ⦇[e, S]⦈° ⦇[e', S']⦈ by Rel.Lang.Tm.hylo_fixed_den  -- Freyd.Alg.hylo_fixed, 06-recursive.typ:120, 09-dynamic.typ:88
    theorem hyloLeOfPrefixed(e : 1 ⟶ β, S : β×α ⟶ β, e' : 1 ⟶ γ, S' : γ×α ⟶ γ, X : β ⟶ γ) if e°e' ∪ (S°(X×𝟙)S') ⊑ X : ⦇[e, S]⦈° ⦇[e', S']⦈ ⊑ X by Rel.Lang.Tm.hylo_le_of_prefixed_den  -- Freyd.Alg.hylo_le_of_prefixed, 06-recursive.typ:121
    theorem relCataAlpha : ⦇[nil, snoc]⦈ = 𝟙 by Rel.Lang.Tm.fold_nil_snoc_den  -- Freyd.Alg.relCata_alpha, 02-categories.typ:84

-- not ported: hylo_body_coprod (Freyd.Alg.hylo_body_coprod, 06-recursive.typ:135): element quantifier ∀/∃ in the statement
-- not ported: hylo_eq_mu (Freyd.Alg.hylo_eq_mu, 06-recursive.typ:123): `μ` of a Lean function `fun X => S° ≫ F(X) ≫ R`, which the language does not state; its two halves are `hyloFixed` and `hyloLeOfPrefixed`
-- not ported: hylo_eq_mu_coprod (Freyd.Alg.hylo_eq_mu_coprod, 06-recursive.typ:137): element quantifier ∀/∃ in the statement
end Rel.Programs
