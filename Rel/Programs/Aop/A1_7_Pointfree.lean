import Rel.Programs.Prelude
import Rel.Lang.Laws.AopA1_7_Pointfree

/-! # The point-free filter of B&dM §1.7 (`AOP/A1_7_Pointfree.lean`), in Rel

`filter_pointfree` is `⟨𝟙, list(p)⟩ zip filter(π₂) list(π₁) = filter(p)` for a boolean relation `p : A ⟶ Bool`, with
`filter(q) = concat list(q → τ, nil)`. `zip : [α]×[β] ⟶ [α×β]` is a row (`doc/rel-rows.md`, `Prim.den_zip`: it stops at
the shorter list, as freyd's `czip`), so a program writes it without a prelude definition.
Still missing for the rest:
- the conditional `(q → R, S)` needs a boolean object `q : X ⟶ Bool`; the Prelude has none;
- the Prelude's `filter(p : α ⟶ α)` keeps the elements in `dom(p)`: it is not freyd's conditional filter, so
  `filter(π₂)` at `α×Bool` would keep every pair. -/

namespace Rel.Programs

open Rel.Programs.prelude in
rel_program aopA1_7_Pointfree where
    theorem zipNatural(R : α ⟶ β, S : α ⟶ γ) : ⟨F(R), F(S)⟩ zip = F(⟨R, S⟩) by Rel.Lang.Tm.zipNatural_den  -- Freyd.Alg.RelSet.Pointfree.zip_natural, 01-programs.typ:23
    -- not ported: nil_list (Freyd.Alg.RelSet.Pointfree.nil_list, 01-programs.typ:23): needs the constant `nil` at a boolean-tested conditional; the instance `nil F(R) = nil` does not match the elaborated cast-prim form (A5_5_TypeFunctor)
    -- not ported: conditional_comp (Freyd.Alg.RelSet.Pointfree.conditional_comp, 01-programs.typ:23): no boolean object for `q`
    -- not ported: pair_conditional (Freyd.Alg.RelSet.Pointfree.pair_conditional, 01-programs.typ:23): no boolean object
    -- not ported: zip_laxNatural_left, zip_laxNatural_right, conditional_τ_laxNatural, conditional_outl_τ_laxNatural, filter_outr_laxNatural (Freyd.Alg.RelSet.Pointfree.*, 01-programs.typ:23): laxNatural over a relator (A5_7: not portable)
    -- not ported: filter_pointfree_step1 .. filter_pointfree_step10 (Freyd.Alg.RelSet.Pointfree.filter_pointfree_step*, 01-programs.typ:23): each is one rewrite of the calculation, and each side mentions the conditional filter
    -- not ported: filter_pointfree (Freyd.Alg.RelSet.Pointfree.filter_pointfree, 01-programs.typ:23): the 可写 row; `zip` is available (row), but the conditional filter needs a boolean object and a relation `p` whose both answers can hold, which the prelude `filter(p : α ⟶ α)` (keeps `dom(p)`) cannot state; a coreflexive reading holds only for a function `p` and needs a list-level proof over the `filter` row (budget an opus agent)

end Rel.Programs
