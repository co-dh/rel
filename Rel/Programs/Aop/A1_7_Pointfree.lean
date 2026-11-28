import Rel.Programs.Prelude
import Rel.Lang.Laws.AopA1_7_Pointfree

/-! # The point-free filter of B&dM §1.7 (`AOP/A1_7_Pointfree.lean`), in Rel

freyd's `filter_pointfree` is `⟨𝟙, list(p)⟩ zip filter(π₂) list(π₁) = filter(p)` for a relation `p : A ⟶ Bool`, with
`filter(q) = concat list(q → τ, nil)`: keep `x` where `q x true`, drop it where `q x false` (both for a relational `q`).
Rel has no Bool object, and needs none: the test is two coreflexives, `dom(K)` (keep) and `dom(D)` (drop), and
`cfilter(K, D)` is the conditional filter as a right fold. Freyd's statement is the instance `β = Bool`, `K = {true}`,
`D = {false}` of `filterPointfree`, which holds at ANY `p : α ⟶ β` and tests `K`, `D` on `β`, overlapping or not.
`zip` is a row (`Prim.den_zip`, truncating as freyd's `czip`). The prelude's `filter(p)` is `cfilter(p, 𝟙 − dom(p))`
on snoc lists, a test with no overlap. -/

namespace Rel.Programs

open Rel.Programs.prelude in
rel_program aopA1_7_Pointfree where
    -- freyd's `filter q = F((q → τ, nil)) concat` as one fold: keep `x` where `dom(K)`, drop it where `dom(D)`
    cfilter(K : α ⟶ γ, D : α ⟶ γ) : [α] ⟶ [α] ≜ ⦇[nil, dom(π₁K)cons ∪ (dom(π₁D)π₂)]⦈ʳ
    theorem zipNatural(R : α ⟶ β, S : α ⟶ γ) : ⟨F(R), F(S)⟩ zip = F(⟨R, S⟩) by Rel.Lang.Tm.zipNatural_den  -- Freyd.Alg.RelSet.Pointfree.zip_natural, 01-programs.typ:23
    -- Stronger form of filter_pointfree: any `p : α ⟶ β` with tests `K`, `D` on `β` (freyd: `β = Bool`, `K = {true}`, `D = {false}`)
    theorem filterPointfree(p : α ⟶ β, K : β ⟶ γ, D : β ⟶ γ) : ⟨𝟙, F(p)⟩ zip cfilter(π₂K, π₂D) F(π₁) = cfilter(p K, p D) by Rel.Lang.Tm.filterPointfree_den  -- Freyd.Alg.RelSet.Pointfree.filter_pointfree, 01-programs.typ:23
    -- not ported: nil_list (Freyd.Alg.RelSet.Pointfree.nil_list, 01-programs.typ:23): `nil F(R) = nil` does not match the elaborated cast-prim form of `nil` (A5_5_TypeFunctor); filterPointfree does not use it (its proof is one list induction)
    -- not ported: conditional_comp, pair_conditional (Freyd.Alg.RelSet.Pointfree.*, 01-programs.typ:23): statable as `cond(K, D, R, S) ≜ dom(K)R ∪ (dom(D)S)`; not yet proved (needs a den lemma for a 4-parameter call node)
    -- not ported: zip_laxNatural_left, zip_laxNatural_right, conditional_τ_laxNatural, conditional_outl_τ_laxNatural, filter_outr_laxNatural (Freyd.Alg.RelSet.Pointfree.*, 01-programs.typ:23): laxNatural over a relator (A5_7: not portable)
    -- not ported: filter_pointfree_step1 .. filter_pointfree_step10 (Freyd.Alg.RelSet.Pointfree.filter_pointfree_step*, 01-programs.typ:23): each is one rewrite of freyd's definition `F(cond) concat`; `cfilter` is the fold, so steps 1 and 10 would be the theorem `cfilter = F(cond) concat` (concat a prelude call); filterPointfree is proved directly by `cfiltL_zip`

end Rel.Programs
