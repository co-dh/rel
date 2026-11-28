import Rel.Programs.Prelude
import Rel.Lang.Laws.AopA5_7

/-! # Lax squares of freyd §5.7 (`AOP/A5_7.lean`), in Rel

Each theorem is named after the last component of its freyd declaration, with the declaration and the companion
position (chapter file : line) beside it (`Rel/Lang/Laws/AopA5_7.lean`). -/

namespace Rel.Programs

open Rel.Programs.prelude in
rel_program aopA5_7 where
    theorem compSlides(Ta : α ⟶ α', Tb : β ⟶ β', Tc : γ ⟶ γ', X : α' ⟶ β', X' : α ⟶ β, Y : β' ⟶ γ', Y' : β ⟶ γ) if Ta X ⊑ X' Tb, Tb Y ⊑ Y' Tc : Ta (X Y) ⊑ (X' Y') Tc by Rel.Lang.Tm.comp_slides_den  -- Freyd.Alg.comp_slides, 05-datatypes.typ:844
    theorem unionSlides(Ta : α ⟶ α', Tb : β ⟶ β', X : α' ⟶ β', Y : α' ⟶ β', X' : α ⟶ β, Y' : α ⟶ β) if Ta X ⊑ X' Tb, Ta Y ⊑ Y' Tb : Ta (X ∪ Y) ⊑ (X' ∪ Y') Tb by Rel.Lang.Tm.union_slides_den  -- Freyd.Alg.union_slides, 05-datatypes.typ:804
    -- not ported: Freyd.Alg.laxNatural_comp_slide (05-datatypes.typ:778): laxNatural_* quantifies over every relation R and a relator F
    -- not ported: Freyd.Alg.laxNatural_hcomp_outer_first (05-datatypes.typ:784): laxNatural_* quantifies over every relation R and a relator F
    -- not ported: Freyd.Alg.laxNatural_union (05-datatypes.typ:800): laxNatural_* quantifies over every relation R and a relator F
    -- not ported: Freyd.Alg.laxNatural_hcomp_outer_first_slide (05-datatypes.typ:797): laxNatural_* quantifies over every relation R and a relator F
    -- not ported: Freyd.Alg.laxNatural_union_slide (05-datatypes.typ:805): laxNatural_* quantifies over every relation R and a relator F
    -- not ported: Freyd.Alg.laxNatural_prod (05-datatypes.typ:814): laxNatural_* quantifies over every relation R and a relator F
    -- not ported: Freyd.Alg.laxNatural_prod_slide (05-datatypes.typ:821): laxNatural_* quantifies over every relation R and a relator F
    -- not ported: Freyd.Alg.laxNatural_sum (05-datatypes.typ:824): laxNatural_* quantifies over every relation R and a relator F
    -- not ported: Freyd.Alg.laxNatural_sum_slide (05-datatypes.typ:829): laxNatural_* quantifies over every relation R and a relator F
    -- not ported: Freyd.Alg.recip_oplax (05-datatypes.typ:900): oplax naturality quantifies over every relation R and a relator F
    -- not ported: Freyd.Alg.laxNatural_const_iff (05-datatypes.typ:915): laxNatural_* quantifies over every relation R and a relator F

end Rel.Programs
