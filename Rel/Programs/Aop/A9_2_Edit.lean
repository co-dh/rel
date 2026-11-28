import Rel.Programs.Prelude
import Rel.Lang.Laws.AopS2_10

/-! # Edit-distance definitions of freyd `AOP/A9_2_Edit.lean`; no theorem is ported (see the `not ported` lines at the end). -/

namespace Rel.Programs

open Rel.Programs.prelude in
rel_program aopA9_2_Edit where
    obj N
    cpy : α ⟶ α+(α+α) ≜ inl
    del : α ⟶ α+(α+α) ≜ inl inr
    ins : α ⟶ α+(α+α) ≜ inr inr
    step : (α+(α+α))×([α]×[α]) ⟶ [α]×[α] ≜ ⟨⟨π₁cpy°,π₂π₁⟩cons,⟨π₁cpy°,π₂π₂⟩cons⟩ ∪ ⟨⟨π₁del°,π₂π₁⟩cons,π₂π₂⟩ ∪ ⟨π₂π₁,⟨π₁ins°,π₂π₂⟩cons⟩
    edit : [α+(α+α)] ⟶ [α]×[α] ≜ ⦇[⟨nil,nil⟩, step]⦈ʳ
    R(U : [α] ⟶ [α]) : [α] ⟶ [α] ≜ length ≤(N,N) (U length)°
    Rfull : [α+(α+α)] ⟶ [α+(α+α)] ≜ length ≤(N,N) length°
    dropStep : (α+(α+α))×([α+(α+α)]×[α+(α+α)]) ⟶ [α+(α+α)]×[α+(α+α)] ≜ ⟨⟨π₁ (cpy°cpy),π₂π₁⟩cons,⟨π₁cpy°del,π₂π₁⟩cons⟩ ∪ ⟨⟨π₁ (del°del),π₂π₁⟩cons,⟨π₁ (del°del),π₂π₂⟩cons⟩ ∪ ⟨⟨π₁ (ins°ins),π₂π₁⟩cons,π₂π₁⟩
    dropT : [α+(α+α)] ⟶ [α+(α+α)]×[α+(α+α)] ≜ ⦇[⟨nil,nil⟩, dropStep]⦈ʳ
    dropTgt : [α+(α+α)] ⟶ [α+(α+α)] ≜ dropT π₂


-- not ported (all): a theorem of this chapter states `edit`, `tail`, `R` or `dropTgt` as relations, and the language cannot state them as the rows need:
-- (1) `R ≜ length ≤ length°` has no universe at `[α]`: `length°` is "the lazy converse of a row ... [α+(α+α)] has no universe", so `R` and `R°` exist only as `R(U)` for a set `U` of lists composed before `length` (`(U length)°`), which restricts R's target to `U` and is not freyd's `R`; every row with `R` (dropTgt_le, edit_tail_snd, edit_suffix_*, edit_V*, edit_mono, edit_thin_condition, α_pres_R) would need this relativisation plus a statement that matches the elaborated term.
-- (2) the prelude `tail` elaborates to a `Tm.call` node whose body holds `cast ⋯` and a literal `Gen.relV` value, so no `*_den` lemma can state it; edit_dropTgt and edit_tail_snd use `tail` (a local `cons° π₂` would avoid it).
-- (3) every theorem's expected type is the whole inlined `Tm` (the `foldr` of `step` is ~40 lines), so its `Rel.Lang.Tm.<name>_den` must restate that term by hand, casts included.
-- not ported: F_obj, R_eq, V_eq, edit_cata, length_cata, editFn_dropTgt_of_eq: syntactic identities once `edit`, `R`, `V`, `length` are defined as these folds

end Rel.Programs
