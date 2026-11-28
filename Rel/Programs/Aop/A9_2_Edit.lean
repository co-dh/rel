import Rel.Programs.Prelude
import Rel.Lang.Laws.AopS2_10
import Rel.Lang.Laws.AopA9_2_Edit

/-! # Laws of freyd §9.2 `AOP/A9_2_Edit.lean` (edit distance), in Rel; rows not ported are listed at the end. -/

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
    -- freyd's `edit_dropTgt` is `=`; the prelude `tail` is partial at `[]` (freyd's maps `[]` to `[]`), so only `⊑` holds
    theorem editDropTgt : edit (𝟙×tail) ⊑ dropTgt edit by Rel.Lang.Tm.editDropTgt_den  -- Freyd.Alg.RelSet.Edit.edit_dropTgt, 09-dynamic.typ:433
    -- `R°` at a generic `Q` (stronger form): `R = length ≤(N,N) length°` compares `Int64.ofNat` lengths, which wrap at 2^63, so the rows are stated with what `R°` supplies as premises
    theorem dropTgtLe(Q : [α+(α+α)] ⟶ [α+(α+α)]) if nil°nil ⊑ Q, ⟨π₁, π₂ Q⟩cons ⊑ cons Q, ⟨π₁ cpy°del, π₂⟩cons ⊑ ⟨π₁ (cpy°cpy), π₂⟩cons Q, ⟨π₁ (ins°ins), π₂⟩π₂ ⊑ ⟨π₁ (ins°ins), π₂⟩cons Q : dropTgt ⊑ Q by Rel.Lang.Tm.dropTgtLe_den  -- Freyd.Alg.RelSet.Edit.dropTgt_le, 09-dynamic.typ:434
    theorem editTailSnd(Q : [α+(α+α)] ⟶ [α+(α+α)]) if dropTgt ⊑ Q : edit (𝟙×tail) ⊑ Q edit by Rel.Lang.Tm.editTailSnd_den  -- Freyd.Alg.RelSet.Edit.edit_tail_snd, 09-dynamic.typ:449
    dropStepS : (α+(α+α))×([α+(α+α)]×[α+(α+α)]) ⟶ [α+(α+α)]×[α+(α+α)] ≜ ⟨⟨π₁ (cpy°cpy),π₂π₁⟩cons,⟨π₁cpy°ins,π₂π₁⟩cons⟩ ∪ ⟨⟨π₁ (del°del),π₂π₁⟩cons,π₂π₁⟩ ∪ ⟨⟨π₁ (ins°ins),π₂π₁⟩cons,⟨π₁ (ins°ins),π₂π₂⟩cons⟩
    dropS : [α+(α+α)] ⟶ [α+(α+α)]×[α+(α+α)] ≜ ⦇[⟨nil,nil⟩, dropStepS]⦈ʳ
    dropSrc : [α+(α+α)] ⟶ [α+(α+α)] ≜ dropS π₂
    Vc : [α]×[α] ⟶ [α]×[α] ≜ suffix×suffix
    -- the rows below iterate `editTailSnd`'s step along `suffix = tail*`, `Q` standing for `R°` (reflexive, transitive)
    theorem editSuffixRight(Q : [α+(α+α)] ⟶ [α+(α+α)]) if dropTgt ⊑ Q, 𝟙 ⊑ Q, Q Q ⊑ Q : edit (𝟙×suffix) ⊑ Q edit by Rel.Lang.Tm.editSuffixRight_den  -- Freyd.Alg.RelSet.Edit.edit_suffix_right, 09-dynamic.typ:517
    theorem editSuffixLeft(Q : [α+(α+α)] ⟶ [α+(α+α)]) if dropSrc ⊑ Q, 𝟙 ⊑ Q, Q Q ⊑ Q : edit (suffix×𝟙) ⊑ Q edit by Rel.Lang.Tm.editSuffixLeft_den  -- Freyd.Alg.RelSet.Edit.edit_suffix_left, 09-dynamic.typ:519
    -- freyd's `V ≜ suffix°×suffix°`: the converse of the row `suffix` at `[α]` has no universe, so only `V° = Vc` is statable
    theorem editVrecip(Q : [α+(α+α)] ⟶ [α+(α+α)]) if dropSrc ⊑ Q, dropTgt ⊑ Q, 𝟙 ⊑ Q, Q Q ⊑ Q : edit Vc ⊑ Q edit by Rel.Lang.Tm.editVrecip_den  -- Freyd.Alg.RelSet.Edit.edit_Vrecip, 09-dynamic.typ:357

-- not ported: F_obj (09-dynamic.typ:335), edit_cata (338), length_cata (349), R_eq (352), V_eq (355): syntactic identities once `edit`, `R`, `V`, `length` are defined as these folds
-- not ported: editFn_dropTgt_of_eq (09-dynamic.typ:403): host pointwise fact about `edit` as a Lean function; its content is `Rel.Lang.editDrop_core`, which `editDropTgt` uses
-- not ported: α_pres_R (09-dynamic.typ:387), edit_mono (505): `cons` is not monotone on `R = length ≤(N,N) length°` (`Int64.ofNat` lengths wrap: `|xs| = 0 ≤ |ys| = 2^63−1`, but `ofNat 1 ≤ ofNat 2^63` fails); at a generic `Q` the row is its own premise
-- not ported: edit_V (09-dynamic.typ:513): the converse of `editVrecip`, `V edit° ⊑ edit° R`; it needs `V = suffix°×suffix°` and `edit°`, whose converse at `[α]×[α]` has no universe (a lazy converse of a row reads it on its source's universe); `editVrecip` is its content
-- not ported: edit_thin_condition (09-dynamic.typ:509), edit_branch (537), edit_body_split (527): all three read `V = suffix°×suffix°` (thin(U×V), thin(F(⊤,V))), whose converse of `suffix` at `[α]` has no universe (see `editVrecip`); edit_branch and edit_body_split also take `P((𝟙×X)cons)` = powerRel at a generic relation `X` (powerRel has a port only at a map, and `X`, the fixed point of the body, is not one), `Λ(editAlg°)` over the sum object `1+(Op×[pair])` and Proposition 9.1 `thin` over the base bifunctor `F(⊤,V)`; `edit_body_split` is not a plain union split of the step body: its content is that thinning/`P`/`est(R)` distribute over the two disjoint ranges of `[base,step]`
-- not ported: mle_head_column (09-dynamic.typ:596): host functions `mle`, `column`, `head` over `ConsList`, no relation statement

end Rel.Programs
