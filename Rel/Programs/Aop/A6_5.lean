import Rel.Programs.Prelude
import Rel.Lang.Laws.AopA6_5

/-! # Laws of freyd §6.5 (`AOP/A6_5.lean`), in Rel

Each theorem is named after the last component of its freyd declaration, with the declaration and the companion
position (chapter file : line) beside it. -/

namespace Rel.Programs

open Rel.Programs.prelude in
rel_program aopA6_5 where
    theorem divDivCompLe(X : β ⟶ α, R : α ⟶ α, S : α ⟶ α) if R R ⊑ S R : ((X / R) / S) R R ⊑ X by Rel.Lang.Tm.div_div_comp_le_den  -- Freyd.Alg.div_div_comp_le, 06-recursive.typ:188

-- not ported: inductive_of_comp_le (Freyd.Alg.inductive_of_comp_le): `Inductive S` is `∀ X, X/S ⊑ X → ⊤ ⊑ X`, a quantifier over relations that a `theorem … if` premise (one relation formula) cannot state
-- not ported: member_const, member_prod, member_sum (Freyd.Alg.member_*): equations of a `LaxMembership` structure on a relator F; a rel_program has no variable for a relator or its membership
-- not ported: thm63_unique, thm63_entire, cor62, cor62_simple, cor63, thm64, thm64_forward, thm64_backward, thm64_claim (Freyd.Alg.*): about an abstract relator F (`F.map`), `InitialAlgebra F`, `Membership F` and `Inductive`; a program names a concrete functor only, and these laws hold for every F by its relator axioms (`F(R°) = F(R)°`, `F(RS) = F(R)F(S)`)

end Rel.Programs
