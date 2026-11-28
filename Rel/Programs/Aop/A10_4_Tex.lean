import Rel.Programs.Prelude
import Rel.Lang.Laws.AopA10_4_Tex

/-! # Laws of freyd §10.4 (`AOP/A10_4_Tex.lean`), in Rel

The Set-model objects of the TeX problem (`Real`, `Interval`, `Decimal`) are host types (`Int × Nat` quotient, `Fin`),
so a statement about them is not a statement about relations. The fusion step (B&dM p.260) is stated for any seeds `e`,
`e'`, steps `S`, `S'` and the relation `R` (freyd's `inrange°`): `e` and `e'` are `1 ⟶ _` and `⦇[e,S]⦈ʳ` is the fold
over lists of `δ`. -/

namespace Rel.Programs

open Rel.Programs.prelude in
rel_program aopA10_4_Tex where
    -- Freyd.Alg.RelSet.Tex.tex_fusion, 10-greedy.typ:583
    theorem texFusion(e : 1 ⟶ β, S : δ×β ⟶ β, e' : 1 ⟶ γ, S' : δ×γ ⟶ γ, R : γ ⟶ β) if e ⊑ e' R, ⟨π₁,π₂R⟩ S ⊑ S' R : ⦇[e, S]⦈ʳ ⊑ ⦇[e', S']⦈ʳ R by Rel.Lang.Tm.tex_fusion_den
    -- Freyd.Alg.RelSet.Tex.tex_fusion_condition, 10-greedy.typ:44
    theorem texFusionCondition(e : 1 ⟶ β, S : δ×β ⟶ β, e' : 1 ⟶ γ, S' : δ×γ ⟶ γ, R : γ ⟶ β) if e ⊑ e' R, ⟨π₁,π₂R⟩ S ⊑ S' R : [e, ⟨π₁,π₂R⟩ S] ⊑ [e', S'] R by Rel.Lang.Tm.tex_fusion_condition_den

-- not ported: tex_greedy (Freyd.Alg.RelSet.Tex.tex_greedy, 10-greedy.typ:46): needs the order `length ≤ length°` of lists and `length nil = 0` as laws of the prelude `length` fold, with the objects 1+δ×α; no such lemma exists in rel yet and the budget of this unit ran out
-- not ported: round_recip (10-greedy.typ:530): `round°=interval inrange` is the definition of `round` on the host `Real` (a quotient of `Int × Nat`), not a law of relations
-- not ported: digit_unique (10-greedy.typ:627), f_agree (637), tex_extern (641): statements about `Real`/`Int`/`Fin 65536` host arithmetic (`IsDigit`, `Prog.f`)
-- not ported: run_input, run_pick0, run_pick1, run_pick2, run_pick3, run_cands3, run_out (10-greedy.typ:650-674): `#eval`-style checks of the integer program `Prog` on host `Int` lists, no relation statement
-- not ported: f_nil, f_cons (10-greedy.typ:630,633): host `List`/`Nat`/`Decidable` in the statement
-- not ported: f_eq (10-greedy.typ:620), tex_f (624), tex_laws (45): element ∃ over the inductive `Fn.f` on `Real`; `graph fun` of the host `Fn.f`, and `mu` over `Λ(...)` with `est Q` of the model objects

end Rel.Programs
