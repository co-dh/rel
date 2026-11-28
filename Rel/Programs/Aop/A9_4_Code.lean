import Rel.Programs.Prelude
import Rel.Lang.Laws.AopA9_4_Code

/-! # Laws of freyd §9.4 (`AOP/A9_4_Code.lean`), in Rel

`F(U,V) = 𝟙 + (V×U)` on the snoc functor `F(E,X) = 1+(X×E)` is written `[𝟙(1) inl, ⟨π₁V,π₂U⟩ inr]` (the prelude `⊕`
spelled out). The two composition laws of `code_thin_condition`'s calc are stated for any relations `V`, `W`, `U`,
`R`, not only `prefix°`, `decode°`, `⊤+⊤`, `R≜size≤size°` (`Rel/Lang/Laws/AopA9_4_Code.lean`). -/

namespace Rel.Programs

open Rel.Programs.prelude in
rel_program aopA9_4_Code where
    -- Freyd.Alg.RelSet.Code.code_thin_step2, 09-dynamic.typ:1119: F(U,V)F(W) = F(U,VW)
    theorem codeThinStep2(V : α ⟶ β, W : β ⟶ γ, U : δ ⟶ ε) : [𝟙(1) inl, ⟨π₁V,π₂U⟩ inr] [𝟙(1) inl, ⟨π₁W,π₂𝟙⟩ inr] = [𝟙(1) inl, ⟨π₁|(V W),π₂U⟩ inr] by Rel.Lang.Tm.snocBi_comp_den
    -- Freyd.Alg.RelSet.Code.code_thin_step4, 09-dynamic.typ:1131: F(V)F(U,W) = F(U,VW)
    theorem codeThinStep4(V : α ⟶ β, W : β ⟶ γ, U : δ ⟶ ε) : [𝟙(1) inl, ⟨π₁V,π₂𝟙⟩ inr] [𝟙(1) inl, ⟨π₁W,π₂U⟩ inr] = [𝟙(1) inl, ⟨π₁|(V W),π₂U⟩ inr] by Rel.Lang.Tm.snocBi_comp_left_den

-- not ported (identity): Q_eq (09-dynamic.typ:1048), U_eq (1045), R_eq (1039), prefixR_eq (1042), size_cata (1036), code_thin_step1 (1111): `Q = F(⊤+⊤,prefix°)`, `U = ⊤+⊤` (`Code` is the sum `Char+(String×String)`, so `[sym,ptr]` is 𝟙), `R = size≤size°`, `prefix = cat°π₁` (the prelude's own definition), `size = ⦇[0,distr[𝟙×c,𝟙×p] plus]⦈` are definitions here, a syntactic identity
-- not ported: code_thin_step3 (1124): needs `code_V` (`decode_prefix`), an induction on the fold `decode` over `prefix`/`cat` of snoc-strings with the partial `extend`; no lemma on the prelude `cat` fold-with-guard exists in rel
-- not ported: code_thin_step5 (1136): needs `size` as a fold over `Nat` costs with `plus` and `≤` (`bytes_U`, snoc adds a constant); the prelude `plus` wraps on overflow, so monotonicity has no premise-free statement
-- not ported: code_thin_condition (1104): the calc of steps 1-5, blocked by steps 3 and 5
-- not ported: code_disj (1145): `extend nil° = 𝟘` needs `extend` (snoc arm and the guarded `cat` arm with `prefix−𝟙`, `head`) and denotation lemmas for the prelude `cat`/`snoc`/`at` definitions; not attempted within the budget
-- not ported: code_branch (1087): `thin(·)`/`powerRel` of Proposition 9.1 (`thin_arm₂_le`, A9_1) are not rel definitions; a definition with a bare `∋°` is refused
-- not ported: code_prog (1093): `reduce` is a host list function (`prefixesFn`/`splitsFn`/`keepExtends`), and `list(R)`, `minL`, `thin` are not prelude definitions
-- not ported: code_laws (1060): `mu` over `Λ(…)thin(Q)P(…)est(R)` with the relator `F(X)` of an abstract functor; `fun` of the host `con` as a relation
-- not ported: mem_reduce (1051): an `↔` of host `ListRel.inlistP` membership; run_compress (1172), run_cuts (1176): `rfl` on host `SnocList`/`Char` values

end Rel.Programs
