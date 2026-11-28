import Rel.Programs.Prelude
import Rel.Lang.Laws.AopA9_3_Bracket

/-! # Laws of freyd §9.3 (`AOP/A9_3_Bracket.lean`), in Rel

Each theorem is named after the last component of its freyd declaration, with the declaration and the companion
position (chapter file : line) beside it. -/

namespace Rel.Programs

open Rel.Programs.prelude in
rel_program aopA9_3_Bracket where
    -- g ≜ [zero, (𝟙×sz)² opb π₁]: the cost of a node from the cost and the size of each flattening
    g(Z : α ⟶ γ, sz : [α] ⟶ σ, opb : (γ×σ)×(γ×σ) ⟶ γ×σ) : α+((γ×[α])×(γ×[α])) ⟶ γ ≜ [Z, ((𝟙×sz)×(𝟙×sz)) opb π₁]
    -- `sz` is a parameter (freyd's `sz` is a recursion on `list⁺`, which the proof never reads); `inl g = Z` is the β-law of `[Z, _]`
    theorem gFnInl(Z : α ⟶ γ, sz : [α] ⟶ σ, opb : (γ×σ)×(γ×σ) ⟶ γ×σ) : inl g(Z, sz, opb) = Z by Rel.Lang.Tm.gFnInl_den  -- Freyd.Alg.RelSet.Bracket.gFn_inl, 09-dynamic.typ:669

-- not ported (Tree A): rel has no recursive datatype `tree A`, only lists, so `flatten`, `cost`, `size`, `R`, `mct`, `row`, `col`, `array` have no object to range over
-- not ported: flatten_cata (09-dynamic.typ:627), R_eq (639), mct_cost_alg (679), mct_g_mono (716), mct_mono (768), mct_rec (85), col_rec (86), row_rec (87): Tree A (and the relator `(TT.F A).map`)
-- not ported: row.eq_1 (655), col.eq_1 (658), mix.eq_1 (661), next.eq_1 (664): equation lemmas of `row`/`col`/`mix`/`next`, definitions over `Tree A`
-- not ported: array_cons (951), col_cons (846), tops_rec (874), rests_eq (900), newrows_rec (920): `array`/`tops`/`rests`/`newrows` are arrays of `Tree A`
-- not ported: splits_eq (649): `splits` is a structural recursion on `list⁺` and `zip` is not in the prelude; defining `splits` as `⟨inits⁺,tails⁺⟩ zip` would make the law a tautology, and the recursive form needs a fold-with-state proof
-- not ported: array_apply (670), mix_apply (671), mct_branch (781), mct_laws (749), mct_prog (788), size_eq_sz_flatten (636), run_cands (996), run_costs (1000), run_mct (988), run_splits (992): 语法缺 rows, each over `Tree A`, a relator, an element quantifier or the host `List`/`Nat`

end Rel.Programs
