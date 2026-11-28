import Rel.Programs.Prelude
import Rel.Lang.Laws.AopA6_6e_Quicksort

/-! # Laws of freyd §6.6 (`AOP/A6_6e_Quicksort.lean`), in Rel -/

namespace Rel.Programs

open Rel.Programs.prelude in
rel_program aopA6_6e_Quicksort where
    -- p.154 join(x,a,y) = x ⧺ [a] ⧺ y, on the left-nested triple `([α]×α)×[α]`
    join : ([α]×α)×[α] ⟶ [α] ≜ (snoc×𝟙)cat
    -- p.155 check'(R): (x,a,y) with b R a for every b in x and a R b for every b in y (R a parameter, not only ≤)
    check'(R : α ⟶ α) : ([α]×α)×[α] ⟶ ([α]×α)×[α] ≜ dom(π₁⟨π₂,π₁⟩cor(R°/∋)) ∩ dom(⟨π₁π₂,π₂⟩cor(R/∋))
    -- p.378 join_perm
    theorem joinPerm : join perm = ((perm×𝟙)×perm) join perm by Rel.Lang.Tm.joinPerm_den
    -- p.155 check'_perm
    theorem checkPerm(R : α ⟶ α) : check'(R) ((perm×𝟙)×perm) = ((perm×𝟙)×perm) check'(R) by Rel.Lang.Tm.checkPerm_den  -- Freyd.Alg.RelSet.Sort.check'_perm, 06-recursive.typ:390
    -- p.155 base(a) = ([], a, [])
    base : α ⟶ ([α]×α)×[α] ≜ ⟨⟨nil,𝟙⟩,nil⟩
    theorem splitBase(R : α ⟶ α) : base ⊑ τ perm join° check'(R) by Rel.Lang.Tm.splitBase_den  -- Freyd.Alg.RelSet.Sort.split_base, 06-recursive.typ:422

-- not ported: flatten_ordered (06-recursive.typ:354), quicksort (342): element ∀ over `tree A` (`flatten`, `inordered`, `check`, `fork` are folds over the recursive datatype `tree A ::= null | fork(tree A, A, tree A)`, which rel does not have)
-- not ported: check_flatten (366), split_proviso (401): `flatten`/`check`/`fork` are over `tree A`
-- not ported: split_step (434): host `List`/`Nat`/`Decidable` (step by `if R a b`), `embed`/`list⁺` object
-- not ported: split_cata (411): `embed ⦇[base, step]⦈` is a fold on the non-empty list `list⁺ A`, which rel does not have

-- not ported: qsort_rec (445): `X = (⦇[nil, split°]⦈)° flatten` is a fold over `tree A`, which rel does not have

end Rel.Programs
