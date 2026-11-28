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

-- not ported: flatten_ordered (06-recursive.typ:354), quicksort (342): element ∀ over `tree A` (`flatten`, `inordered`, `check`, `fork` are folds over the recursive datatype `tree A ::= null | fork(tree A, A, tree A)`, which rel does not have)
-- not ported: check_flatten (366), split_proviso (401): `flatten`/`check`/`fork` are over `tree A`
-- not ported: split_step (434): host `List`/`Nat`/`Decidable` (step by `if R a b`), `embed`/`list⁺` object
-- not ported: split_cata (411): `embed ⦇[base, step]⦈` is a fold on the non-empty list `list⁺ A`, which rel does not have

-- not ported: join_perm (06-recursive.typ:378), check'_perm (390), split_base (422), qsort_rec (445): statable (the elaborated join perm is a Tm.call tree of prelude perm, not yet matched by a Tm lemma; list core is joinPerm_core in Laws/AopA6_6e_Quicksort), needs a den lemma for the perm call node (as Tm.permConv_den) and was out of budget

end Rel.Programs
