import Rel.Lang.PrefixFold

/-! # `prefix` as a catamorphism

B&dM p.126: `prefix = ⦇[nil, nil ∪ cons]⦈`, the fold on cons lists whose step, at each element `x` and the prefix
`acc` of the rest, either stops (`nil`) or keeps `x` (`cons`). B&dM's lists are cons lists, so it is the right fold
`⦇…⦈ʳ` here, whose step reads `(x, acc)`. The prelude's `prefix ≜ cat° π₁` is the same relation
(`Rel/Lang/PrefixCata.lean`). -/

namespace Rel.Programs

open Rel.Programs.prelude in
rel_program prefixCata where
    obj N = 0…9                                   -- the elements

    x : 1 ⟶ [N] ≜ {(∗,3 1 2)}
    e : 1 ⟶ [N] ≜ nil                             -- the empty array

    prefixC : [α] ⟶ [α] ≜ ⦇[nil, nil ∪ cons]⦈ʳ    -- B&dM p.126 prefix = ⦇[nil, nil ∪ cons]⦈

    check x prefixC = x prefix by Rel.Lang.Tm.prefixFold_input
    check e prefixC = e prefix
    check {(∗,3 1)} ⊑ x prefixC

#guard prefixCata.ok

end Rel.Programs
