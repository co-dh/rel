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

    /- B&dM p.126 `⦇[nil, nil ∪ cons]⦈ʳ = prefix`: `cat° π₁` satisfies the fixed-point equation of the fold, so by the
       fold's universal property it is the fold. -/

    theorem prefixEq : cat° π₁ = nil°nil ∪ (cons°(𝟙×(cat° π₁))(nil ∪ cons)) by Rel.Lang.Tm.prefixEq_den  -- `prefix` satisfies the equation

    theorem prefixFold : prefixC = prefix := calc
      prefixC
        := ≜ prefixC
      ⦇[nil, nil ∪ cons]⦈ʳ
        := foldrUP(nil, nil ∪ cons, cat° π₁)
      cat° π₁
        := ≜ prefix
      prefix

    check x prefixC = x prefix by Rel.Lang.Tm.prefixFold_input
    check e prefixC = e prefix
    check {(∗,3 1)} ⊑ x prefixC

#guard prefixCata.ok

end Rel.Programs

