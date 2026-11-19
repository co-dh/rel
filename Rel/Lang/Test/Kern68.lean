import Rel.Lang.Test.Common

namespace Rel.Lang.Test

open Tab Rel.Lang Rel.Alg Rel

/-! The kernel path, steps T6, T8: `kernT68` uses `inl inr [R,S]` and the folds `⦇e,S⦈`, `⦇e,S⦈ʳ` (on atom, tuple
    and array carriers, a nondeterministic step, a step with no row, an empty demand), and a fold given a family
    (`pF`), and the rows `prefix`, `suffix` (`pr`, `su`); `kernT68Old` is the same definitions on the old layer. `x` holds an empty cell and the cell `1 2` twice;
    `sm` a left summand from the empty `z`. -/
open Rel.Programs.prelude in
rel_program kernT68 where
    obj N = 0…5
    obj K = 0…2
    r : N ⟶ N ≜ {(1,2),(2,3),(3,3)}
    s : N ⟶ N ≜ {(2,1),(3,4),(3,3)}
    w : N ⟶ N×N ≜ {(1,(1,2)),(2,(3,4)),(3,(5,5))}
    x : N ⟶ [N] ≜ {(1,3 1 2),(2,[]),(3,1 2),(4,1 2),(5,2 2)}
    z : N ⟶ N ≜ r 𝟘
    zr : 1 ⟶ N ≜ {(∗,0)}
    il : N ⟶ N+N ≜ r inl
    ir : N ⟶ N+N ≜ s inr
    sm : N ⟶ N+N ≜ il ∪ ir ∪ (z inl)
    j1 : N ⟶ N ≜ sm [r°, s]
    j2 : N ⟶ N×N ≜ sm [w, ⟨𝟙,𝟙⟩]
    j3 : N ⟶ N ≜ sm [𝟘, 𝟙]
    f1 : N ⟶ N ≜ x ⦇[zr, plus]⦈
    f2 : N ⟶ N ≜ x ⦇[zr, π₂ ∪ π₁]⦈
    f3 : N ⟶ N ≜ x ⦇[zr, π₁ ∪ π₂]⦈ʳ
    f4 : N ⟶ [N] ≜ x ⦇[nil, snoc ∪ π₁]⦈
    f5 : N ⟶ [N] ≜ x ⦇[nil, ⟨π₂,π₁⟩cons]⦈
    f6 : N ⟶ [N] ≜ x ⦇[nil, cons]⦈ʳ
    f7 : N ⟶ N×N ≜ x ⦇[⟨zr,zr⟩, ⟨⟨π₁π₁,π₂⟩plus, π₁π₂ succ⟩]⦈
    f8 : N ⟶ N ≜ x ⦇[zr, 𝟘]⦈
    f9 : N ⟶ N ≜ z x ⦇[zr, plus]⦈
    p(R : N ⟶ N) : N ⟶ N ≜ ran(x ⦇[zr, π₁ ∪ (π₂ R)]⦈)
    Fm : K ⟶ N×N ≜ {(0,(1,2)),(0,(2,3)),(1,(3,3)),(2,(1,1))}
    pF : K ⟶ N×N ≜ p(Fm)
    pr : N ⟶ [N] ≜ x prefix
    su : N ⟶ [N] ≜ x suffix

open Rel.Programs.prelude in
set_option rel.kernel false in
rel_program kernT68Old where
    obj N = 0…5
    obj K = 0…2
    r : N ⟶ N ≜ {(1,2),(2,3),(3,3)}
    s : N ⟶ N ≜ {(2,1),(3,4),(3,3)}
    w : N ⟶ N×N ≜ {(1,(1,2)),(2,(3,4)),(3,(5,5))}
    x : N ⟶ [N] ≜ {(1,3 1 2),(2,[]),(3,1 2),(4,1 2),(5,2 2)}
    z : N ⟶ N ≜ r 𝟘
    zr : 1 ⟶ N ≜ {(∗,0)}
    il : N ⟶ N+N ≜ r inl
    ir : N ⟶ N+N ≜ s inr
    sm : N ⟶ N+N ≜ il ∪ ir ∪ (z inl)
    j1 : N ⟶ N ≜ sm [r°, s]
    j2 : N ⟶ N×N ≜ sm [w, ⟨𝟙,𝟙⟩]
    j3 : N ⟶ N ≜ sm [𝟘, 𝟙]
    f1 : N ⟶ N ≜ x ⦇[zr, plus]⦈
    f2 : N ⟶ N ≜ x ⦇[zr, π₂ ∪ π₁]⦈
    f3 : N ⟶ N ≜ x ⦇[zr, π₁ ∪ π₂]⦈ʳ
    f4 : N ⟶ [N] ≜ x ⦇[nil, snoc ∪ π₁]⦈
    f5 : N ⟶ [N] ≜ x ⦇[nil, ⟨π₂,π₁⟩cons]⦈
    f6 : N ⟶ [N] ≜ x ⦇[nil, cons]⦈ʳ
    f7 : N ⟶ N×N ≜ x ⦇[⟨zr,zr⟩, ⟨⟨π₁π₁,π₂⟩plus, π₁π₂ succ⟩]⦈
    f8 : N ⟶ N ≜ x ⦇[zr, 𝟘]⦈
    f9 : N ⟶ N ≜ z x ⦇[zr, plus]⦈
    p(R : N ⟶ N) : N ⟶ N ≜ ran(x ⦇[zr, π₁ ∪ (π₂ R)]⦈)
    Fm : K ⟶ N×N ≜ {(0,(1,2)),(0,(2,3)),(1,(3,3)),(2,(1,1))}
    pF : K ⟶ N×N ≜ p(Fm)
    pr : N ⟶ [N] ≜ x prefix
    su : N ⟶ [N] ≜ x suffix

#guard kernT68.kernel && !kernT68Old.kernel && kernT68.ok && kernT68Old.ok
#guard ["z", "j1", "j3", "f1", "f2", "f3", "f8", "f9"].all (sameK kernT68.expanded kernT68Old.expanded · .long .long)
#guard ["il", "ir", "sm"].all (sameK kernT68.expanded kernT68Old.expanded · .long (.sum .long .long))
#guard ["j2", "f7", "pF"].all (sameK kernT68.expanded kernT68Old.expanded · .long (.prod .long .long))
#guard ["x", "f4", "f5", "f6", "pr", "su"].all (sameK kernT68.expanded kernT68Old.expanded · .long (.arr .long))
-- not vacuous: the kernel tables have rows
#guard ["j1", "j3", "f1", "f2", "f3", "f8"].all fun d =>
  ((get kernT68.expanded d .long .long).map (·.n.toNat != 0)) == some true
#guard ["j2", "f7", "pF"].all fun d =>
  ((get kernT68.expanded d .long (.prod .long .long)).map (·.n.toNat != 0)) == some true
#guard ["f4", "f5", "f6", "pr", "su"].all fun d => ((get kernT68.expanded d .long (.arr .long)).map (·.n.toNat != 0)) == some true


end Rel.Lang.Test
