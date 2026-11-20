import Rel.Lang.Test.Common

namespace Rel.Lang.Test

open Tab Rel.Lang Rel.Alg Rel

/-! The kernel path, steps T6, T8: `kernT68` uses `inl inr [R,S]` and the folds `⦇e,S⦈`, `⦇e,S⦈ʳ` (on atom, tuple
    and array carriers, a nondeterministic step, a step with no row, an empty demand), and a fold given a family
    (`pF`), and the rows `prefix`, `suffix` (`pr`, `su`). `x` holds an empty cell and the cell `1 2` twice;
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
    -- the rows worked by hand from each definition's relations, not read from a run; a sum side is read by its two
    -- summands, `[𝟙,𝟘]` and `[𝟘,𝟙]`, since a literal writes no `inl`/`inr`
    check r = {(1,2),(2,3),(3,3)}
    check s = {(2,1),(3,4),(3,3)}
    check w = {(1,(1,2)),(2,(3,4)),(3,(5,5))}
    check x = {(1,3 1 2),(2,[]),(3,1 2),(4,1 2),(5,2 2)}
    check z = 𝟘
    check zr = {(∗,0)}
    check il [𝟙,𝟘] = {(1,2),(2,3),(3,3)}
    check il [𝟘,𝟙] = 𝟘
    check ir [𝟙,𝟘] = 𝟘
    check ir [𝟘,𝟙] = {(2,1),(3,4),(3,3)}
    check sm [𝟙,𝟘] = {(1,2),(2,3),(3,3)}
    check sm [𝟘,𝟙] = {(2,1),(3,4),(3,3)}
    -- left summands by `r°`, right ones by `s`
    check j1 = {(1,1),(2,2),(2,3),(3,2),(3,3),(3,4)}
    check j2 = {(1,(3,4)),(2,(5,5)),(2,(1,1)),(3,(5,5)),(3,(4,4)),(3,(3,3))}
    check j3 = {(2,1),(3,4),(3,3)}
    -- the sum: `3+1+2 = 6` is not in `N = 0…5`, so `1` has no row
    check f1 = {(2,0),(3,3),(4,3),(5,4)}
    -- each step keeps the accumulator or takes the element: `0` and every element
    check f2 = {(1,0),(1,1),(1,2),(1,3),(2,0),(3,0),(3,1),(3,2),(4,0),(4,1),(4,2),(5,0),(5,2)}
    check f3 = {(1,0),(1,1),(1,2),(1,3),(2,0),(3,0),(3,1),(3,2),(4,0),(4,1),(4,2),(5,0),(5,2)}
    -- every subsequence
    check f4 = {(1,[]),(1,[3]),(1,[1]),(1,[2]),(1,3 1),(1,3 2),(1,1 2),(1,3 1 2),(2,[]),(3,[]),(3,[1]),(3,[2]),(3,1 2),(4,[]),(4,[1]),(4,[2]),(4,1 2),(5,[]),(5,[2]),(5,2 2)}
    -- the reverse
    check f5 = {(1,2 1 3),(2,[]),(3,2 1),(4,2 1),(5,2 2)}
    check f6 = {(1,3 1 2),(2,[]),(3,1 2),(4,1 2),(5,2 2)}
    -- (sum, length); `1`'s sum 6 is not in `N`
    check f7 = {(2,(0,0)),(3,(3,2)),(4,(3,2)),(5,(4,2))}
    check f8 = {(2,0)}
    check f9 = 𝟘
    check Fm = {(0,(1,2)),(0,(2,3)),(1,(3,3)),(2,(1,1))}
    -- `p(R)` is the identity on `{0} ∪ R({1,2,3})`, the elements of `x` being `1 2 3`
    check pF = {(0,(0,0)),(0,(2,2)),(0,(3,3)),(1,(0,0)),(1,(3,3)),(2,(0,0)),(2,(1,1))}
    check pr = {(1,[]),(1,[3]),(1,3 1),(1,3 1 2),(2,[]),(3,[]),(3,[1]),(3,1 2),(4,[]),(4,[1]),(4,1 2),(5,[]),(5,[2]),(5,2 2)}
    check su = {(1,3 1 2),(1,1 2),(1,[2]),(1,[]),(2,[]),(3,1 2),(3,[2]),(3,[]),(4,1 2),(4,[2]),(4,[]),(5,2 2),(5,[2]),(5,[])}

#guard kernT68.ok
-- not vacuous: the kernel tables have rows
#guard ["j1", "j3", "f1", "f2", "f3", "f8"].all fun d =>
  ((get kernT68.expanded d .long .long).map (·.n.toNat != 0)) == some true
#guard ["j2", "f7", "pF"].all fun d =>
  ((get kernT68.expanded d .long (.prod .long .long)).map (·.n.toNat != 0)) == some true
#guard ["f4", "f5", "f6", "pr", "su"].all fun d => ((get kernT68.expanded d .long (.arr .long)).map (·.n.toNat != 0)) == some true


end Rel.Lang.Test
