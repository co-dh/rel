import Rel.Lang.Test.Common

namespace Rel.Lang.Test

open Tab Rel.Lang Rel.Alg Rel

/-! The kernel path, steps T4, T5, T7: `kernT45` uses `≤ < succ plus Λ E nil at` and the rows
    `∋ τ length setify sum snoc cons cat zip cons° snoc° cat°` with T2 operators, so it runs on the five kernels,
    on inputs with empty cells and duplicate rows. `es`, `th` are `est(≤)`, `thin(≤)` on `x`, the pair test
    elaborated through `⟨π₁, π₂⟩`. -/
rel_program kernT45 where
    obj N = 0…5
    r : N ⟶ N ≜ {(1,2),(2,3),(3,3)}
    w : N ⟶ N×N ≜ {(1,(1,2)),(2,(3,4)),(3,(5,5))}
    un : N ⟶ N ≜ 𝟙(N)
    x : N ⟶ [N] ≜ {(1,3 1 2),(2,[]),(3,1 2),(4,1 2)}
    q : N×N ⟶ N×N ≜ {((1,1),(1,1)),((1,2),(1,2)),((1,3),(1,3)),((2,2),(2,2)),((2,3),(2,3)),((3,3),(3,3))}
    pa : N ⟶ [N]×N ≜ {(1,(3 1,2)),(2,([],4)),(3,(3 1,2))}
    pc : N ⟶ N×[N] ≜ {(1,(2,3 1)),(2,(4,[]))}
    pp : N ⟶ [N]×[N] ≜ {(1,(3 1,2 2)),(2,([],[4])),(3,([],[]))}
    le : N ⟶ N ≜ r ≤
    lq : N ⟶ N ≜ ≤ r
    lt : N ⟶ N ≜ r <
    sc : N ⟶ N ≜ r succ
    pl : N ⟶ N ≜ w plus
    lr : N ⟶ [N] ≜ Λ(r)
    lw : N ⟶ [N×N] ≜ Λ(w)
    er : N ⟶ [N] ≜ x E(r)
    ew : N ⟶ [N×N] ≜ x E(w)
    nl : N ⟶ [N] ≜ r nil
    a1 : N ⟶ N ≜ x at(1)
    ms : N ⟶ N ≜ x ∋
    tu : N ⟶ [N] ≜ r τ
    ln : N ⟶ N ≜ x length
    st : N ⟶ [N] ≜ x setify
    sm : N ⟶ N ≜ x sum
    sn : N ⟶ [N] ≜ pa snoc
    cn : N ⟶ [N] ≜ pc cons
    ct : N ⟶ [N] ≜ pp cat
    zp : N ⟶ [N×N] ≜ pp zip
    zm : N ⟶ N×N ≜ zp ∋
    uc : N ⟶ N×[N] ≜ x cons°
    us : N ⟶ [N]×N ≜ x snoc°
    ut : N ⟶ [N]×[N] ≜ x cat°
    es : N ⟶ N ≜ x est(≤)
    th : N ⟶ [N] ≜ x thin(≤)

#guard kernT45.ok
-- not vacuous: the kernel tables have rows
#guard ["le", "a1", "ms", "sm", "es"].all fun d => ((get kernT45.expanded d .long .long).map (·.n.toNat != 0)) == some true
#guard ((get kernT45.expanded "th" .long (.arr .long)).map (·.n.toNat != 0)) == some true


end Rel.Lang.Test
