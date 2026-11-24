import Rel.Lang.Test.Common

namespace Rel.Lang.Test

open Tab Rel.Lang Rel.Alg Rel

/-! The kernel path, steps T4, T5, T7: `kernT45` uses `≤ < succ plus Λ E nil at` and the rows
    `∋ τ length setify sum snoc cons cat zip cons° snoc° cat°` with T2 operators, so it runs on the five kernels,
    on inputs with empty cells and duplicate rows. `es`, `th` are `est(≤)`, `front(≤)` on `x`, the pair test
    elaborated through `⟨π₁, π₂⟩`. -/
open Rel.Programs.prelude in
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
    th : N ⟶ [N] ≜ x front(≤)
    -- the rows worked by hand from each definition's relations, not read from a run
    check r = {(1,2),(2,3),(3,3)}
    check w = {(1,(1,2)),(2,(3,4)),(3,(5,5))}
    check un = {(0,0),(1,1),(2,2),(3,3),(4,4),(5,5)}
    check x = {(1,3 1 2),(2,[]),(3,1 2),(4,1 2)}
    check q = {((1,1),(1,1)),((1,2),(1,2)),((1,3),(1,3)),((2,2),(2,2)),((2,3),(2,3)),((3,3),(3,3))}
    check pa = {(1,(3 1,2)),(2,([],4)),(3,(3 1,2))}
    check pc = {(1,(2,3 1)),(2,(4,[]))}
    check pp = {(1,(3 1,2 2)),(2,([],[4])),(3,([],[]))}
    check le = {(1,2),(1,3),(1,4),(1,5),(2,3),(2,4),(2,5),(3,3),(3,4),(3,5)}
    check lq = {(0,2),(1,2),(0,3),(1,3),(2,3),(3,3)}
    check lt = {(1,3),(1,4),(1,5),(2,4),(2,5),(3,4),(3,5)}
    check sc = {(1,3),(2,4),(3,4)}
    -- `2+3+4 = 7` and `5+5` are not in `N = 0…5`
    check pl = {(1,3)}
    -- `Λ` on all of `N`: an element `r` relates to nothing has the empty set
    check lr = {(0,[]),(1,[2]),(2,[3]),(3,[3]),(4,[]),(5,[])}
    check lw = {(0,[]),(1,[(1,2)]),(2,[(3,4)]),(3,[(5,5)]),(4,[]),(5,[])}
    -- `E(r)`: the cell read as a set, its image under `r`
    check er = {(1,2 3),(2,[]),(3,2 3),(4,2 3)}
    check ew = {(1,(1,2) (3,4) (5,5)),(2,[]),(3,(1,2) (3,4)),(4,(1,2) (3,4))}
    check nl = {(1,[]),(2,[]),(3,[])}
    check a1 = {(1,1),(3,2),(4,2)}
    check ms = {(1,1),(1,2),(1,3),(3,1),(3,2),(4,1),(4,2)}
    check tu = {(1,[2]),(2,[3]),(3,[3])}
    check ln = {(1,3),(2,0),(3,2),(4,2)}
    check st = {(1,1 2 3),(2,[]),(3,1 2),(4,1 2)}
    -- `3+1+2 = 6` is not in `N = 0…5`, as `pl` drops `7`
    check sm = {(2,0),(3,3),(4,3)}
    check sn = {(1,3 1 2),(2,[4]),(3,3 1 2)}
    check cn = {(1,2 3 1),(2,[4])}
    check ct = {(1,3 1 2 2),(2,[4]),(3,[])}
    -- `zip` stops at the shorter array
    check zp = {(1,(3,2) (1,2)),(2,[]),(3,[])}
    check zm = {(1,(3,2)),(1,(1,2))}
    check uc = {(1,(3,1 2)),(3,(1,[2])),(4,(1,[2]))}
    check us = {(1,(3 1,2)),(3,([1],2)),(4,([1],2))}
    check ut = {(1,([],3 1 2)),(1,([3],1 2)),(1,(3 1,[2])),(1,(3 1 2,[])),(2,([],[])),(3,([],1 2)),(3,([1],[2])),(3,(1 2,[])),(4,([],1 2)),(4,([1],[2])),(4,(1 2,[]))}
    -- `est(≤)`: the elements `≤` every other one, the least; `front(≤)` the set of them
    check es = {(1,1),(3,1),(4,1)}
    check th = {(1,[1]),(2,[]),(3,[1]),(4,[1])}

#guard kernT45.ok

/-! `sum = ⦇[0, plus]⦈` and `length = ⦇[0, π₁ succ]⦈` at an object with a universe run as their folds, so every
    step, not only the result, is in the object: `3 3 -3` has the partial sum `3+3 = 6 ∉ M`; `length` starts at
    `0 ∉ P`. `g` the same inside a constant generic over its number variable. -/
open Rel.Programs.prelude in
rel_program sumFold where
    obj M = -3…3
    a : M ⟶ [M] ≜ {(1,3 3 -3),(2,3 -3 3),(3,[])}
    s : M ⟶ M ≜ a sum
    g(R : α ⟶ [β]) : α ⟶ β ≜ R sum
    t : M ⟶ M ≜ g(a)
    -- the rows worked by hand: from the start, `3 3 -3` gives 3, 6 (dropped); `3 -3 3` gives 3, 0, 3; `[]` gives 0
    check s = {(2,3),(3,0)}
    check t = {(2,3),(3,0)}

#guard sumFold.ok

-- the fold's base is the literal `0`, read at the target like any literal: `0 ∉ P`, so the text is refused there
/-- error: line 19, col 24: `ran` at this call, where α is 1, β is P: 0 is not in P = 1…5 -/
#guard_msgs in
open Rel.Programs.prelude in
rel_program lenFoldP where
    obj P = 1…5
    b : P ⟶ [P] ≜ {(1,[]),(2,1 2),(3,[5])}
    l : P ⟶ P ≜ b length
-- not vacuous: the kernel tables have rows
#guard ["le", "a1", "ms", "sm", "es"].all fun d => ((get kernT45.expanded d .long .long).map (·.n.toNat != 0)) == some true
#guard ((get kernT45.expanded "th" .long (.arr .long)).map (·.n.toNat != 0)) == some true

/-! `front` reads its test on the diagonal (`frontDen`: `TQ (b,c) (b,c)`), so a `Q` that is not coreflexive counts
    only at its diagonal. `qn` has `(2,1) ↦ (2,1)` and `(1,2) ↦ (2,1)`: on the diagonal `2` beats `1` strictly
    (`(1,2) ↦ (1,2)` is absent), and `(1,2) ↦ (2,1)` counts for nothing. Worked by hand on `x`: `3 1 2` keeps `2 3`,
    `1 2` keeps `2`, `[]` keeps `[]`. A reading by domain would keep `1 2 3` and `1 2`; `Q(D) − dom(swap)` on pairs
    would keep `1 3` and `[1]`. -/
rel_program frontDiag where
    obj N = 0…5
    x : N ⟶ [N] ≜ {(1,3 1 2),(2,[]),(3,1 2),(4,1 2)}
    qn : N×N ⟶ N×N ≜ {((1,2),(2,1)),((2,1),(2,1))}
    pp : N ⟶ [N]×[N] ≜ {(1,([1],[2])),(2,([2],[1])),(3,([],[1]))}

#guard frontDiag.ok
#guard (do
    let X ← get frontDiag.expanded "x" .long (.arr .long)
    let Q ← get frontDiag.expanded "qn" (.prod .long .long) (.prod .long .long)
    let l := ((Tab.front (fun _ => .ok Q) X.val).toOption.map Tab.toList).getD []
    let e : List ((Obj.arr .long).El × (Obj.arr .long).El) := [([3, 1, 2], [2, 3]), ([], []), ([1, 2], [2])]
    pure (e.all (l.contains ·) && l.all (e.contains ·))) == some true

/-! `thinL` and `merge` read `qn` on the diagonal too (`diag`): `a ≤ b` is `(a,b) qn (a,b)`, so only `2 ≤ 1`.
    `thinL`, right fold of `bump` from `[]`, by hand: `3 1 2`: `2` gives `[2]`; `1` meets `2`, `2 ≤ 1`, keeps `[2]`; `3`
    meets `2`, neither, gives `3 2`. `1 2` gives `[2]`, `[]` gives `[]`. By domain `1 ≤ 2` too (`(1,2) ↦ (2,1)`), so
    `3 1` and `[1]`. `merge` on `pp`: `[1] [2]`, not `1 ≤ 2`, takes `2` first: `2 1`; `[2] [1]`, `2 ≤ 1`: `2 1`;
    `[] [1]`: `[1]`. By domain `[1] [2]` would give `1 2`. -/
#guard (do
    let X ← get frontDiag.expanded "x" .long (.arr .long)
    let Q ← get frontDiag.expanded "qn" (.prod .long .long) (.prod .long .long)
    let l := ((Tab.thinL (fun _ => .ok Q) X.val).toOption.map Tab.toList).getD []
    let e : List ((Obj.arr .long).El × (Obj.arr .long).El) := [([3, 1, 2], [3, 2]), ([], []), ([1, 2], [2])]
    pure (e.all (l.contains ·) && l.all (e.contains ·))) == some true
#guard (do
    let P ← get frontDiag.expanded "pp" .long (.prod (.arr .long) (.arr .long))
    let Q ← get frontDiag.expanded "qn" (.prod .long .long) (.prod .long .long)
    let l := ((Tab.merge (fun _ => .ok Q) P).toOption.map Tab.toList).getD []
    let e : List ((Obj.long).El × (Obj.arr .long).El) := [(1, [2, 1]), (2, [2, 1]), (3, [1])]
    pure (e.all (l.contains ·) && l.all (e.contains ·))) == some true


end Rel.Lang.Test
