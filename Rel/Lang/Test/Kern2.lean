import Rel.Lang.Test.Common

namespace Rel.Lang.Test

open Tab Rel.Lang Rel.Alg Rel

/-! The kernel path (`GenK`, steps T2, T3): every node of `kernT2` has a kernel body, so the program runs on the
    five kernels. -/
open Rel.Programs.prelude in
rel_program kernT2 where
    obj N = 0…5
    r : N ⟶ N ≜ {(1,2),(2,3),(3,3)}
    s : N ⟶ N ≜ {(2,1),(3,4),(3,3)}
    c : N ⟶ N ≜ r s
    v : N ⟶ N ≜ r°
    m : N ⟶ N ≜ r ∩ s°
    j : N ⟶ N ≜ r ∪ s
    d : N ⟶ N ≜ r − s°
    dr : N ⟶ N ≜ dom(r)
    rr : N ⟶ N ≜ ran(r)
    i : N ⟶ N ≜ r 𝟙
    z : N ⟶ N ≜ r 𝟘
    p : N ⟶ N×N ≜ {(1,(2,3)),(2,(3,3)),(2,(4,4))}
    q : N ⟶ N×N ≜ {(2,(3,3)),(5,(1,1))}
    pc : N ⟶ N ≜ p p° r
    pv : N×N ⟶ N ≜ p°
    pm : N ⟶ N×N ≜ p ∩ q
    pj : N ⟶ N×N ≜ p ∪ q
    pd : N ⟶ N×N ≜ p − q
    pdom : N ⟶ N ≜ dom(p)
    pran : N×N ⟶ N×N ≜ ran(p)
    -- T3: `⊤ π₁ π₂ ⟨R,S⟩ × \ /`, `ν`, `μ`
    t : N ⟶ N ≜ r ⊤ s°
    o1 : N ⟶ N ≜ p π₁
    o2 : N ⟶ N ≜ p π₂
    pr : N ⟶ N×N ≜ ⟨r, s°⟩
    px : N×N ⟶ N×N ≜ r × s
    ld : N ⟶ N ≜ r\s
    rd : N ⟶ N ≜ s/r
    pl : N×N ⟶ N ≜ p\r
    fn : N ⟶ N ≜ νX : (r ∪ s) ∩ (X X)
    fm : N ⟶ N ≜ μX : r ∪ (X r)
    -- the rows worked by hand from each definition's relations, not read from a run
    test r = {(1,2),(2,3),(3,3)}
    test s = {(2,1),(3,4),(3,3)}
    test c = {(1,1),(2,3),(2,4),(3,3),(3,4)}
    test v = {(2,1),(3,2),(3,3)}
    test m = {(1,2),(3,3)}
    test j = {(1,2),(2,1),(2,3),(3,3),(3,4)}
    test d = {(2,3)}
    test dr = {(1,1),(2,2),(3,3)}
    test rr = {(2,2),(3,3)}
    test i = {(1,2),(2,3),(3,3)}
    test z = 𝟘
    test p = {(1,(2,3)),(2,(3,3)),(2,(4,4))}
    test q = {(2,(3,3)),(5,(1,1))}
    -- `p p°` is `{(1,1),(2,2)}`, then `r`
    test pc = {(1,2),(2,3)}
    test pv = {((2,3),1),((3,3),2),((4,4),2)}
    test pm = {(2,(3,3))}
    test pj = {(1,(2,3)),(2,(3,3)),(2,(4,4)),(5,(1,1))}
    test pd = {(1,(2,3)),(2,(4,4))}
    test pdom = {(1,1),(2,2)}
    test pran = {((2,3),(2,3)),((3,3),(3,3)),((4,4),(4,4))}
    -- `dom(r) × dom(s)`: `{1,2,3} × {2,3}`
    test t = {(1,2),(1,3),(2,2),(2,3),(3,2),(3,3)}
    test o1 = {(1,2),(2,3),(2,4)}
    test o2 = {(1,3),(2,3),(2,4)}
    test pr = {(1,(2,2)),(3,(3,3))}
    test px = {((1,2),(2,1)),((1,3),(2,3)),((1,3),(2,4)),((2,2),(3,1)),((2,3),(3,3)),((2,3),(3,4)),((3,2),(3,1)),((3,3),(3,3)),((3,3),(3,4))}
    -- `x (r\s) y` iff every `a` with `a r x` has `a s y`: `2` and `3` (`r`'s range) reach no `y`, the others all
    test ld = {(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(4,0),(4,1),(4,2),(4,3),(4,4),(4,5),(5,0),(5,1),(5,2),(5,3),(5,4),(5,5)}
    -- `x (s/r) y` iff `x s z` for every `z` with `y r z`: `y` off `dom(r)` is reached from every `x`
    test rd = {(0,0),(1,0),(2,0),(3,0),(4,0),(5,0),(0,4),(1,4),(2,4),(3,4),(4,4),(5,4),(0,5),(1,5),(2,5),(3,5),(4,5),(5,5),(3,2),(3,3)}
    -- `p\r` on `ran(p)`, and on one pair off it (which reaches every `y`); its other 32 such pairs are not written
    test ran(p) pl = {((2,3),2),((3,3),3),((4,4),3)}
    test {((0,0),(0,0))} pl = {((0,0),0),((0,0),1),((0,0),2),((0,0),3),((0,0),4),((0,0),5)}
    -- the greatest `X ⊑ r ∪ s` with `X ⊑ X X`: one step from `r ∪ s` leaves these, which are stable
    test fn = {(2,3),(3,3),(3,4)}
    -- `r`'s transitive closure
    test fm = {(1,2),(1,3),(2,3),(3,3)}


-- not vacuous: the kernel tables have rows
#guard ((get kernT2.expanded "c" .long .long).map (·.n.toNat)) == some 5
#guard ["t", "o1", "pr", "px", "ld", "fn", "fm"].all fun x =>
  ((get kernT2.expanded x .long .long).map (·.n.toNat)).any (0 < ·) ||
  ((get kernT2.expanded x .long (.prod .long .long)).map (·.n.toNat)).any (0 < ·) ||
  ((get kernT2.expanded x (.prod .long .long) (.prod .long .long)).map (·.n.toNat)).any (0 < ·)


end Rel.Lang.Test
