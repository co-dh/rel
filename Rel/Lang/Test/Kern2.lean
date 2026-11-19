import Rel.Lang.Test.Common

namespace Rel.Lang.Test

open Tab Rel.Lang Rel.Alg Rel

/-! The kernel path (`GenK`, steps T2, T3): every node of `kernT2` has a kernel body, so the program runs on the
    five kernels; `kernT2Old` is the same definitions with `set_option rel.kernel false`, so it runs on the old
    layer. Each operator's kernel body against its old body, as sets of rows, at an
    atom side and a tuple side. -/
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

set_option rel.kernel false in
rel_program kernT2Old where
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
    po : N ⟶ N ≜ p π₁

#guard kernT2.kernel && !kernT2Old.kernel && kernT2.ok && kernT2Old.ok
-- atom sides: `val`, `≫`, `°`, `∩`, `∪`, `−`, `dom`, `ran`, `𝟙`, `𝟘`
#guard ["r", "s", "c", "v", "m", "j", "d", "dr", "rr", "i", "z", "pc"].all
  (sameK kernT2.expanded kernT2Old.expanded · .long .long)
-- tuple sides
#guard ["p", "q", "pm", "pj", "pd"].all (sameK kernT2.expanded kernT2Old.expanded · .long (.prod .long .long))
#guard sameK kernT2.expanded kernT2Old.expanded "pv" (.prod .long .long) .long &&
  sameK kernT2.expanded kernT2Old.expanded "pdom" .long .long &&
  sameK kernT2.expanded kernT2Old.expanded "pran" (.prod .long .long) (.prod .long .long)
-- T3, atom sides: `⊤`, `π₁`, `π₂`, `\`, `/`, `ν`, `μ`; tuple sides: `⟨R,S⟩`, `×`, `\` from a pair
#guard ["t", "o1", "o2", "ld", "rd", "fn", "fm"].all (sameK kernT2.expanded kernT2Old.expanded · .long .long)
#guard sameK kernT2.expanded kernT2Old.expanded "pr" .long (.prod .long .long) &&
  sameK kernT2.expanded kernT2Old.expanded "px" (.prod .long .long) (.prod .long .long) &&
  sameK kernT2.expanded kernT2Old.expanded "pl" (.prod .long .long) .long
-- not vacuous: the kernel tables have rows
#guard ((get kernT2.expanded "c" .long .long).map (·.n.toNat)) == some 5
#guard ["t", "o1", "pr", "px", "ld", "fn", "fm"].all fun x =>
  ((get kernT2.expanded x .long .long).map (·.n.toNat)).any (0 < ·) ||
  ((get kernT2.expanded x .long (.prod .long .long)).map (·.n.toNat)).any (0 < ·) ||
  ((get kernT2.expanded x (.prod .long .long) (.prod .long .long)).map (·.n.toNat)).any (0 < ·)


end Rel.Lang.Test
