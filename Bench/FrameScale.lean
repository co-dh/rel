import Rel.Lang.TestFrameScale

/-! `TestFrameScale`'s programs at sizes over what a program may cost the gate (`gateMs`): its generator at 10⁴ rows
    on the declared `M`, and at 10⁴ and 10⁵ rows at the unbounded `N`. -/

namespace Rel.Lang.TestFrameScale

open Rel.Programs.prelude Rel.Programs.frame Rel.Programs.frameGroup Rel.Programs.frameJoin in
rel_program frameScaleT where
    -- one object for positions, keys and values, holding the largest sum: 49T + 50T(T−1) = 499900, 1275T = 127500
    obj M = 0…499999
    -- `i < b` as `i div b = 0`: `dom(< b̂°)` reads `<` on M×M, |M|² pairs
    below(b : 1 ⟶ M) : M ⟶ M ≜ dom(⟨𝟙, ⊤ b⟩div {(0,0)})
    x : M ⟶ M×M ≜ below({(∗,10000)}) ⟨⟨𝟙, ⊤ {(∗,100)}⟩mod, 𝟙⟩
    y : M ⟶ M×M ≜ below({(∗,100)}) ⟨𝟙, succ⟩
    xf : M ⟶ M×M ≜ filterBy(dom(π₁ below({(∗,50)})), x)
    check count(xf) = {(∗,5000)}
    -- group `j` is key `j` (keys 0…49 first occur at positions 0…49): `(j, 100j + 495000)`
    check aggregate(π₁, F(xf π₂) sum, xf) = below({(∗,50)}) ⟨𝟙, ⟨𝟙, ⊤ {(∗,100)}⟩times ⟨𝟙, ⊤ {(∗,495000)}⟩plus⟩
    j : M ⟶ (M×M)×(M×M) ≜ innerJoin(π₁, π₁, xf, y)
    check count(j) = {(∗,5000)}
    check summarize(F(j π₂ π₂) sum, j) = {(∗,127500)}

#guard frameScaleT.ok
-- n = 10⁴, T = 100: key `k` sums to `100k + 50·100·99`
open Rel.Programs.prelude Rel.Programs.frame Rel.Programs.frameGroup Rel.Programs.frameJoin scaleN in
rel_program frameScaleN4 where
    d4 : 1 ⟶ N ≜ ⟨d3, D⟩ ⟨⟨π₁, ⊤ {(∗,10)}⟩times, π₂⟩plus
    x : N ⟶ N×N ≜ ran(d4) ⟨⟨𝟙, ⊤ {(∗,100)}⟩mod, 𝟙⟩
    xf : N ⟶ N×N ≜ filterBy(dom(π₁ k50), x)
    check count(xf) = {(∗,5000)}
    j : N ⟶ (N×N)×(N×N) ≜ innerJoin(π₁, π₁, xf, y)
    check count(j) = {(∗,5000)}
    check summarize(F(j π₂ π₂) sum, j) = {(∗,127500)}
    check aggregate(π₁, F(xf π₂) sum, xf) = k50 ⟨𝟙, ⟨⟨𝟙, ⊤ {(∗,100)}⟩times, ⊤ {(∗,495000)}⟩plus⟩
    -- the comparison rows as at 10³, the running sum by `cumSum` (`cumAgg`'s m²/2 pairs do not fit; measured)
    t : N ⟶ N×N ≜ take({(∗,5000)}, x)
    check summarize(F(t π₂) sum, t) = {(∗,12497500)}
    dr : N ⟶ N×N ≜ drop({(∗,5000)}, x)
    check summarize(F(dr π₂) sum, dr) = {(∗,37497500)}
    r : N ⟶ N ≜ rolling({(∗,3)}, F(x π₂) sum, x)
    check summarize(F(r) sum, r) = {(∗,149955004)}
    check cumSum(x π₂) = ran(d4) ⟨⟨𝟙, succ⟩times, ⊤ {(∗,2)}⟩div
    c : N ⟶ 1+N ≜ dom(x) tot(dom(x π₁ {(0,0)}) x π₂)
    check fills(c) [{(∗,0)}, 𝟙] = ran(d4) ⟨⟨𝟙, ⊤ {(∗,100)}⟩div, ⊤ {(∗,100)}⟩times
    -- Σ (i − 99) over i ≥ 100: (n−100)(n−99)/2
    q : N ⟶ N×N ≜ x ⟨π₁, π₂ succ⟩
    a : N ⟶ (N×N)×(1+(N×N)) ≜ aj(π₁, π₂, π₁, π₂, x, q)
    check summarize(F(a π₂ [{(∗,0)}, π₂]) sum, a) = {(∗,49009950)}
    check topK({(∗,3)}, π₂, x) = {(0,(99,9999)),(1,(98,9998)),(2,(97,9997))}
    check sortBy(π₁, x) = ran(d4) ⟨⟨𝟙, ⊤ {(∗,100)}⟩div, ⟨⟨⟨𝟙, ⊤ {(∗,100)}⟩mod, ⊤ {(∗,100)}⟩times, ⟨𝟙, ⊤ {(∗,100)}⟩div⟩plus⟩

#guard frameScaleN4.ok
-- n = 10⁵, T = 1000: key `k` sums to `1000k + 50·1000·999`
open Rel.Programs.prelude Rel.Programs.frame Rel.Programs.frameGroup Rel.Programs.frameJoin scaleN in
rel_program frameScaleN5 where
    d4 : 1 ⟶ N ≜ ⟨d3, D⟩ ⟨⟨π₁, ⊤ {(∗,10)}⟩times, π₂⟩plus
    d5 : 1 ⟶ N ≜ ⟨d4, D⟩ ⟨⟨π₁, ⊤ {(∗,10)}⟩times, π₂⟩plus
    x : N ⟶ N×N ≜ ran(d5) ⟨⟨𝟙, ⊤ {(∗,100)}⟩mod, 𝟙⟩
    xf : N ⟶ N×N ≜ filterBy(dom(π₁ k50), x)
    check count(xf) = {(∗,50000)}
    j : N ⟶ (N×N)×(N×N) ≜ innerJoin(π₁, π₁, xf, y)
    check count(j) = {(∗,50000)}
    check summarize(F(j π₂ π₂) sum, j) = {(∗,1275000)}
    check aggregate(π₁, F(xf π₂) sum, xf) = k50 ⟨𝟙, ⟨⟨𝟙, ⊤ {(∗,1000)}⟩times, ⊤ {(∗,49950000)}⟩plus⟩
    -- the comparison rows as at 10³ that finish within 5 s; `aj` takes 2.4 s here (measured; 3.3 s with the generator)
    t : N ⟶ N×N ≜ take({(∗,50000)}, x)
    check summarize(F(t π₂) sum, t) = {(∗,1249975000)}
    dr : N ⟶ N×N ≜ drop({(∗,50000)}, x)
    check summarize(F(dr π₂) sum, dr) = {(∗,3749975000)}
    r : N ⟶ N ≜ rolling({(∗,3)}, F(x π₂) sum, x)
    check summarize(F(r) sum, r) = {(∗,14999550004)}
    check cumSum(x π₂) = ran(d5) ⟨⟨𝟙, succ⟩times, ⊤ {(∗,2)}⟩div
    c : N ⟶ 1+N ≜ dom(x) tot(dom(x π₁ {(0,0)}) x π₂)
    check fills(c) [{(∗,0)}, 𝟙] = ran(d5) ⟨⟨𝟙, ⊤ {(∗,100)}⟩div, ⊤ {(∗,100)}⟩times
    -- Σ (i − 99) over i ≥ 100: (n−100)(n−99)/2
    q : N ⟶ N×N ≜ x ⟨π₁, π₂ succ⟩
    a : N ⟶ (N×N)×(1+(N×N)) ≜ aj(π₁, π₂, π₁, π₂, x, q)
    check summarize(F(a π₂ [{(∗,0)}, π₂]) sum, a) = {(∗,4990054950)}
    check topK({(∗,3)}, π₂, x) = {(0,(99,99999)),(1,(98,99998)),(2,(97,99997))}
    check sortBy(π₁, x) = ran(d5) ⟨⟨𝟙, ⊤ {(∗,1000)}⟩div, ⟨⟨⟨𝟙, ⊤ {(∗,1000)}⟩mod, ⊤ {(∗,100)}⟩times, ⟨𝟙, ⊤ {(∗,1000)}⟩div⟩plus⟩

#guard frameScaleN5.ok

-- `cumAgg` reads `dom(x) ≥ dom(x)`, 10¹⁰ pairs at 10⁵ rows: the message is the cross bound's, which `GenK.comp`
-- once dropped for the one of the order it tried second ("a leaf on demand ran with its domain unknown")
open Rel.Programs.prelude Rel.Programs.frame scaleN frameScaleN5 in
rel_program cumAggPast where
    check cumAgg(F(x π₂) sum, x) = x π₂

/--
info: [Rel.Lang.Msg.user
   "check cumAgg(F(x π₂) sum, x), x π₂: cross: 100000 values of the left object by 100000 of the right is 10000000000 pairs, past the bound 268435456: a relation on two whole objects (`≤`, `<`, `⊤`) read where nothing bounds it to fewer pairs; meet it with a table (`T ∩ ≤` tests T's pairs only) or compose a smaller table on each side (`K ≤ L`); run the other operand first: a leaf on demand ran with its domain unknown; run the other operand first: a leaf on demand ran with its domain unknown; run the other operand first: a leaf on demand ran with its domain unknown",
 Rel.Lang.Msg.user
   "cumAgg(F(x π₂) sum, x): cross: 100000 values of the left object by 100000 of the right is 10000000000 pairs, past the bound 268435456: a relation on two whole objects (`≤`, `<`, `⊤`) read where nothing bounds it to fewer pairs; meet it with a table (`T ∩ ≤` tests T's pairs only) or compose a smaller table on each side (`K ≤ L`); run the other operand first: a leaf on demand ran with its domain unknown; run the other operand first: a leaf on demand ran with its domain unknown; run the other operand first: a leaf on demand ran with its domain unknown"]
-/
#guard_msgs in
#eval cumAggPast.failures.map (·.msg)

end Rel.Lang.TestFrameScale
