import Rel.Programs.Prelude
import Rel.Lang.Laws.Map
import Rel.Lang.Laws.Order
import Rel.Lang.Laws.MssFused
import Rel.Lang.Laws.MssEst
import Rel.Lang.Laws.MssGreedy

/-! # The maximum segment sum

B&dM Ex 7.40, the maximum segment sum: the note diag/aop/07-optimisation.typ §mss (line 688), Lean AOP/A7_7_MSS.lean
`mss` (:106) and `mss_eq_scan` (:993). The numbers are signed, so a longer segment can sum to less: `oplus` cuts a
negative running sum back to 0, and an all-negative list has the empty segment's 0. -/

namespace Rel.Programs

open Rel.Programs.prelude in
rel_program mss where
    obj N = -10…20                                -- the elements and the sums

    zero : 1 ⟶ N ≜ {(∗,0)}                        -- the note's `zero`

    /- The specification, Lean `mss ≜ Λ(segment sum) est(≥)`. -/

    segment : [α] ⟶ [α] ≜ suffix prefix           -- the note's `segment = suffix prefix`
    mss : [N] ⟶ N ≜ (𝟙÷∋)E(segment sum)est(≥)

    /- The versions the note's derivation passes through, Lean `mss_eq_scan : mss = ⦇k⦈ π₂ est(≥)`. The note writes ⊕
       as an operator; ⊕ is the sum of relations here, so it is the ordinary definition `oplus`. -/

    oplus : N×N ⟶ N ≜ (𝟙÷∋)E(⊤zero ∪ plus)est(≥)       -- the larger of 0 and a+b; `⊤zero` is the note's `⊸ zero`
    g : [N] ⟶ N ≜ ⦇[zero, oplus]⦈ʳ
    w : N×(N×α) ⟶ N ≜ (𝟙×π₁)oplus                 -- the head oplus the value the tail carries

    shape : [N] ⟶ N ≜ (𝟙÷∋)E(suffix)E((𝟙÷∋)E(prefix sum)est(≥))est(≥)               -- the largest over suffixes of the largest prefix sum
    fused : [N] ⟶ N ≜ (𝟙÷∋)E(suffix)E((𝟙÷∋)E(⦇[zero, ⊤zero ∪ plus]⦈ʳ)est(≥))est(≥)   -- `prefix sum` fused into the fold `⦇S⦈`
    greedy : [N] ⟶ N ≜ (𝟙÷∋)E(suffix)E(g)est(≥)                                -- each suffix keeps the one value `g`
    safe : [N] ⟶ [N] ≜ 𝟙 − dom(segment (𝟙 − dom(sum)))   -- the lists whose every segment has a sum in `N`
    sets : [N] ⟶ [[N]] ≜ (𝟙÷∋)E(suffix)E((𝟙÷∋)E(prefix sum))   -- per suffix, the set of its prefix sums

    /- `k ≜ [zero⟨𝟙,Λ(𝟙)⟩, ⟨w,⟨wΛ(𝟙),π₂π₂⟩ cup⟩]` (note :844) is the fold's seed and step below; the step's set is Lean's
       own `Λ(w ∪ π₂π₂∋)` (`k`, :756), an array: the language has no `cup`. -/

    scan : [N] ⟶ N ≜ ⦇[zero⟨𝟙,(𝟙÷∋)⟩, ⟨w,(𝟙÷∋)E(w ∪ (π₂π₂∋))⟩]⦈ʳπ₂est(≥)

    /- The arrays over D = {-2,-1,3} of length at most 3: one fold round per element of D, each adding a head or not. -/

    D : N ⟶ N ≜ {(-2,-2),(-1,-1),(3,3)}
    A : [N] ⟶ [N] ≜ ran((𝟙÷∋)E(⊤(1,N)D)⦇[⊤(1,1)nil, π₁ ∪ (⟨π₁,⊤D⟩snoc)]⦈)

    check A shape = A mss
    check A fused = A mss
    check A greedy = A mss
    check A scan = A mss

    /- The arrays over {-9,5,10,15}, where sums pass 20: unguarded `mss`/`scan`, `shape`/`fused` and `gl`/`gr` differ
       there (`[5,15,15]`, `[10,15,-9]`, `[15,15]`), guarded by `safe` they agree. -/

    D9 : N ⟶ N ≜ {(-9,-9),(5,5),(10,10),(15,15)}
    A9 : [N] ⟶ [N] ≜ ran((𝟙÷∋)E(⊤(1,N)D9)⦇[⊤(1,1)nil, π₁ ∪ (⟨π₁,⊤D9⟩snoc)]⦈)
    check A9 safe mss = A9 safe scan
    check A9 safe shape = A9 safe fused
    check A9 safe fused = A9 safe greedy
    check A9 safe (𝟙÷∋)E(⦇[zero, ⊤zero ∪ plus]⦈ʳ)est(≥) = A9 safe ⦇[(𝟙÷∋)E(zero)est(≥), (𝟙÷∋)E(⊤zero ∪ plus)est(≥)]⦈ʳ

    /- B&dM Ex 7.40: the spec is the linear `scan`, one theorem per step of the note's derivation. `plus` has no value
       past 20, so the steps past `toShape` hold only on the lists `safe` keeps: `[5,15,15]` has `mss` 20 and `scan` 15,
       `[10,15,-9]` has `shape` 15 and `fused` 16, `[15,15]` breaks `greedyFold`. `estUnion`, `greedyFold` and
       `toFused` are proved here, `by` a Lean lemma about `Tm.den` (`Rel/Lang/Laws/MssEst.lean`, `MssFused.lean`, `MssGreedy.lean`); the
       laws with neither a `by` nor a `calc` (`toScan`, `linear`'s steps) are still owed to Lean:
       `rel_aop mss` (relaop/RelAop/Mss.lean) proves them over the book's model (`Int`, cons lists, the power object), so
       they are theorems about that model, not about the executable `mss.rel.*`; the evidence between those two is the
       `check`s above. -/

    /- The facts that discharge `estMap(zero, ≥)`'s hypotheses: `zero` is a map and `≥` is reflexive. -/

    theorem zeroEntire : dom(zero) = 𝟙 by Rel.Lang.Tm.dom_single
    theorem zeroSimple : zero°zero ⊑ 𝟙 by Rel.Lang.Tm.simple_single
    theorem geqRefl : 𝟙(N) ⊑ ≥ by Rel.Lang.Tm.geq_refl
    theorem estUnion : sets E(∋)est(≥) = sets E(est(≥))est(≥) by Rel.Lang.Tm.estUnion_den
    -- the greedy row (𝟙÷∋)E(⦇S⦈)est(≥) = ⦇(𝟙÷∋)E(S)est(≥)⦈
    theorem greedyFold : safe (𝟙÷∋)E(⦇[zero, ⊤zero ∪ plus]⦈ʳ)est(≥) = safe ⦇[(𝟙÷∋)E(zero)est(≥), (𝟙÷∋)E(⊤zero ∪ plus)est(≥)]⦈ʳ by Rel.Lang.Tm.greedyMss_den

    theorem toShape : mss = shape := calc         -- note `mss-shape`
      mss
        := ≜ segment
      (𝟙÷∋)E(suffix      prefix sum)       est(≥)
        := absorption(suffix, prefix sum)
      (𝟙÷∋)E(suffix) E(  prefix sum)       est(≥)
        := Eunion(prefix sum)
      (𝟙÷∋)E(suffix) E((𝟙÷∋)E(prefix sum)) E(∋) est(≥)
        := estUnion
      (𝟙÷∋)E(suffix) E((𝟙÷∋)E(prefix sum)) E(   est(≥)) est(≥)
        := Ecomp((𝟙÷∋)E(prefix sum), est(≥))
      (𝟙÷∋)E(suffix) E((𝟙÷∋)E(prefix sum)       est(≥)) est(≥)
        := ≜ shape
      shape
    -- B&dM's fusion of a fold into `prefix`; its premises are the no-overflow laws (`+` associates, `0` commutes with it)
    theorem prefixFuse(e : 1 ⟶ β, S : β×β ⟶ β) if ⟨⊤e,𝟙⟩S = ⟨𝟙,⊤e⟩S, ⟨π₁ S, π₂⟩S = ⟨π₁π₁, ⟨π₁π₂,π₂⟩S⟩S : prefix ⦇[e, S]⦈ = ⦇[e, ⊤e ∪ S]⦈ʳ by Rel.Lang.Tm.prefixFuse_var_den
    theorem toFused : safe shape = safe fused by Rel.Lang.Tm.toFused_den               -- note `mss-prefix-sum`
    theorem toGreedy : safe fused = safe greedy := calc     -- note `mss-mono`, `mss-step`, the greedy row
      safe fused
        := ≜ fused
      safe (𝟙÷∋)E(suffix) E((𝟙÷∋)E(⦇[zero, ⊤zero ∪ plus]⦈ʳ)est(≥))est(≥)
        := greedyFold
      safe (𝟙÷∋)E(suffix) E(⦇[(𝟙÷∋)E(zero) est(≥), (𝟙÷∋)E(⊤zero ∪ plus)est(≥)]⦈ʳ)est(≥)
        := estMap(zero, ≥)
      safe (𝟙÷∋)E(suffix) E(⦇[  zero, (𝟙÷∋)E(⊤zero ∪ plus)est(≥)]⦈ʳ)est(≥)
        := ≜ oplus
      safe (𝟙÷∋)E(suffix) E(⦇[  zero, oplus]⦈ʳ)est(≥)
        := ≜ g
      safe (𝟙÷∋)E(suffix) E(g)est(≥)
        := ≜ greedy
      safe greedy
    theorem toScan : greedy = scan                -- note `mss-scan`
    theorem linear : safe mss = safe scan := calc
      safe mss
        := toShape
      safe shape
        := toFused
      safe fused
        := toGreedy
      safe greedy
        := toScan
      safe scan

    /- Inputs: [3,1,4,1,5], [2,0,7], [], [3,-4,2,-1,2], [-2,-1,-3] keyed by a, b, c, d, e. -/

    obj K = {a,b,c,d,e}
    x : K ⟶ [N] ≜ {(a,3 1 4 1 5),(b,2 0 7),(c,[]),(d,3 -4 2 -1 2),(e,-2 -1 -3)}
    check x mss = {(a,14),(b,9),(c,0),(d,3),(e,0)}
    check x scan = {(a,14),(b,9),(c,0),(d,3),(e,0)}

#guard mss.ok

end Rel.Programs

#check Rel.Programs.mss.proof.zeroEntire
#check Rel.Programs.mss.proof.zeroSimple
#check Rel.Programs.mss.proof.geqRefl
