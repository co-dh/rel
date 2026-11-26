import Rel.Lang.Test.Common

namespace Rel.Lang.Test

open Tab Rel.Lang Rel.Alg Rel

/-! Terms on an object with no universe (§a): a converse pushed to the leaves, a division tested on the pairs a
    meet supplies, `R×S` as `⟨π₁R,π₂S⟩`; and what is still refused. Expected values by hand. -/

open Rel.Programs.prelude in
rel_program chs where
    obj Ch = {a,b}
    obj N = 0…3
    x : 1 ⟶ [Ch] ≜ {(∗,a b)}
    y : 1 ⟶ [Ch] ≜ {(∗,a a b)}
    ns : 1 ⟶ [N] ≜ {(∗,2 3)}
    ms : 1 ⟶ [N] ≜ {(∗,3 1 2)}
    ks : 1 ⟶ [N] ≜ {(∗,3 1 1)}
    ok : α×[α] ⟶ α×[α] ≜ cor(≤/∋)


-- the converse: `(RS)° = S°R°`, `∩`, a pair with one side's converse, `R°° = R`, a coreflexive, `cons° = uncons`
open Rel.Programs.prelude chs in
rel_program chsConv where
    print x cons° (perm cons°)°
    print x (perm ∩ perm)° cons°
    print x ⟨cons°π₁, perm⟩°° π₂
    print x (dom(π₁{(a,a)}) cons)°
    print x (dom(π₁{(b,b)}) cons)°
#guard printed chsConv.prints ==
  ["{(∗, a b), (∗, b a)}", "{(∗, (a, [b])), (∗, (b, [a]))}", "{(∗, a b), (∗, b a)}",
   "{(∗, (a, [b]))}", "{}"]
-- `⟨R,S⟩°` with each side read through one projection: `(P×Q)° = P°×Q°`, so the book's `join°` runs as
-- `cat°(snoc°×𝟙)`; `⟨π₁,π₂⟩° = 𝟙`; a product of converses `(cons×perm)° = uncons×perm`. Expected values by hand.
open Rel.Programs.prelude chs in
rel_program chsJoin where
    join : ([α]×α)×[α] ⟶ [α] ≜ (snoc×𝟙)cat
    print y join°
    print y cat°(snoc°×𝟙)
    print x (cons° ⟨π₁,π₂⟩ cons)°
    print ⟨y,x⟩(cons×perm)°
#guard printed chsJoin.prints ==
  ["{(∗, (([], a), a b)), (∗, (([a], a), [b])), (∗, ((a a, b), []))}",
   "{(∗, (([], a), a b)), (∗, (([a], a), [b])), (∗, ((a a, b), []))}",
   "{(∗, a b)}", "{(∗, ((a, a b), a b)), (∗, ((a, a b), b a))}"]
-- refused at a leaf whose converse does not run on demand: `π₁` in `⟨π₁,π₁⟩°` (both sides through `π₁`, the
-- second component unbounded), `∋` in `∈`
#eval errAt "print ⟨{(∗,a)},{(∗,a)}⟩(cons° ⟨π₁,π₁⟩)°\n" 1 "the converse of π₁ does not run on demand" (prog := chs)
#eval errAt "print {(∗,a)} ∈\n" 1 "the converse of ∋ does not run on demand" (prog := chs)
-- a division tested on the pairs: `R/S`, `R\S`, `frac`, `∼`, `−`, each beside a term run on demand
open Rel.Programs.prelude chs in
rel_program chsDiv where
    print ⟨{(∗,1)},ns⟩ok
    print ⟨{(∗,3)},ns⟩ok
    print ⟨{(∗,2)},ns⟩ok
    print ms (∋ ∩ (cons\(π₁ ≤)))
    print ks (subseq ∩ frac(∋,∋))
    print ⟨{(∗,3)},ns⟩(π₂ ∩ (π₁∼(≤/∋)))
    print ⟨{(∗,1)},ns⟩(π₂ ∩ (π₁∼(≤/∋)))
    print ⟨{(∗,3)},ns⟩(π₂ − (π₁ (≤/∋)))
#guard printed chsDiv.prints ==
  ["{(∗, (1, 2 3))}", "{}", "{(∗, (2, 2 3))}", "{(∗, 3)}", "{(∗, 3 1), (∗, 3 1 1)}",
   "{(∗, 2 3)}", "{}", "{(∗, 2 3)}"]
-- refused: a division with no term on demand to test it against, and a meet of two
#eval errAt "print {(∗,1)}(≤/∋)\n" 1 "R/S reads its operands whole" (prog := chs)
#eval errAt "print {(∗,1)}((≤/∋) ∩ (≤/∋))\n" 1 "R/S reads its operands whole" (prog := chs)
-- `R×S` on demand as `⟨π₁R,π₂S⟩`; closed, as before
open Rel.Programs.prelude chs in
rel_program chsProd where
    print ⟨{(1,1)},⟨{(1,2)},^({(1,1)})⟩⟩(𝟙×π₁)plus
    print y cons°(𝟙×perm)
    print ⟨x,{(∗,b)}⟩(perm×𝟙)
    print {(1,1)}×{(2,3)}
#guard printed chsProd.prints ==
  ["{(1, 3)}", "{(∗, (a, a b)), (∗, (a, b a))}", "{(∗, (a b, b)), (∗, (b a, b))}", "{((1, 2), (1, 3))}"]
-- refused: an operand that does not run, named; the object printed as the program writes it, `[Ch]`
#eval errAt "print ⟨{(∗,a)},{(∗,b)}⟩(∈×𝟙)\n" 1 "the converse of ∋ does not run on demand" (prog := chs)
#eval errAt "print ⟨{(∗,a)},{(∗,b)}⟩(∈×𝟙)\n" 1 "[Ch] has no universe" (prog := chs)
-- `loop(F)` runs `F` on the pairs each round meets: a state that is an array (a copy, a reverse, the
-- subsequences), and a pair with an array (the copy with its length)
open Rel.Programs.prelude chs in
rel_program chsLoop where
    print x ⟨nil,𝟙⟩loop(snoc)
    print y ⟨nil,𝟙⟩loop(⟨π₂,π₁⟩cons)
    print x ⟨nil,𝟙⟩loop(snoc ∪ π₁)
    print x ⟨⟨nil,⊤{(0,0)}⟩,𝟙⟩loop(⟨⟨π₁π₁,π₂⟩snoc,π₁π₂ succ⟩)
#guard printed chsLoop.prints ==
  ["{(∗, a b)}", "{(∗, b a a)}", "{(∗, []), (∗, [a]), (∗, a b), (∗, [b])}", "{(∗, (a b, 2))}"]
-- refused: an `F` that runs neither way, the leaf named
#eval errAt "print x ⟨nil,𝟙⟩loop(snoc ran(snoc))\n" 1 "ran( ) reads its argument whole: [Ch]×Ch has no universe" (prog := chs)


end Rel.Lang.Test
