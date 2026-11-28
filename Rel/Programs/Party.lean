import Rel.Programs.Prelude
import Rel.Lang.Laws.PartyGuests

/-! # Planning a company party

B&dM §7.3 (diag/aop/07-optimisation.typ, "Planning a company party"): a party is a set of employees with none beside
his boss; `party ≜ fold choose` and `best` picks one of greatest total rating. The efficient version carries the cost
as the relation `c` and recovers the guests with `win` and `guests`. Design: doc/rel-party-design.md. -/

namespace Rel.Programs

open Rel.Programs.prelude in
rel_program partyPlan where
    obj E = {a,b,c,d,e,f,g,h,i,k,l,m}             -- one forest: exStaff a…f, a chain g h i, a tie k l, one employee m
    obj N = 0…40                                  -- ratings and their totals, non-negative

    /- An employee stands for the subtree under him, so every employee is one instance of the check. -/

    boss : E ⟶ E ≜ {(b,a),(c,a),(d,b),(e,b),(f,c),(h,g),(i,h),(l,k)}
    rating : E ⟶ N ≜ {(a,3),(b,7),(c,2),(d,5),(e,1),(f,8),(g,4),(h,5),(i,4),(k,2),(l,2),(m,0)}

    under(B : E ⟶ E) : E ⟶ E ≜ B°*                        -- e and everyone below e
    kids(B : E ⟶ E) : E ⟶ [E] ≜ Λ(B°)
    -- builtin F(r) : [α] ⟶ [β] relates [a₁,…,aₙ] to [b₁,…,bₙ] when every aᵢ r bᵢ (Run/Lang/Elab.lean, `.map`)
    cost(r : α ⟶ β) : [α] ⟶ β ≜ F(r) sum
    R(r : α ⟶ β) : [α] ⟶ [α] ≜ cost(r) ≤ cost(r)°

    /- The book's fold ⦇S⦈ (p. 177), : unfold by ⟨𝟙, kids⟩, fold by S, the tree never built. -/

    choose  : [E]×[E] ⟶ [E]         ≜ π₁ ∪ π₂
    include : E×[[E]×[E]] ⟶ [E]     ≜ (𝟙×(F(π₂)concat))cons
    exclude : E×[[E]×[E]] ⟶ [E]     ≜ π₂F(choose)concat
    S       : E×[[E]×[E]] ⟶ [E]×[E] ≜ ⟨include, exclude⟩
    fold(B : E ⟶ E) : E ⟶ [E]×[E]  ≜ hylo(⟨𝟙, kids(B)⟩, S)
    party(B : E ⟶ E) : E ⟶ [E]      ≜ fold(B) choose
    best(B : E ⟶ E, r : E ⟶ N) : E ⟶ [E] ≜ Λ(party(B))est(R(r)°)

    -- the sets with no employee beside his boss
    test party(boss) setify = Λ(under(boss))subseq (𝟙 − dom(∋ ∩ (∋ boss)))setify
    -- the premises of partySet at the sample: each employee has at most one boss, and a party
    test boss°boss ⊑ 𝟙
    test dom(party(boss)) = 𝟙
    theorem partySet(B : E ⟶ E) if B°B ⊑ 𝟙, dom(party(B)) = 𝟙 : party(B) setify = Λ(under(B))subseq (𝟙 − dom(∋ ∩ (∋ B)))setify by Rel.Lang.Tm.partySet_den

    /- The greedy form (p. 178): exclude keeps only the best party of each child. -/

    exclude₁(r : E ⟶ N) : E×[[E]×[E]] ⟶ [E] ≜ π₂F(Λ(choose)est(R(r)°))concat
    gfold(B : E ⟶ E, r : E ⟶ N) : E ⟶ [E]×[E] ≜ hylo(⟨𝟙, kids(B)⟩, ⟨include, exclude₁(r)⟩)
    test gfold(boss, rating) Λ(choose)est(R(rating)°) ⊑ best(boss, rating)
    theorem gfoldBest(B : E ⟶ E, r : E ⟶ N) if r°r ⊑ 𝟙, B ⊑ 𝟙B, dom(Λ(party(B))) = 𝟙, party(B) ⊑ party(B) dom(cost(r)) : gfold(B, r) Λ(choose)est(R(r)°) ⊑ best(B, r) by Rel.Lang.Tm.gfoldBest_den

    /- The efficient form: c is (cost with e, cost without e), win the employees whose best party holds them, ties
       to include, and guests the party as a relation into E. -/

    tally(r : E ⟶ N) : E×[N×N] ⟶ N×N ≜ ⟨(π₁r) + (π₂F(π₂)sum), π₂F(max)sum⟩
    c(B : E ⟶ E, r : E ⟶ N) : E ⟶ N×N ≜ hylo(⟨𝟙, kids(B)⟩, tally(r))
    win(B : E ⟶ E, r : E ⟶ N) : E ⟶ E ≜ dom((c(B, r) π₁ ≥) ∩ (c(B, r) π₂))
    guests(B : E ⟶ E, r : E ⟶ N) : E ⟶ E ≜ (win(B, r) B° B° ∪ ((𝟙 − win(B, r))B°))* win(B, r)   -- μX : win (𝟙 ∪ boss° boss° X) ∪ ((𝟙 − win)boss° X)
    test Λ(guests(boss, rating)) ⊑ best(boss, rating)
    test c(boss, rating) max = best(boss, rating) cost(rating)
    -- the premises of cMax at the sample: rating simple, boss inside E, parties a list, every party a cost
    test rating°rating ⊑ 𝟙
    test boss ⊑ 𝟙boss
    test dom(Λ(party(boss))) = 𝟙
    test party(boss) ⊑ party(boss) dom(cost(rating))
    theorem cMax(B : E ⟶ E, r : E ⟶ N) if r°r ⊑ 𝟙, B ⊑ 𝟙B, dom(Λ(party(B))) = 𝟙, party(B) ⊑ party(B) dom(cost(r)) : c(B, r) max = best(B, r) cost(r) by Rel.Lang.Tm.cMax_den
    -- law 53 compared as sets (the list orders differ); the premises are cMax's (rating simple, so win reads c's one
    -- value) and partySet's dom(party(boss)) = 𝟙 (each employee has a fold value, so c has one), all tested above
    test Λ(guests(boss, rating)) setify ⊑ best(boss, rating) setify
    theorem guestsBest(B : E ⟶ E, r : E ⟶ N) if r°r ⊑ 𝟙, B ⊑ 𝟙B, dom(party(B)) = 𝟙, dom(Λ(party(B))) = 𝟙, party(B) ⊑ party(B) dom(cost(r)) : Λ(guests(B, r)) setify ⊑ best(B, r) setify by Rel.Lang.Tm.guestsBest_den
    root   : E ⟶ E         ≜ {(a,a)}
    test root best(boss, rating) = {(a,a d e f)}
    test root c(boss, rating) max = {(a,17)}



end Rel.Programs
