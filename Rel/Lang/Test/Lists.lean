import Rel.Lang.Test.Common

namespace Rel.Lang.Test

open Tab Rel.Lang Rel.Alg Rel

/-! The list builtins of §b on arrays built by `Λ` and `cons`, each value as `Algebra.lean`'s guard of the op
    states it: `x` is `a ↦ [3 1 2]`, `b ↦ [1 5]`; `y` is `a ↦ [7]`, `b ↦ [8 9]`; `z` is `a ↦ [3 3 1 2]`. -/
open Rel.Programs.prelude in
rel_program lists where
    obj N = 0…9
    obj K = {a,b}
    x : K ⟶ [N] ≜ ⟨{(a,3),(b,1)}, Λ({(a,1),(a,2),(b,5)})⟩cons
    y : K ⟶ [N] ≜ Λ({(a,7),(b,8),(b,9)})
    z : K ⟶ [N] ≜ ⟨{(a,3)}, x⟩cons
    print x inits
    print x tails
    print ⟨x,y⟩cat
    print x cat°
    print ⟨x,y⟩zip
    print ⟨x,{(a,4),(b,6)}⟩snoc
    print x snoc°
    print x init
    print x inits concat
    print y perm
    print z setify
    print x ordered(≤)
    print x sort(≤)
    print y subseq
    print x thinL(≤)
    print ⟨Λ({(a,1),(a,5)}),Λ({(a,2),(a,3)})⟩merge(≤)
    print ⟨{(a,0),(b,1)},x⟩loop(plus)

-- `thinL(≤)` runs the one-pass thinning: each element bumped into the thinned rest keeps the lower of the two
#guard lists.ok && lists.prints == [
  "x inits = {(a, [] [3] [3 1] [3 1 2]), (b, [] [1] [1 5])}",
  "x tails = {(a, [3 1 2] [1 2] [2] []), (b, [1 5] [5] [])}",
  "⟨x, y⟩ cat = {(a, 3 1 2 7), (b, 1 5 8 9)}",
  "x cat° = {(a, ([], 3 1 2)), (a, ([3], 1 2)), (a, (3 1, [2])), (a, (3 1 2, [])), " ++
    "(b, ([], 1 5)), (b, ([1], [5])), (b, (1 5, []))}",
  "⟨x, y⟩ zip = {(a, [(3, 7)]), (b, (1, 8) (5, 9))}",
  "⟨x, {(a, 4), (b, 6)}⟩ snoc = {(a, 3 1 2 4), (b, 1 5 6)}",
  "x snoc° = {(a, (3 1, 2)), (b, ([1], 5))}",
  "x init = {(a, 3 1), (b, [1])}",
  "x inits concat = {(a, 3 3 1 3 1 2), (b, 1 1 5)}",
  "y perm = {(a, [7]), (b, 8 9), (b, 9 8)}",
  "z setify = {(a, 1 2 3)}",
  "x ordered(≤) = {(b, 1 5)}",
  "x sort(≤) = {(a, 1 2 3), (b, 1 5)}",
  "y subseq = {(a, []), (a, [7]), (b, []), (b, [8]), (b, 8 9), (b, [9])}",
  "x thinL(≤) = {(a, [1]), (b, [1])}",
  "⟨Λ({(a, 1), (a, 5)}), Λ({(a, 2), (a, 3)})⟩ merge(≤) = {(a, 1 2 3 5), (b, [])}",
  "⟨{(a, 0), (b, 1)}, x⟩ loop(plus) = {(a, 6), (b, 7)}"]

/-! `at(i)`, positions from `0`, on the arrays `x` above: `at(0) = head`, `tail at(i) = at(i+1)`, and a position
    past every array's end the empty relation. -/
#eval trips ["at(0)", "at(12)", "R at(2) S"]
open Rel.Programs.prelude in
rel_program ats where
    obj N = 0…9
    obj K = {a,b}
    x : K ⟶ [N] ≜ ⟨{(a,3),(b,1)}, Λ({(a,1),(a,2),(b,5)})⟩cons
    print x at(0)
    print x at(1)
    print x at(2)
    print x at(3)
    check x at(0) = x head
    check x tail at(0) = x at(1)
    check x tail at(1) = x at(2)
    check x tail at(2) = x at(3)
    check x at(3) = 𝟘
#guard ats.ok && ats.prints == ["x at(0) = {(a, 3), (b, 1)}", "x at(1) = {(a, 1), (b, 5)}", "x at(2) = {(a, 2)}",
  "x at(3) = {}"]
#eval errAt "obj N = 0…9\nf : [N] ⟶ N ≜ at(x)\n" 2 "at( ) takes a position, a number from 0, found 'x'"
#eval errAt "obj N = 0…9\nf : [N] ⟶ N ≜ at(-1)\n" 2 "at( ) takes a position from 0 that fits a long, found -1"

open Rel.Programs.prelude in
/-- A list builtin in a lifted body takes the closed row (§e): at each key of a two-key family the fibre of the
    lifted body is the body on the fibre. -/
rel_program listsLifted where
    obj N = 0…9
    obj K = {a,b}
    obj J = {i,j}
    R₀ : K ⟶ N ≜ {(a,3),(a,1)}
    R₁ : K ⟶ N ≜ {(a,2),(b,5),(b,1)}
    Fm : J ⟶ K×N ≜ {(i,i)}⊤(J,K)⟨𝟙,R₀⟩ ∪ ({(j,j)}⊤(J,K)⟨𝟙,R₁⟩)
    f(S : K ⟶ N) : K ⟶ [[N]] ≜ ⟨S,Λ(S)⟩cons inits ∪ (Λ(S)cat°π₁ tails)
    fF : J ⟶ K×[[N]] ≜ f(Fm)
    check {(i,i)}fF = {(i,i)}⊤(J,K)⟨𝟙,f(R₀)⟩
    check {(j,j)}fF = {(j,j)}⊤(J,K)⟨𝟙,f(R₁)⟩

#guard listsLifted.ok

open Rel.Programs.prelude in
/-- Orders on demand (§a): each operator runs its order on the pairs it compares, here `R ≜ length ≤ length°` on
    `[N]`, which has no universe; a closed order as before; and `∼R`, tested as the complement of `R`'s test. -/
rel_program onDemand where
    obj N = 0…9
    obj K = {a,b}
    L : K ⟶ [[N]] ≜ {(a,[1 2] [3] [8]),(b,[5] [4 6 7] [9])}
    G : K ⟶ [[N]] ≜ Λ(L∋)
    R : [α] ⟶ [β] ≜ length ≤(N,N) length°
    p : [α] ⟶ [α] ≜ dom(length{(1,1)})
    print G est(R)
    print G front(R)
    print L filter(p)
    print L takewhile(p)
    print {(a,[3] [1 2]),(b,[1 2] [3])} ordered(R)
    print L sort(R)
    print L thinL(R)
    print ⟨L sort(R),{(a,[[1 2]]),(b,[[5]])}⟩merge(R)
    print Λ({(a,3),(a,1),(b,5)})est(≤)
    print G est(∼R)

#guard onDemand.ok && onDemand.prints == [
  "G est(R) = {(a, [3]), (a, [8]), (b, [5]), (b, [9])}",
  "G front(R) = {(a, [3] [8]), (b, [5] [9])}",
  "L filter(p) = {(a, [3] [8]), (b, [5] [9])}",
  "L takewhile(p) = {(a, []), (b, [[5]])}",
  "{(a, [3] [1 2]), (b, [1 2] [3])} ordered(R) = {(a, [3] [1 2])}",
  "L sort(R) = {(a, [3] [8] [1 2]), (a, [8] [3] [1 2]), (b, [5] [9] [4 6 7]), (b, [9] [5] [4 6 7])}",
  "L thinL(R) = {(a, [[3]]), (a, [[8]]), (b, [[5]]), (b, [[9]])}",
  "⟨L sort(R), {(a, [[1 2]]), (b, [[5]])}⟩ merge(R) = {(a, [3] [8] [1 2] [1 2]), (a, [8] [3] [1 2] [1 2]), " ++
    "(b, [5] [9] [5] [4 6 7]), (b, [9] [5] [5] [4 6 7])}",
  "Λ({(a, 3), (a, 1), (b, 5)}) est(≤) = {(a, 1), (b, 5)}",
  "G est(∼R) = {(a, 1 2), (b, 4 6 7)}"]
-- refused: an order with a leaf that reads its argument whole, so neither side of its composition is tested
#eval errAt ("obj N = 0…9\nobj K = {a,b}\nL : K ⟶ [[N]] ≜ {(a,[1 2] [3])}\n" ++
  "S : [N] ⟶ [α] ≜ ran(𝟙([N])) length ≤(N,N) length°\nprint L sort(S)\n") 5
  "⊤'s target: [N] has no universe"

/-! `concat` is `List.flatten` (`rep_concatC`): order and duplicates kept. `w` is `a ↦ [[3 1] [2] [1]]`;
    `d` is `a ↦ [[1] [] [1]]`, `b ↦ [[] [1] []]`; `e` is `a ↦ [[3 1]]`, `b ↦ []`, an empty outer array. -/
open Rel.Programs.prelude in
rel_program concats where
    obj N = 0…9
    obj K = {a,b}
    w : K ⟶ [[N]] ≜ ⟨⟨{(a,3)},Λ({(a,1)})⟩cons, ⟨Λ({(a,2)}), Λ(Λ({(a,1)}))⟩cons⟩cons
    d : K ⟶ [[N]] ≜ ⟨Λ({(a,1)}), ⟨Λ({(b,1)}), Λ(Λ({(a,1)}))⟩cons⟩cons
    e : K ⟶ [[N]] ≜ Λ(⟨{(a,3)},Λ({(a,1)})⟩cons)
    print w concat
    print d concat
    print e concat

#guard concats.ok && concats.prints == [
  "w concat = {(a, 3 1 2 1)}",
  "d concat = {(a, 1 1), (b, [1])}",
  "e concat = {(a, 3 1), (b, [])}"]


end Rel.Lang.Test
