import Rel.Lang.Test.Common

namespace Rel.Lang.Test

open Tab Rel.Lang Rel.Alg Rel

/-! The kernel's value verbs of §b on pairs of numbers, each `Alg.arith` with its opcode: a result outside the
    declared object has no row (`minus` below `0`, as `succ` at the top), nor a zero divisor. -/

open Rel.Programs.prelude in
rel_program arith where
    obj N = 0…20
    w : N×N ⟶ N×N ≜ {((7,2),(7,2)),((2,7),(2,7)),((7,0),(7,0)),((3,5),(3,5))}
    print w plus
    print w times
    print w minus
    print w div
    print w mod
    print w max
    print w min
    D : N×N ⟶ N×N ≜ dom(𝟙(N×N) div)
    check D⟨⟨π₂,div⟩times,mod⟩plus = Dπ₁
    check D⟨mod,π₂⟩ = D⟨mod,π₂⟩(𝟙 ∩ (π₁ < π₂°))

-- `a = b·div + mod` and `mod < b` on every pair of `N` with a divisor other than `0`
#guard arith.ok
#guard arith.prints == [
  "w plus = {((2, 7), 9), ((3, 5), 8), ((7, 0), 7), ((7, 2), 9)}",
  "w times = {((2, 7), 14), ((3, 5), 15), ((7, 0), 0), ((7, 2), 14)}",
  "w minus = {((7, 0), 7), ((7, 2), 5)}",
  "w div = {((2, 7), 0), ((3, 5), 0), ((7, 2), 3)}",
  "w mod = {((2, 7), 2), ((3, 5), 3), ((7, 2), 1)}",
  "w max = {((2, 7), 7), ((3, 5), 5), ((7, 0), 7), ((7, 2), 7)}",
  "w min = {((2, 7), 2), ((3, 5), 3), ((7, 0), 0), ((7, 2), 2)}"]

#eval trips ["plus", "times", "minus", "div", "mod", "max", "min", "⟨R, S⟩ times", "R mod°"]

open Rel.Programs.prelude in
/-- A value verb in a lifted body takes the closed row (§e): at each key the fibre is the body on the fibre. -/
rel_program arithLifted where
    obj N = 0…9
    obj K = {a,b}
    obj J = {i,j}
    R₀ : K ⟶ N ≜ {(a,3),(b,1)}
    R₁ : K ⟶ N ≜ {(a,2),(b,5),(b,1)}
    Fm : J ⟶ K×N ≜ {(i,i)}⊤(J,K)⟨𝟙,R₀⟩ ∪ ({(j,j)}⊤(J,K)⟨𝟙,R₁⟩)
    f(S : K ⟶ N) : K ⟶ N ≜ ⟨S,S⟩times ∪ (⟨S succ,S⟩mod)
    fF : J ⟶ K×N ≜ f(Fm)
    check {(i,i)}fF = {(i,i)}⊤(J,K)⟨𝟙,f(R₀)⟩
    check {(j,j)}fF = {(j,j)}⊤(J,K)⟨𝟙,f(R₁)⟩
    print f(R₀)

#guard arithLifted.ok
#guard arithLifted.prints == ["f(R₀) = {(a, 1), (a, 9), (b, 0), (b, 1)}"]

open Rel.Programs.prelude in
/-- B&dM's digits of a number (`val_converse_eq`): `op°`, the converse of `op(n,d) = 10n+d` on a digit `d`,
    taken from `x` once a round until it reaches `0`, each digit put on the front of the list. The rounds `K`
    hold no number of `N`, so a literal's words name one object (§c). -/
rel_program digits where
    obj N = 0…199
    obj K = 200…203
    ten : N ⟶ N ≜ ⊤(N,N){(10,10)}
    dg : N ⟶ N ≜ dom(<{(10,10)})
    op : N×N ⟶ N ≜ ⟨⟨π₁,π₁ ten⟩times,π₂ dg⟩plus
    x : N ⟶ N ≜ {(107,107)}
    r : N ⟶ [K] ≜ x ((𝟙÷∋)E(⊤(N,K)))
    nz : N ⟶ N ≜ 𝟙(N) − {(0,0)}
    step : N×[N] ⟶ N×[N] ≜ ⟨π₁{(0,0)},π₂⟩ ∪ ⟨π₁ nz op° π₁,⟨π₁ nz op° π₂,π₂⟩cons⟩
    ds : N ⟶ [N] ≜ r⦇[x⟨𝟙,nil⟩, π₁ step]⦈π₂
    print ds

#guard digits.ok && digits.prints == ["ds = {(107, 1 0 7)}"]

open Rel.Programs.prelude in
/-- `⦇R⦈` with `R` not written as `[a,S]`, a name and a composite: read through `inl R`, `inr R`, the fold of
    `[nil, snoc]` is `𝟙` on the arrays `As` over `X` of length at most 2. -/
rel_program foldNamed where
    obj X = {A,B}
    R : 1+([X]×X) ⟶ [X] ≜ [nil, snoc]
    As : [X] ⟶ [X] ≜ ran((𝟙÷∋)E(⊤(1,X))⦇[⊤(1,1)nil, π₁ ∪ (⟨π₁,⊤⟩snoc)]⦈)
    check As⦇R⦈ = As
    check As⦇R 𝟙⦈ = As
    check As⦇[nil, snoc]⦈ = As

#guard foldNamed.ok

-- a prelude definition given a family through a typed parameter: the lifted body reaches `perm`, closed on `[N]`
#eval errAt "obj N = 0…3\nobj St = [N×N]\nf(S : N ⟶ N) : [N] ⟶ [N] ≜ sort(S)\ng : St ⟶ [N]×[N] ≜ f(∋)\n" 3
  "a closed term in a lifted body: [N] has no universe"


end Rel.Lang.Test
