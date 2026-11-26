import Rel.Lang.Test.Common

namespace Rel.Lang.Test

open Tab Rel.Lang Rel.Alg Rel

open Rel.Programs.prelude in
/-- `X⦇R⦈` given a family (§e): at each key of a three-key family, the fibre of the lifted fold is the fold of
    the fibre. `p(R)` holds the pairs `(a,b)` with `b` at most two steps of `R` from `a`. -/
rel_program foldLaw where
    obj X = {A,B,C}
    obj K = 0…2
    obj L = 5…6
    ℓ : 1 ⟶ [L] ≜ ^(⊤(1,L))
    p(R : X ⟶ X) : X×X ⟶ X×X ≜ ran(ℓ⦇[⟨𝟙,𝟙⟩, π₁ ∪ (π₁ (𝟙×R))]⦈)
    R₀ : X ⟶ X ≜ {(A,B)}
    R₁ : X ⟶ X ≜ {(A,B),(B,C)}
    R₂ : X ⟶ X ≜ {(A,B),(B,C),(C,A)}
    Fm : K ⟶ X×X ≜ {(0,0)}⊤(K,X)⟨𝟙,R₀⟩ ∪ ({(1,1)}⊤(K,X)⟨𝟙,R₁⟩) ∪ ({(2,2)}⊤(K,X)⟨𝟙,R₂⟩)
    pF : K ⟶ (X×X)×(X×X) ≜ p(Fm)
    p₀ : X×X ⟶ X×X ≜ p(R₀)
    p₁ : X×X ⟶ X×X ≜ p(R₁)
    p₂ : X×X ⟶ X×X ≜ p(R₂)

/-- At each key `k` of `pF`, its fibre is the relation `pₖ`. -/
def fibres (gs : List (String × Gen.Gv)) : Bool :=
  [((0 : Int64), "p₀"), (1, "p₁"), (2, "p₂")].all fun (k, n) =>
    match get gs "pF" .long (.prod XX XX), get gs n XX XX with
    | some F, some R =>
      let f := (F.toList.filter (·.1 == k)).map (·.2)
      !R.toList.isEmpty && f.all R.toList.contains && R.toList.all f.contains
    | _, _ => false

#guard foldLaw.ok && fibres foldLaw.expanded

open Rel.Programs.prelude in
/-- A lifted fold whose step has closed parts (§e, cost of the keyed fold): `G`, `∼R ∩ G` (a complement, so
    `⊤`), `dom(R)`, `π₂⟨π₁,π₁⟩`, each keyed on the pairs a round meets; at every key the fibre is the fold of
    the fibre. -/
rel_program foldClosed where
    obj X = {A,B,C}
    obj K = 0…2
    obj L = 5…6
    ℓ : 1 ⟶ [L] ≜ ^(⊤(1,L))
    G : X ⟶ X ≜ {(A,B),(C,C)}
    p(R : X ⟶ X) : X×X ⟶ X×X ≜ ran(ℓ⦇[⟨𝟙,𝟙⟩, π₁ (𝟙×G) ∪ (π₁ (𝟙×(∼R ∩ G))) ∪ (π₁ (𝟙×dom(R))) ∪ (π₁⟨π₁,π₁⟩)]⦈)
    R₀ : X ⟶ X ≜ {(A,B)}
    R₁ : X ⟶ X ≜ {(A,B),(B,C)}
    R₂ : X ⟶ X ≜ {(A,B),(B,C),(C,A)}
    Fm : K ⟶ X×X ≜ {(0,0)}⊤(K,X)⟨𝟙,R₀⟩ ∪ ({(1,1)}⊤(K,X)⟨𝟙,R₁⟩) ∪ ({(2,2)}⊤(K,X)⟨𝟙,R₂⟩)
    pF : K ⟶ (X×X)×(X×X) ≜ p(Fm)
    p₀ : X×X ⟶ X×X ≜ p(R₀)
    p₁ : X×X ⟶ X×X ≜ p(R₁)
    p₂ : X×X ⟶ X×X ≜ p(R₂)

#guard foldClosed.ok && fibres foldClosed.expanded

open Rel.Programs.prelude in
/-- Object variables (§e): `uq : α ⟶ β` at `X ⟶ N` and at `N ⟶ X` against the ground copies `uX`, `uN`; and
    `d : α ⟶ α` given `Fm : K ⟶ X×X`, which `α ⟶ α` reads as a family, against `d` of each fibre. -/
rel_program objVars where
    obj X = {A,B,C}
    obj N = {x,y,z}
    obj K = 0…2
    uq(R : α ⟶ β) : α ⟶ β ≜ R ∩ (R°\𝟙)
    uX(R : X ⟶ N) : X ⟶ N ≜ R ∩ (R°\𝟙)
    uN(R : N ⟶ X) : N ⟶ X ≜ R ∩ (R°\𝟙)
    R₁ : X ⟶ N ≜ {(A,x),(A,y),(B,z)}
    R₂ : N ⟶ X ≜ {(x,A),(y,B),(y,C),(z,C)}
    a₁ : X ⟶ N ≜ uq(R₁)
    b₁ : X ⟶ N ≜ uX(R₁)
    a₂ : N ⟶ X ≜ uq(R₂)
    b₂ : N ⟶ X ≜ uN(R₂)
    d(R : α ⟶ α) : α ⟶ α ≜ R ∩ (R°\𝟙)
    F₀ : X ⟶ X ≜ {(A,B),(A,C)}
    F₁ : X ⟶ X ≜ {(A,B),(B,C)}
    F₂ : X ⟶ X ≜ {(A,A),(B,A),(B,B),(C,A)}
    Fm : K ⟶ X×X ≜ {(0,0)}⊤(K,X)⟨𝟙,F₀⟩ ∪ ({(1,1)}⊤(K,X)⟨𝟙,F₁⟩) ∪ ({(2,2)}⊤(K,X)⟨𝟙,F₂⟩)
    dF : K ⟶ X×X ≜ d(Fm)
    d₀ : X ⟶ X ≜ d(F₀)
    d₁ : X ⟶ X ≜ d(F₁)
    d₂ : X ⟶ X ≜ d(F₂)

#guard let o := objVars.expanded
  let g (n : String) := get o n .long .long
  objVars.ok && (g "a₁").map (·.toList) == (g "b₁").map (·.toList) &&
    (g "a₂").map (·.toList) == (g "b₂").map (·.toList) &&
    (g "a₁").map (·.toList) == some [(1, 2)] &&
    (g "a₂").map (·.n) == some 2 &&
    [((0 : Int64), "d₀"), (1, "d₁"), (2, "d₂")].all fun (k, n) =>
      match get o "dF" .long XX, g n with
      | some F, some R =>
        let f := (F.toList.filter (·.1 == k)).map (·.2)
        f.all R.toList.contains && R.toList.all f.contains && (k == 0 || !f.isEmpty)
      | _, _ => false

open Rel.Programs.prelude in
/-- The order of `est front thinL` given as a converse `Q°` against the converse written by hand: a builtin
    (`≤°`, `≥`), a parametrised definition applied then conversed (`R(rating)°`), and a monomorphic one (`R₀°`). -/
rel_program estConv where
    obj E = {a,b,c}
    obj N = 0…20
    rating : E ⟶ N ≜ {(a,3),(b,7),(c,2)}
    H : E ⟶ [E] ≜ {(a,a b),(a,b c),(a,a c),(b,b c),(b,a b)}
    Hn : N ⟶ N ≜ {(1,3),(1,5),(2,4),(2,9)}
    cost(r : α ⟶ β) : [α] ⟶ β ≜ F(r)sum
    R(r : α ⟶ β) : [α] ⟶ [α] ≜ cost(r) ≤ cost(r)°
    Rc(r : α ⟶ β) : [α] ⟶ [α] ≜ cost(r) ≥ cost(r)°
    c₀ : [E] ⟶ N ≜ F(rating)sum
    R₀ : [E] ⟶ [E] ≜ c₀ ≤ c₀°
    R₀c : [E] ⟶ [E] ≜ c₀ ≥ c₀°
    check ^(Hn)est(≤°) = ^(Hn)est(≥)
    check ^(Hn)front(≤°) = ^(Hn)front(≥)
    check ^(H)est(R(rating)°) = ^(H)est(Rc(rating))
    check ^(H)front(R(rating)°) = ^(H)front(Rc(rating))
    check ^(H)est(R₀°) = ^(H)est(R₀c)
    check ^(H)front(R₀°) = ^(H)front(R₀c)
    check ^(H)thinL(R₀°) = ^(H)thinL(R₀c)
    check ^(H)est(R₀) = ^(H)est(R(rating))
    print ^(Hn)est(≤°)
    print ^(H)est(R(rating)°)
    print ^(H)est(R(rating))

-- `R°` picks the greatest cost (`a b`, 10), `R` the least (`a c`, 5)
#guard estConv.ok && estConv.prints == [
  "^(Hn) est(≤°) = {(1, 5), (2, 9)}", "^(H) est(R(rating)°) = {(a, a b), (b, a b)}",
  "^(H) est(R(rating)) = {(a, a c), (b, b c)}"]


end Rel.Lang.Test
