module
public import Rel.Run.Lang.Embed
public import Rel.Run.Lang.Expand
public import Rel.Lang.GenSound
public import Rel.Lang.Laws.Absorb
public import Rel.Lang.Laws.Ecomp
public import Rel.Lang.Laws.EstMap
public import Rel.Lang.Laws.FoldUP
public import Rel.Lang.Laws.PermConv
public import Rel.Lang.Laws.StarLinear
@[expose] public section
/-! # The prelude: definitions every program sees (`rel_program … after prelude`), elaborated before it. A program
    that defines one of these names again gets "already defined … in the prelude". -/
namespace Rel.Programs
rel_program prelude where
    obj 1 = {∗}                                   -- the terminal object: its one value

    dom(R : α ⟶ β) : α ⟶ α ≜ ⟨𝟙,R⟩π₁              -- the domain of R as a subset of 𝟙
    ran(R : α ⟶ β) : β ⟶ β ≜ dom(R°)              -- the range of R as a subset of 𝟙
    nil : α ⟶ [β] ≜ Λ(𝟘)                          -- every source to the empty list
    τ : α ⟶ [α] ≜ Λ(𝟙)                            -- each value to its one-element list
    front(Q : β ⟶ β) : [β] ⟶ [β] ≜ Λ(∋ − (∋ (Q − Q°)))   -- the list's elements with no Q-predecessor in it
    flat(R : ι ⟶ α×β) : ι×α ⟶ β ≜ ⟨π₁R,π₂⟩dom(π₁π₁ ∩ π₂)π₁π₂   -- the family R as one relation of key and source
    foldI(e : ι ⟶ β×β, S : (ι×β)×α ⟶ ι×β) : ι×[α] ⟶ β ≜ (π₁π₁° ∩ (π₂⦇[⊤ ran(⟨𝟙,e π₂⟩), S ∩ (π₁π₁π₁°)]⦈))π₂   -- the fold of a family: one fold per (key, list)
    loop(T : χ×υ ⟶ χ) : χ×[υ] ⟶ χ ≜ foldI(⟨𝟙,𝟙⟩, ⟨π₁π₁, ⟨π₁π₂,π₂⟩T⟩)   -- the left fold of T from the pair's own first component

    length : [α] ⟶ β ≜ ⦇[{(∗,0)}, π₁ succ]⦈               -- the count of a list: the fold from 0 adding 1 per element
    sum : [β] ⟶ β ≜ ⦇[{(∗,0)}, plus]⦈                       -- the sum of a list: the fold from 0 adding each element

    -- the order of any object (O2): `Obj.lt`, the sorted pair `Λ(π₁ ∪ π₂)` starting with `x`; the row `cmpRow` runs
    -- instead at an integer-stored atom (`Tm.ltDef_den`), and as itself at a float atom, where IEEE's `<` is not this.
    -- Above `>`, `≥` and every other use of `<`: a use sees `lt` only where it is already defined (`cmpTest`)
    lt : α×α ⟶ α×α ≜ dom(Λ(π₁ ∪ π₂) at(0) ∩ π₁) − dom(π₁ ∩ π₂)   -- the pairs in order: the sorted pair starts with x, x ≠ y
    le : α×α ⟶ α×α ≜ lt ∪ dom(π₁ ∩ π₂)                          -- the pairs in order or equal

    ∈ : α ⟶ [α] ≜ ∋°                            -- membership, the converse of ∋
    ≥ : α ⟶ α ≜ ≤°                                -- the named converse of ≤
    > : α ⟶ α ≜ <°                                -- the named converse of <
    ≠ : α ⟶ α ≜ ∼𝟙                                -- inequality: the complement of equality, 𝟙
    _⇒_(R : α ⟶ β, S : α ⟶ β) : α ⟶ β ≜ ∼R ∪ S                  -- implication
    _⊕_(R : α ⟶ β, S : γ ⟶ δ) : α+γ ⟶ β+δ ≜ [R inl, S inr]      -- the sum of relations, A+B ⟶ C+D
    _+_(R : α ⟶ β, S : α ⟶ β) : α ⟶ β ≜ ⟨R,S⟩plus               -- the sum of two values
    frac(R : α ⟶ γ, S : β ⟶ γ) : α ⟶ β ≜ R/S ∩ (S/R)°           -- the symmetric division
    cor(S : α ⟶ β) : α×β ⟶ α×β ≜ dom(π₁S ∩ π₂)                  -- the pairs of S, as a coreflexive
    mid(R : α ⟶ α) : α ⟶ α×α ≜ ⟨R°,R⟩                            -- y ↦ (x,z) with x R y and y R z: mid(<) is x<y<z
    est(Q : β ⟶ β) : [β] ⟶ β ≜ ∋ − (⟨∋,∋⟩(𝟙 − cor(Q ∪ 𝟙))π₁)       -- the Q-extreme: an element with no partner outside Q ∪ 𝟙
    asc(P : β ⟶ β) : ν ⟶ β ≜ (dom(P) Λ(> dom(P)) length)°         -- q's asc: j ↦ the j-th smallest element of dom(P), counted by the elements below it
    iasc(c : β ⟶ α) : β ⟶ β ≜ asc(ran(⟨c,𝟙⟩))π₂                  -- q's iasc: j ↦ the position of c's j-th smallest, ties by position
    unenum(I : α ⟶ β, D : β ⟶ γ) : α ⟶ γ ≜ I D                   -- q's unenumerate: each id of I through the dictionary D (`dictionary D : S ⟶ [C]`)
    rank(D : α ⟶ β) : α ⟶ γ ≜ D asc(ran(D))°                     -- an id to its text's position in text order: iasc(D)°, the order `<` on sym compares
    -- infix operators fold left to right, so `R X` is parenthesised: `𝟙 ∪ R X` is `(𝟙 ∪ R) X`, whose `μ` is `𝟘`
    star(R : α ⟶ α) : α ⟶ α ≜ μX : 𝟙 ∪ (R X)                     -- R*, the reflexive transitive closure

    -- The list functions of B&dM written as their definitions (diagram order); `ran(nil)` is the fold's seed [].

    -- `at(0)τ ∩ 𝟙` holds the one-element arrays; it stands for τ°, whose converse does not run on demand.

    -- `cat` is the left fold over the reversed first list from the second, by `cons` alone (`snoc` is defined from `cat`):
    -- `r` reverses a list (the left fold of `cons` from `[]`), `s` is `cons` on (acc, x)
    cat : [α]×[α] ⟶ [α] ≜ ⟨π₂, π₁ r⟩ loop(s) where s ≜ ⟨π₂,π₁⟩cons, r ≜ ⟨nil,𝟙⟩ loop(s)   -- B&dM p.129 ⧺: (xs, ys) ↦ xs ++ ys
    snoc : [α]×α ⟶ [α] ≜ (𝟙×τ) cat                                 -- B&dM p.249 snoc: (xs, x) ↦ xs ++ [x]

    head : [α] ⟶ α ≜ at(0)                                       -- B&dM p.267 head = outl cons°
    tail : [α] ⟶ [α] ≜ cat° dom(π₁ (at(0)τ ∩ 𝟙))π₂                -- B&dM p.149 tail = outr cons°
    init : [α] ⟶ [α] ≜ cat° dom(π₂ (at(0)τ ∩ 𝟙))π₁                -- B&dM p.249 init = outl snoc°
    last : [α] ⟶ α ≜ cat° π₂ (at(0)τ ∩ 𝟙)at(0)                    -- B&dM p.267 last = outr snoc°
    -- `⦇[a, S]⦈` is the left fold, `S` on (acc, x), building by snoc; `⦇[a, S]⦈ʳ` the right fold, `S` on (x, acc),
    -- kept where the meaning reads the input from its end (doc/rel-rows.md, column `reads`).

    prefix : [α] ⟶ [α] ≜ cat° π₁                                  -- B&dM p.126 prefix: x ⧺ y ↦ x
    suffix : [α] ⟶ [α] ≜ cat° π₂                                  -- B&dM p.127 suffix, dual to prefix: x ⧺ y ↦ y
    inits : [α] ⟶ [[α]] ≜ Λ(prefix)                                -- the prefixes of a list, shortest first
    setify : [α] ⟶ [α] ≜ Λ(∋)                                       -- the elements of a list as a set: sorted, no repeats
    concat : [[α]] ⟶ [α] ≜ ⦇[nil, cat]⦈                    -- B&dM p.129
    subseq : [α] ⟶ [α] ≜ ⦇[nil, snoc ∪ π₁]⦈                -- B&dM p.123, on snoc lists
    tails : [α] ⟶ [[α]] ≜ ⦇[nil τ, ⟨⟨π₁,π₂head⟩cons,π₂⟩cons]⦈ʳ   -- B&dM p.127 tails = ⦇[wrap nil, extend]⦈
    filter(p : α ⟶ α) : [α] ⟶ [α] ≜ ⦇[nil, dom(π₂p)snoc ∪ ((𝟙 − dom(π₂p))π₁)]⦈      -- B&dM p.66 ⦇[nil, p outl → cons, outr]⦈
    takewhile(p : α ⟶ α) : [α] ⟶ [α] ≜ ⦇[nil, dom(π₁p)cons ∪ ((𝟙 − dom(π₁p))nil)]⦈ʳ  -- B&dM p.174 (7.39) ⦇[nil, p outl → cons, nil]⦈
    -- B&dM thinning `⦇[nil, bump(Q)]⦈ʳ`, `h = (x, head ys)`: `x Q b` gives `x :: tail ys`; `b Q x` gives `ys`; neither, or `ys = []`, gives `x :: ys`
    thinL(Q : α ⟶ α) : [α] ⟶ [α] ≜ ⦇[nil, (dom(h cor(Q)) ⟨π₁, π₂ tail⟩cons) ∪ (dom(h ⟨π₂,π₁⟩ cor(Q)) π₂) ∪ ((𝟙 − dom(h cor(Q)) − dom(h ⟨π₂,π₁⟩ cor(Q))) cons)]⦈ʳ where h ≜ ⟨π₁, π₂ at(0)⟩
    positions(p : α ⟶ α) : [α] ⟶ [ν] ≜ (𝟙 − dom(s (𝟙 − dom(len)))) Λ(s len) where s ≜ cat° dom(π₂ at(0) p) π₁, len ≜ length   -- q's where of the mask dom(p): the positions of the passing elements, ascending
    merge(Q : α ⟶ α) : [α]×[α] ⟶ [α] ≜ ⟨⟨𝟙, nil⟩, cat⟩ loop(π₁ (l ⟨⟨π₁π₁ tail, π₁π₂⟩, ⟨π₂, a⟩snoc⟩ ∪ ((𝟙 − l) ⟨⟨π₁π₁, π₁π₂ tail⟩, ⟨π₂, b⟩snoc⟩))) π₂ where a ≜ π₁π₁ at(0), b ≜ π₁π₂ at(0), l ≜ dom(⟨a,b⟩ cor(Q)) ∪ (dom(a) − dom(b))   -- merge by a clocked loop: take the head `a` of the first when `a Q b` or the second is empty

    -- B&dM p.130 `perm ≜ ⦇[nil, add]⦈`: add puts the new element anywhere in the array so far. Its converse is
    -- itself, stated by the theorem `permConv` below (`Elab.convs`), because `perm° = perm` cannot be derived.

    perm : [α] ⟶ [α] ≜ ⦇[nil, add]⦈ where add ≜ (cat°×𝟙)⟨⟨π₁π₁,π₂⟩snoc,π₁π₂⟩cat
    ordered(Q : α ⟶ α) : [α] ⟶ [α] ≜ 𝟙 − dom(tails ∋ ⟨at(0),tail⟩(π₁∼Q ∩ (π₂∋)))   -- every element is Q-related to each later one
    sort(Q : α ⟶ α) : [α] ⟶ [α] ≜ perm ordered(Q)
    -- Laws of any relation, proved by `rel_aop prelude` (relaop/RelAop/Prelude.lean); a map is `dom(f) = 𝟙` and `simple(f)`.

    simple(f : α ⟶ β) ≜ f°f ⊑ 𝟙                                   -- f relates each input to at most one output
    theorem absorption(S : α ⟶ β, R : β ⟶ γ) if dom(Λ(S)) = 𝟙 : (𝟙÷∋)E(S)E(R) = (𝟙÷∋)E(S R) by Rel.Lang.Tm.absorption_den
    theorem Eunion(R : α ⟶ β) if dom(Λ(R)) = 𝟙 : E(R) = E((𝟙÷∋)E(R))E(∋) by Rel.Lang.Tm.Eunion_den
    theorem Ecomp(R : α ⟶ β, S : β ⟶ γ) if dom(E(R)) = 𝟙 : E(R S) = E(R)E(S) by Rel.Lang.Tm.Ecomp_den
    theorem estMap(f : α ⟶ β, R : β ⟶ β) if f°f ⊑ 𝟙 : (𝟙÷∋)E(f)est(R) = f by Rel.Lang.Tm.estMap_den
    theorem permConv : perm° = perm by Rel.Lang.Tm.permConv_den
    theorem starLinear(R : α ⟶ α, S : α ⟶ β) : μX : S ∪ (R X) = star(R) S by Rel.Lang.Tm.starLinear_den  -- a linear recursion is star(R) on S
    theorem foldUP(e : 1 ⟶ β, S : β×α ⟶ β, X : [α] ⟶ β) if X = nil°e ∪ (snoc°(X×𝟙)S) : X = ⦇[e, S]⦈ by Rel.Lang.Tm.foldUP_den  -- B&dM (5.12): the left fold's universal property
    theorem foldrUP(e : 1 ⟶ β, S : α×β ⟶ β, X : [α] ⟶ β) if X = nil°e ∪ (cons°(𝟙×X)S) : X = ⦇[e, S]⦈ʳ by Rel.Lang.Tm.foldrUP_den  -- B&dM (5.12): the right fold's universal property

end Rel.Programs

namespace Rel.Lang

/-- The declaration of each definition of the program `src` read after the prelude (`Expand.read`: every
    declaration elaborated, nothing evaluated), in order; with no program, the prelude's. -/
def typesOf (src : Option Program) : EM (List String) := do
  let prog := src.getD Programs.prelude
  -- the prelude under its own constant, as `rel_program` reads it: a definition with a fused row (`useDef`) then runs
  -- as that row, as at a use, so `foldI` at a key with no universe is the row, not its text
  let _ ← if src.isSome then Expand.read (fun _ => none) [(``Programs.prelude, Programs.prelude)] prog
    else Expand.read (fun _ => none) [] prog (own := ``Programs.prelude)
  pure (prog.filterMap fun | .defn _ n ps _ ty => some (sigOf n ps ty) | _ => none)

-- the prelude's converse table is its one `c° = c'` theorem; rows answer from `Prim.conv`, a name with neither has none
#guard convs Programs.prelude == [("perm", "perm")]
#guard convOf (convs Programs.prelude) "perm" == some "perm"
#guard convOf (convs Programs.prelude) "cons" == some "uncons"
#guard convOf (convs Programs.prelude) "length" == none

end Rel.Lang
