import Rel.Run.Lang.Embed
/-! # The prelude: definitions every program sees (`rel_program … after prelude`), elaborated before it. A program
    that defines one of these names again gets "already defined … in the prelude". -/
namespace Rel.Programs
rel_program prelude where
    obj 1 = {∗}                                   -- the terminal object: its one value

    ∈ : α ⟶ [α] ≜ ∋°                              -- membership, the converse of ∋
    ≥ : α ⟶ α ≜ ≤°                                -- the named converse of ≤
    > : α ⟶ α ≜ <°                                -- the named converse of <
    ≠ : α ⟶ α ≜ ∼𝟙                                -- inequality: the complement of equality, 𝟙
    _⇒_(R : α ⟶ β, S : α ⟶ β) : α ⟶ β ≜ ∼R ∪ S                  -- implication
    _⊕_(R : α ⟶ β, S : γ ⟶ δ) : α+γ ⟶ β+δ ≜ [R inl, S inr]      -- the sum of relations, A+B ⟶ C+D
    _+_(R : α ⟶ β, S : α ⟶ β) : α ⟶ β ≜ ⟨R,S⟩plus               -- the sum of two values
    frac(R : α ⟶ γ, S : β ⟶ γ) : α ⟶ β ≜ R/S ∩ (S/R)°           -- the symmetric division
    cor(S : α ⟶ β) : α×β ⟶ α×β ≜ dom(π₁S ∩ π₂)                  -- the pairs of S, as a coreflexive
    mid(R : α ⟶ α) : α ⟶ α×α ≜ ⟨R°,R⟩                            -- y ↦ (x,z) with x R y and y R z: mid(<) is x<y<z
    iasc(c : β ⟶ α) : β ⟶ β ≜ asc(ran(⟨c,dom(c)⟩))π₂             -- q's iasc: j ↦ the position of c's j-th smallest, ties by position

    -- The list functions of B&dM written as their definitions (diagram order); `ran(nil)` is the fold's seed [].

    -- `at(0)τ ∩ 𝟙` holds the one-element arrays; it stands for τ°, whose converse does not run on demand.

    head : [α] ⟶ α ≜ at(0)                                        -- B&dM p.267 head = outl cons°
    tail : [α] ⟶ [α] ≜ cat° dom(π₁ (at(0)τ ∩ 𝟙))π₂                -- B&dM p.149 tail = outr cons°
    init : [α] ⟶ [α] ≜ cat° dom(π₂ (at(0)τ ∩ 𝟙))π₁                -- B&dM p.249 init = outl snoc°
    last : [α] ⟶ α ≜ cat° π₂ (at(0)τ ∩ 𝟙)at(0)                    -- B&dM p.267 last = outr snoc°
    -- `⦇[a, S]⦈` is the left fold, `S` on (acc, x), building by snoc; `⦇[a, S]⦈ʳ` the right fold, `S` on (x, acc),
    -- kept where the meaning reads the input from its end (doc/rel-rows.md, column `reads`).

    prefix : [α] ⟶ [α] ≜ cat° π₁                                  -- B&dM p.126 prefix: x ⧺ y ↦ x
    suffix : [α] ⟶ [α] ≜ cat° π₂                                  -- B&dM p.127 suffix, dual to prefix: x ⧺ y ↦ y
    concat : [[α]] ⟶ [α] ≜ ⦇[nil, cat]⦈                    -- B&dM p.129
    subseq : [α] ⟶ [α] ≜ ⦇[nil, snoc ∪ π₁]⦈                -- B&dM p.123, on snoc lists
    tails : [α] ⟶ [[α]] ≜ ⦇[nil τ, ⟨⟨π₁,π₂head⟩cons,π₂⟩cons]⦈ʳ   -- B&dM p.127 tails = ⦇[wrap nil, extend]⦈
    filter(p : α ⟶ α) : [α] ⟶ [α] ≜ ⦇[nil, dom(π₂p)snoc ∪ ((𝟙 − dom(π₂p))π₁)]⦈      -- B&dM p.66 ⦇[nil, p outl → cons, outr]⦈
    takewhile(p : α ⟶ α) : [α] ⟶ [α] ≜ ⦇[nil, dom(π₁p)cons ∪ ((𝟙 − dom(π₁p))nil)]⦈ʳ  -- B&dM p.174 (7.39) ⦇[nil, p outl → cons, nil]⦈

    -- B&dM p.130 `perm ≜ ⦇[nil, add]⦈`: add puts the new element anywhere in the array so far. Its converse is
    -- itself, a rule the language keeps for this one name (`Tm.own`), because `perm° = perm` cannot be derived.

    perm : [α] ⟶ [α] ≜ ⦇[nil, add]⦈ where add ≜ (cat°×𝟙)⟨⟨π₁π₁,π₂⟩snoc,π₁π₂⟩cat
    ordered(Q : α ⟶ α) : [α] ⟶ [α] ≜ 𝟙 − dom(tails ∋ ⟨at(0),tail⟩(π₁∼Q ∩ (π₂∋)))   -- every element is Q-related to each later one
    sort(Q : α ⟶ α) : [α] ⟶ [α] ≜ perm ordered(Q)

    -- Laws of any relation, proved by `rel_aop prelude` (relaop/RelAop/Prelude.lean); a map is `dom(f) = 𝟙` and `simple(f)`.

    simple(f : α ⟶ β) ≜ f°f ⊑ 𝟙                                   -- f relates each input to at most one output
    theorem absorption(S : α ⟶ β, R : β ⟶ γ) : Λ(S)E(R) = Λ(S R)  -- B&dM (4.24) Λ-absorption
    theorem Eunion(R : α ⟶ β) : E(R) = E(Λ(R))E(∋)                 -- E(R) is the union of the images of Λ(R)
    theorem Ecomp(R : α ⟶ β, S : β ⟶ γ) : E(R S) = E(R)E(S)        -- E is a functor
    theorem estMap(f : α ⟶ β, R : β ⟶ β) if dom(f) = 𝟙, simple(f), 𝟙 ⊑ R : Λ(f)est(R) = f  -- a singleton's R-extreme is itself

end Rel.Programs

namespace Rel.Lang

/-- The declaration of each definition of the program `src` read after the prelude (`Expand.read`: every
    declaration elaborated, nothing evaluated), in order; with no program, the prelude's. -/
def typesOf (src : Option Program) : EM (List String) := do
  let prog := src.getD Programs.prelude
  let _ ← Expand.read (fun _ => none) (if src.isSome then [(`prelude, Programs.prelude)] else []) prog
  pure (prog.filterMap fun | .defn _ n ps _ ty => some (sigOf n ps ty) | _ => none)

end Rel.Lang
