import Rel.Programs.Prelude

/-! # String edit -/

namespace Rel.Programs

open Rel.Programs.prelude in
rel_program edit where
    obj A = {a,b}                                 -- the alphabet
    obj Op = A+(A+A)                              -- Op ::= cpy A ∣ del A ∣ ins A
    obj N = 0…6                                   -- lengths, and the fold rounds

    cpy : A ⟶ A+(A+A) ≜ inl
    del : A ⟶ A+(A+A) ≜ inl inr
    ins : A ⟶ A+(A+A) ≜ inr inr

    /- The universe: the strings of length ≤ 1, and every edit sequence of length ≤ 2, which holds all the edit sequences
       of a pair of them (each operation consumes a character of one string). -/

    r₂ : 1 ⟶ [N] ≜ ^(⊤{(0,0)})                    -- the array 0, one fold round
    r₄ : 1 ⟶ [N] ≜ ^(⊤{(0,0),(1,1)})              -- the array 0…1
    Ss : [A] ⟶ [A] ≜ ran(r₂⦇[nil, π₁ ∪ (⟨π₁,π₁⊤⟩snoc)]⦈)    -- the strings
    Es : [A+(A+A)] ⟶ [A+(A+A)] ≜ ran(r₄⦇[nil, π₁ ∪ (⟨π₁,π₁⊤⟩snoc)]⦈)   -- the edit sequences
    D : [A]×[A] ⟶ [A]×[A] ≜ Ss×Ss                 -- the pairs of strings

    /- The specification (09:485, edit-defn). -/

    base : 1 ⟶ [A]×[A] ≜ ⟨nil,nil⟩                -- ([],[])
    step : ([A]×[A])×(A+(A+A)) ⟶ [A]×[A] ≜ ⟨⟨π₁π₁,π₂cpy°⟩snoc,⟨π₁π₂,π₂cpy°⟩snoc⟩ ∪ ⟨⟨π₁π₁,π₂del°⟩snoc,π₁π₂⟩ ∪ ⟨π₁π₁,⟨π₁π₂,π₂ins°⟩snoc⟩
    edit : [A+(A+A)] ⟶ [A]×[A] ≜ Es⦇[base, step]⦈   -- edit ≜ ⦇[base,step]⦈, on the sequences Es
    R : [α] ⟶ [β] ≜ length ≤(N,N) length°         -- R ≜ length ≤ length°, run on the pairs est compares
    spec : [A]×[A] ⟶ [A+(A+A)] ≜ D^(edit°)est(R)  -- Λ(edit°) est(R): a shortest sequence of each pair

    /- The tabulation (09:596-610) read left to right: the book's columns hold the edits of the suffixes of `x` and
       fold `y` from its end; here each column holds the edits of the prefixes of `x` (entry `i` for `x[:i]`), `y` is
       folded from its start and every array is built by snoc, so `mle (x,y)` is `last (column x y)`. Each definition
       names the book's, of which it is the mirror image. A `'` marks a name the book also uses for the specification.

       `fstcol` is the first column, the edit sequences that delete a prefix of `x` (p.228 `fstcol = tails · list del`). -/

    fstcol(x : 1 ⟶ [A]) : 1 ⟶ [[A+(A+A)]] ≜ x F(del) ⦇[nil τ, ⟨π₁,⟨π₁ last,π₂⟩snoc⟩snoc]⦈   -- the prefixes of list(del) x

    /- `base'(b,u)` is the one-element array holding `u` then the insertion of `b` (p.229, `base(b,u) = [[ins(b)]⧺u]`). -/

    base'(b : 1 ⟶ A, u : 1 ⟶ [Op]) : 1 ⟶ [[A+(A+A)]] ≜ ⟨u,b ins⟩snoc τ

    /- `bmin(R)(p,q)` is `p` when `p` is shorter than or equal to `q`, else `q`; `R` is `length ≤ length°` (p.267,
       `bmin r = cond r (outl, outr)`). -/

    bmin : [α]×[α] ⟶ [α] ≜ q π₁ ∪ (π₂ − (q π₂)) where q ≜ dom(⟨π₁length,π₂length⟩(𝟙(N×N) ∩ (π₁ ≤ π₂°)))   -- bmin(R)(p,q): p if p R q, else q

    /- `ne` is the test "otherwise" of `step` (p.229, `a ≠ b`); the book has no name for it. -/

    ne : A×A ⟶ A×A ≜ 𝟙 − dom(π₁ ∩ π₂)

    /- `step'(b)` takes `(ws,(a,(u,v)))`: `u` with `a` copied when `a = b`, else the shorter of the last entry of `ws`
       then `del a`, and `v` then `ins b` (p.229). Here `π₁` is `ws`, `π₂π₁` is `a`, `π₂π₂π₁` is `u`, `π₂π₂π₂` is `v`, `⊤b` is `b`. -/

    step'(b : 1 ⟶ A) : [[Op]]×(A×([Op]×[Op])) ⟶ [[Op]] ≜ dom(π₂π₁ ∩ (⊤b))⟨π₁,⟨π₂π₂π₁,π₂π₁cpy⟩snoc⟩snoc ∪ (dom(⟨π₂π₁,⊤b⟩ne)⟨π₁,⟨⟨π₁ last,π₂π₁del⟩snoc,⟨π₂π₂π₂,⊤b ins⟩snoc⟩bmin⟩snoc)

    /- `nextcol(x,b,us)` is the next column, a fold over `xus` from `base'(b,head(us))` by `step'(b)` (p.228,
       `nextcol x (b, us) = ([base (b, last us), step b]) xus`); its seed depends on `(b,us)`, a family over the key of
       the fold's own left (§e), so the fold is the left one. `xus` pairs each character of `x` with the entries of `us`
       for the prefix before it and the prefix ending at it (p.229, `xus = zip (x, zip (init us, tail us))`). -/

    nextcol(x : 1 ⟶ [A], b : 1 ⟶ A, us : 1 ⟶ [[Op]]) : 1 ⟶ [[Op]] ≜ xus⦇[base'(b,us head), step'(b)]⦈ where xus ≜ ⟨x,⟨us init,us tail⟩zip⟩zip

    /- `column(x,y)` is the fold over `y` from `fstcol(x)` by `nextcol x` (p.228, `column x = ([fstcol x, nextcol x])`):
       the step takes `(us,b)` to `nextcol(x,b,us)`, applied to the closed families of `(x,(b,us))`. -/

    column(x : 1 ⟶ [A], y : 1 ⟶ [A]) : 1 ⟶ [[Op]] ≜ y⦇[fstcol(x), ⟨⊤x,⟨π₂,π₁⟩⟩(nextcol(⟨⊤,π₁⟩,⟨⊤,π₂π₁⟩,⟨⊤,π₂π₂⟩)π₂)]⦈

    /- `mle` is the last entry of the column, a minimal edit sequence (p.229, `mle (x,y) = outl (head (column x y))`). -/

    mle : [A]×[A] ⟶ [Op] ≜ column(⟨⊤,π₁⟩,⟨⊤,π₂⟩)π₂ last

    /- The tabulation gives a shortest edit sequence of every pair of `D`, of the specification's length. -/

    check D mle ⊑ spec
    check D mle length 𝟙(N) = (spec length 𝟙(N))

    /- The specification's own values are not written out, being too many rows; `TestEdit.lean` checks the first print. -/

    print spec length 𝟙(N)
    print Ddom(⟨π₁length,π₂length⟩{((1,1),(1,1))})spec

#guard edit.ok

end Rel.Programs
