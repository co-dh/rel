import Rel.Lang.Test.Common

namespace Rel.Lang.Test

open Tab Rel.Lang Rel.Alg Rel

/-! One front-end error of each class, at its line: the text read after the prelude (`Expand.read`), nothing
    evaluated. -/

-- unknown name
#eval errAt "obj X = {A,B,C}\nf : X ⟶ X ≜ {(A,B)}\ng ≜ fh\n" 3 "unknown name 'h'"
-- type mismatch
#eval errAt "obj X = {A,B,C}\nobj N = 0…3\na : X ⟶ X ≜ {(A,B)}\nb : N ⟶ N ≜ {(1,2)}\nf ≜ ab\n" 5
  "found N, expected X"
-- a family given where the row is not liftable
#eval errAt "obj X = {A,B,C}\nobj St = [X×X]\nL(S : X ⟶ X) : X ⟶ X ≜ ⦇[S,S]⦈\nf : St ⟶ X×X ≜ L(∋)\n" 3
  "not liftable"
-- a term that needs a universe its object does not have
#eval errAt "obj X = {A,B,C}\nobj St = [X×X]\nprint ⊤(St,X)\n" 3 "has no universe"
-- a definition or parameter taking a builtin's name, or a name already defined or declared
#eval errAt "obj B = 0…1\nq : α×β ⟶ α ≜ π₁\nπ₂ ≜ π₁π₁\n" 3 "`π₂` is a builtin"
#eval errAt "obj B = 0…1\nf(S : B ⟶ B, E : B ⟶ B) : B ⟶ B ≜ S ∩ E\n" 2 "`E` is a builtin"
#eval errAt "obj B = 0…1\nK : α×β ⟶ α ≜ π₁\nq : α×β ⟶ α ≜ K\nK ≜ π₂\n" 4 "`K` is already defined at line 2"
#eval errAt "obj B = 0…1\nB ≜ π₁\n" 2 "`B` is already defined at line 1"
-- an object variable met at two objects, in one parameter's type or across two; a defined name is no variable
#eval errAt "obj X = {A,B,C}\nobj N = 0…3\nf(R : α ⟶ α) : α ⟶ α ≜ R\ng ≜ f({(A,1)})\n" 4
  "`α` in the type of 'R' is both X and N"
#eval errAt "obj X = {A,B,C}\nobj N = 0…3\nh(R : α ⟶ X, S : α ⟶ X) : α ⟶ X ≜ R\ng ≜ h({(A,B)},{(1,B)})\n" 4
  "`α` in the type of 'S' is both X and N"
#eval errAt "obj X = {A,B,C}\nπ : X ⟶ X ≜ 𝟙(X)\nf(R : π ⟶ π) ≜ R\n" 3 "expected an object, found 'π'"
-- a `where` item taking a defined name, a parameter's, an earlier item's or a builtin's; an item used outside
#eval errAt "obj B = 0…1\nK : α×β ⟶ α ≜ π₁\nf ≜ a where a ≜ π₂, K ≜ π₁\n" 3 "`K` is already defined at line 2"
#eval errAt "obj B = 0…1\nf(S : B ⟶ B) : B ⟶ B ≜ a where a ≜ S, S ≜ π₁\n" 2 "`S` is already a parameter of `f`"
#eval errAt "obj B = 0…1\nf : α×β ⟶ β ≜ a where a ≜ π₂, a ≜ π₁\n" 2 "`a` is already an item"
#eval errAt "obj B = 0…1\nf : α×β ⟶ β ≜ a where a ≜ π₂, π₁ ≜ a\n" 2 "`π₁` is a builtin"
#eval errAt "obj B = 0…1\nf : α×β ⟶ β ≜ a where a ≜ π₂\ng ≜ a\n" 3 "unknown name 'a'"

/-! The parser's round trip: each operator row of §b, printed as it was read. -/

#eval trips ["R S", "R°", "R ∩ S", "R ∪ S", "R − S", "∼R", "R ⇒ S", "𝟘", "⊤", "𝟙", "⊤(X, X)", "𝟙(X)", "dom(R)",
  "ran(R)", "R \\ S", "R / S", "frac(R, S)", "⟨R, S⟩", "π₁", "π₂", "R × S", "[R, S]", "inl", "inr", "R + S",
  "Λ(R)", "∋", "∈", "E(R)", "τ", "nil", "α", "cons°", "⦇R⦈", "F(R)", "est(R)", "front(R)",
  "filter(p)", "takewhile(p)", "length", "sum", "head", "tail", "suffix", "succ", "plus", "≤", "<",
  "{(A, B), (B, A)}", "R ∪ S R", "R S ∪ R", "R ∩ S ∪ R", "R ∪ S ∩ R", "R ∪ (S R)", "R (S p)", "∼(R S)°",
  "(∼R)°", "∼R S", "{((A, B), A), ((B, A), B)}", "{(A, (B, (A, B)))}"]
-- `prefix` is a Lean keyword, written in Lean's escape
#eval readsAll [("«prefix»", "prefix")]
-- and written bare
#eval readsAll [("prefix", "prefix"), ("suffix prefix", "(suffix prefix)")]
-- a space before `(` and `|` compose, as juxtaposition does; `R|S` is `R S` at the one level
#eval readsAll [("R (S)", "(R S)"), ("R|(S)", "(R S)"), ("R | S", "(R S)"), ("R | S p ∪ R", "(((R S) p) ∪ R)"),
  ("tail|(S)", "(tail S)"), ("𝟙 (S)", "(𝟙 S)")]
-- `f(a)` with no space applies `f`: a name taking no arguments, or a builtin taking objects, is an error there
#eval errAt "obj X = {A,B}\nf : X ⟶ X ≜ {(A,B)}\ng : X ⟶ X ≜ f(f)\n" 3 "`f` takes no arguments; write `f (…)` or `f|(…)`"
#eval errAt "obj X = {A,B}\nf : X ⟶ X ≜ {(A,B)}\ng : X ⟶ X ≜ 𝟙(f)\n" 3 "`𝟙(…)` gives `𝟙` its objects"
#eval errAt "obj X = {A,B}\nf : X ⟶ X ≜ {(A,B)}\ng : X ⟶ X ≜ 𝟙(f f)\n" 3 "`𝟙` takes objects, not terms"
-- the same as Lean reports it on a program
/--
error: line 65, col 17: `f` takes no arguments; write `f (…)` or `f|(…)` to compose
-/
#guard_msgs in
rel_program arity0 where
    obj X = {A,B}
    f : X ⟶ X ≜ {(A,B)}
    g : X ⟶ X ≜ f(f)

open Rel.Programs.prelude in
open Rel.Programs.prelude in
/-- Lean keywords as Rel names in a program, bare: one defined (`do`), one used (`prefix`); a Lean command that starts
    with a keyword (`example`) still ends the program. -/
rel_program kwNames where
    do : [α] ⟶ [α] ≜ suffix prefix
example : True := trivial
#guard kwNames.ok

#eval trips ["inits", "tails", "cat", "cat°", "zip", "snoc", "snoc°", "init", "concat", "perm", "setify", "asc(R)", "distinct",
  "subseq", "tic", "ordered(R)", "sort(R)", "thinL(R)", "merge(R)", "loop(R)", "R inits concat", "⟨R, S⟩ merge(p)"]

#eval readsAll [("R ∪ S R", "((R ∪ S) R)"), ("R S ∪ R", "((R S) ∪ R)"), ("R ∩ S ∪ R", "((R ∩ S) ∪ R)"),
  ("R ∪ S ∩ R", "((R ∪ S) ∩ R)"), ("∼R S", "(∼R S)"), ("R ∪ (S R)", "(R ∪ (S R))")]

-- a `where` item in place in the body and in the items after it (§c)
#eval do
  match ← readIn (preludeScope) "obj B = 0…1\nf(S) ≜ b ∪ S where a ≜ π₁, b ≜ a π₂ S\n" with
  | .ok p => unless p.filterMap reading == [("f", "(((π₁ π₂) S) ∪ S)")] do throwError "{p.filterMap reading}"
  | .error e => throwError "{e}"


end Rel.Lang.Test
