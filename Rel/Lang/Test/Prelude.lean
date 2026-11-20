import Rel.Lang.Test.Common
import Rel.RepCanon

namespace Rel.Lang.Test

open Tab Rel.Lang Rel.Alg Rel

-- the prelude's definitions type-check
#eval show Lean.Meta.MetaM Unit from do match ← (typesOf none).run with | .error e => throwError "{e}" | .ok _ => pure ()
#guard Programs.prelude.ok

-- `prims` names the prelude definitions its rows run unchecked (Syntax cannot import the prelude), so each is checked here
run_cmd do
  for r in prims do
    if let some c := r.prelude then
      unless (← Lean.getEnv).contains c do Lean.throwError "prims: the prelude definition of `{r.sym}` is `{c}`, which is not declared"

/-! The prelude (§c): each definition moved there against the builtin it replaced (`Alg.perm`, `Alg.ordered`, and
    `sort(Q) = perm ordered(Q)`), on a repeated element, the empty array, two element objects and arrays of arrays;
    the converses; the declared infix operators; the errors. -/

open Rel.Programs.prelude in
rel_program pre where
    obj N = 0…9
    obj K = {a,b,c,d}
    obj Ch = {p,q}
    x : K ⟶ [N] ≜ {(a,3 1 2),(b,2 1 2),(c,[]),(d,[5])}
    le : N ⟶ N ≜ 𝟙(N) ≤
    pm : K ⟶ [N] ≜ x perm
    od : K ⟶ [N] ≜ x ordered(≤)
    st : K ⟶ [N] ≜ x sort(≤)
    y : K ⟶ [Ch] ≜ {(a,p q p),(b,[])}
    py : K ⟶ [Ch] ≜ y perm
    z : K ⟶ [[N]] ≜ {(a,[1 2] [3] []),(b,[] [])}
    pz : K ⟶ [[N]] ≜ z perm

/-- The rows `(k, ys)` with `(k, xs)` a row of `rs` and `ys` a permutation of `xs` (`List.Perm`, decided by `isPerm`,
    among the arrays of its length drawn from its elements): the rows of `R perm` (B&dM p.130) for `R` of rows `rs`. -/
def permRows {κ α : Type} [BEq α] (rs : List (κ × List α)) : List (κ × List α) :=
  rs.flatMap fun (k, xs) => ((List.replicate xs.length xs).foldr (fun c acc => c.flatMap fun a => acc.map (a :: ·))
    [[]]).filter (·.isPerm xs) |>.map (k, ·)

-- each definition against its meaning on its argument's rows, as sets (`specOk`): `R perm` by `permRows`,
-- `R ordered(Q)` keeps the rows whose array has `Q` from each element to every later one (`List.Pairwise`), and
-- `R sort(Q) = R perm ordered(Q)` the permuted rows so ordered; `Q` is the program's `le`
#guard let o := pre.expanded
  let t (n : String) (B : Obj) : Except String (Tab .long B) := (get o n .long B).elim (.error n) .ok
  match t "x" (.arr .long), t "le" .long, t "y" (.arr .long), t "z" (.arr (.arr .long)) with
  | .ok X, .ok Le, .ok Y, .ok Z =>
    let ord (xs : List Int64) := decide (xs.Pairwise fun a b => Le.toList.contains (a, b))
    specOk (t "pm" (.arr .long)) (permRows X.toList) && specOk (t "od" (.arr .long)) (X.toList.filter (ord ·.2)) &&
      specOk (t "st" (.arr .long)) ((permRows X.toList).filter (ord ·.2)) &&
      specOk (t "py" (.arr .long)) (permRows Y.toList) && specOk (t "pz" (.arr (.arr .long))) (permRows Z.toList)
  | _, _, _, _ => false

-- the converses: `perm° = perm` (the one rule kept for a definition), `ordered(Q)` a coreflexive, and
-- `sort(Q)° = ordered(Q)° perm°` from them
open Rel.Programs.prelude in
rel_program converses where
    obj N = 0…9
    x : 1 ⟶ [N] ≜ {(∗,1 2 3)}
    print x perm°
    print x ordered(≤)°
    print x sort(≤)°
    print {(∗,3 1 2)} sort(≤)°
#guard printed converses.prints ==
  ["{(∗, 1 2 3), (∗, 1 3 2), (∗, 2 1 3), (∗, 2 3 1), (∗, 3 1 2), (∗, 3 2 1)}", "{(∗, 1 2 3)}",
   "{(∗, 1 2 3), (∗, 1 3 2), (∗, 2 1 3), (∗, 2 3 1), (∗, 3 1 2), (∗, 3 2 1)}", "{}"]

-- a declared infix operator: `R + S = ⟨R,S⟩plus`, the prelude's `⇒` and `⊕`, a program's own `_≼_`, each read at
-- the one level with `∩`, left to right
open Rel.Programs.prelude in
rel_program infixes where
    obj N = 0…9
    w : N×N ⟶ N×N ≜ {((2,3),(2,3)),((4,1),(4,1))}
    print w (π₁ + π₂)
    check w (π₁ + π₂) = w⟨π₁,π₂⟩plus
    _≼_(R : α ⟶ β, S : β ⟶ α) : α ⟶ β ≜ R ∩ S°
    print {(1,1),(2,2)}(≤ ≼ ≤)
    print {(1,1)}(≤ ≼ ≤ ∪ <)
    print {(1,1)}(< ∪ 𝟙(N) ≼ ≤)
    print {(1,1)}(𝟙(N) ∩ {(1,2)} ⇒ <)
    print {(1,1)}inl(N,N+N)(𝟙 ⊕ succ)
#guard infixes.ok && printed infixes.prints ==
  ["{((2, 3), 5), ((4, 1), 5)}", "{(1, 1), (2, 2)}",
   "{(1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (1, 8), (1, 9)}", "{(1, 1)}",
   "{(1, 0), (1, 1), (1, 2), (1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (1, 8), (1, 9)}", "{(1, inl 1)}"]
#eval trips ["R ⇒ S", "R ⊕ S", "R + S", "frac(R, S)", "∈", "perm", "ordered(R)", "sort(R)", "cor(R)"]
-- `cor(R)`: the pairs of `R` as a coreflexive on `A×B`
open Rel.Programs.prelude in
rel_program corPairs where
    obj N = 0…3
    print {((1,2),(1,2)),((2,1),(2,1)),((3,3),(3,3))}cor(≤)
#guard printed corPairs.prints == ["{((1, 2), (1, 2)), ((3, 3), (3, 3))}"]
#eval readsAll [("R ∩ S ⇒ R", "((R ∩ S) ⇒ R)"), ("R ⇒ S ∩ R", "((R ⇒ S) ∩ R)"), ("R S + R", "((R S) + R)"),
  ("R + S R", "((R + S) R)")]
-- infix only: used before its arguments, alone, or declared with other than two parameters
#eval errAt "obj B = 0…1\nf ≜ ⇒(π₁,π₂)\n" 2 "`⇒` is an infix operator: write `R ⇒ S`, not `⇒(R, S)`"
#eval errAt "obj B = 0…1\nf ≜ π₁ ∪ ⇒\n" 2 "`⇒` is an infix operator: it stands between two terms, `R ⇒ S`"
#eval errAt "obj B = 0…1\n_≼_(R) ≜ R\n" 2 "the infix operator `≼` takes two parameters, `_≼_(R, S)`, found 1"
-- a prelude name taken again, as a definition, an infix operator's name or an object, is the program's own: the
-- local name wins over an opened one (module design §2.3)
#eval show CM Unit from do
  for src in ["obj N = 0…9\nperm : N ⟶ N ≜ 𝟙(N)\n", "obj N = 0…9\n⊕ : N ⟶ N ≜ 𝟙(N)\n",
      "obj N = 0…9\n_sort_(R : N ⟶ N, S : N ⟶ N) : N ⟶ N ≜ R ∩ S\n", "obj 1 = {∗}\nobj N = 0…9\n"] do
    if let .error e ← readIn preludeScope src then throwError "{e}"
-- an error of the prelude's own text, and one raised in a prelude body at a use: the prelude's line, the use's
/-- The text `src` read after the prelude `pre`: its error. -/
def afterErr (pre src : String) : CM Err := do
  let p ← match ← readIn { cs := #[] } pre with | .ok p => pure p | .error e => throwError "{e}"
  let q ← match ← readIn { cs := #[], res := Parse.openAll [(`pre, p)] } src with | .ok q => pure q | .error e => return e
  match ← Lean.Elab.Command.liftTermElabM (Expand.read (fun _ => none) [(`pre, p)] q).run with
  | .error e => pure e
  | .ok _ => throwError "expected an error, got none"
-- the prelude's line 1 starts after `rel_program t where `, 20 columns
#eval do
  let e ← afterErr "    f ≜ g\n" "obj X = {A}\n"
  unless toString e == "in the program `pre`, line 1, col 29: unknown name 'g'" do throwError "{e}"
#eval do
  let e ← afterErr "    f(R : α ⟶ β) : α ⟶ β ≜ R g\n" "obj X = {A}\nx : X ⟶ X ≜ {(A,A)}\ny : X ⟶ X ≜ f(x)\n"
  unless e.pos.line == 3 && e.msg == "in `pre.f` (its line 1): unknown name 'g'" do throwError "{e}"


end Rel.Lang.Test
