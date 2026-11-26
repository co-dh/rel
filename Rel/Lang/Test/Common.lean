import Rel.Programs.Blocks
import Rel.Programs.SudokuAC

namespace Rel.Lang.Test

open Tab Rel.Lang Rel.Alg Rel

abbrev CM := Lean.Elab.Command.CommandElabM

/-- The scope of a text read after the prelude outside any Lean scope: its names unqualified (`Parse.openAll`). -/
def preludeScope : Parse.S := { cs := #[], res := Parse.openAll [(`Rel.Programs.prelude, Programs.prelude)] }

/-- The statements `src` read as a `rel_program`'s (`Embed`, the one grammar) in the scope `s`, nothing elaborated;
    they start on the line of `where`, so a line of `src` is a line of the error. A Lean parse error has no line. -/
def readIn (s : Parse.S) (src : String) : CM (Except Err Program) := do
  let txt := "rel_program t where " ++ src
  match Lean.Parser.runParserCategory (← Lean.getEnv) `command txt with
  | .ok stx => pure ((Embed.program (Lean.FileMap.ofString txt) s stx[4].getArgs).map (·.1))
  | .error e => pure (.error ⟨default, e⟩)

/-- The definition `n` of an expansion at the objects `A ⟶ B`. -/
def get (gs : List (String × Gen.Gv)) (n : String) (A B : Obj) : Option (Tab A B) := do
  let (_, ⟨A', B', c⟩) ← gs.find? (·.1 == n)
  if h : A' = A ∧ B' = B then (h.1 ▸ h.2 ▸ c).toOption else none

/-- The value printed by each line of `ps`, after its ` = `. -/
def printed (ps : List String) : List String := ps.map fun s => (s.splitOn " = ").getLastD ""

abbrev XX : Obj := .prod .long .long
abbrev St : Obj := .arr XX


/-- The program `prog` read after the prelude: its error, if any. -/
def elabErr (prog : Except Err Program) : Lean.Meta.MetaM (Option Err) := do
  match prog with
  | .error e => pure (some e)
  | .ok p => match ← (Expand.read (fun _ => none) [(`Rel.Programs.prelude, Programs.prelude)] p).run with
    | .error e => pure (some e)
    | .ok _ => pure none

/-- The statements `src` read after the prelude and `prog` fail at `line` (and `col`, when given) with `what` in the
    message. -/
def errAt (src : String) (line : Nat) (what : String) (col : Option Nat := none) (prog : Program := []) :
    CM Unit := do
  let r ← readIn (Parse.after (preludeScope) prog) src
  match ← Lean.Elab.Command.liftTermElabM (elabErr (r.map (prog ++ ·))) with
  | some e => unless e.pos.line == line && col.all (· == e.pos.col) && ((toString e.msg).splitOn what).length > 1 do
      throwError "expected an error at line {line} with '{what}', got {e}"
  | none => throwError "expected an error at line {line} with '{what}', got none"

/-- The term `s` read after the prelude with `R S p e` and the object `X` in scope, printed by `out`. -/
def parsed (s : String) (out : Expr → String) : CM String := do
  let sc := preludeScope
  match ← readIn { sc with known := [("R", 0), ("S", 0), ("p", 0), ("e", 0)] ++ sc.known, objs := "X" :: sc.objs }
      ("print " ++ s) with
  | .ok [.print _ e _] => pure (out e)
  | .ok _ => throwError "'{s}' is no one term"
  | .error e => throwError "'{s}': {e}"
/-- Each `s` of `ss` reads back as itself. -/
def trips (ss : List String) : CM Unit := ss.forM fun s => do
  let r ← parsed s Expr.show
  unless r == s do throwError "'{s}' reads back as '{r}'"
/-- Each `s` reads as its `r`, every composite and infix term of `r` in parentheses (§c: one level, left to right). -/
def readsAll (ps : List (String × String)) : CM Unit := ps.forM fun (s, r) => do
  let q ← parsed s (·.render 0 true)
  unless q == r do throwError "'{s}' reads as '{q}', not '{r}'"


def sameSet {α : Type} [BEq α] (a b : List α) : Bool := a.all b.contains && b.all a.contains

def reading : Decl → Option (String × String)
  | .defn _ n _ (.rel e) _ => some (n, e.render 0 true)
  | .defn _ n _ (.test e f) _ => some (n, s!"{e.render 0 true} ⊑ {f.render 0 true}")
  | .print _ e _ => some ("print", e.render 0 true)
  | .check _ e f eq _ _ => some ("check", s!"{e.render 0 true} {if eq then "=" else "⊑"} {f.render 0 true}")
  | _ => none

end Rel.Lang.Test
