import Rel.Run.Lang.Embed
import Rel.Programs.Prelude
/-! The Rel language written inside Lean (`Embed`): the grammar's closedness, a Lean term in a body is an
    error (a keyword in it is a Rel name). The programs written with it are `Rel.Programs`, run by the
    `Test*` modules. -/

namespace Rel.Lang.EmbedTest

open Lean

/-! Closedness: a Lean term in a body is an error, never a term elaborated; a keyword in it is a Rel name. -/

elab "#rel_parse " s:str : command => do
  match Parser.runParserCategory (← getEnv) `relStmt s.getString with
  | .ok t => logInfo m!"parsed {t}"
  | .error e => logInfo e

/-- info: parsed f:A⟶A≜R∩∼S° -/
#guard_msgs in #rel_parse "f : A ⟶ A ≜ R ∩ ∼S°"
/-- info: <input>:1:18: expected end of input -/
#guard_msgs in #rel_parse "f : A ⟶ A ≜ fun x => x"
/-- info: <input>:1:18: expected end of input -/
#guard_msgs in #rel_parse "f : A ⟶ A ≜ let x := R; x"
/-- info: parsed f:A⟶A≜do R -/
#guard_msgs in #rel_parse "f : A ⟶ A ≜ do R"
/-- info: parsed f:A⟶A≜if R then S else T -/
#guard_msgs in #rel_parse "f : A ⟶ A ≜ if R then S else T"
/-- info: <input>:1:14: expected ')' -/
#guard_msgs in #rel_parse "f : A ⟶ A ≜ (R, S)"
/-- info: <input>:1:12: expected a name -/
#guard_msgs in #rel_parse "f : A ⟶ A ≜ 1 + 1"
/-- info: <input>:1:15: expected a name -/
#guard_msgs in #rel_parse "f : A ⟶ A ≜ R (1 + 1)"
/-- info: <input>:1:20: expected ')' -/
#guard_msgs in #rel_parse "f : A ⟶ A ≜ R(fun x => x)"
/-- info: <input>:1:22: expected '≜' -/
#guard_msgs in #rel_parse "f : A ⟶ A ≜ R where x := 1"

-- Lean gives every category the antiquotation `$x`, `$(…)` at any quotation depth, so these parse; reading the
-- program refuses them. Only where a term starts: after a term, `$` is the cast row (`x $ F`), so `𝟙 $x` is a cast
-- whose object is missing.
/-- info: parsed f:A⟶A≜$x -/
#guard_msgs in #rel_parse "f : A ⟶ A ≜ $x"
/-- info: parsed f:A⟶A≜$(fun x => x) -/
#guard_msgs in #rel_parse "f : A ⟶ A ≜ $(fun x => x)"
/-- error: line 50, col 17: `$` is no term of the Rel language: an antiquotation has no place in a program -/
#guard_msgs in
open Rel.Programs.prelude in
rel_program antiquot where
    f : 1 ⟶ 1 ≜ $x
/-- error: line 55, col 17: expected a term -/
#guard_msgs in
open Rel.Programs.prelude in
rel_program antiquot2 where
    f : 1 ⟶ 1 ≜ 𝟙 $x

/-! `theorem n : e = f := calc` (`doc/rel-mss-proof-design.md` §3, §8): the chain alternates terms and reason lines
    `:= n` (`⊑ := n` for `⊑`); `n` cites a theorem, `≜ n` a definition; `on A` evaluates each step as a `check`. -/

open Rel.Programs.prelude in
rel_program thm where
    obj N = 0…3
    obj K = {a,b}
    two : N ⟶ N ≜ {(1,2),(2,2)}
    up : N ⟶ N ≜ {(1,2)}
    x : K ⟶ N ≜ {(a,1),(b,2)}
    theorem unit : two 𝟙 = two
    theorem good on x : two 𝟙 = two := calc
      two 𝟙
        := ≜ two
      {(1,2),(2,2)}
        := ≜ two
      two
    theorem le on x : up ⊑ two := calc
      up
        ⊑ := unit
      two 𝟙
        := unit
      two

#guard thm.ok
-- the chains stay in the program's constant, for `rel_aop` to read back
#guard (thm.filterMap fun | .«theorem» _ n _ _ _ _ _ _ ss _ => some (n, ss.length) | _ => none) ==
  [("unit", 0), ("good", 2), ("le", 2)]

/-- error: line 93, col 7: theorem `t`: this step x is K ⟶ N, the statement's two is N ⟶ N -/
#guard_msgs in
open Rel.Programs.prelude thm in
rel_program thmType where
    theorem t : two = two := calc
      two
        := unit
      x
        := unit
      two

/-- error: line 104, col 7: `unit` is a theorem, not a relation -/
#guard_msgs in
open Rel.Programs.prelude thm in
rel_program thmAsRel where
    theorem t : two = two := calc
      two
        := unit
      unit

/-- error: line 112, col 12: `two` is a definition; write `≜ two` -/
#guard_msgs in
open Rel.Programs.prelude thm in
rel_program relAsThm where
    theorem t : two = two := calc
      two
        := two
      two

/-- error: line 121, col 14: `unit` is a theorem, not a definition -/
#guard_msgs in
open Rel.Programs.prelude thm in
rel_program thmAsDef where
    theorem t : two = two := calc
      two
        := ≜ unit
      two

/-- error: line 130, col 12: unknown theorem 'nope' -/
#guard_msgs in
open Rel.Programs.prelude thm in
rel_program thmUnknown where
    theorem t : two = two := calc
      two
        := nope
      two

/-- error: line 140, col 7: the chain of `t` ends at two 𝟙, not at its right side two -/
#guard_msgs in
open Rel.Programs.prelude thm in
rel_program thmEnds where
    theorem t : two 𝟙 = two := calc
      two 𝟙
        := unit
      two 𝟙

/-- error: line 147, col 7: the chain starts at `up`, the statement's left side is `two` -/
#guard_msgs in
open Rel.Programs.prelude thm in
rel_program thmStarts where
    theorem t : two = two := calc
      up
        := unit
      two

/-- error: line 157, col 9: `t` states `=`: a step `⊑` proves only `⊑` -/
#guard_msgs in
open Rel.Programs.prelude thm in
rel_program thmLe where
    theorem t : up = two := calc
      up
        ⊑ := unit
      two

open Rel.Programs.prelude thm in
rel_program thmData where
    theorem t on x : up = two := calc
      up
        := unit
      two

#guard !thmData.ok
#guard thmData.failures.map toString ==
  [s!"line {decl_line% thmData + 4}, col 7: check failed: x up = \{(a, 2)}, x two = \{(a, 2), (b, 2)}"]

/-! A juxtaposed antiquotation ends its statement at its line, as a name does: the next line, a statement or a Lean
    command, is not read into it. `#rel_stmts` shows each statement a program's lines parse to. -/

syntax (name := relStmtsCmd) "#rel_stmts" Embed.relStmts : command
open Elab Command in
@[command_elab relStmtsCmd] def elabRelStmts : CommandElab := fun stx => do
  for s in stx[1].getArgs do logInfo m!"{s}"

/-- info: f:1⟶1≜𝟙$x
---
info: g:1⟶1≜𝟙
---
info: h:1⟶1≜𝟙$(fun x => x)
---
info: k:1⟶1≜𝟙 -/
#guard_msgs in
#rel_stmts
    f : 1 ⟶ 1 ≜ 𝟙 $x
    g : 1 ⟶ 1 ≜ 𝟙
    h : 1 ⟶ 1 ≜ 𝟙 $(fun x => x)
    k : 1 ⟶ 1 ≜ 𝟙

section antiquot
/-- info: f:1⟶1≜𝟙$x -/
#guard_msgs in
#rel_stmts
    f : 1 ⟶ 1 ≜ 𝟙 $x
end antiquot

end Rel.Lang.EmbedTest
