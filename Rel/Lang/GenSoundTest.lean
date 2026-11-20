import Rel.Lang.GenSound
import Rel.Run.Lang.Embed
import Rel.Programs.Blocks
import Rel.Programs.Chess
import Rel.Programs.Circuit
import Rel.Programs.CSP
import Rel.Programs.Detab
import Rel.Programs.Edit
import Rel.Programs.JobShop
import Rel.Programs.Knapsack
import Rel.Programs.Mss
import Rel.Programs.Party
import Rel.Programs.Prelude
import Rel.Programs.Quicksort
import Rel.Programs.Selsort
import Rel.Programs.SudokuAC
import Rel.Programs.SudokuPC
import Rel.Programs.SudokuPC9
import Rel.Programs.Wumpus

/-! `Tm.gen_sound` is not vacuous: each registered program re-read (`Expand.read`, at the homes and scope the
    registry recorded), the definitions with no `Tm.gap` node counted, and four of them, of 8 to 431 nodes, required
    to be among them. -/

namespace Rel.Lang.GenSoundTest

open Lean Elab Command Rel.Lang Rel.Lang.Embed

/-- What the registered program `n` reads, re-read at its recorded homes (`.chain`) and scopes (`.prog`), every
    parametric definition expanded at its use, as `walk` expands one with no constant: a call means its callee's
    term with the arguments put for its parameters (Q11), so no `call` node is left for `Tm.den` to read. -/
def reread (n : Name) : CommandElabM (Except Err Expand.Read) := do
  let env ← getEnv; let opts ← getOptions
  let reg := Expand.relRegistry.getState env
  let progs ← ((reg.chains.lookup n).getD []).mapM fun m => return (m, ← programOf m)
  let resOf (h : Name) : String → Found := match reg.progs.find? (·.1 == h) with
    | some (_, ns, os) => (resolverAt env opts reg ns os).1
    | none => fun _ => .none
  liftTermElabM (Expand.read (fun _ => none) progs (← programOf n) n resOf).run

run_cmd do
  let reg := Expand.relRegistry.getState (← getEnv)
  let mut total := 0
  let mut ok : List String := []
  for (n, _, _) in reg.progs do
    match ← reread n with
    | .error e => throwError "GenSoundTest: re-reading {n}: {e}"
    | .ok (ds, _, _, _, fs) =>
      for (x, ⟨_, _, t⟩) in ds ++ fs.map fun o => (toString o.const, o.res) do
        total := total + 1
        if !t.gap then ok := ok ++ [s!"{n}.{x}"]
  logInfo m!"{ok.length} of {total} definitions of {reg.progs.size} programs have no gap node"
  for x in ["Rel.Programs.chess.K", "Rel.Programs.chess.N", "Rel.Programs.blocks.r", "Rel.Programs.edit.ne"] do
    unless ok.contains x do throwError "GenSoundTest: {x} has a gap node or is no definition"

end Rel.Lang.GenSoundTest
