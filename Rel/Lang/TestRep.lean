import Rel.Lang.RelRep
import Rel.Lang.Test
import Rel.Lang.EmbedTest
import Rel.Lang.ModuleTest
import Rel.Lang.TestChess
import Rel.Lang.TestCircuit
import Rel.Lang.TestDetab
import Rel.Lang.TestEdit
import Rel.Lang.TestKnapsack
import Rel.Lang.TestMss
import Rel.Lang.TestNative
import Rel.Lang.TestHylo
import Rel.Lang.TestSelsort
import Rel.Lang.TestWumpus
import Rel.Programs.JobShop
import Rel.Programs.Party
import Rel.Programs.Quicksort
import Rel.Programs.SudokuPC
import Rel.Programs.SudokuPC9

/-! The representation theorems `n.rep_x` (`Expand.rep`) of every program the modules above define, in the order
    they were defined: the registry lists them, so a program is checked here as soon as its module is imported. -/

open Lean Elab Command in
run_cmd do
  for (n, _) in (Rel.Lang.Expand.relRegistry.getState (← getEnv)).progs do
    liftTermElabM (Rel.Lang.Expand.rep n)
