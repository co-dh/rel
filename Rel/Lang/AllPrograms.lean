import Rel.Run.Lang.Expand
import Rel.Programs.Blocks
import Rel.Programs.Chess
import Rel.Programs.Circuit
import Rel.Programs.CSP
import Rel.Programs.Detab
import Rel.Programs.Edit
import Rel.Programs.Frame
import Rel.Programs.FrameGroup
import Rel.Programs.FrameJoin
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
import Rel.Lang.EmbedTest
import Rel.Lang.ModuleTest
import Rel.Lang.Test
import Rel.Lang.TestArcs
import Rel.Lang.TestAsc
import Rel.Lang.TestChess
import Rel.Lang.TestCircuit
import Rel.Lang.TestDemand
import Rel.Lang.TestTopProd
import Rel.Lang.TestDetab
import Rel.Lang.TestEdit
import Rel.Lang.TestFrame
import Rel.Lang.TestFrameCols
import Rel.Lang.TestFrameGroup
import Rel.Lang.TestFrameJoin
import Rel.Lang.TestFrameNull
import Rel.Lang.TestFramePos
import Rel.Lang.TestFrameScale
import Rel.Lang.TestFrameUnbounded
import Rel.Lang.TestGenericLit
import Rel.Lang.TestGenericN
import Rel.Lang.TestGroups
import Rel.Lang.TestHylo
import Rel.Lang.TestKnapsack
import Rel.Lang.TestMss
import Rel.Lang.TestNative
import Rel.Lang.TestPositions
import Rel.Lang.TestSchema
import Rel.Lang.TestSelsort
import Rel.Lang.TestSum
import Rel.Lang.TestUnbounded
import Rel.Lang.TestWumpus

/-! The one list of the modules holding a `rel_program`, imported by the two gates that visit every registered
    program (`GenSoundTest`, `test/TestCompile.lean`): a registry read from an environment holds only the programs of
    the modules that environment imports. The check below makes the list complete by itself: every module of the
    `Rel` library on disk (found by walking `Rel/`) that is not among this module's imports has its olean read, and
    one whose registry extension (`Expand.relRegistry`) holds an entry defines a program and is an error. -/

open Lean Elab Command

/-- The modules `.lean` files under `Rel/` name, as Lean's own path API reads them. -/
def Rel.Lang.AllPrograms.diskModules : IO (Array Name) := do
  let root ← IO.currentDir
  let files ← try System.FilePath.walkDir (root / "Rel") catch e =>
    throw <| IO.userError s!"AllPrograms: cannot list {root / "Rel"} (run `lake` from the package root): {e}"
  (files.filter (·.extension == some "lean")).mapM (moduleNameOfFileName · (some root))

run_cmd do
  let env ← getEnv
  let imported : Std.HashSet Name := env.header.moduleNames.foldl (·.insert ·) {}
  let mut missing : Array Name := #[]
  for m in ← Rel.Lang.AllPrograms.diskModules do
    unless imported.contains m || m == env.mainModule do
      let o ← match ← (findOLean m).toBaseIO with
        | .ok o => pure o
        | .error e => throwError "AllPrograms: {m} is in Rel/ but has no olean ({e}); run `lake build {m}` so its programs can be checked"
      let (md, region) ← (readModuleData o)
      if (md.entries.find? (·.1 == Rel.Lang.Expand.relRegistry.name)).any (·.2.size > 0) then missing := missing.push m
      region.free
  unless missing.isEmpty do
    throwError "AllPrograms: {missing.size} module(s) of Rel/ define a `rel_program` but are not imported here, so the \
      gates built on this list never visit them; add `import <module>` for each: {missing.qsort Name.lt}"
