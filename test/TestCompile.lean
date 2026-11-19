import Rel.Lang.Test
import Rel.Lang.TestMss
import Rel.Lang.TestWumpus
import Rel.Lang.TestSelsort
import Rel.Lang.TestKnapsack
import Rel.Lang.TestCircuit
import Rel.Lang.TestHylo
import Rel.Lang.TestDetab
import Rel.Lang.TestEdit
import Rel.ObjOrder
-- every program of `Rel.Programs`, so the gate visits each, a test module or not
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

/-! A regression pin of the generated code's results, with no independent oracle: every closed definition of every
    registered program, the constant `rel_program` generated for it (`GenK`), against the pin `compile-diff.json`
    beside this file, by name. The pin is an earlier run's output, so a difference says a result CHANGED, and a
    match says nothing about whether it is right. A definition's result is its status (`ok`, or why the constant
    vouches for nothing) and, where ok, its table as a SET of rows read as values (`rowsOf`), so a body that moves
    from `Obj.lt` order to `kasc` order, or to another encoding, reads the same.

    `REL_COMPILE_DIFF_WRITE=1` regenerates the baseline from the current run instead of comparing; the file is
    never edited by hand. -/

namespace Rel.Lang.TestCompile

open Lean Elab Command Tab Rel.Lang Rel.Lang.Expand

/-- Whether `Obj.key` reads `A`'s elements as values: every atom but `general`, which keys as `[]` (all tie). A
    float's key merges NaNs and `±0`, as q's equality does. -/
def keyed : Obj → Bool
  | .atom t => t != .general
  | .prod a b | .sum a b => keyed a && keyed b
  | .arr b => keyed b

/-- `R`'s rows as a set of values: each row `Obj.key` of the pair (the order code q's `asc` sorts by, independent
    of row order and of the storage encoding), sorted, each once. -/
def rowsOf {A B : Obj} (R : Tab A B) : List (List Nat) :=
  ((R.toList.map fun (x, y) => (Obj.prod A B).key (x, y)).mergeSort fun a b => !decide (b < a)).eraseReps

/-- A table over this many rows is stored as its row count and `hash` of its `rowsOf`: its rows would make the
    baseline too large to review. A toolchain whose `hash` changes regenerates the baseline. -/
def rowCap : Nat := 512

/-- A definition's result, `c` its value as `n.expanded` lists it: its status and, where ok, its rows. An error is
    a result the baseline may not hold: a side `rowsOf` cannot read. -/
def result {A B : Obj} (c : CRel A B) : Except String (String × List (List Nat)) := do
  let some g := c | return ("not ok: the generated constant vouches for nothing", [])
  if !(keyed A && keyed B) then throw "a side holds a `general` atom, whose `Obj.key` is `[]`"
  pure ("ok", rowsOf g)

/-- A result as the baseline stores it: the status and the rows, or over `rowCap` rows their count and digest. -/
def toEntry (s : String) (rs : List (List Nat)) : Json :=
  if rs.length ≤ rowCap then .mkObj [("status", s), ("rows", toJson rs)]
  else .mkObj [("status", s), ("count", rs.length), ("digest", (hash rs).toNat)]

/-- At most three rows, for a report. -/
def few (rs : List (List Nat)) : String := s!"{rs.take 3}{if rs.length > 3 then " …" else ""}"

/-- How the run's `(s, rs)` differs from the baseline entry `b`, in the form `b` is stored in; `none` where it
    does not. -/
def diff (b : Json) (s : String) (rs : List (List Nat)) : Except String (Option String) := do
  let bs ← b.getObjValAs? String "status"
  if bs != s then return some s!"status: baseline `{bs}`, run `{s}`"
  match b.getObjValAs? (List (List Nat)) "rows" with
  | .ok brs =>
    let brs := (brs.mergeSort fun a b => !decide (b < a)).eraseReps
    if brs == rs then return none
    return some s!"rows differ: {rs.length} in the run, {brs.length} in the baseline; only in the run \
      {few (rs.filter (!brs.contains ·))}, only in the baseline {few (brs.filter (!rs.contains ·))}"
  | .error _ =>
    let n ← b.getObjValAs? Nat "count"; let d ← b.getObjValAs? Nat "digest"
    if n == rs.length && d == (hash rs).toNat then return none
    return some s!"rows differ: {rs.length} rows, digest {(hash rs).toNat} in the run; {n}, {d} in the baseline"

run_cmd do
  let reg := relRegistry.getState (← getEnv)
  let mut run : Std.HashMap String (String × List (List Nat)) := {}
  let mut errs : Array String := #[]
  let mut open' : List String := []
  for (n, _, _) in reg.progs do
    let gs ← unsafe IO.ofExcept ((← getEnv).evalConst (List (String × Gen.Gv)) (← getOptions) (n ++ `expanded))
    for (x, ⟨_, _, c⟩) in gs do
      let nm := s!"{n}.{x}"
      match result c with
      | .error e => errs := errs.push s!"`{nm}`: {e}"
      | .ok (s, rs) =>
        if run.contains nm then throwError "TestCompile: `{nm}` is visited twice"
        run := run.insert nm (s, rs)
        if s != "ok" then open' := open' ++ [nm]
  logInfo m!"the generated code is ok on {run.size - open'.length} definitions; not ok on \
    {open'.length}: {open'}"
  let names := (run.toList.map (·.1)).mergeSort fun a b => decide (a ≤ b)
  let stored := (names.filter fun nm => match run[nm]? with | some (_, rs) => rs.length > rowCap | none => false)
  logInfo m!"{names.length} definitions, {names.length - stored.length} stored as rows, {stored.length} as a \
    digest: {stored.map fun nm => (nm, (run[nm]?.map (·.2.length)).getD 0)}"
  unless errs.isEmpty do throwError "TestCompile: {errs.size} definitions fail:\n{"\n".intercalate errs.toList}"
  -- `REL_COMPILE_DIFF_BASELINE` names another baseline: a scratch copy, to show the gate red on a broken one
  let path := (← IO.getEnv "REL_COMPILE_DIFF_BASELINE").getD
    ((System.FilePath.mk (← getFileName)).withFileName "compile-diff.json").toString
  if (← IO.getEnv "REL_COMPILE_DIFF_WRITE") == some "1" then
    let lines := names.filterMap fun nm => run[nm]?.map fun (s, rs) => s!"{(toJson nm).compress}: {(toEntry s rs).compress}"
    IO.FS.writeFile path ("{\n" ++ ",\n".intercalate lines ++ "\n}\n")
    logInfo m!"wrote {path}: {lines.length} definitions"
    return
  let text ← try IO.FS.readFile path catch e =>
    throwError "TestCompile: read {path}: {e.toMessageData}; regenerate it with `make compile-diff-write`"
  let base ← IO.ofExcept (Json.parse text >>= (·.getObj?))
  let mut bad : Array String := #[]
  for nm in names do
    let some (s, rs) := run[nm]? | throwError "TestCompile: `{nm}` listed but not run"
    match base.get? nm with
    | none => bad := bad.push s!"`{nm}`: in the run, not in the baseline"
    | some b => match diff b s rs with
      | .error e => bad := bad.push s!"`{nm}`: baseline entry unreadable: {e}"
      | .ok none => pure ()
      | .ok (some d) => bad := bad.push s!"`{nm}`: {d}"
  for (nm, _) in base.toList do
    unless run.contains nm do bad := bad.push s!"`{nm}`: in the baseline, not in the run"
  unless bad.isEmpty do
    throwError "TestCompile: {bad.size} definitions changed since the pin {path} (a regression pin, no oracle: \
      read each change, and regenerate with `make compile-diff-write` only where the new result is the right one):\
      \n{"\n".intercalate bad.toList}"
  logInfo m!"every definition's result is unchanged from the pin {path} (a regression pin, not a check of correctness)"

end Rel.Lang.TestCompile
