import Rel.Lang.Test
import Rel.Lang.TestMss
import Rel.Lang.TestWumpus
import Rel.Lang.TestSelsort
import Rel.Lang.TestKnapsack
import Rel.Lang.TestCircuit
import Rel.Lang.TestHylo
import Rel.Lang.TestDetab
import Rel.Lang.TestEdit
-- every test module holding a `rel_program` (the dataframe library's definitions are generic: its closed uses are here)
import Rel.Lang.TestAsc
import Rel.Lang.TestDemand
import Rel.Lang.TestFrame
import Rel.Lang.TestFrameCols
import Rel.Lang.TestFrameGroup
import Rel.Lang.TestFrameJoin
import Rel.Lang.TestFrameNull
import Rel.Lang.TestFramePos
import Rel.Lang.TestFrameScale
import Rel.Lang.TestFrameUnbounded
import Rel.Lang.TestGenericN
import Rel.Lang.TestNative
import Rel.Lang.TestPositions
import Rel.Lang.TestSchema
import Rel.Lang.TestSum
import Rel.Lang.TestUnbounded
import Rel.ObjOrder
import Rel.Lang.GenSoundTest
-- every program of `Rel.Programs`, so the gate visits each, a test module or not
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

/-! Two checks of the generated code's results. A definition's result is its status (`ok`, or why the constant
    vouches for nothing) and, where ok, its table as a SET of rows read as values (`rowsOf`), so a body that moves
    from `Obj.lt` order to `kasc` order, or to another encoding, reads the same.

    - The differential test: each closed definition of every registered program, re-read as a `Tm`
      (`GenSoundTest.reread`) where `Tm.gen` has code at every node (`Tm.hasCode`), run as
      `(Tm.code Code.empty t).runE {}` and required to have the result of the constant `rel_program` generated
      (`n.expanded`). So on these definitions the generated code equals `Tm.gen`'s, and where the term has no
      `Tm.gap` node `Tm.gen_sound` relates `Tm.gen` to `Tm.den` under its hypotheses (the bit-matrix laws, `LamLaw`
      at each `Λ`); a definition with no code is listed with the nodes that have none, and the definitions
      elaborated once (`Once`) have no closed constant to compare.
    - The regression pin, with no independent oracle: every closed definition's result against the pin
      `compile-diff.json` beside this file, by name. The pin is an earlier run's output, so a difference says a
      result CHANGED, and a match says nothing about whether it is right; for the definitions with no code it is the
      only check.

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
def result {A B : Obj} (c : Except String (Tab A B)) : Except String (String × List (List Nat)) := do
  let .ok g := c | return ("not ok: the generated constant vouches for nothing", [])
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

/-- `t`'s constructor's name (`ctors`, by `Tm.ctorIdx`). -/
def ctorName (ctors : List Name) {A B : Obj} (t : Tm A B) : String :=
  toString ((ctors.getD t.ctorIdx .anonymous).componentsRev.headD .anonymous)

/-- The head of the spine `t`: its row (`arg` of a row with no code at these objects), or another constructor. -/
partial def spineHead (ctors : List Name) {A B : Obj} : Tm A B → String
  | .arg f _ => spineHead ctors f
  | .prim r => s!"arg {r.sym}"
  | t => s!"arg headed by {ctorName ctors t}"

mutual
/-- The nodes of `t` where `Tm.gen` returns its error table (`Tm.hasCode` false there, true at their parts): the
    constructor, and for a row or a spine its row's symbol. -/
partial def noCode (ctors : List Name) {A B : Obj} (t : Tm A B) : List String :=
  if t.hasCode then [] else match t with
  | .prim r => [s!"prim {r.sym}"]
  | .arg .. => match argNoCode ctors t with
    | [] => [spineHead ctors t]
    | l => l
  | _ => match t.parts.flatMap fun ⟨_, _, u⟩ => noCode ctors u with
    | [] => [ctorName ctors t]
    | l => l

/-- The nodes with no code in the arguments of the spine `t`. -/
partial def argNoCode (ctors : List Name) {A B : Obj} : Tm A B → List String
  | .arg f x => argNoCode ctors f ++ noCode ctors x
  | _ => []
end

/-- One more than every variable `t` reads or binds outside a call's body: a number no binder of `t` shadows. -/
partial def fresh {A B : Obj} (t : Tm A B) : Nat :=
  let own := match t with | .var _ k | .nu k .. | .mu k .. | .hylo k .. => k + 1 | _ => 0
  t.parts.foldl (fun m ⟨_, _, u⟩ => max m (fresh u)) own

/-- `t` with each sub-term equal (`Tm.diffAt`) to an earlier definition of `prev` replaced by that definition's
    variable, which the run binds to its table (`Code.bind`): a closed definition is in scope as its term, so a later
    one holds it inline once per use, and `Tm.code` would run it again at each. `GenK.memo` of a closed term is
    `.tab` of its table in every context, so the result is the same. A call's body is not entered (`Tm.mapM`):
    `Code.args` rebinds the variables there. -/
partial def reuse (prev : List (Nat × Res)) {A B : Obj} (t : Tm A B) : Tm A B :=
  match prev.findSome? fun (k, ⟨C, D, u⟩) =>
      if C == A && D == B && (Tm.diffAt id (fun _ => "") [] ⟨A, B, t⟩ ⟨C, D, u⟩).isNone then some k else none with
  | some k => .var false k
  | none => Id.run (t.mapM fun c => pure (reuse prev c))

/-- A run slower than this many milliseconds is reported as slow. -/
def slowMs : Nat := 60000

run_cmd do
  let reg := relRegistry.getState (← getEnv)
  let ctors := (← getConstInfoInduct ``Tm).ctors
  let mut run : Std.HashMap String (String × List (List Nat)) := {}
  let mut errs : Array String := #[]
  let mut open' : List String := []
  -- the differential test's obligations: each definition is compared (`same` or `differ`), `none'`, or `once`
  let mut same : List String := []
  let mut differ : Array String := #[]
  let mut none' : List (String × List String) := []
  let mut once : List String := []
  let mut slow : List (String × Nat) := []
  let mut times : Array String := #[]
  let mut closed := 0
  -- each closed definition no literal-row `check` of its program mentions
  let mut unchecked : List String := []
  for (n, _, _) in reg.progs do
    let gs ← unsafe IO.ofExcept ((← getEnv).evalConst (List (String × Gen.Gv)) (← getOptions) (n ++ `expanded))
    let (ds, _, _, _, fs) ← match ← GenSoundTest.reread n with
      | .ok r => pure r
      | .error e => throwError "TestCompile: re-reading {n}: {e}"
    for (x, _) in ds do
      unless gs.any (·.1 == x) do throwError "TestCompile: `{n}.{x}` is re-read but not in `{n ++ `expanded}`"
    once := once ++ fs.map (toString ·.const)
    -- the names the other side of each literal-row `check` mentions (`𝟘` the literal with no rows, which `{…}`
    -- cannot write): only those see a wrong `Tm` or a wrong pin
    let lit := (← Embed.programOf n).flatMap fun
      | .check _ (.lit ..) g _ | .check _ g (.lit ..) _ | .check _ (.op _ .zero _ []) g _
      | .check _ g (.op _ .zero _ []) _ => g.names
      | _ => []
    -- the definitions run so far whose `Tm.gen` table is ok, each a variable numbered past every binder of `ds`
    let base := ds.foldl (fun m (_, ⟨_, _, t⟩) => max m (fresh t)) 0
    let mut prev : List (Nat × Res) := []
    let mut η : Code := Code.empty
    for (x, ⟨A, B, c⟩) in gs do
      let nm := s!"{n}.{x}"
      unless lit.contains x do unchecked := unchecked ++ [nm]
      closed := closed + 1
      let some ⟨A', B', t⟩ := ds.lookup x | throwError "TestCompile: `{nm}` is in `{n ++ `expanded}` but not re-read"
      unless A' == A && B' == B do throwError "TestCompile: `{nm}` is re-read at other objects than it is generated at"
      match result c with
      | .error e => errs := errs.push s!"`{nm}`: {e}"
      | .ok (s, rs) =>
        if run.contains nm then throwError "TestCompile: `{nm}` is visited twice"
        run := run.insert nm (s, rs)
        if s != "ok" then open' := open' ++ [nm]
        if !t.hasCode then none' := none' ++ [(nm, (noCode ctors t).eraseDups)] else
          let t0 ← IO.monoMsNow
          let g ← IO.lazyPure fun _ => (Tm.code η (reuse prev t)).runE {}
          let r := result g
          let ms := (← IO.monoMsNow) - t0
          if let .ok T := g then
            let k := base + prev.length
            prev := (k, ⟨A', B', t⟩) :: prev; η := η.bind k (GenK.const A' B' (.ok T))
          times := times.push s!"{nm}\t{ms}"
          if ms > slowMs then slow := slow ++ [(nm, ms)]
          match r with
          | .error e => differ := differ.push s!"`{nm}`: `Tm.gen`'s result unreadable: {e}"
          | .ok (s', rs') =>
            if s' != s then differ := differ.push s!"`{nm}`: status: generated `{s}`, `Tm.gen` `{s'}`"
            else if rs' != rs then differ := differ.push s!"`{nm}`: rows differ: {rs.length} generated, \
              {rs'.length} by `Tm.gen`; only generated {few (rs.filter (!rs'.contains ·))}, only by `Tm.gen` \
              {few (rs'.filter (!rs.contains ·))}"
            else same := same ++ [nm]
  -- `REL_COMPILE_TIMES` names a file for each compared definition's run time, tab-separated, in ms
  if let some p ← IO.getEnv "REL_COMPILE_TIMES" then IO.FS.writeFile p ("\n".intercalate times.toList ++ "\n")
  -- each node kind with no code, with the number of definitions it is in
  let kinds := (none'.flatMap (·.2)).eraseDups.map fun k => (k, (none'.filter (·.2.contains k)).length)
  logInfo m!"the differential test (generated code against `Tm.gen`): {same.length + differ.size} compared, \
    {same.length} equal, {differ.size} different, {none'.length} with no code ({kinds}), {once.length} elaborated \
    once (no closed constant), {slow.length} slow (over {slowMs} ms: {slow})\nno code: {none'}\nonce: {once}"
  logInfo m!"{closed - unchecked.length} of {closed} closed definitions are mentioned by a literal-row `check`; \
    {unchecked.length} are not: {unchecked}"
  -- every closed definition of `n.expanded` is in exactly one of `same`, `differ`, `none'`, `errs` (fails below)
  unless same.length + differ.size + none'.length + errs.size == closed do
    throwError "TestCompile: {closed} closed definitions, but {same.length} equal, {differ.size} different, \
      {none'.length} with no code and {errs.size} unreadable"
  unless differ.isEmpty do
    throwError "TestCompile: {differ.size} definitions differ between the generated code and `Tm.gen`:\
      \n{"\n".intercalate differ.toList}"
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
