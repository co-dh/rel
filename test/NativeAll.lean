import Rel.Lang.AllPrograms

/-! Gate `native-all`: which registered definitions run natively. Each closed definition `x` of each program `n` in
    `Rel.Lang.AllPrograms` (the registry `Expand.relRegistry`, the enumeration `test/TestCompile.lean` visits) is
    planned (`planOfRead`) and its plan's writes compared with its Lean value (`writesAgree`), the checks of the
    `TestNative*` modules, under a wall-clock budget. One line `n x: FIRST LINE OF THE ERROR` is printed for each that
    refuses to plan, disagrees or is over the budget; `make native-all` compares the sorted lines with
    `native-all-allow.txt`. Elaborated by `lake lean` outside the library, as `test/AllCovered.lean`.

    The work is shared by `shardCap` child processes (never tasks of one process: tasks share the one imported
    environment and contend on it) through the directory `NATIVE_ALL_CLAIMS`: whoever `mkdir`s `p<p>` owns program `p`,
    whoever `mkdir`s `d<p>.<d>` checks definition `d` of `p`. A child that has no program left helps with the programs
    others own and have unclaimed definitions (`cnt<p>` holds the count), so one program of many definitions (a chess program) is
    not the wall time. A program's `expanded` and its reading (`Expand.reread`) are computed once per child that
    touches it. -/

open Lean Elab Command Rel.Lang Rel.Lang.Expand Rel.Lang.TestNative

namespace Rel.Lang.NativeAll

/-- What one definition may cost (plan, plan run and comparison), in ms. The task is abandoned when it is over, not
    stopped: Lean cannot interrupt code that checks no cancel token. -/
def budgetMs : Nat := 10000

/-- At most this many child processes (shards) at once, so memory stays within the cap. -/
def shardCap : Nat := 16

/-- The first line of an error text, which is the kind of failure. -/
def firstLine (s : String) : String := (s.takeWhile (· != '\n')).toString

/-- A line when the definition `x` of the program `n` (read as `r`), whose Lean value is `v`, does not run natively: its
    plan fails, its writes differ from `v`, or the budget ends first. -/
def failure (env : Environment) (n : Name) (r : Except Err Expand.Read) (x : String) {A B : Obj}
    (v : Except String (Tab A B)) : IO (Option String) := do
  -- a definition Lean itself refuses (`v` an error: a refusal a test pins) has no value to compare: not a native gap
  if let .error _ := v then return none
  let run : IO (Option String) := try
      let _ ← (Lean.withCurrHeartbeats do writesAgree x (planOfRead n r x) v : Meta.MetaM Unit).run'.toIO
        { fileName := "native-all", fileMap := default } { env }
      pure none
    catch e => pure (some (firstLine (toString e)))
  let work ← IO.asTask (prio := .dedicated) run
  -- the timer polls its cancel flag, so a finished definition does not leave a sleeping thread behind
  let timer ← IO.asTask (prio := .dedicated) do
    for _ in [0:budgetMs / 20] do
      if ← IO.checkCanceled then return none
      IO.sleep 20
    pure (some s!"timeout: over {budgetMs} ms")
  let r ← IO.waitAny [work, timer]
  IO.cancel timer
  match r with
  | .ok l => pure l
  | .error e => pure (some (firstLine (toString e)))

/-- The records a child prints, tab-separated, one per line: `P p` before it evaluates program `p`, `D p d x` before it
    checks definition `d` of program `p`, `F p d text` for a failure, and `DONE` at the end. -/
def rec (fs : List String) : IO Unit := do
  -- the process's own stdout: `run_cmd` swaps `IO.getStdout` for a buffer that a crash loses
  let o ← IO.FS.Handle.mk "/dev/stdout" .append
  o.putStrLn ("\t".intercalate fs)
  o.flush


/-- `true` for the one process that makes the directory `name` of `dir`: the claim is atomic, as `mkdir` is. -/
def claim (dir name : String) : IO Bool := do
  try IO.FS.createDir s!"{dir}/{name}"; pure true
  catch | .alreadyExists .. => pure false | e => throw e

/-- Whether program `p` may have definitions no process has claimed: its count `cnt<p>` is not written yet or not all
    its `d<p>.<d>` exist. Nothing is evaluated to tell. -/
def pending (dir : String) (p : Nat) : IO Bool := do
  unless ← System.FilePath.pathExists s!"{dir}/cnt{p}" do return true
  let some c := (← IO.FS.readFile s!"{dir}/cnt{p}").trimAscii.toString.toNat? | return true
  (List.range c).anyM fun d => not <$> System.FilePath.pathExists s!"{dir}/d{p}.{d}"

/-- Check the definitions of program `p` that no process has claimed. -/
def runProg (env : Environment) (progs : Array Name) (dir : String) (p : Nat) : CommandElabM Unit := do
  let some n := progs[p]? | throwError "native-all: no program {p}"
  rec ["P", toString p]
  let gT := listT (pairT (mkConst ``String) (mkConst ``Gen.Gv))
  let gs ← liftTermElabM (unsafe Meta.evalExpr (List (String × Gen.Gv)) gT (mkConst (n ++ `expanded)))
  let gs := gs.toArray
  IO.FS.writeFile s!"{dir}/cnt{p}" (toString gs.size)
  let r ← liftTermElabM (Expand.reread n)
  for d in [0:gs.size] do
    unless ← claim dir s!"d{p}.{d}" do continue
    let some (x, ⟨_, _, v⟩) := gs[d]? | throwError "native-all: {n} has no definition {d}"
    rec ["D", toString p, toString d, x]
    if let some e ← failure env n r x v then rec ["F", toString p, toString d, s!"{n} {x}: {e}"]

/-- A child: the programs it can claim, then the others' that still have definitions to claim. -/
def child (progs : Array Name) (dir : String) : CommandElabM Unit := do
  let env ← getEnv
  let mut owned := #[]
  for p in [0:progs.size] do
    if ← claim dir s!"p{p}" then runProg env progs dir p else owned := owned.push p
  for p in owned do
    if ← pending dir p then runProg env progs dir p
  rec ["DONE"]

/-- What the children of `lean file` with the precompiled libraries of `lib` found, sharing the claims in `dir`, as
    `(failure lines, definitions started)`. A kernel panic aborts the process (`panic = abort`), so a child that ends
    without `DONE` is a failure of the definition it last started (which stays claimed), and the next child starts
    after it; a program whose evaluation crashes has count 0, so no child evaluates it again. -/
partial def drive (lib file dir : String) (progs : Array Name) (bad : Array String) (n : Nat) : IO (Array String × Nat) := do
  let o ← IO.Process.output { cmd := "lean", args := #[s!"--load-dynlib={lib}/librelk.so", s!"--load-dynlib={lib}/librel_RelKernel.so", s!"--plugin={lib}/librel_Rel_Run.so", file], env := #[("NATIVE_ALL_CLAIMS", some dir), ("NATIVE_ALL_CHILD", some "1")] }
  let rs := (o.stdout.splitOn "\n").map (·.splitOn "\t")
  let bad := rs.foldl (init := bad) fun b r => match r with | "F" :: _ :: _ :: t => b.push ("\t".intercalate t) | _ => b
  let n := n + (rs.filter (·.head? == some "D")).length
  if rs.contains ["DONE"] then
    unless o.exitCode == 0 do throw (.userError s!"native-all: a child finished with exit {o.exitCode}:\n{o.stdout}")
    return (bad, n)
  let why := s!"crashed, exit {o.exitCode}: {((o.stderr.trimAscii.toString).splitOn "\n").getLast?.getD ""}"
  match rs.reverse.find? (fun r => r.head? == some "D" || r.head? == some "P") with
  | some ("D" :: p :: _ :: x) =>
    drive lib file dir progs (bad.push s!"{progs[p.toNat?.getD 0]?.getD .anonymous} {"\t".intercalate x}: {why}") n
  | some ("P" :: p :: _) =>
    IO.FS.writeFile s!"{dir}/cnt{p}" "0"
    drive lib file dir progs (bad.push s!"{progs[p.toNat?.getD 0]?.getD .anonymous} (its closed definitions): {why}") n
  | _ => throw (.userError s!"native-all: a child {why} before its first program\n{o.stdout}")

/-- The parent: `K` children at once on a fresh claim directory, the failure lines of all sorted. -/
def parent (progs : Array Name) (dir : String) : CommandElabM Unit := do
  let some lib ← IO.getEnv "NATIVE_ALL_LIB" | throwError "native-all: NATIVE_ALL_LIB names .lake/build/lib, whose precompiled libraries the children load"
  let file ← getFileName
  if ← System.FilePath.pathExists dir then IO.FS.removeDirAll dir
  IO.FS.createDirAll dir
  let K := min shardCap ((← IO.Process.output { cmd := "nproc" }).stdout.trimAscii.toString.toNat?.getD 1)
  -- a thread only waits for its child process
  let ts ← (List.range K).mapM fun _ => IO.asTask (prio := .dedicated) (drive lib file dir progs #[] 0)
  let rs ← ts.mapM fun t => IO.ofExcept t.get
  let bad := rs.foldl (init := #[]) fun b r => b ++ r.1
  let n : Nat := rs.foldl (· + ·.2) 0
  IO.print ("".intercalate ((bad.qsort (· < ·)).toList.map (· ++ "\n")))
  -- `run_cmd` carries a stderr line to the list, so the counts go to the Makefile's own line
  -- every program's count is read, so a program no child evaluated, or a definition checked twice or never, is an error
  let mut total := 0
  for p in [0:progs.size] do
    let f := s!"{dir}/cnt{p}"
    unless ← System.FilePath.pathExists f do throwError "native-all: no child evaluated {progs[p]?.getD .anonymous} (no {f})"
    total := total + (← IO.FS.readFile f).trimAscii.toString.toNat?.getD 0
  unless n == total && n > 0 do throwError "native-all: {n} definitions were checked, {total} counted"

run_cmd do
  let progs := (relRegistry.getState (← getEnv)).progs.map (·.1)
  let some dir ← IO.getEnv "NATIVE_ALL_CLAIMS" | throwError "native-all: NATIVE_ALL_CLAIMS names the directory the children claim work in"
  if (← IO.getEnv "NATIVE_ALL_CHILD").isSome then child progs dir else parent progs dir

end Rel.Lang.NativeAll
