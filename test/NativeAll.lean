import Rel.Lang.AllPrograms

/-! Gate `native-all`: which registered definitions run natively. Each closed definition `x` of each program `n` in
    `Rel.Lang.AllPrograms` (the registry `Expand.relRegistry`, the enumeration `test/TestCompile.lean` visits) is
    planned (`planOfIn`) and its plan's writes compared with its Lean value (`writesAgree`), the checks of the
    `TestNative*` modules, under a wall-clock budget. One line `n x: FIRST LINE OF THE ERROR` is printed for each that
    refuses to plan, disagrees or is over the budget; `make native-all` compares the sorted lines with
    `native-all-allow.txt`. Elaborated by `lake lean` outside the library, as `test/AllCovered.lean`. -/

open Lean Elab Command Rel.Lang Rel.Lang.Expand Rel.Lang.TestNative

namespace Rel.Lang.NativeAll

/-- What one definition may cost (plan, plan run and comparison), in ms. The task is abandoned when it is over, not
    stopped: Lean cannot interrupt code that checks no cancel token. -/
def budgetMs : Nat := 10000

/-- The first line of an error text, which is the kind of failure. -/
def firstLine (s : String) : String := (s.takeWhile (· != '\n')).toString

/-- A line when the definition `x` of the program `n`, whose Lean value is `v`, does not run natively: its plan
    fails, its writes differ from `v`, or the budget ends first. -/
def failure (env : Environment) (n : Name) (x : String) {A B : Obj} (v : Except String (Tab A B)) :
    IO (Option String) := do
  let run : IO (Option String) := try
      let _ ← (Lean.withCurrHeartbeats do writesAgree x (← planOfIn n x) v : Meta.MetaM Unit).run'.toIO
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

/-- The definitions `d ≥ d0` of program `p0`, and every later program, checked in this process. -/
def child (progs : Array Name) (p0 d0 : Nat) : CommandElabM Unit := do
  let env ← getEnv
  let gT := listT (pairT (mkConst ``String) (mkConst ``Gen.Gv))
  for h : p in [p0:progs.size] do
    let n := progs[p]
    rec ["P", toString p]
    let gs ← liftTermElabM (unsafe Meta.evalExpr (List (String × Gen.Gv)) gT (mkConst (n ++ `expanded)))
    let gs := gs.toArray
    for d in [(if p == p0 then d0 else 0):gs.size] do
      let some (x, ⟨_, _, v⟩) := gs[d]? | throwError "native-all: {n} has no definition {d}"
      rec ["D", toString p, toString d, x]
      if let some e ← failure env n x v then rec ["F", toString p, toString d, s!"{n} {x}: {e}"]
  rec ["DONE"]

/-- What the children of `lean file` with the precompiled libraries of `lib` found from definition `d` of program `p` on, as `(failure lines, definitions
    started)`. A kernel panic aborts the process (`panic = abort`), so a child that ends without `DONE` is a failure of
    the definition it last started, and the next child starts after it. -/
partial def drive (lib file : String) (progs : Array Name) (p d : Nat) (bad : Array String) (n : Nat) :
    IO (Array String × Nat) := do
  let o ← IO.Process.output { cmd := "lean", args := #[s!"--load-dynlib={lib}/librelk.so", s!"--load-dynlib={lib}/librel_RelKernel.so", s!"--plugin={lib}/librel_Rel_Run.so", file], env := #[("NATIVE_ALL_RESUME", some s!"{p} {d}")] }
  let rs := (o.stdout.splitOn "\n").map (·.splitOn "\t")
  let bad := rs.foldl (init := bad) fun b r => match r with | "F" :: _ :: _ :: t => b.push ("\t".intercalate t) | _ => b
  let n := n + (rs.filter (·.head? == some "D")).length
  if rs.contains ["DONE"] then
    unless o.exitCode == 0 do throw (.userError s!"native-all: a child finished with exit {o.exitCode}:\n{o.stdout}")
    return (bad, n)
  let why := s!"crashed, exit {o.exitCode}: {((o.stderr.trimAscii.toString).splitOn "\n").getLast?.getD ""}"
  match rs.reverse.find? (fun r => r.head? == some "D" || r.head? == some "P") with
  | some ("D" :: p :: d :: x) =>
    let (p, d) := (p.toNat?.getD 0, d.toNat?.getD 0)
    drive lib file progs p (d + 1) (bad.push s!"{progs[p]?.getD .anonymous} {"\t".intercalate x}: {why}") n
  | some ("P" :: p :: _) =>
    let p := p.toNat?.getD 0
    drive lib file progs (p + 1) 0 (bad.push s!"{progs[p]?.getD .anonymous} (its closed definitions): {why}") n
  | _ => throw (.userError s!"native-all: the first child {why}\n{o.stdout}")

run_cmd do
  let progs := (relRegistry.getState (← getEnv)).progs.map (·.1)
  match ← IO.getEnv "NATIVE_ALL_RESUME" with
  | some r =>
    let [p, d] := (r.splitOn " ").map String.toNat? | throwError "native-all: NATIVE_ALL_RESUME is `{r}`"
    child progs (p.getD 0) (d.getD 0)
  | none =>
    let some lib ← IO.getEnv "NATIVE_ALL_LIB" | throwError "native-all: NATIVE_ALL_LIB names .lake/build/lib, whose precompiled libraries the children load"
    let (bad, n) ← drive lib (← getFileName) progs 0 0 #[] 0
    let out := "".intercalate ((bad.qsort (· < ·)).toList.map (· ++ "\n"))
    IO.print out
    -- `run_cmd` carries a stderr line to the list, so the counts go to the Makefile's own line
    unless n > 0 do throwError "native-all: no closed definition was checked"

end Rel.Lang.NativeAll
