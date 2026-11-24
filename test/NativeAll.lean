import Rel.Lang.AllPrograms

/-! Gate `native-all`: which registered definitions run natively. Each closed definition `x` of each program `n` in
    `Rel.Lang.AllPrograms` (the registry `Expand.relRegistry`, the enumeration `test/TestCompile.lean` visits) is
    planned (`planOfIn`) and its plan's writes compared with its Lean value (`writesAgree`), the checks of the
    `TestNative*` modules, under a wall-clock budget. One line `n x: FIRST LINE OF THE ERROR` is printed for each that
    refuses to plan, disagrees or is over the budget; `make native-all` compares the sorted lines with
    `native-all-allow.txt`. Elaborated by `lake lean` outside the library, as `test/AllCovered.lean`.

    The work runs in child processes, never in tasks of one process (tasks share the one imported environment and
    contend on it). Phase 1: one child per shard of the programs counts the closed definitions of each. Phase 2: the
    definitions are numbered `0 … total-1` in program order and cut into chunks of consecutive numbers, which
    `workerCap` workers take from a queue, one child per chunk; a chunk touches few programs, so each program's
    `expanded` is evaluated about once. -/

open Lean Elab Command Rel.Lang Rel.Lang.Expand Rel.Lang.TestNative

namespace Rel.Lang.NativeAll

/-- What one definition may cost (plan, plan run and comparison), in ms. The task is abandoned when it is over, not
    stopped: Lean cannot interrupt code that checks no cancel token. -/
def budgetMs : Nat := 10000

/-- At most this many child processes at once, so memory stays within the cap. -/
def workerCap : Nat := 12

/-- The first line of an error text, which is the kind of failure. -/
def firstLine (s : String) : String := (s.takeWhile (· != '\n')).toString

/-- A line when the definition `x` of the program `n`, whose Lean value is `v`, does not run natively: its plan
    fails, its writes differ from `v`, or the budget ends first. -/
def failure (env : Environment) (n : Name) (r : Except Err Expand.Read) (x : String) {A B : Obj} (v : Except String (Tab A B)) :
    IO (Option String) := do
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

/-- The records a child prints, tab-separated, one per line: `P p` before it evaluates program `p`, `C p c` when `p` has
    `c` closed definitions, `D p d g x` before it checks definition `d` (numbered `g` overall, named `x`) of `p`,
    `F p d text` for a failure, and `DONE` at the end. -/
def rec (fs : List String) : IO Unit := do
  -- the process's own stdout: `run_cmd` swaps `IO.getStdout` for a buffer that a crash loses
  let o ← IO.FS.Handle.mk "/dev/stdout" .append
  o.putStrLn ("\t".intercalate fs)
  o.flush

/-- The closed definitions of program `n`. -/
def definitions (n : Name) : CommandElabM (Array (String × Gen.Gv)) := do
  let gT := listT (pairT (mkConst ``String) (mkConst ``Gen.Gv))
  return (← liftTermElabM (unsafe Meta.evalExpr (List (String × Gen.Gv)) gT (mkConst (n ++ `expanded)))).toArray

/-- Phase 1 child: the number of definitions of each program `p ≥ p0` with `p % K = k`. -/
def countChild (progs : Array Name) (p0 k K : Nat) : CommandElabM Unit := do
  for h : p in [p0:progs.size] do
    unless p % K == k do continue
    rec ["P", toString p]
    rec ["C", toString p, toString (← definitions progs[p]).size]
  rec ["DONE"]

/-- Phase 2 child: the definitions numbered `g ∈ [g0, g1)`, program `p` holding the `cs[p]` numbers after those of the
    programs before it. -/
def child (progs : Array Name) (cs : Array Nat) (g0 g1 : Nat) : CommandElabM Unit := do
  let env ← getEnv
  let mut off := 0
  for h : p in [0:progs.size] do
    let c := cs[p]?.getD 0
    let (lo, hi) := (max g0 off, min g1 (off + c))
    if lo < hi then
      rec ["P", toString p]
      let gs ← definitions progs[p]
      -- read once for all the definitions of `p`: `planOfIn` rereads the whole program for each
      let r ← liftTermElabM (Expand.reread progs[p])
      for g in [lo:hi] do
        let some (x, ⟨_, _, v⟩) := gs[g - off]? | throwError "native-all: {progs[p]} has no definition {g - off}"
        rec ["D", toString p, toString (g - off), toString g, x]
        if let some e ← failure env progs[p] r x v then rec ["F", toString p, toString (g - off), s!"{progs[p]} {x}: {e}"]
    off := off + c
  rec ["DONE"]

/-- A child `lean file` on the precompiled libraries of `lib`, with the variable `NATIVE_ALL_CHILD` set to `v`, and its
    records. -/
def spawn (lib file v : String) : IO (IO.Process.Output × List (List String)) := do
  let o ← IO.Process.output { cmd := "lean", args := #[s!"--load-dynlib={lib}/librelk.so", s!"--load-dynlib={lib}/librel_RelKernel.so", s!"--plugin={lib}/librel_Rel_Run.so", file], env := #[("NATIVE_ALL_CHILD", some v)] }
  pure (o, (o.stdout.splitOn "\n").map (·.splitOn "\t"))

/-- Why a child that ended without `DONE` failed. -/
def why (o : IO.Process.Output) : String :=
  s!"crashed, exit {o.exitCode}: {((o.stderr.trimAscii.toString).splitOn "\n").getLast?.getD ""}"

/-- The failure lines of the definitions `g ≥ g0` of the chunk ending before `g1`, as `(lines, definitions started)`. A
    kernel panic aborts the process (`panic = abort`), so a child that ends without `DONE` is a failure of the
    definition it last started, and the next child starts after it. -/
partial def drive (lib file : String) (progs : Array Name) (cs : String) (g0 g1 : Nat) (bad : Array String) (n : Nat) :
    IO (Array String × Nat) := do
  let (o, rs) ← spawn lib file s!"check {g0} {g1} {cs}"
  let bad := rs.foldl (init := bad) fun b r => match r with | "F" :: _ :: _ :: t => b.push ("\t".intercalate t) | _ => b
  let n := n + (rs.filter (·.head? == some "D")).length
  if rs.contains ["DONE"] then
    unless o.exitCode == 0 do throw (.userError s!"native-all: a child finished with exit {o.exitCode}:\n{o.stdout}")
    return (bad, n)
  match rs.reverse.find? (·.head? == some "D") with
  | some ("D" :: p :: _ :: g :: x) =>
    let (p, g) := (p.toNat?.getD 0, g.toNat?.getD 0)
    drive lib file progs cs (g + 1) g1 (bad.push s!"{progs[p]?.getD .anonymous} {"\t".intercalate x}: {why o}") n
  | _ => throw (.userError s!"native-all: a child {why o} before its first definition\n{o.stdout}")

/-- The definition counts `(p, c)` of the programs `p ≥ p0` of shard `k` of `K`, and the failure lines of those whose
    evaluation crashes (which then count none). -/
partial def driveCount (lib file : String) (progs : Array Name) (k K p0 : Nat) (cs : Array (Nat × Nat))
    (bad : Array String) : IO (Array (Nat × Nat) × Array String) := do
  let (o, rs) ← spawn lib file s!"count {p0} {k} {K}"
  let cs := rs.foldl (init := cs) fun cs r => match r with
    | "C" :: p :: c :: _ => cs.push (p.toNat?.getD 0, c.toNat?.getD 0) | _ => cs
  if rs.contains ["DONE"] then
    unless o.exitCode == 0 do throw (.userError s!"native-all: a child finished with exit {o.exitCode}:\n{o.stdout}")
    return (cs, bad)
  match rs.reverse.find? (·.head? == some "P") with
  | some ("P" :: p :: _) =>
    let p := p.toNat?.getD 0
    driveCount lib file progs k K (p + 1) cs (bad.push s!"{progs[p]?.getD .anonymous} (its closed definitions): {why o}")
  | _ => throw (.userError s!"native-all: a child {why o} before its first program\n{o.stdout}")

/-- Chunks `c, c+1, …` taken from the queue `q`, each of `size` definitions of `total`. -/
partial def work (q : IO.Ref Nat) (size total : Nat) (lib file : String) (progs : Array Name) (cs : String)
    (acc : Array String × Nat) : IO (Array String × Nat) := do
  let c ← q.modifyGet fun c => (c, c + 1)
  if c * size ≥ total then return acc
  let t0 ← IO.monoMsNow
  let (b, n) ← drive lib file progs cs (c * size) (min total ((c + 1) * size)) #[] 0
  IO.eprintln s!"TIMING chunk {c} {(← IO.monoMsNow) - t0} ms"
  work q size total lib file progs cs (acc.1 ++ b, acc.2 + n)

/-- Run `f` on every `k < K` in its own thread and collect the results; a thread only waits for its child process. -/
def forkJoin (K : Nat) (f : Nat → IO α) : IO (List α) := do
  let ts ← (List.range K).mapM fun k => IO.asTask (prio := .dedicated) (f k)
  ts.mapM fun t => IO.ofExcept t.get

run_cmd do
  let progs := (relRegistry.getState (← getEnv)).progs.map (·.1)
  match ← IO.getEnv "NATIVE_ALL_CHILD" with
  | some r =>
    let ns := (r.splitOn " ").map String.toNat?
    match r.splitOn " " with
    | "count" :: _ =>
      let [p0, k, K] := ns.drop 1 | throwError "native-all: NATIVE_ALL_CHILD is `{r}`"
      countChild progs (p0.getD 0) (k.getD 0) (K.getD 1)
    | "check" :: g0 :: g1 :: cs => child progs (cs.map (·.toNat?.getD 0)).toArray (g0.toNat?.getD 0) (g1.toNat?.getD 0)
    | _ => throwError "native-all: NATIVE_ALL_CHILD is `{r}`"
  | none =>
    let some lib ← IO.getEnv "NATIVE_ALL_LIB" | throwError "native-all: NATIVE_ALL_LIB names .lake/build/lib, whose precompiled libraries the children load"
    let file ← getFileName
    let W := min workerCap ((← IO.Process.output { cmd := "nproc" }).stdout.trimAscii.toString.toNat?.getD 1)
    let rs ← forkJoin W fun k => driveCount lib file progs k W 0 #[] #[]
    let counts := rs.foldl (init := progs.map fun _ => 0) fun a r => r.1.foldl (init := a) fun a (p, c) => a.modify p fun _ => c
    let total := counts.foldl (· + ·) 0
    -- about two chunks per worker: the queue evens out the cost of a definition, which varies by 10x
    let size := max 1 ((total + 2 * W - 1) / (2 * W))
    let csv := " ".intercalate (counts.toList.map toString)
    let q ← IO.mkRef 0
    let rs2 ← forkJoin W fun _ => work q size total lib file progs csv (#[], 0)
    let bad := rs.foldl (init := rs2.foldl (init := #[]) fun b r => b ++ r.1) fun b r => b ++ r.2
    let n : Nat := rs2.foldl (· + ·.2) 0
    let out := "".intercalate ((bad.qsort (· < ·)).toList.map (· ++ "\n"))
    IO.print out
    -- `run_cmd` carries a stderr line to the list, so the counts go to the Makefile's own line
    unless n > 0 do throwError "native-all: no closed definition was checked"

end Rel.Lang.NativeAll
