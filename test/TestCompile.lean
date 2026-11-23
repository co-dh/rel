import Rel.Lang.AllPrograms
import Rel.ObjOrder
import Rel.Lang.GenSoundTest

/-! The differential test of the generated code's results. A definition's result is its status (`ok`, or why the
    constant vouches for nothing) and, where ok, its table compared as a SET of rows read as values (`Tab.le` both
    ways, as a program's `check R = S` decides), so a body that moves from `Obj.lt` order to `kasc` order, or to
    another encoding, reads the same. The kernels compare: `rowsOf` sorts boxed `Nat` keys in the interpreter, which
    cost a table of 10^5 rows hundreds of ms, so it only lists the rows of a difference.

    Each closed definition of every registered program, re-read as a `Tm`
      (`GenSoundTest.reread`) where `Tm.gen` has code at every node (`Tm.hasCode`), run as
      `(Tm.code η t).runE {}`, `η` the table of the program's closed parts (`Code.program`, `Code.shares`), and required to have
      the result of the constant `rel_program` generated
      (`n.expanded`). So on these definitions the generated code equals `Tm.gen`'s, and where the term has no
      `Tm.gap` node `Tm.gen_sound` relates `Tm.gen` to `Tm.den` under its hypotheses (the bit-matrix laws,
      `Tm.GenHyp`); a definition with no code is listed with the nodes that have none, and the definitions
      elaborated once (`Once`) have no closed constant to compare. -/

namespace Rel.Lang.TestCompile

open Lean Elab Command Tab Rel.Lang Rel.Lang.Expand

open Rel.Lang.GenSoundTest (rowsOf)

/-- A definition's result, `c` its value as `n.expanded` lists it: its status and, where ok, its table. An error is
    a result that cannot be compared: a side holding a `general` atom, whose rows do not read as values. -/
def result {A B : Obj} (c : Except String (Tab A B)) : Except String (String × Option (Tab A B)) := do
  let .ok g := c | return ("not ok: the generated constant vouches for nothing", none)
  -- `Rel.Lang.keyed` (Elab) shadows the opened name
  if !(Rel.Lang.GenSoundTest.keyed A && Rel.Lang.GenSoundTest.keyed B) then
    throw "a side holds a `general` atom, whose `Obj.key` is `[]`"
  pure ("ok", some g)

/-- At most three rows, for a report. -/
def few (rs : List (List Nat)) : String := s!"{rs.take 3}{if rs.length > 3 then " …" else ""}"

/-- One more than every variable `t` reads or binds outside a call's body: a number no binder of `t` shadows. -/
partial def fresh {A B : Obj} (t : Tm A B) : Nat :=
  let own := match t with | .var k | .nu k .. | .mu k .. | .hylo k .. => k + 1 | _ => 0
  t.parts.foldl (fun m ⟨_, _, u⟩ => max m (fresh u)) own

/-- `t` with each sub-term equal (`Tm.diffAt`) to an earlier definition of `prev` replaced by that definition's
    variable, which the run binds to its table (`Code.bind`): a closed definition is in scope as its term, so a later
    one holds it inline once per use, and `Tm.code` would run it again at each. `GenK.memo` of a closed term is
    `.tab` of its table in every context, so the result is the same. A call's body is not entered (`Tm.mapM`):
    `Code.args` rebinds the variables there. -/
partial def reuse (prev : List (Nat × Res)) {A B : Obj} (t : Tm A B) : Tm A B :=
  match prev.findSome? fun (k, ⟨C, D, u⟩) =>
      if C == A && D == B && (Tm.diffAt id (fun _ => "") [] ⟨A, B, t⟩ ⟨C, D, u⟩).isNone then some k else none with
  | some k => .var k
  | none => Id.run (t.mapM fun c => pure (reuse prev c))

/-- `t` with each numbered part read as slot `f k` of another numbering, `k` its own (`Tm.numberKey` at `f = id`):
    a call's body is entered, as `Tm.number` numbers it. -/
partial def renumber (f : Nat → Nat) {A B : Obj} (t : Tm A B) : Tm A B := match t with
  | .share k _ => .share (f k) .zero
  | .call ks c os b => .call ks c os (renumber f b)
  | .callCv ks c c' os b u => .callCv ks c c' os (renumber f b) u
  | t => Id.run (t.mapMSz fun c _ => pure (renumber f c))

/-- What one program may cost this gate, in ms: its constant evaluated, its re-read and every run of its code. The gate
    checks correctness, so a program's instance is small; an instance that measures size or throughput lives in
    `Bench/` (`make bench`), which no gate imports. -/
def gateMs : Nat := 1000

run_cmd do
  let reg := relRegistry.getState (← getEnv)
  let ctors := (← getConstInfoInduct ``Tm).ctors
  let mut run : Std.HashMap String String := {}
  let mut errs : Array String := #[]
  let mut open' : List String := []
  -- the differential test's obligations: each definition is compared (`same` or `differ`), `none'`, or `once`
  let mut same : List String := []
  let mut differ : Array String := #[]
  let mut none' : List (String × List String) := []
  let mut once : List String := []
  let mut slow : List (Name × Nat) := []
  let mut times : Array String := #[]
  let mut closed := 0
  -- each closed definition no literal-row `check` of its program mentions
  let mut unchecked : List String := []
  for (n, _, _) in reg.progs do
    let p0 ← IO.monoMsNow
    -- one evaluation of both, so `n.shares`, which every definition of `n.expanded` reads, is computed once
    let gT := listT (pairT (mkConst ``String) (mkConst ``Gen.Gv))
    let (η1, gs) ← liftTermElabM (unsafe Meta.evalExpr (Code × List (String × Gen.Gv)) (pairT (mkConst ``Code) gT)
      (mkApp4 (mkConst ``Prod.mk [0, 0]) (mkConst ``Code) gT (mkConst (n ++ `shares)) (mkConst (n ++ `expanded))))
    let (ds, _, _, _, fs, _) ← match ← GenSoundTest.reread n with
      | .ok r => pure r
      | .error e => throwError "TestCompile: re-reading {n}: {e}"
    for (x, _) in ds do
      unless gs.any (·.1 == x) do throwError "TestCompile: `{n}.{x}` is re-read but not in `{n ++ `expanded}`"
    once := once ++ fs.map (toString ·.const)
    -- the names the other side of each literal-row `check` mentions (`𝟘` the literal with no rows, which `{…}`
    -- cannot write): only those see a wrong `Tm` or a wrong generated constant
    let lit := (← Embed.programOf n).flatMap fun
      | .check _ (.lit ..) g _ _ | .check _ g (.lit ..) _ _ | .check _ (.op _ .zero _ []) g _ _
      | .check _ g (.op _ .zero _ []) _ _ => g.names
      | _ => []
    -- the definitions run so far whose `Tm.gen` table is ok, each a variable numbered past every binder of `ds`
    let base := ds.foldl (fun m (_, ⟨_, _, t⟩) => max m (fresh t)) 0
    let mut prev : List (Nat × Res) := []
    -- the program numbered as one (`Code.program`): each closed part, a call body's included, computed once
    let t0 ← IO.monoMsNow
    let (dn, ts) := Code.program (ds.map (·.2))
    -- `Code.shares ts`, reading the generated side's table (`n.shares`, computed evaluating `n.expanded`) instead of
    -- running every kernel twice: a re-read part `ts[k]`, its own parts read as the generated slots they matched
    -- (`renumber`; one with none as `gt.size`, which no slot term reads), equal (`Tm.diffAt`) to a generated slot
    -- term has that slot's code, the same pure function of an equal term; any other part is computed here, as
    -- `Code.shares` does. `emit` numbers prints, checks and outputs with the definitions, so the two numberings
    -- differ
    let some (.defnInfo sc) := (← getEnv).find? (n ++ `shares)
      | throwError "TestCompile: no definition `{n ++ `shares}`"
    unless sc.value.isAppOfArity ``Code.shares 1 do
      throwError "TestCompile: `{n ++ `shares}` is not `Code.shares` of the slot terms: {sc.value}"
    let gt ← liftTermElabM
      (unsafe Meta.evalExpr (Array Res) (mkApp (mkConst ``Array [0]) (mkConst ``Res)) sc.value.appArg!)
    let mut sh : Codes := []
    let mut slots : Array (Option Nat) := #[]
    for h : k in [0:ts.size] do
      let ⟨A, B, u⟩ := ts[k]
      let key := renumber (fun i => (slots[i]?.join).getD gt.size) u
      match gt.findIdx? fun ⟨C, D, v⟩ => C == A && D == B &&
          (Tm.diffAt id (fun _ => "") [] ⟨A, B, key⟩ ⟨C, D, v.numberKey⟩).isNone with
      | some j =>
        let some x := η1.sh[j]? | throwError "TestCompile: `{n ++ `shares}` has {η1.sh.length} slots, not {gt.size}"
        slots := slots.push (some j); sh := sh ++ [x]
      | none => slots := slots.push none; sh := sh ++ [⟨A, B, u.code { Code.empty with sh }⟩]
    let η0 : Code := { Code.empty with sh }
    times := times.push s!"{n}.(share table)\t{(← IO.monoMsNow) - t0}"
    let dn := (ds.map (·.1)).zip dn
    let mut η : Code := η0
    for (x, ⟨A, B, c⟩) in gs do
      let nm := s!"{n}.{x}"
      unless lit.contains x do unchecked := unchecked ++ [nm]
      closed := closed + 1
      let some ⟨A', B', t⟩ := dn.lookup x | throwError "TestCompile: `{nm}` is in `{n ++ `expanded}` but not re-read"
      -- the proof casts the re-read term to the generated constant's objects, so the two tables compare
      let .isTrue h := inferInstanceAs (Decidable (A' = A ∧ B' = B))
        | throwError "TestCompile: `{nm}` is re-read at other objects than it is generated at"
      let t : Tm A B := h.1 ▸ h.2 ▸ t
      match result c with
      | .error e => errs := errs.push s!"`{nm}`: {e}"
      | .ok (s, R) =>
        if run.contains nm then throwError "TestCompile: `{nm}` is visited twice"
        run := run.insert nm s
        if s != "ok" then open' := open' ++ [nm]
        if !t.hasCode then none' := none' ++ [(nm, (noCode ctors t).eraseDups)] else
          let t0 ← IO.monoMsNow
          let g ← IO.lazyPure fun _ => (Tm.code η (reuse prev t)).runE {}
          let r := result g
          let ms := (← IO.monoMsNow) - t0
          if let .ok T := g then
            let k := base + prev.length
            prev := (k, ⟨A, B, t⟩) :: prev; η := η.bind k (GenK.const A B (.ok T))
          times := times.push s!"{nm}\t{ms}"
          match r with
          | .error e => differ := differ.push s!"`{nm}`: `Tm.gen`'s result unreadable: {e}"
          | .ok (s', R') =>
            if s' != s then differ := differ.push s!"`{nm}`: status: generated `{s}`, `Tm.gen` `{s'}`" else
            match R, R' with
            | some R, some R' =>
              match (do pure ((← R.le R') && (← R'.le R)) : Except String Bool) with
              | .error e => differ := differ.push s!"`{nm}`: comparing the tables: {e}"
              | .ok true => same := same ++ [nm]
              | .ok false =>
                let (rs, rs') := (rowsOf R, rowsOf R')
                differ := differ.push s!"`{nm}`: rows differ: {rs.length} generated, {rs'.length} by `Tm.gen`; \
                  only generated {few (rs.filter (!rs'.contains ·))}, only by `Tm.gen` {few (rs'.filter (!rs.contains ·))}"
            | _, _ => same := same ++ [nm]
    let pm := (← IO.monoMsNow) - p0
    times := times.push s!"{n}.(program)\t{pm}"
    if pm > gateMs then slow := slow ++ [(n, pm)]
  -- `REL_COMPILE_TIMES` names a file for each compared definition's run time, tab-separated, in ms
  if let some p ← IO.getEnv "REL_COMPILE_TIMES" then IO.FS.writeFile p ("\n".intercalate times.toList ++ "\n")
  -- each node kind with no code, with the number of definitions it is in
  let kinds := (none'.flatMap (·.2)).eraseDups.map fun k => (k, (none'.filter (·.2.contains k)).length)
  logInfo m!"the differential test (generated code against `Tm.gen`): {same.length + differ.size} compared, \
    {same.length} equal, {differ.size} different, {none'.length} with no code ({kinds}), {once.length} elaborated \
    once (no closed constant)\nno code: {none'}\nonce: {once}"
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
  unless errs.isEmpty do throwError "TestCompile: {errs.size} definitions fail:\n{"\n".intercalate errs.toList}"
  unless slow.isEmpty do
    throwError "TestCompile: {slow.length} programs cost this gate over {gateMs} ms each (program, ms): {slow}; \
      give each a small instance, and move the large one to Bench/ (`make bench`)"

end Rel.Lang.TestCompile
