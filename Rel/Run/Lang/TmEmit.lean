module

public meta import Rel.Run.Lang.TmGen
public meta import Rel.Run.Lang.Expand
public meta import Rel.Run.Lang.Grammar
public meta import Rel.Run.Lang.Tm

/-! The half of `Tm.gen`'s file that runs only at elaboration (`rel_program`): a term as the `Expr` that builds it
(`Expand.tmE`), the share table, `Expand.emit`. Apart from `TmGen` because a module's `meta` definitions cannot call
its runtime ones (`Tm.code`, `Tm.hasCode`), which `Rel.Lang.GenSound` also reads. -/

namespace Rel.Lang

open Rel Rel.Kernel Rel.Verify Gen

public meta section


/-! ### A term as the `Expr` that builds it: what `rel_program` emits `Tm.gen` of -/

namespace Expand

open Lean

/-- A row field by field: its `sym` is a key of `prims`, but a row is data, so it is rebuilt, not looked up. -/
instance : ToExpr Prim where
  toExpr r :=
    let ex (c : Name) (a : Lean.Expr) := mkApp3 (mkConst c [0, 0]) (mkConst ``String) (mkConst ``Lean.Name) a
    mkAppN (mkConst ``Prim.mk) #[toExpr r.sym, toExpr r.sig, toExpr r.conv, toExpr r.written, toExpr r.prelude,
      match r.aop with | .ok n => ex ``Except.ok (toExpr n) | .error e => ex ``Except.error (toExpr e),
      toExpr r.mono, toExpr r.dem, toExpr r.num, toExpr r.ord, toExpr r.keyLift]
  toTypeExpr := mkConst ``Prim

/-- `t` as the `Expr` that builds it, constructor by constructor, its objects by `oE` and a constant by `relE`,
    `valsE`; a `share k R` whose slot `sh` names (`emit`'s constant of slot `k`) by that constant, not by `R`
    again. Not a `ToExpr`: it fails where those do (a symbol, general or ALP payload is not rebuilt). -/
def tmE (sh : Array Lean.Expr) : {A B : Obj} → Tm A B → Except String Lean.Expr
  | _, _, .val (A := A) (B := B) R => return g ``Tm.val #[oE A, oE B, fst (g ``Tab #[oE A, oE B]) (← relE R)]
  | _, _, .uni (A := A) (m := m) U => return g ``Tm.uni #[oE A, uE m, fst (g ``Vals #[oE A, uE m]) (← valsE A m U)]
  | _, _, .zero (A := A) (B := B) => return g ``Tm.zero #[oE A, oE B]
  | _, _, .id (A := A) => return g ``Tm.id #[oE A]
  | _, _, .top (A := A) (B := B) V => return g ``Tm.top #[oE A, oE B, ← tmE sh V]
  | _, _, .outl (A := A) (B := B) => return g ``Tm.outl #[oE A, oE B]
  | _, _, .outr (A := A) (B := B) => return g ``Tm.outr #[oE A, oE B]
  | _, _, .comp (A := A) (B := B) (C := C) R S => return g ``Tm.comp #[oE A, oE B, oE C, ← tmE sh R, ← tmE sh S]
  | _, _, .conv (A := A) (B := B) R => return g ``Tm.conv #[oE A, oE B, ← tmE sh R]
  | _, _, .meet (A := A) (B := B) R S => return g ``Tm.meet #[oE A, oE B, ← tmE sh R, ← tmE sh S]
  | _, _, .join (A := A) (B := B) R S => return g ``Tm.join #[oE A, oE B, ← tmE sh R, ← tmE sh S]
  | _, _, .diff (A := A) (B := B) R S => return g ``Tm.diff #[oE A, oE B, ← tmE sh R, ← tmE sh S]
  | _, _, .ldiv (A := A) (B := B) (C := C) R S U V =>
    return g ``Tm.ldiv #[oE A, oE B, oE C, ← tmE sh R, ← tmE sh S, ← tmE sh U, ← tmE sh V]
  | _, _, .rdiv (A := A) (B := B) (C := C) R S U V =>
    return g ``Tm.rdiv #[oE A, oE B, oE C, ← tmE sh R, ← tmE sh S, ← tmE sh U, ← tmE sh V]
  | _, _, .pair (A := A) (B := B) (C := C) R S => return g ``Tm.pair #[oE A, oE B, oE C, ← tmE sh R, ← tmE sh S]
  | _, _, .lam (A := A) (B := B) R => return g ``Tm.lam #[oE A, oE B, ← tmE sh R]
  | _, _, .mem (B := B) => return g ``Tm.mem #[oE B]
  | _, _, .inl (A := A) (B := B) => return g ``Tm.inl #[oE A, oE B]
  | _, _, .inr (A := A) (B := B) => return g ``Tm.inr #[oE A, oE B]
  | _, _, .prim (A := A) (B := B) r => return g ``Tm.prim #[oE A, oE B, toExpr r]
  | _, _, .atPos (B := B) k => return g ``Tm.atPos #[oE B, toExpr k]
  | _, _, .own (A := A) R => return g ``Tm.own #[oE A, ← tmE sh R]
  | _, _, .leq t U => return g ``Tm.leq #[toExpr t, ← tmE sh U]
  | _, _, .lt t U => return g ``Tm.lt #[toExpr t, ← tmE sh U]
  | _, _, .foldr (E := E) (V := V) e S => return g ``Tm.foldr #[oE E, oE V, ← tmE sh e, ← tmE sh S]
  | _, _, .fold (E := E) (V := V) e S => return g ``Tm.fold #[oE E, oE V, ← tmE sh e, ← tmE sh S]
  | _, _, .share (A := A) (B := B) k R =>
    return g ``Tm.share #[oE A, oE B, toExpr k, ← match sh[k]? with | some c => pure c | none => tmE sh R]
  | _, _, .var (A := A) (B := B) d k => return g ``Tm.var #[oE A, oE B, toExpr d, toExpr k]
  | _, _, .call (A := A) (B := B) ks c os b =>
    return g ``Tm.call #[oE A, oE B, toExpr ks, toExpr c, toExpr os, ← tmE sh b]
  | _, _, .callCv (A := A) (B := B) ks c c' os b u =>
    return g ``Tm.callCv #[oE A, oE B, toExpr ks, toExpr c, toExpr c', toExpr os, ← tmE sh b, ← tmE sh u]
  | _, _, .arg (A := A) (B := B) (C := C) (D := D) f x =>
    return g ``Tm.arg #[oE A, oE B, oE C, oE D, ← tmE sh f, ← tmE sh x]
  | _, _, .nu (A := A) (B := B) k S b => return g ``Tm.nu #[oE A, oE B, toExpr k, ← tmE sh S, ← tmE sh b]
  | _, _, .mu (A := A) (B := B) k w n b => return g ``Tm.mu #[oE A, oE B, toExpr k, toExpr w, toExpr n, ← tmE sh b]
  | _, _, .hylo (A := A) (B := B) k w b => return g ``Tm.hylo #[oE A, oE B, toExpr k, toExpr w, ← tmE sh b]
where
  /-- The first of `relE`'s, `valsE`'s pair (the table, beside its flag), `ty` its type. -/
  fst (ty e : Lean.Expr) : Lean.Expr := mkApp3 (mkConst ``Prod.fst [0, 0]) ty (mkConst ``Bool) e

end Expand

/-! ### The share table: each closed part of a program computed once -/

/-- The closed parts numbered so far, and the slot of each by its key (`Tm.numberKey`). -/
abbrev Shares := Array Res × Std.HashMap Lean.Expr Nat

/-- `t` with each numbered part read as its slot: equal keys are equal terms, slot by slot. -/
def Tm.numberKey {A B : Obj} (t : Tm A B) : Tm A B := match t with
  | .share k _ => .share k .zero
  | .call ks c os b => .call ks c os b.numberKey
  | .callCv ks c c' os b u => .callCv ks c c' os b.numberKey u
  | t => Id.run (t.mapMSz fun c _ => pure c.numberKey)
termination_by t.size
decreasing_by all_goals first | assumption | (simp only [Tm.size]; omega)

/-- `t` as a slot where it is closed: a slot of an equal part numbered before (its key, `Tm.numberKey`), read as that
    slot's own term, so a `share k R` always holds slot `k`'s term; else a new slot. -/
def Tm.numberSlot {A B : Obj} (t : Tm A B) : StateM Shares (Tm A B) := fun (ts, m) =>
  if !Expand.closed t then (t, ts, m) else
  let new (m : Std.HashMap Lean.Expr Nat) : Tm A B × Shares := (.share ts.size t, ts.push ⟨A, B, t⟩, m)
  -- a part `tmE` cannot rebuild (a symbol, general or ALP payload) has no key: a slot of its own, never shared
  match Expand.tmE #[] t.numberKey with
  | .error _ => new m
  | .ok e => match m[e]? with
    | none => new (m.insert e ts.size)
    | some k => match ts[k]? with
      | some ⟨A', B', R⟩ => if h : A' = A ∧ B' = B then (.share k (h.1 ▸ h.2 ▸ R), ts, m) else new m
      | none => new m

/-- `numberSlot` but at the head of a spine (`hd`), where a node stays as it is: the head and the earlier arguments
    are each a function of the arguments still to come (`Tm.argGen`), no closed part however closed it reads, and
    a slot would run it on none of them. -/
abbrev Tm.numberWrap (hd : Bool) {A B : Obj} (t : Tm A B) : StateM Shares (Tm A B) :=
  if hd then pure t else t.numberSlot

/-- `t` with each closed part `R` (`Expand.closed`) wrapped as `.share k R`, `k` its slot: a new one appended to the
    table, or the slot of an equal part numbered before (`Tm.numberSlot`). A call's body is entered, which
    `Tm.mapM` does not, so its closed parts are computed once per program (`Code.shares`), not at each call site
    and fixed-point round. A part's own parts get the lower slots. -/
def Tm.number {A B : Obj} (t : Tm A B) (hd : Bool := false) : StateM Shares (Tm A B) := match t with
  | .share _ R => R.number hd
  | .arg f x => (do return .arg (← f.number true) (← x.number)) >>= Tm.numberWrap hd
  | .call ks c os b => (do return .call ks c os (← b.number)) >>= Tm.numberWrap hd
  | .callCv ks c c' os b u => (do return .callCv ks c c' os (← b.number) u) >>= Tm.numberWrap hd
  | t => do (← t.mapMSz fun c _ => c.number).numberSlot
termination_by t.size
decreasing_by all_goals first | assumption | (simp only [Tm.size]; omega)

/-- The share table of the closed parts `ts`: slot `k` the code of `ts[k]` under the slots before it (which hold its
    own parts, `Tm.number`), each computed here, once. -/
def Code.shares (ts : Array Res) : Code :=
  { Code.empty with sh := ts.foldl (fun σ ⟨A, B, R⟩ => σ ++ [⟨A, B, R.code { Code.empty with sh := σ }⟩]) [] }

/-- The terms `ds` of one program numbered together (`Tm.number`), with their closed parts, whose table
    (`Code.shares`) computes each, a call body's included, once per program: `emit` builds it once per program, as
    the constant `n.shares`. -/
def Code.program (ds : List Res) : List Res × Array Res :=
  let r := (ds.mapM (m := StateM Shares) fun (r : Res) => do pure (⟨r.1, r.2.1, ← r.2.2.number⟩ : Res)).run (#[], {})
  (r.1, r.2.1)

/-- Two call sites of one body `b`, which reads its parameter `0` beside the closed part `(𝟘)°`; each call given a
    free variable, so neither call is closed. -/
private def twoCalls (b : Tm .long .long) : Tm .long .long :=
  .join (.arg (.call [0] `f [] b) (.var (A := .long) (B := .long) false 5)) (.arg (.call [0] `g [] b) (.var (A := .long) (B := .long) false 6))

-- the body's closed part is numbered inside both calls, to one slot (`𝟘` its own part, slot 0): two slots in all,
-- each computed once (`Code.shares`), where `Tm.mapM`'s walk numbers none and one slot per site would be four
#guard
  let b : Tm .long .long := .meet (.var false 0) (.conv .zero)
  let (t, ts, _) := ((twoCalls b).number).run (#[], {})
  let b' : Tm .long .long := .meet (.var false 0) (.share 1 (.conv (.share 0 .zero)))
  ts.size == 2 && ((Expand.tmE #[] t).toOption.map toString == (Expand.tmE #[] (twoCalls b')).toOption.map toString)

/-! ### What `rel_program n` emits: its share table once, each term as `Tm.gen` under it -/

namespace Expand

open Lean Meta

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

def liftE {α : Type} (x : Except String α) : MetaM α := match x with
  | .ok a => pure a
  | .error e => throwError "rel_program expansion: {e}"

def pairT (a b : Lean.Expr) : Lean.Expr := mkApp2 (mkConst ``Prod [0, 0]) a b
def listT (a : Lean.Expr) : Lean.Expr := mkApp (mkConst ``List [0]) a

/-- `fun A => (B : Obj) × F A B`, `F` the family `Tm` (a `Res` is a `Sigma` over it) or `Rel.Rel` (an entry of
    `Codes`). -/
def sigM (F : Name) : Lean.Expr :=
  let o := mkConst ``Obj
  .lam `A o (mkApp2 (mkConst ``Sigma [0, 0]) o (.lam `B o (mkApp2 (mkConst F) (.bvar 1) (.bvar 0)) .default)) .default

/-- `⟨A, B, x⟩ : (A : Obj) × sigM F A`. -/
def sigE (F : Name) (A B : Obj) (x : Lean.Expr) : Lean.Expr :=
  let o := mkConst ``Obj
  mkApp4 (mkConst ``Sigma.mk [0, 0]) o (sigM F) (oE A) (mkApp4 (mkConst ``Sigma.mk [0, 0]) o
    (.lam `B o (mkApp2 (mkConst F) (oE A) (.bvar 0)) .default) (oE B) x)

/-- The objects `objs` as a print reads them (`infoOf`). -/
def objsE (objs : Objs) : MetaM Lean.Expr := do
  let ty := pairT (mkConst ``String) (mkConst ``ObjInfo)
  mkListLit ty (objs.map fun (x, i) => mkApp4 (mkConst ``Prod.mk [0, 0]) (mkConst ``String) (mkConst ``ObjInfo)
    (toExpr x) (g ``infoOf #[toExpr i.ty, toExpr i.elems, toExpr i.range]))

/-- `t : Tab A B` as a relation computed now (`Rel.tab`), the form a run-time definition's variable is bound to. -/
def tabRel (A B t : Lean.Expr) : Lean.Expr :=
  mkApp3 (mkConst ``Rel.Rel.tab) A B (mkApp3 (mkConst ``Except.ok [0, 0]) (mkConst ``String) (mkApp2 (mkConst ``Tab) A B) t)

/-- `m >>= fun x => k x` in `IO`, `x : α`, the rest an `IO Unit` (`ioE`). -/
def bindIO (inst m α : Lean.Expr) (x : String) (k : Lean.Expr → MetaM Lean.Expr) : MetaM Lean.Expr :=
  withLocalDeclD (.mkSimple x) α fun v => do
    pure (mkAppN (mkConst ``Bind.bind [0, 0]) #[mkConst ``IO, inst, α, mkConst ``Unit, m, ← mkLambdaFVars #[v] (← k v)])

/-- The writes of `n.io` (`ioE`), after each output's table is bound: `ws` the writes so far, `σ` the run-time names'
    tables (name, `A`, `B`, table); a closed definition's table from its constant (`Rel.tab`), run as a run-time one's
    (`Table.ofRun`). An output keyed by positions writes its value side, renumbered (`Table.write`), any other the key
    table and the value table (`Table.writeKeyed`); a CSV output both forms in one file (`Table.writeCsv`), its symbol
    columns decoded through the program's dictionary `d`. -/
def ioOut (inst done d : Lean.Expr) (σ : List (String × Obj × Obj × Lean.Expr)) :
    List (String × Obj × Obj × Schema × Schema × Option Db.CsvCols × String × Option Lean.Name) → List Lean.Expr →
      MetaM Lean.Expr
  | [], ws => ws.foldrM (fun w r => bindIO inst w (mkConst ``Unit) "_" fun _ => pure r) done
  | (x, A, B, k, v, c, p, cl) :: os, ws => do
    let write (t : Lean.Expr) : Lean.Expr := match c with
      | some h => mkApp6 (mkConst ``Table.writeCsv) (mkApp2 (mkConst ``Option.some [.zero]) (mkConst ``Table.Dict) d)
          (toExpr k) (toExpr v) (toExpr h) (toExpr p) t
      | none => mkApp5 (mkConst ``Table.writeOwn) d (toExpr k) (toExpr v) (toExpr p) <| if k.isEmpty
        then mkApp4 (mkConst ``Table.write) (mkApp3 (mkConst ``Tab.n) (oE A) (oE B) t) (toExpr v) (toExpr p)
          (mkApp3 (mkConst ``Tab.val) (oE A) (oE B) t)
        else mkApp4 (mkConst ``Table.writeKeyed) (toExpr k) (toExpr v) (toExpr p) t
    match cl, σ.lookup x with
    | some c, _ =>
      bindIO inst (mkApp4 (mkConst ``Table.ofRun) (oE A) (oE B) (toExpr x) (mkApp3 (mkConst ``Rel.Rel.tab) (oE A) (oE B)
        (mkConst c))) (mkApp2 (mkConst ``Tab) (oE A) (oE B)) x fun t => ioOut inst done d σ os (ws ++ [write t])
    | none, some (_, _, t) => ioOut inst done d σ os (ws ++ [write t])
    | none, none => throwError "rel_program expansion: internal: the output `{x}` is no run-time name bound before it"

/-- The reads and run-time definitions of `n.io` (`ioE`) from `ss` on, each one `reach` holds bound once in statement
    order: an input read from its path (`Table.read`, `readKeyed`, `readCsvDict`); a definition its constant's body
    (`body`, numbered with the program's terms, as an `Expr`) run by `Tm.gen` under the share table `sh`, its
    variables (`Once.binds`) bound to the tables of its run-time names (`Code.args`, as `Sound.inputs` states), and
    run (`Table.ofRun`); then `fin` of the tables bound and the dictionary. `d` is the program's one dictionary
    (§0.2): each CSV input's texts interned into the `d` the input before grew, so equal texts are one id. -/
def ioGo (inst sh : Lean.Expr) (body : Lean.Name → Option (Once × Lean.Expr)) (reach : List String)
    (fin : List (String × Obj × Obj × Lean.Expr) → Lean.Expr → MetaM Lean.Expr) :
    List Io → List (String × Obj × Obj × Lean.Expr) → Lean.Expr → MetaM Lean.Expr
  | [], σ, d => fin σ d
  | .input x A B k v c p :: ss, σ, d => if !reach.contains x then ioGo inst sh body reach fin ss σ d else
    let tT := mkApp2 (mkConst ``Tab) (oE A) (oE B)
    let dT := mkConst ``Table.Dict
    match c with
    | some h =>
      bindIO inst (mkApp5 (mkConst ``Table.readCsvDict) d (toExpr k) (toExpr v) (toExpr h) (toExpr p)) (pairT tT dT) x
        fun r => ioGo inst sh body reach fin ss ((x, A, B, mkApp3 (mkConst ``Prod.fst [0, 0]) tT dT r) :: σ)
          (mkApp3 (mkConst ``Prod.snd [0, 0]) tT dT r)
    | none =>
      let m := mkApp5 (mkConst ``Table.readOwn) (oE A) (oE B) d (toExpr p) <| if k.isEmpty
        then mkApp2 (mkConst ``Table.read) (toExpr v) (toExpr p)
        else mkApp3 (mkConst ``Table.readKeyed) (toExpr k) (toExpr v) (toExpr p)
      bindIO inst m tT x fun t => ioGo inst sh body reach fin ss ((x, A, B, t) :: σ) d
  | .defn x c ds :: ss, σ, d => if !reach.contains x then ioGo inst sh body reach fin ss σ d else do
    let some (o, e) := body c
      | throwError "rel_program expansion: internal: `{x}` reaches an output and its constant `{c}` has no body here"
    let ⟨A, B, _⟩ := o.res
    let args ← ds.mapM fun d => match σ.lookup d with
      | some a => pure a
      | none => throwError "rel_program expansion: internal: `{d}` is not bound before `{x}`"
    unless o.binds.length == args.length do
      throwError "rel_program: the constant `{c}` of `{x}` binds {o.binds.length} variables, and `{x}` mentions the \
        run-time names {ds}; a run-time definition takes no object variable"
    -- `Code.bind` reads a variable at other objects than it is bound at as `𝟘`: each table at its parameter's
    for (d, (X, Y, _), (P, Q, _)) in ds.zip (args.zip o.params) do
      unless X == P && Y == Q do
        throwError "rel_program expansion: internal: `{d}` is a table at {repr X} ⟶ {repr Y}, and `{x}` reads it \
          at {repr P} ⟶ {repr Q}"
    let xs ← mkListLit (mkApp2 (mkConst ``Sigma [0, 0]) (mkConst ``Obj) (sigM ``Rel.Rel)) (args.map fun (X, Y, t) => sigE ``Rel.Rel X Y (tabRel (oE X) (oE Y) t))
    let v := g ``Tm.gen #[g ``Code.args #[sh, toExpr o.binds, xs], oE A, oE B, e]
    bindIO inst (mkApp4 (mkConst ``Table.ofRun) (oE A) (oE B) (toExpr x) v) (mkApp2 (mkConst ``Tab) (oE A) (oE B)) x
      fun t => ioGo inst sh body reach fin ss ((x, A, B, t) :: σ) d
  | .output .. :: ss, σ, d => ioGo inst sh body reach fin ss σ d

/-- The run-time names the outputs of `io` reach, through each definition's own (each mentions only names before
    it). -/
def ioReach (io : List Io) : List String :=
  io.reverse.foldl (init := io.filterMap fun | .output x .. => some x | _ => none) fun r s => match s with
    | .defn x _ ds => if r.contains x then r ++ ds else r
    | _ => r

/-- `n.io : IO Unit` (IO design B): the inputs the outputs reach (`reach`) read and the run-time definitions they
    reach computed, once each in statement order (`ioGo`); every output's table; then the writes in statement order
    (`ioOut`), so a failure in reading or computing writes no file. -/
def ioE (io : List Io) (reach : List String) (sh : Lean.Expr) (body : Lean.Name → Option (Once × Lean.Expr)) :
    MetaM Lean.Expr := do
  let inst ← synthInstance (mkApp (mkConst ``Bind [0, 0]) (mkConst ``IO))
  let outs := io.filterMap fun | .output x A B k v c p cl => some (x, A, B, k, v, c, p, cl) | _ => none
  let done ← mkAppOptM ``Pure.pure #[mkConst ``IO, none, mkConst ``Unit, mkConst ``Unit.unit]
  -- the dictionary starts as the library's of the own tables with symbol columns (`progLib`), else empty, and grows
  -- with the CSV inputs, appended after the library's texts so the library's ids stay
  let owns := io.filterMap fun
    | .input x _ _ k v none p => if reach.contains x then some (x, p, k, v) else none
    | .output x _ _ k v none p _ => some (x, p, k, v)
    | _ => none
  let d0 ← match ← liftE (Table.progLib owns) with
    | some L => pure (mkApp (mkConst ``Table.libDict) (toExpr L))
    | none => mkAppM ``IO.ofExcept #[mkConst ``Table.Dict.empty]
  bindIO inst d0 (mkConst ``Table.Dict) "dict" fun d =>
    ioGo inst sh body reach (fun σ d => ioOut inst done d σ outs []) io [] d

/-- The Lean definitions of what the program `n` reads (`read`). Its terms (definitions, prints, checks, and the bodies
    of the run-time definitions an output reaches) numbered together (`Code.program`): `n.c.t<k>` the term of slot
    `k`, `n.shares` the table (`Code.shares`), each slot computed once per program; `n.x` each closed definition's
    `Tm.gen n.shares` run in the empty context. Then `n.expanded` (the definitions with their objects), `n.objs`,
    `n.printed` (each `print`'s line and ok bit), `n.prints` (the lines), `n.failures` (`failures`: each `check` that
    does not hold, and each term that threw) and `n.ok`, that there is none; `n.inputs`, `n.outputs` (each
    statement's name, `csv`, path, an import's inputs first) and `n.io` (`ioE`). -/
def emit (n : Name) (r : Read) : MetaM Unit := do
  let (ds, ps, cs, objs, os, io) := r
  addConst (n ++ `objs) (mkConst ``Objs) (← objsE objs)
  let objsC := mkConst (n ++ `objs)
  -- the registry holds each body as elaborated, not numbered: a call copies it (`callTm`)
  for o in os do modifyEnv (relRegistry.addEntry · (.call o.key o))
  let reg := relRegistry.getState (← getEnv)
  let onces := reg.calls.map (·.2) ++ reg.again.toList
  let reach := ioReach io
  -- the run-time definitions an output reaches, each its constant's body (this program's `Once`, or an import's)
  let rts ← io.filterMapM fun
    | .defn x c _ => if !reach.contains x then pure none else match onces.find? (·.const == c) with
      | some o => pure (some (x, o))
      | none => throwError "rel_program: `{x}` reaches an output and its constant `{c}` was elaborated once by no \
          program, so `io` cannot compute it"
    | _ => pure none
  let terms : List Res := ds.map (·.2) ++ ps.map (·.2.1) ++
    cs.map (fun (_, _, _, _, _, _, ⟨A, B, R, _⟩) => ⟨A, B, R⟩) ++ cs.map fun (_, _, _, _, _, _, ⟨A, B, _, S⟩) => ⟨A, B, S⟩
  -- every node of every term the program runs has code (`Tm.hasCode`)
  let ctors := (← getConstInfoInduct ``Tm).ctors
  let off := (terms.flatMap fun ⟨_, _, t⟩ => noCode ctors t).eraseDups
  unless off.isEmpty do
    throwError "rel_program {n}: these nodes have no kernel body (GenK), so the program cannot run: {off}"
  for (x, o) in rts do
    let off := (noCode ctors o.res.2.2).eraseDups
    unless off.isEmpty do
      throwError "rel_program: `{x}` reaches an output and these nodes of its body have no kernel body (GenK), so \
        `io` cannot compute it: {off}"
  let (nt, parts) := Code.program (terms ++ rts.map (·.2.res))
  -- slot `k`'s term as the constant `n.c.t<k>`, its own parts (lower slots) by theirs: each part's term built once
  let mut sh : Array Lean.Expr := #[]
  for ⟨A, B, t⟩ in parts do
    let c := n ++ `c ++ Name.mkSimple s!"t{sh.size}"
    addConst c (g ``Tm #[oE A, oE B]) (← liftE (tmE sh t))
    sh := sh.push (mkConst c)
  addConst (n ++ `shares) (mkConst ``Code) (g ``Code.shares
    #[← mkArrayLit (mkConst ``Res) ((parts.toList.zip sh.toList).map fun (⟨A, B, _⟩, c) => sigE ``Tm A B c)])
  let shC := mkConst (n ++ `shares)
  let es ← nt.mapM fun ⟨A, B, t⟩ => return (A, B, ← liftE (tmE sh t))
  -- `tmE` checked, not proved: a `Lean.Expr` has no meaning inside Lean's logic. Every term written (each slot's
  -- constant, each numbered term), evaluated, is the term `Code.program` gave, node by node (`Tm.diffAt`); a `share`
  -- compares its slot only (`Tm.numberKey`), since that slot's constant is checked itself
  let written := (parts.toList.zip sh.toList).map (fun (⟨A, B, _⟩, c) => sigE ``Tm A B c) ++
    es.map fun (A, B, e) => sigE ``Tm A B e
  let vs ← withCurrHeartbeats do
    unsafe evalExpr (List Res) (listT (mkConst ``Res)) (← mkListLit (mkConst ``Res) written)
  let want := parts.toList ++ nt
  unless vs.length == want.length do
    throwError "rel_program {n}: internal: {written.length} terms written by `Expand.tmE` evaluate to {vs.length}"
  let slot (r : Res) : Res := ⟨r.1, r.2.1, r.2.2.numberKey⟩
  for (w, v) in want.zip vs do
    if let some d := Tm.diffAt id (fun i => toString (ctors.getD i .anonymous)) [] (slot w) (slot v) then
      throwError "rel_program {n}: internal: a term written by `Expand.tmE`, evaluated, is not the term \
        `Code.program` numbered: {d}"
  let code := es.map fun (A, B, e) => (A, B, g ``Tm.gen #[shC, oE A, oE B, e])
  let (dC, rest) := code.splitAt ds.length
  let (pC, rest) := rest.splitAt ps.length
  let (cR, rest) := rest.splitAt cs.length
  let pairs := cs.zip (cR.zip (rest.take cs.length))
  let rE := es.drop terms.length
  -- a closed term's table: its code run in the empty context `{}`, which knows neither side; each side a `none`
  -- at its field's type, read off the field's default (which has no executable code of its own)
  let app (A B : Obj) (t : Lean.Expr) : MetaM Lean.Expr := do
    let none' (f : Name) := return mkApp (mkConst ``Option.none [0]) (← inferType (g f #[oE A, oE B])).appArg!
    pure (g ``Rel.Rel.runE #[oE A, oE B, t,
      g ``Rel.Known.mk #[oE A, oE B, ← none' ``Rel.Known.dom._default, ← none' ``Rel.Known.ran._default,
        ← none' ``Rel.Known.pairs._default]])
  let mut entries : List Lean.Expr := []
  for ((x, ⟨A, B, t⟩), (_, _, v)) in ds.zip dC do
    unless !t.dem do throwError "rel_program expansion: internal: `{x}` needs keys"
    let k := Parse.constOf n x
    addConst k (mkApp2 (mkConst ``Except [0, 0]) (mkConst ``String) (mkApp2 (mkConst ``Tab) (oE A) (oE B))) (← app A B v)
    entries := entries ++ [g ``Gen.entry #[toExpr x, oE A, oE B, mkConst k]]
  -- each term's error message, so `failures` names the op that could not run
  let one (x : String) : Obj × Obj × Lean.Expr → Lean.Expr := fun (A, B, v) =>
    mkApp4 (mkConst ``Prod.mk [0, 0]) (mkConst ``String) (mkApp (mkConst ``Option [0]) (mkConst ``String))
      (toExpr x) (g ``Rel.Rel.err #[oE A, oE B, v])
  let errs := (ds.zip dC).map (fun ((x, _), v) => one x v) ++ (ps.zip pC).map (fun ((x, _), v) => one x v) ++
    pairs.map (fun ((_, x, _), v, _) => one x v) ++ pairs.map fun ((_, _, y, _), _, v) => one y v
  let printed ← (ps.zip pC).mapM fun ((x, _, s, u), (A, B, v)) => do
    pure (g ``printText #[oE A, oE B, objsC, toExpr x, toExpr s, toExpr u, ← app A B v])
  let checked ← pairs.mapM fun ((p, x, y, eq, s, u, _), (A, B, R), (_, _, S)) => do
    pure (g ``checkErr #[oE A, oE B, objsC, toExpr p, toExpr x, toExpr y, toExpr eq, toExpr s, toExpr u,
      ← app A B R, ← app A B S])
  let ety := pairT (mkConst ``String) (mkConst ``Gen.Gv)
  addConst (n ++ `expanded) (listT ety) (← mkListLit ety entries)
  let pty := pairT (mkConst ``String) (mkConst ``Bool)
  addConst (n ++ `printed) (listT pty) (← mkListLit pty printed)
  -- every term spelled with its implicit arguments: `mkAppM` unifies, and its `isDefEq` is a heartbeat check
  -- against the whole command's count, which the expansion's own work has already spent (`addConst`)
  addConst (n ++ `prints) (listT (mkConst ``String)) (mkApp4 (mkConst ``List.map [0, 0]) pty (mkConst ``String)
    (mkApp2 (mkConst ``Prod.fst [0, 0]) (mkConst ``String) (mkConst ``Bool)) (mkConst (n ++ `printed)))
  let cty := pairT (mkApp (mkConst ``Option [0]) (mkConst ``Err)) (mkConst ``Bool)
  addConst (n ++ `failures) (listT (mkConst ``Err))
    (g ``failures #[← mkListLit cty checked,
      ← mkListLit (pairT (mkConst ``String) (mkApp (mkConst ``Option [0]) (mkConst ``String))) errs])
  addConst (n ++ `ok) (mkConst ``Bool) (mkApp2 (mkConst ``List.isEmpty [0]) (mkConst ``Err) (mkConst (n ++ `failures)))
  -- IO design B: what the program reads and writes, by statement, and the one action that does it
  let lty := listT (pairT (mkConst ``String) (pairT (mkConst ``Bool) (mkConst ``String)))
  addConst (n ++ `inputs) lty (toExpr (io.filterMap fun | .input x _ _ _ _ c p => some (x, c.isSome, p) | _ => none))
  addConst (n ++ `outputs) lty (toExpr (io.filterMap fun | .output x _ _ _ _ c p _ => some (x, c.isSome, p) | _ => none))
  let body (c : Lean.Name) := (rts.zip rE).findSome? fun ((_, o), (_, _, e)) => if o.const == c then some (o, e) else none
  addConst (n ++ `io) (mkApp (mkConst ``IO) (mkConst ``Unit)) (← ioE io reach shC body)

end Expand

end
end Rel.Lang
