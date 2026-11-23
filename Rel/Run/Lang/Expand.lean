module

public import Lean
public import Rel.Run.Lang.GenK
public import Rel.Run.Lang.Elab
public import Rel.Run.Lang.Parse
public import Rel.Run.ValEq
public import Rel.Run.Table

-- exposed: every def body is a spec a downstream `rfl`/`decide`/`simp` may unfold (PLAN W.8)
@[expose] public section

/-! The expander of `rel_program n`: each closed definition `x ≜ …` becomes the Lean definition
    `n.x : Except String (Tab A B)`, its term's code (`Tm.gen`) run in the empty context (`Rel.runE`), or the
    message of the op that failed. Here the program is elaborated (`elabE`, `build`) to its core terms `Tm`, as a
    run does; `Expand.emit` (`Rel.Run.Lang.TmGen`) numbers their closed parts into one share table per program and
    emits each term as the `Expr` that builds it (`tmE`). -/

namespace Rel.Lang

open Tab Rel.Alg

/-- An object variable left in an object. -/
def OTy.poly : OTy → Bool
  | .mv _ => true
  | .prod a b | .sum a b => a.poly || b.poly
  | .arr a => a.poly
  | .base _ => false

def objInfo (env : Env) (n : String) : ObjDef → EM ObjInfo
  -- one element is the terminal object: stored at `1`, no column (`Obj.one`)
  | .elems ws => pure {
      ty := .base n, elems := ws, uni := some ⟨_, col ((List.range ws.length).map Int64.ofNat)⟩,
      seg := ws.length != 1, obj := if ws.length = 1 then .one else .long }
  | .range lo hi =>
    pure { ty := .base n, range := some (lo, hi), uni := some ⟨_, col ((List.range (hi + 1 - lo).toNat).map fun k : Nat => Int64.ofInt (lo + k))⟩, seg := lo == 0 }
  | .alias o => do let (t, _) ← (oty env [] o).run {}; pure { ty := t }
  | .num t => pure { ty := .base n, num := true, obj := .atom t }
  -- the object `Schema.obj` lays out, at the program's objects; `col` reads the columns back (`elabE`)
  | .schema cs => do
    let cs ← cs.mapM fun (c, o) => return (c, (← (oty env [] o).run {}).1)
    pure { ty := Schema.objAt (.base n) .prod cs, cols := cs }

/-- The definition `d` whose constant is `c`, as a use sees it. `prelude.perm` is its own converse, the one converse
    rule kept for a definition (`Tm.own`): `perm° = perm` is a theorem the language cannot derive from the fold
    `perm` is: it has no kernel, so it is no row. A prelude definition that is a row's constant `Prim.prelude`, given
    relations and not families, runs as that row's kernel. `imported`: `d` is another program's, so an error its body raises at a use names `c` and its
    line there, at the use; one about the arguments (at the use) passes as it is. -/
def useDef (c : Lean.Name) (imported : Bool) (d : Def) : Def :=
  { d with apply := fun p as => do
      let reword (e : Err) : M Arg :=
        throw (if e.pos == p then e else ⟨p, s!"in `{c}` (its line {e.pos.line}): {e.msg}"⟩)
      let row := prims.find? (·.prelude == some c)
      -- given a family, a row whose meaning commutes with keying (`keyLift`) runs once on the keyed families, as
      -- any row applied to one does
      match row, as.find? Arg.isFam with
      | some x, some (.fam _ I _ _) => if x.keyLift && as.length == x.sig.1.length then return ← appliedRowL I p x as
      | _, _ => pure ()
      let r ← if imported then tryCatch (d.apply p as) reword else d.apply p as
      -- the body's positions are its program's: at the use, so what `build` raises later is at the use
      -- a prelude definition with a row of its own runs as that row's constant
      -- given relations, not families, as its parameters are
      let rels := as.filterMap fun | .rel a s _ => some (a, s) | _ => none
      match c, r, row with
      | _, .rel q s t, some x =>
        if rels.length == as.length && as.length == x.sig.1.length then
          pure (.rel (.prim x ((x.sig.1.zip rels).map fun ((_, f), (a, s')) => x.pass p f a s') s t) s t)
        else pure (.rel (if imported then q.at p else q) s t)
      | `Rel.Programs.prelude.perm, .rel q s t, _ => pure (.rel (.own (q.at p)) s t)
      | _, .rel q s t, _ => pure (.rel (if imported then q.at p else q) s t)
      | _, .fam q i a b, _ => pure (.fam (if imported then q.at p else q) i a b) }

/-! ### Printing a relation with the program's names -/

/-- An array of the printed elements `xs`, as a literal's side reads it (§c): two or more juxtaposed, else
    bracketed; `item`: it stands next to others (in an array, after `inl`), so it is always bracketed. -/
def arrText (item : Bool) (xs : List String) : String :=
  Tup.render item (.arr (xs.map .leaf))

/-- An element printed with the program's names, as a literal's side reads it (§c): a named element by its name,
    a number as itself, an array by `arrText`, its elements as items. -/
def showEl (objs : Objs) (item : Bool) : OTy → (A : Obj) → A.El → String
  | .base n, .atom .i64, x =>
    let v : Int64 := x
    match objs.lookup n with
    | some i => if i.range.isSome then toString v else (i.elems[v.toInt.toNat]?).getD (toString v)
    | none => toString v
  -- an object declared at another atom: its word as a literal writes it (`wordText`)
  | .base _, .atom t, x => match elWord t x with | some w => wordText t w | none => "?"
  -- an object of one element (`1 = {∗}`): that element's name
  | .base n, .one, () => ((objs.lookup n).bind (·.elems.head?)).getD "()"
  | .prod a b, .prod A B, (x, y) => s!"({showEl objs false a A x}, {showEl objs false b B y})"
  | .sum a _, .sum A _, .inl x => s!"inl {showEl objs true a A x}"
  | .sum _ b, .sum _ B, .inr y => s!"inr {showEl objs true b B y}"
  | .arr a, .arr A, xs => arrText item (xs.map (showEl objs true a A))
  | _, _, _ => "?"

/-- The order a print lists elements in: a number by its value (`-2` before `-1`, `2` before `10`), a named
    element by its name, a pair and an array lexicographically, `inl` before `inr`. -/
def cmpEl (objs : Objs) : OTy → (A : Obj) → A.El → A.El → Ordering
  | .base n, .atom .i64, x, y =>
    let (v, w) : Int64 × Int64 := (x, y)
    if ((objs.lookup n).bind (·.range)).isSome then compare v.toInt w.toInt
    else compare (showEl objs false (.base n) (.atom .i64) x) (showEl objs false (.base n) (.atom .i64) y)
  -- at another atom by value: the order code of its word (`Kernel.ascOrd`, a float's totalOrder)
  | s, .atom t, x, y => match elWord t x, elWord t y, Kernel.ascOrd t with
    | some u, some v, some f => compare (f u) (f v)
    | _, _, _ => compare (showEl objs false s (.atom t) x) (showEl objs false s (.atom t) y)
  | .prod a b, .prod A B, (x, y), (x', y') => (cmpEl objs a A x x').then (cmpEl objs b B y y')
  | .sum a _, .sum A _, .inl x, .inl y => cmpEl objs a A x y
  | .sum _ b, .sum _ B, .inr x, .inr y => cmpEl objs b B x y
  | .sum _ _, .sum _ _, .inl _, .inr _ => .lt
  | .sum _ _, .sum _ _, .inr _, .inl _ => .gt
  | .arr a, .arr A, xs, ys =>
    let (xs, ys) : List A.El × List A.El := (xs, ys)
    ((xs.zip ys).foldl (fun (o : Ordering) (x, y) => o.then (cmpEl objs a A x y)) Ordering.eq).then (compare xs.length ys.length)
  | s, A, x, y => compare (showEl objs false s A x) (showEl objs false s A y)

/-- A relation printed as its set of pairs: each pair once (`Tab.canon`, `kasc` then `kseen`), sorted by `cmpEl`; the
    message of a kernel that could not run. -/
def showRel (objs : Objs) (s t : OTy) {A B : Obj} (R : Tab A B) : Except String String := do
  let ps := (← R.canon).toArray.qsort fun (x, y) (x', y') => ((cmpEl objs s A x x').then (cmpEl objs t B y y')) == .lt
  pure ("{" ++ (ps.mapIdx fun i (x, y) =>
    s!"{if i = 0 then "" else ", "}({showEl objs false s A x}, {showEl objs false t B y})").foldl (· ++ ·) "" ++ "}")

/-- A declared object as a print reads it: its names and range, no universe. -/
def infoOf (ty : OTy) (elems : List String) (range : Option (Int × Int)) : ObjInfo := { ty, elems, range }

/-- A `print`'s line, the term's text `x` and its value; and the value's ok bit. -/
def printText (A B : Obj) (objs : Objs) (x : String) (s t : OTy) (c : Except String (Tab A B)) : String × Bool :=
  match c >>= showRel objs s t with
  | .ok r => (s!"{x} = {r}", true)
  | .error e => (s!"{x}: {e}", false)

/-- A `check` at `p` that does not hold, `x ⊑ y` (and `y ⊑ x` for `=`), as its error; and the sides' ok bits. -/
def checkErr (A B : Obj) (objs : Objs) (p : Pos) (x y : String) (eq : Bool) (s t : OTy)
    (R S : Except String (Tab A B)) : Option Err × Bool :=
  let holds : Except String (Tab A B × Tab A B × Bool) := do
    let a ← R; let b ← S; pure (a, b, (← a.le b) && (!eq || (← b.le a)))
  (match holds with
   | .ok (_, _, true) => none
   | .ok (a, b, false) => some ⟨p, match showRel objs s t a, showRel objs s t b with
     | .ok r, .ok q => s!"check failed: {x} = {r}, {y} = {q}"
     | .error e, _ | _, .error e => s!"check failed: {x}, {y}: {e}"⟩
   | .error e => some ⟨p, s!"check {x}, {y}: {e}"⟩, R.toBool && S.toBool)

/-- A program's failures: each `check` that does not hold, and each term that threw (`Rel.runE`), named by `es`,
    `μ` cap included. -/
def failures (cs : List (Option Err × Bool)) (es : List (String × Option String)) : List Err :=
  cs.filterMap (·.1) ++ es.filterMap (fun (x, e) => e.map fun m => ⟨{}, s!"{x}: {m}"⟩)

namespace Expand

/-- A top-level term, a `print`'s or a `check` side's: closed, with its objects as the program names them. -/
abbrev Top := ((A : Obj) × (B : Obj) × Tm A B) × OTy × OTy

/-- A `check`: where, both sides' texts, `=` (else `⊑`), the objects as named, both sides at one type. -/
abbrev Chk := Pos × String × String × Bool × OTy × OTy × ((A : Obj) × (B : Obj) × Tm A B × Tm A B)

/-- The object variable of the family index class `i` at a call (§e): a name no declaration can write. -/
def idxVar (i : Nat) : String := s!"ι#{i}"

/-- The registry key of the constant of `c` at the argument forms `fs` and, per object variable, whether the call
    puts an unbounded number object there and whether one whose universe is an initial segment of ℕ (`nb`, `num` and
    `seg`): `c` itself when every argument is closed and no variable is either. -/
def formKey (c : Lean.Name) (fs : List Form) (nb : List (Bool × Bool) := []) : Lean.Name :=
  let k := if fs.all (· == (none, none)) then c
    else fs.foldl (fun k (t, i) => .num k ((match t with | none => 0 | some false => 1 | some true => 2) +
      3 * (match i with | some i => i + 1 | none => 0))) (c ++ `form)
  if nb.any (fun (u, s) => u || s) then nb.foldl (fun k (u, s) => .num k (u.toNat + 2 * s.toNat)) (k ++ `num) else k

/-- What a call reads of the constant `o` (`Sig`): the universes its body reads. -/
def sigOf (o : Once) : Sig :=
  let ⟨_, _, t⟩ := o.res
  { const := o.const, vars := o.gen.zip ((List.range o.gen.length).map t.fv.contains), tst := o.tst, kf := o.kf }

/-- The converse of `o`'s body, when it has one (`convTm`) and is not a pair test, and its constant. `convTm` takes
    a parameter for its own converse (`Tm.ConvOK`), true of one tested on pairs only: a body reading a parameter run
    on demand (`R : A ⟶ B`, whose converse is no parameter) has none. -/
def convOf (o : Once) : Option (Lean.Name × Res) :=
  let dem := o.res.2.2.dem && o.forms.zipIdx.any fun (f, i) => f == some false && o.res.2.2.fv.contains (o.gen.length + i)
  if o.tst || dem then none else match o.res with
    | ⟨A, B, t⟩ => (convTm t).toOption.map fun u => (o.const ++ `conv, ⟨B, A, u⟩)

/-- A statement `n.io` runs (IO design B), in statement order; a name is the spelling the program's statements reach
    it by: its own short name, an imported one's constant (`Parse.constOf`). -/
inductive Io
  /-- `input n : A ⟶ B from path`: the table of key columns `key` (`[]`: positions) and value columns `val`, read from
      the table directory `path`, or from the CSV file `path` with the header `csv`. -/
  | input (n : String) (A B : Obj) (key val : Schema) (csv : Option Db.CsvCols) (path : String)
  /-- A run-time definition: the body of its constant `c` run with its variables bound to the tables of the run-time
      names `deps` (`Expand.ioGo`). -/
  | defn (n : String) (c : Lean.Name) (deps : List String)
  /-- `output n to path`: the table of `n` written as `key ⟶ val`, to the table directory `path`, or to the CSV file
      `path` with the header `csv`; `n` a run-time name or the closed definition whose constant is `closed`. -/
  | output (n : String) (A B : Obj) (key val : Schema) (csv : Option Db.CsvCols) (path : String)
      (closed : Option Lean.Name)

/-- `s` with each name `f` renames. -/
def Io.rename (f : String → String) : Io → Io
  | .input n A B k v c p => .input (f n) A B k v c p
  | .defn n c ds => .defn (f n) c (ds.map f)
  | .output n A B k v c p cl => .output (f n) A B k v c p cl

/-- The run-time names in scope (IO design A.2), in statement order: each input, and each definition whose body
    mentions one, with its declared type and, for a definition, the run-time names it mentions. -/
abbrev Rt := List (String × Param × Option (List String))

/-- What a program reads: its closed definitions, its prints (text and term), its checks, its objects, its
    definitions elaborated once, and the statements `n.io` runs, its imports' inputs and run-time definitions first. -/
abbrev Read := List (String × Res) × List (String × Top) × List Chk × Objs × List Once × List Io

/-- The object variables of a definition, in order, each once: its parameters' then its type's. -/
def varsOf (qs : List Param) (ty : OExp × OExp) : List String :=
  (qs.flatMap (fun P => match P.ty with | some (x, y) => x.vars ++ y.vars | none => []) ++ ty.1.vars ++ ty.2.vars).eraseDups

/-- The body of `n(qs) ≜ e : ty` at the objects `objs`, its object variables `vs` rigid: each an object of its own
    whose universe is the variable of its place, each parameter the variable after them in its form `fs` (`Form`):
    closed, tested on pairs, or a family over the index variable of its class, lifted as `mkDef` lifts a use (§e);
    its parameters' objects and demand bits as the constant takes them, its elaboration and the objects it solved,
    `specs` the constants built so far. -/
def elabOnce (env : Env) (p : Pos) (n : String) (qs : List Param) (e : Expr) (ty : OExp × OExp) (vs : List String)
    (fs : List Form) (objs : Objs) (specs : List Once) : EM (List (Obj × Obj × Bool) × Arg × St) := do
  let nv := vs.length
  let rigid := vs.map fun v => (v, OTy.base v)
  let env' := { env with objs }
  let ((r, os), st) ← (do
    let mut args : List Arg := []
    let mut os : List (Obj × Obj × Bool) := []
    for ((P, t, i), j) in (qs.zip fs).zipIdx do
      let some (x, y) := P.ty | throw ⟨p, s!"parameter '{P.name}' declares no type"⟩
      let s ← oty env rigid x; let u ← oty env rigid y
      let S ← objOf objs p s; let U ← objOf objs p u
      -- a family is the relation from its index (§e); either way the parameter takes its argument's form `t`
      let (A, B) ← match i with
        | some i =>
          let I := OTy.base (idxVar i)
          args := args ++ [.fam (.var p (nv + j) I (.prod s u) t) I s u]; pure (← objOf objs p I, .prod S U)
        | none => args := args ++ [.rel (.var p (nv + j) s u t) s u]; pure (S, U)
      os := os ++ [match t with
        | some true => (.prod A B, .prod A B, true) | some false => (A, B, true) | none => (A, B, false)]
    let r ← (mkDef env' n p qs (.rel e) (some ty)).apply p args
    -- a variable only the declared result names is rigid too, as `mkDef` leaves it to the use
    let (s, u) := match r with | .rel _ s u => (s, u) | .fam _ _ a b => (a, b)
    declared env' p n rigid ty s u
    settleOpen env' p [r.plain.1]
    settleUses
    pure (r, os) : M (Arg × List (Obj × Obj × Bool))).run { fixes := nv + qs.length, specs, objs }
  pure (os, r, st)

/-! ### A row of `prims` at its objects -/

open Lean in deriving instance ToExpr for Rel.Obj
open Lean in deriving instance ToExpr for MVarId
open Lean in deriving instance ToExpr for OTy
open Lean in deriving instance ToExpr for Rel.Db.CsvShape

open Lean in def oE (A : Obj) : Lean.Expr := toExpr A
open Lean in def uE (n : USize) : Lean.Expr := mkApp (mkConst ``USize.ofNat) (toExpr n.toNat)
open Lean in def g (n : Lean.Name) (as : Array Lean.Expr) : Lean.Expr := mkAppN (mkConst n) as

/-- The row a spine of `arg`s is headed by, and its relations in order. -/
def primOf : {A B : Obj} → Tm A B → Option (Prim × List Res)
  | _, _, .prim r => some (r, [])
  | _, _, .arg f x => (primOf f).map fun (r, xs) => (r, xs ++ [⟨_, _, x⟩])
  | _, _, _ => none

/-- The type `Rel A B` of a code of `t : Tm A B`. -/
def fnTy (t : Res) : Lean.Expr := g ``Rel.Rel #[oE t.1, oE t.2.1]

/-- The wrappers a row's constant runs under (`GenK.ofVals` …), tried in order. -/
def primWrappers : List Lean.Name :=
  [``GenK.ofVals, ``GenK.after, ``GenK.elems, ``GenK.testVals, ``GenK.testAfter, ``GenK.stepAfter, ``GenK.ofRel,
   ``GenK.onKeys]

open Lean Meta in
/-- `c` at fresh metavariables: those whose type `sel` picks are `hs` in order (each given with its type), and `ok`
    holds of all of them and the type; none when a type differs or one is left open. The one rule by which `primE`
    fits a wrapper and a row's constant. -/
def fitConst (c : Lean.Name) (sel : Lean.Expr → MetaM Bool) (hs : Array (Lean.Expr × Lean.Expr))
    (ok : Array Lean.Expr → Lean.Expr → MetaM Bool) (args : List Lean.Expr := []) :
    MetaM (Option Lean.Expr) := withoutModifyingState do
  let k := mkAppN (← mkConstWithFreshMVarLevels c) args.toArray
  let (ms, _, ty) ← forallMetaTelescope (← inferType k)
  let ps ← ms.filterM fun m => do sel (← inferType m)
  unless ps.size == hs.size do return none
  for (m, x, t) in ps.zip hs do
    unless ← isDefEq (← inferType m) t do return none
    m.mvarId!.assign x
  unless ← ok ms ty do return none
  let v ← instantiateMVars (mkAppN k ms)
  return if v.hasMVar then none else some v

open Lean Meta in
/-- A binder of a row's constant that is no relation: an object or a size, solved by unification (`primE`). -/
def objOrSize (t : Lean.Expr) : MetaM Bool := return (← whnfR t).isConstOf ``Obj || (← whnfR t).isConstOf ``USize

open Lean Meta in
/-- Row `r`'s constant at `A ⟶ B` given its relations `xs` (codes with their types), under the first wrapper it
    fits: the wrapper's `Rel` parts are `xs`, its function's explicit binders the constant's that are relations (not
    `objOrSize`), every other solved by unifying the types. The constant is the row's
    `kernRows` operator. -/
def primE (r : Prim) (A B : Obj) (xs : Array (Lean.Expr × Lean.Expr)) : MetaM (Option Lean.Expr) := do
  let some (c, args) := kernRows.lookup r.sym | return none
  let w? ← primWrappers.findSomeM? fun w => fitConst w (fun t => pure (t.isAppOf ``Rel.Rel)) xs fun ws wty => do
    let some f := ws.back? | return false
    unless ← isDefEq wty (g ``Rel.Rel #[oE A, oE B]) do return false
    let v? ← forallTelescope (← instantiateMVars (← inferType f)) fun ys body => do
      let es ← ys.filterM fun y => return (← getFVarLocalDecl y).binderInfo.isExplicit
      let some v ← fitConst c (fun t => return !(← objOrSize t)) (← es.mapM fun y => return (y, ← inferType y))
          (fun _ ty => isDefEq ty body) args | return none
      some <$> mkLambdaFVars ys v
    let some v := v? | return false
    isDefEq f v
  if w?.isSome then return w?
  -- a constant that is itself a code of its relations, any number of them (`GenK.foldI`): its `Rel` binders are
  -- `xs`, its objects solved by unifying; tried last, so no wrapper's fit changes
  fitConst c (fun t => pure (t.isAppOf ``Rel.Rel)) xs (fun _ ty => isDefEq ty (g ``Rel.Rel #[oE A, oE B]))
      args

/-- Each fit `primFit` made, by row, objects and its relations' types. Process-wide rather than in the environment:
    the fit reads only this library's constants, and a backtracking elaborator (`restore`) would drop an env's. -/
initialize primMemo : IO.Ref (Std.HashMap (String × Lean.Expr × Lean.Expr × Array Lean.Expr) (Option Lean.Expr)) ←
  IO.mkRef {}

open Lean Meta in
/-- Row `r` at `A ⟶ B` fitted once per relation types `ts` (`primE` at fresh relations), closed over the relations:
    `fun xs => e`, applied by `Expr.beta`. Every caller goes through it, so a program pays per distinct instance, not
    per occurrence. -/
def primFit (r : Prim) (A B : Obj) (ts : Array Lean.Expr) : MetaM (Option Lean.Expr) := do
  let k := (r.sym, oE A, oE B, ts)
  if let some v := (← primMemo.get)[k]? then return v
  let v ← withLocalDeclsDND (ts.map (`x, ·)) fun xs => do
    match ← primE r A B (xs.zip ts) with | some e => some <$> mkLambdaFVars xs e | none => pure none
  primMemo.modify (·.insert k v); pure v

open Lean Meta in
/-- Each row in `t` fits its constant at its objects (`primFit`), its relations variables of their types. A row at an
    object variable's placeholder (`varObj`) that its constant reads at `.long` (`sum` at `[β]`) does not, and that
    is how `once` finds the variable a number object. -/
partial def primsFit {A B : Obj} (t : Tm A B) : MetaM Bool := do
  let some (r, as) := primOf t | t.inner.allM fun ⟨_, _, c⟩ => primsFit c
  pure (← primFit r A B (as.toArray.map fnTy)).isSome <&&> as.allM fun ⟨_, _, c⟩ => primsFit c

/-- The placeholders of a constant of `n` with `k` object variables in `env`: atoms no object in scope is stored at,
    one per variable, or the definition is refused by name. A refusal of the definition, not of one form of it, so
    `callDef` checks it where its fallback to the expansion cannot swallow it. -/
def placeholdersFor (env : Env) (p : Pos) (n : String) (k : Nat) : Except Err (List Rel.QAtomicType) := do
  let ph := placeholdersOf env.objs
  if ph.length < k then
    throw ⟨p, s!"`{n}` has {k} object variables, and only {ph.length} atoms no object in scope is stored at " ++
      s!"stand for them ({ph.map atomName})"⟩
  pure ph

/-- `n(qs) ≜ e : ty` built once (`elabOnce`); a body that needs keys stays a plan on them, and one that builds no
    relation but tests on pairs is its pair test (`test`, §a). A variable is generic (`varObj`) when the body builds
    with it an object of its own, else `.long`, a number object (`succ`, `sum` …). A body that does not build so is
    an error. `k` its registry key, `c` its constant, `fs` its parameters' forms; with the constants built so far
    and on the way (`specs`). -/
def once (env : Env) (p : Pos) (n : String) (qs : List Param) (e : Expr) (ty : OExp × OExp) (vs : List String)
    (k c : Lean.Name) (fs : List Form) (nb : List (Bool × Bool)) (specs : List Once) :
    EM (Option Once × List Once) := do
  -- per variable: generic over its object, and given its universe; one the call puts an unbounded number object at
  -- is `num`, one it puts an initial segment of ℕ at is `seg` (`nb`), so a row with a `dfn` there runs fused
  -- (`build`), as it does outside a body
  let ph ← liftExcept (placeholdersFor env p n vs.length)
  let run (fl : List (Bool × Bool)) (deferred := false) : EM (Once × List Once) := do
    let objs := vs.zipIdx.map (fun (v, k) =>
      let (gen, uni) := fl.getD k (false, true)
      let obj := if gen then (varObj ph k).getD .long else .long
      let (num, seg) := nb.getD k (false, false)
      (v, ({ ty := .base v, uniVar := if uni then some k else none, obj, num, seg, ovar := true, deferred } :
        ObjInfo))) ++ env.objs
    let (os, r, st) ← elabOnce env p n qs e ty vs fs objs specs
    let (q, _, _) := r.plain
    let gen := fl.map (·.1)
    -- a family that does not build whole (its index has no universe) builds keyed, run on the (key, source) pairs
    let kq := match r with | .fam q i a b => some (keyed i q a b) | .rel .. => none
    let mk (res : Res) (tst kf : Bool) : Once × List Once :=
      ({ key := k, const := c, gen, ph, params := os, forms := fs.map (·.1), res, tst, kf }, st.specs)
    -- a term whose rows do not fit their objects (`primsFit`) does not build
    let fits (x : Except Err Res) : EM (Except Err Res) := do
      if let .ok ⟨A, B, t⟩ := x then unless ← primsFit t do
        return .error ⟨p, s!"`{n}`: a row fits none of {primWrappers} at {oE A} → {oE B}"⟩
      pure x
    let mc ← Lean.getMCtx
    let tst := (test objs mc p q).map fun ⟨A, B, t⟩ => (⟨.prod A B, .prod A B, t⟩ : Res)
    match ← fits (build objs mc p q), ← (kq.map (build objs mc p)).mapM fits, ← fits tst with
    | .ok res, _, _ => pure (mk res false false)
    | .error _, some (.ok res), _ => pure (mk res false true)
    | .error _, _, .ok res => pure (mk res true false)
    | .error err, _, .error _ => throw err
  let mut fl := vs.map fun _ => (false, true)
  -- a body that does not build with every variable `.long` but builds with the number checks on its variables left
  -- to each use (`ObjInfo.deferred`) is well formed and has no constant: each use builds its expansion at the call's
  -- objects, where those checks run (monomorphised, `Pre.call`'s `alt`); a body that fails both is refused with `err`
  let some first ← tryCatch (some <$> run fl) fun err => do
      discard <| tryCatch (run fl (deferred := true)) fun _ => throw err
      pure none
    | return (none, specs)
  let mut out := first
  -- with every variable `.long` the body built above, so one whose own object fails the build is a number object;
  -- one that builds without its universe takes the routes run on demand or tested on pairs, which every object has,
  -- where its universe would refuse a call at an array (§a)
  for i in List.range vs.length do
    for b in [(true, false), (true, true)] do
      -- a body that built stays built: a pair test runs nowhere (`build`'s `.call`)
      if let some o := (← tryCatch (some <$> run (fl.set i b)) fun _ => pure none) then if o.1.tst ≤ out.1.tst then fl := fl.set i b; out := o; break
  pure (some out.1, out.2)

/-- `n(qs) ≜ e : ty`, defined at `dp` in `env`, `c` its constant, `vs` its object variables, `d` its expansion:
    each use is a call (`Pre.call`) of the constant of `n` at its arguments' forms (`Form`, module design §5 M): an
    argument that closes on its source is passed closed, one that does not but tests on pairs as its pair test
    (§a), a family as the relation `I ⟶ A×B`, its index an object variable of the constant (§e). That constant is
    the registry's (`calls`) or one built so far (`St.specs`); else it is built here (`once`), named its key when
    `n` is the program `emitter`'s, else under `emitter`. The expansion gives the call's type and is what the
    analyses read. -/
def callDef (env : Env) (dp : Pos) (n : String) (qs : List Param) (e : Expr) (ty : OExp × OExp) (vs : List String)
    (c emitter : Lean.Name) (calls : Lean.Name → Option Once) (d : Def) : Def :=
  { d with apply := fun p as => do
      let r ← d.apply p as
      let (bs, m) ← (qs.zip as).foldlM (fun (bs, m) (P, a) => do
        let (b, j, m) ← bind env p P a m; pure (bs ++ [(b.2, j)], m)) (([], []) : List (Arg × Option OTy) × List (String × OTy))
      -- an argument that needs keys (`≠`) is read on its source's universe, as a top-level term is (`top`); the
      -- universe is looked up at `build`, in the objects of the program making the call, not of the one defining `n`
      let why := s!"`{c}`'s argument runs in no form it takes: closed, on demand or tested on pairs"
      -- a variable only the declared result names is fixed by the result's type, as `declared` fixes it; first, so
      -- the arguments' objects are as solved as the use makes them when their forms are tried below
      let m ← vs.foldlM (fun m v => do if (m.lookup v).isSome then pure m else return (v, ← fresh) :: m) m
      let (s, t) := match r with | .rel _ s t => (s, t) | .fam _ _ a b => (a, b)
      unify p "" s (← oty env m ty.1); unify p "" t (← oty env m ty.2)
      let mut ix : Array OTy := #[]
      let mut fs : List Form := []
      let mut xs : List (Pre × Bool) := []
      -- the forms with each argument that needs keys passed on demand (`fsL`, `xsL`): tried first, see below
      let mut fsL : List Form := []
      let mut xsL : List (Pre × Bool) := []
      for (b, j?) in bs do
        let (x, a, a') := b.plain
        -- an argument whose objects only the use's context solves, after this call returns, has no form yet: the
        -- use is the expansion, which reads the arguments where `build` has every object solved. Its type's objects,
        -- and those inside it that `settleOpen` settles last (a literal's, `nil`'s source): a form chosen before
        -- reads a literal at no object, in a generic body (`litTy`) or not
        -- all read off what `x` computes: a variable of a call's body (`callOf`) is its argument (`St.args`)
        let mc ← Lean.getMCtx; let xe := (← get).expand x
        let inner := xe.lits.flatMap (fun (_, s, t, _, _) => [s, t]) ++ xe.nilSrcs
        if ([a, a'] ++ inner).any fun o => !(zonk mc o).mvs.isEmpty then return r
        let (ix', k?) ← idxClass ix j?; ix := ix'
        -- the first form the argument (a family: its relation from the index) builds in: closed, run on demand,
        -- tested on pairs; else closed, whose build reports why
        let st ← get; let mc ← Lean.getMCtx
        let bx := build st.objs mc p xe
        let f : Option Bool :=
          if (build st.objs mc p (Pre.close p xe a why)).toOption.isSome then none
          else if bx.toOption.isSome then some false
          else if (test st.objs mc p xe).toOption.isSome then some true else none
        fs := fs ++ [(f, k?)]; xs := xs ++ [(if f.isNone then Pre.close p x a why else x, f == some true)]
        -- closed, an argument that needs keys would be read on its source's whole universe (`closeRes`); on demand it
        -- runs bounded by what the body composes it with, as the inlined body runs it
        let fl := match bx with | .ok ⟨_, _, t⟩ => if t.dem then some false else f | .error _ => f
        fsL := fsL ++ [(fl, k?)]; xsL := xsL ++ [(if fl.isNone then Pre.close p x a why else x, fl == some true)]
      let some us := vs.mapM (m.lookup ·) | throw ⟨p, s!"internal: `{c}` has an object variable no type names"⟩
      -- the variables this call puts an unbounded number object at: the constant is built at them (`once`); an
      -- object still open here stays open in the call, so `build` knows the constant did not see it (`.call`)
      let mc ← Lean.getMCtx; let objs := (← get).objs
      let us := us.map (zonk mc)
      let nb := us.map fun u => (unbounded objs u, initSeg objs u)
      let get? (fs : List Form) : M (Option Once) := do
        let key := formKey c fs nb
        match calls key, (← get).specs.find? (·.key == key) with
        | some o, _ | none, some o => pure (some o)
        | none, none => do
          let k := if c.getPrefix == emitter then key else emitter ++ key
          let vs := vs ++ (List.range ix.size).map idxVar
          -- too few placeholders refuses the definition (an index variable counts), so it is not swallowed below
          let _ ← liftExcept (placeholdersFor env dp n vs.length)
          -- a body that does not build alone at these forms (a family it reads whole, which only the use's
          -- context keys, §e) is no constant: the use is the expansion, whose build reports any error in its words
          match ← (once env dp n qs e ty vs key k fs nb (← get).specs).run with
          | .ok (some o, specs) => modify (fun st => { st with specs := specs ++ [o] }); pure (some o)
          | .ok (none, _) | .error _ => pure none
      -- the arguments that need keys on demand where the body builds so (it composes them with what bounds them),
      -- else closed on their sources' universes, where a body that reads them whole needs them
      let (o?, ys) ← if fsL == fs then pure (← get? fs, xs) else match ← get? fsL with
        | some o => pure (some o, xsL)
        | none => pure (← get? fs, xs)
      let some o := o? | return r
      -- a call's body sees only the variables its call binds (`Code.args`): one read beyond them would run as `𝟘`;
      -- checked here, where the fallback to the expansion cannot swallow it
      let free := o.res.2.2.fv.eraseDups.filter (!o.binds.contains ·)
      unless free.isEmpty do
        throw ⟨p, s!"internal: `{o.const}`'s body reads the variables {free}, which its call binds not ({o.binds})"⟩
      xs := ys
      let { const := k, vars := fl, tst, kf } := sigOf o
      let (ks, ph, t, cv) := (o.binds, o.ph, o.res, convOf o)
      let us := us ++ ix.toList
      unless us.length == fl.length do
        throw ⟨p, s!"internal: `{k}` has {fl.length} object variables in the registry, {us.length} here"⟩
      let (q, a, b) := r.plain
      let call := Pre.call p k (us.zip fl) (xs.map (·.1)) (xs.map (·.2)) q a b ks ph t cv tst
      match r, kf with
      | .rel .., _ => pure (.rel call a b)
      | .fam _ i x y, false => pure (.fam call i x y)
      -- the constant `K : I×x ⟶ y` as the family `I ⟶ x×y`: the identity family then `K` (`compSh`), which
      -- `keyed` reads back as `⟨π₁,π₂𝟙⟩K`, so a use keys it as it keys any lifted composite
      | .fam _ i x y, true =>
        let call := Pre.call p k (us.zip fl) (xs.map (·.1)) (xs.map (·.2)) (keyed i q x y) (.prod i x) y ks ph t cv tst
        pure (.fam (compSh i x x (liftConst i p (.id x) x x).1 call) i x y) }

/-- A top-level term, `r` its elaboration `e` with the objects `st`: closed on its source's universe when it needs
    keys, refused where that object has none. -/
def top (env : Env) (mc : Lean.MetavarContext) (p : Pos) (e : Expr) (r : Arg) : Except Err Top := do
  let (q, s, t) := r.plain
  let ⟨A, B, tm⟩ ← build env.objs mc p (.close p q s noLeft)
  if !tm.dem then pure (⟨A, B, tm⟩, zonk mc s, zonk mc t) else throw ⟨p, s!"{e.show}: {zonk mc s} has no universe; compose a set of its elements before it (§a)"⟩

/-- `check e = f` at `p` (`⊑` when `eq` is false): the two sides
    elaborated together, one type, an object one side leaves open being the other's (§c); with the constants
    `specs` built so far, returned with the ones its calls build. -/
def checkOf (env : Env) (p : Pos) (e f : Expr) (eq : Bool) (specs : List Once) : EM (Chk × List Once) := do
  let ((r, r'), st) ← (do
    let r ← elabE env none e; let r' ← elabE env none f
    let (_, s, t) := r.plain; let (_, s', t') := r'.plain
    let mc ← Lean.getMCtx
    try unify p "" s' s; unify p "" t' t
    catch _ => throw ⟨p, s!"check: the sides have types {zonk mc s} ⟶ {zonk mc t} and {zonk mc s'} ⟶ {zonk mc t'}"⟩
    settleOpen env p [r.plain.1, r'.plain.1]
    settleUses
    pure (r, r') : M (Arg × Arg)).run { specs, objs := env.objs }
  let mc ← Lean.getMCtx
  let (⟨A, B, R⟩, s, t) ← top env mc p e r
  let (⟨A', B', S⟩, s', t') ← top env mc p f r'
  if h : A' = A ∧ B' = B then pure ((p, e.show, f.show, eq, s, t, ⟨A, B, R, h.1 ▸ h.2 ▸ S⟩), st.specs)
  else throw ⟨p, s!"check: the sides have types {s} ⟶ {t} and {s'} ⟶ {t'}"⟩

/-- The CSV columns of a side written `o` (IO design D), each with the labels that name it, outermost first, the
    object as written and as resolved. A schema's columns are its fields; a product's are its factors' columns, a factor
    that is a named object labelling its own (`Trade×(1+Quote)`: `Trade.sym` … `Quote.sym` …; `K×N`: `K`, `N`); a
    sum `1+S` (`Obj.opt`) is one column `1+V` per column `V` of `S`, labelled as `S`'s, so the `1` is every one of
    them null together; any other object is one column. `top`: `o` is the whole side, whose own name labels nothing. -/
def csvLeaves (env : Env) (o : OExp) (top : Bool) : EM (List (List String × OExp × OTy)) := do
  let t ← (oty env [] o).run' {}
  match o with
  | .name _ n =>
    let pre := if top then [] else [n]
    match env.obj? n with
    | some i => if i.cols.isEmpty then pure [(pre, o, t)] else pure (i.cols.map fun (c, f) => (pre ++ [c], f.exp, f))
    | none => pure [(pre, o, t)]
  | .prod a b => return (← csvLeaves env a false) ++ (← csvLeaves env b false)
  | .sum a b =>
    let u ← (oty env [] a).run' {}
    return (← csvLeaves env b top).map fun (ls, e, s) => (ls, .sum a e, .sum u s)
  | _ => pure [([], o, t)]

/-- The columns of an `input`'s or `output`'s type `A ⟶ B` (`what`: the statement), checked: the key's, none where
    `A` is the positions (a number object stored `.long`), then the value's; a schema object its columns, any other
    object the one column `key` or `val` (IO design A.1). For CSV the header is `csvLeaves`'s columns, named by their
    labels joined by `.`, or `key`, `val` where none labels them. Refused: an object variable, an undeclared object, a
    column twice; for CSV a column that is no atom, nullable atom or text, or that `Db.Csv.schema` refuses (C.3). Returned: `A`, `B`, the
    key's columns (`[]`: positions, whose `Schema.obj` is `.long`) and the value's as `Obj`s, and for CSV the header
    (`Db.CsvCols`: each column's atom and, for named elements, their names). -/
def ioCols (env : Env) (p : Pos) (what : String) (ty : OExp × OExp) (csv : Bool) :
    EM (Obj × Obj × Schema × Schema × Db.CsvCols) := do
  if let some v := (ty.1.vars ++ ty.2.vars).head? then
    throw ⟨p, s!"{what}: its type {OExp.arrow ty} has the object variable '{v}'; write a declared object there"⟩
  let side (o : OExp) (one : String) (key : Bool) : EM (Obj × Schema OTy) := do
    let t ← try (oty env [] o).run' {} catch e => throw ⟨e.pos, s!"{what}: {e.msg}"⟩
    let i := match o with | .name _ n => env.obj? n | _ => none
    pure (← liftExcept (objOf env.objs p t), match i with
      -- positions: the number object whose element is the row number (stored `.long`); any other key object is a
      -- key column, a keyed table (ruling H), whatever its atom
      | some i => if !i.cols.isEmpty then i.cols else if key && i.num && i.obj == .long then [] else [(one, t)]
      | none => [(one, t)])
  let (A, ks) ← side ty.1 "key" true
  let (B, vs) ← side ty.2 "val" false
  let cs := ks ++ vs
  if let .error m := Schema.check cs then throw ⟨p, s!"{what}: {m}"⟩
  -- each column's `Obj` is `objOf`'s, so `K.obj = A` and `S.obj = B` hold by construction
  let objs (S : Schema OTy) : EM Schema := S.mapM fun (c, t) => return (c, ← liftExcept (objOf env.objs p t))
  let (K, S) := (← objs ks, ← objs vs)
  let mut hdr : Db.CsvCols := []
  if csv then
    let elems (n : String) := ((env.obj? n).map (·.elems)).getD []
    let kl ← if ks.isEmpty then pure [] else csvLeaves env ty.1 true
    let leaves := kl.map ("key", ·) ++ (← csvLeaves env ty.2 true).map ("val", ·)
    for (one, ls, e, t) in leaves do
      let c := if ls.isEmpty then one else ".".intercalate ls
      -- the column's shape by its declared type and its stored object together; which atoms each takes is `schema`'s
      let col : Option (Db.CsvShape × QAtomicType × List String) := match t, ← liftExcept (objOf env.objs p t) with
        | .base n, .atom a => some (.atom, a, elems n)
        -- `1`: its one element's name, the code `0` of a long column (`Table.csvEncs`)
        | .base n, .one => some (.atom, .i64, elems n)
        | .sum _ (.base n), .opt (.atom a) => some (.null, a, elems n)
        | .arr (.base n), .arr (.atom a) => some (.text, a, elems n)
        | _, _ => none
      let some (s, a, ns) := col
        | throw ⟨p, s!"{what}: column '{c}' is {e.show}; a CSV field holds an atom, a nullable atom `1+V` (`1` an \
            object of one element) or a text `[C]`; declare it a table directory (drop `csv`)"⟩
      hdr := hdr ++ [(c, s, a, ns)]
    if let .error m := Schema.check hdr then throw ⟨p, s!"{what}: {m}"⟩
    -- a symbol column is checked as its texts: `n.io` interns them into the program's dictionary (`Table.readCsvDict`)
    if let .error m := Db.Csv.symText hdr >>= Db.Csv.schema then throw ⟨p, s!"{what}: {m}"⟩
  pure (A, B, K, S, hdr)

/-- The term for each run-time name the terms `es` of a `check` or `print` (`what`) at `p` reach (IO design A.4),
    put in place by `Expr.subst`: an input its `where` item in `bs`, a run-time definition applied to the terms of
    its parameters: a variant program's replacement rule, as one use of the parametric definition. `rt`: the
    run-time names in statement order, each with its declared type and its parameters (`none`: an input). Refused:
    an input the terms reach that `bs` does not give, a `bs` name that is no input. -/
def bindIns (rt : List (String × Param × Option (List String))) (p : Pos) (what : String) (es : List Expr)
    (bs : List (String × Expr)) : Except Err (List (String × Expr)) := do
  for (x, _) in bs do
    unless rt.any fun (y, _, ys) => y == x && ys.isNone do
      throw ⟨p, s!"{what}: `{x}` in its `where` is no input; a `where` here gives the table of an input " ++
        s!"(`input {x} : A ⟶ B from …`)"⟩
  -- each run-time name's inputs, and its term where every one of them is given
  let reach := rt.foldl (init := ([] : List (String × List String))) fun r (y, _, ys) =>
    r ++ [(y, match ys with | none => [y] | some ys => (ys.flatMap fun z => (r.lookup z).getD []).eraseDups)]
  -- a literal table stands where its input does at the input's declared type, so its words are read at the input's
  -- objects as a typed definition's are (`Expr.lit`'s `ty`)
  let σ := rt.foldl (init := ([] : List (String × Expr))) fun σ (y, P, ys) => match ys with
    | none => match bs.lookup y with
      | some (.lit q ps _) => σ ++ [(y, .lit q ps P.ty)]
      | some l => σ ++ [(y, l)]
      | none => σ
    | some ys =>
      if ys.all (σ.lookup · |>.isSome) then σ ++ [(y, Expr.app p y (ys.filterMap fun z => σ.lookup z))] else σ
  for y in es.flatMap (·.names) do
    if (rt.lookup y).isSome && (σ.lookup y).isNone then
      let x := (((reach.lookup y).getD []).find? (bs.lookup · |>.isNone)).getD y
      let ty := match rt.lookup x with | some (P, _) => P.ty.map OExp.arrow | none => none
      throw ⟨p, s!"{what} reaches the input `{x}`{if x == y then "" else s!" (through `{y}`)"}, which has no " ++
        s!"table at elaboration; give one: `{what} … where {x} ≜ " ++ "{…}`" ++
        (ty.map (s!", a table {·}")).getD ""⟩
  pure σ

/-- The spelling the statements use for the written name `y` (IO design A.2): an imported run-time name (in `rt` by its
    constant, `read`) its constant, which Lean's resolver reads in any scope; any other name as written. -/
def rtName (env : Env) (rt : Rt) (y : String) : String :=
  if (env.defs.lookup y).isSome || rt.any (·.1 == y) then y else match env.res y with
    | .ext e => if rt.any (·.1 == e.const.toString) then e.const.toString else y
    | _ => y

/-- `e` with each imported run-time name it mentions spelled as `rtName` spells it. -/
def rtNamesE (env : Env) (rt : Rt) (e : Expr) : Expr :=
  e.subst (e.names.filterMap fun y => let c := rtName env rt y; if c == y then none else some (y, .name e.pos c))

/-- The declarations of `prog`, in order, from the environment `env`: each closed definition (no keys) with its
    core term, each `print` and `check` with its terms; nothing evaluated: a definition is in scope as its built
    term. A parametric definition is called where `calls` gives its constant `own.x`; else, when `emitting`, it is
    built once for `emit` (`once`) after the program is read, and called in the bodies built after it; else
    expanded at each use. `specs`: the constants built so far at the forms calls take (`callDef`), `emitter` the
    program that emits those built here; returned with the ones built here, the run-time names in scope after it
    (`rt₀` those of its imports), and the statements `n.io` runs (`Io`). -/
def walk (prog : Program) (env : Env) (wrap : String → Def → Def) (own : Lean.Name) (calls : Lean.Name → Option Once)
    (emitting : Bool) (emitter : Lean.Name) (specs : List Once) (imported : Bool := false) (rt₀ : Rt := []) :
    EM (Env × List (String × Res) × List (String × Top) × List Chk × List Once × Rt × List Io) := do
  let mut env := env
  let mut specs := specs
  let mut pend : List (Env × Pos × String × List Param × Expr × (OExp × OExp) × List String × Def) := []
  let mut ds : List (String × Res) := []
  let mut pr : List (String × Top) := []
  let mut cs : List Chk := []
  -- the run-time names in scope (IO design A.2): each input, and each definition whose body mentions one, a
  -- parameter of the statements after it that mention it; with its declared type and, for a definition, its own
  let mut rt : Rt := rt₀
  let mut io : List Io := []
  -- each closed definition that computes a whole table, with its type; each output's path
  let mut whole : List (String × (OExp × OExp)) := []
  let mut outs : List (String × Pos) := []
  for d in prog do
    -- an imported program's prints, checks, theorems and outputs ran where it was defined; only its scope is read
    if imported && (match d with | .print .. | .check .. | .«theorem» .. | .output .. => true | _ => false) then
      continue
    match d with
    | .input p n ty csv path =>
      -- an imported program's input is the importer's (IO design A.2), read by the importer's `n.io`
      let (A, B, K, S, hdr) ← ioCols env p s!"input `{n}` from {if csv then "csv " else ""}\"{path}\"" ty csv
      rt := rt ++ [(n, ⟨n, some ty⟩, none)]
      io := io ++ [.input n A B K S (if csv then some hdr else none) path]
    | .output p n csv path =>
      let what := s!"output `{n}` to {if csv then "csv " else ""}\"{path}\""
      let n := rtName env rt n
      if let some q := outs.lookup path then
        throw ⟨p, s!"{what}: the output at line {q.line} writes \"{path}\" already; give each output a path of its own"⟩
      let ty ← match rt.lookup n, whole.lookup n with
        | some (P, _), _ => pure P.ty
        | none, some ty => pure (some ty)
        | none, none => throw ⟨p, if (env.defs.lookup n).isSome then
            s!"{what}: `{n}` computes no whole table: it has parameters or object variables, or needs keys (§a); " ++
              s!"output a definition at declared objects whose source has a universe, as `{n}` after a set of " ++
              "its sources"
          else s!"{what}: `{n}` is not defined before it; an output names a definition or an input of the program"⟩
      let some ty := ty | throw ⟨p, s!"{what}: `{n}` declares no type"⟩
      let (A, B, K, S, hdr) ← ioCols env p what ty csv
      io := io ++ [.output n A B K S (if csv then some hdr else none) path (if (rt.lookup n).isSome then none else some (Parse.constOf own n))]
      outs := outs ++ [(path, p)]
    | .obj _ n od =>
      -- an imported program's object is its constant's, so the importer's types name the same object (§2.3);
      -- an alias stays the object it stands for
      if imported then
        let c := (Parse.constOf own n).toString
        let i ← objInfo env c od
        env := { env with objs := (n, i) :: (c, i) :: env.objs }
      else env := { env with objs := (n, ← objInfo env n od) :: env.objs }
    | .defn p n ps b ty =>
      let b := match b with
        | .rel e => .rel (rtNamesE env rt e)
        | .test e f => .test (rtNamesE env rt e) (rtNamesE env rt f)
      -- the run-time names the body mentions, not its own parameters: the parameters of a definition written with
      -- none, the existing parametric definition (IO design A.2)
      let ys := rt.filter fun (y, _) =>
        (match b with | .rel e => e.names | .test e f => e.names ++ f.names).contains y && !ps.any (·.name == y)
      let ps ← match ys, ps, b with
        | [], _, _ => pure ps
        | _, [], .rel _ =>
          rt := rt ++ [(n, ⟨n, ty⟩, some (ys.map (·.1)))]
          io := io ++ [.defn n (Parse.constOf own n) (ys.map (·.1))]
          pure (ys.map (·.2.1))
        | (y, Y, _) :: _, _, _ => throw ⟨p, s!"`{n}` has parameters and mentions `{y}`, which has no table at " ++
            s!"elaboration; add the parameter `{y}{(Y.ty.map (s!" : {OExp.arrow ·}")).getD ""}` to `{n}` and pass " ++
            s!"`{y}` where `{n}` is used"⟩
      let missing := ps.any (·.ty.isNone) || match b with | .rel _ => ty.isNone | .test .. => false
      if missing then throw ⟨p, s!"`{n}` has no type; it is {← (inferSig env n ps b).run' {}}"⟩
      -- a definition whose type names an object variable is generic whatever its parameters, none included: each
      -- use instantiates its variables, one only the result names from the use's expected type (`mkDef`, `callDef`)
      match ps, b, ty, ty.toList.flatMap fun (a, b) => a.vars ++ b.vars with
      | [], .rel e, ty, [] =>
        let (r, st) ← (do
          let k := (← Lean.getMCtx).mvarCounter
          let r ← elabE env none e
          if let some ty := ty then let (_, s, t) := r.plain; declared env p n [] ty s t
          settleOpen env p [r.plain.1]
          let (q, s, t) := r.plain; generalise n p k [s, t] q
          settleUses
          pure r).run { specs, objs := env.objs }
        specs := st.specs
        let mc ← Lean.getMCtx; let (q, s, t) := r.plain
        let s := zonk mc s; let t := zonk mc t
        let each := wrap n (mkDef env n p [] (.rel e) ty)
        if s.poly || t.poly then env := { env with defs := (n, each) :: env.defs }; continue
        let q := if (uniOf env.objs s).isSome then Pre.close p q s noLeft else q
        let res@⟨_, _, tm⟩ ← match build env.objs mc p q, test env.objs mc p q with
          | .ok r, _ => pure r
          | .error _, .ok _ => env := { env with defs := (n, each) :: env.defs }; continue
          | .error e, .error _ => throw e
        env := { env with defs := (n, wrap n { arity := 0, apply := fun _ _ => pure (.rel (.tm res) s t) }) :: env.defs }
        if !tm.dem then
          ds := ds ++ [(n, res)]
          if let some ty := ty then whole := whole ++ [(n, ty)]
      | qs, b, ty, _ =>
        let d := mkDef env n p qs b ty
        match b, ty with
        | .rel e, some ty =>
          let vs := varsOf qs ty
          let c := Parse.constOf own n
          if (calls c).isSome then
            env := { env with defs := (n, wrap n (callDef env p n qs e ty vs c emitter calls d)) :: env.defs }; continue
          -- built once for `emit`, which adds its constant before any constant that calls it; the uses after it
          -- outside a body expand it, since its constant is built after the program is read, so that an error a use
          -- raises in the body, in the use's words, comes first
          if emitting then pend := pend ++ [(env, p, n, qs, e, ty, vs, d)]
        | _, _ => pure ()
        env :={ env with defs := (n, wrap n d) :: env.defs }
    | .print p e bs =>
      let (e, bs) := (rtNamesE env rt e, bs.map fun (x, l) => (rtName env rt x, l))
      let e := e.subst (← liftExcept (bindIns rt p "print" [e] bs))
      let (r, st) ← (do let r ← elabE env none e; settleOpen env p [r.plain.1]; settleUses; pure r).run { specs, objs := env.objs }
      specs := st.specs
      pr := pr ++ [(e.show, ← top env (← Lean.getMCtx) p e r)]
    | .check p e f eq bs =>
      let (e, f, bs) := (rtNamesE env rt e, rtNamesE env rt f, bs.map fun (x, l) => (rtName env rt x, l))
      let σ ← liftExcept (bindIns rt p "check" [e, f] bs)
      let (c, sp) ← checkOf env p (e.subst σ) (f.subst σ) eq specs; specs := sp; cs := cs ++ [c]
    | .«theorem» p n ps e f eq on hyps steps =>
      let ns := e.names ++ f.names ++ (on.map (·.names)).getD [] ++
        hyps.flatMap (fun (a, b) => a.names ++ (b.map (·.2.names)).getD []) ++ steps.flatMap (·.2.2.1.names)
      let ns := ns.map (rtName env rt)
      if let some (y, Y, _) := rt.find? fun (y, _) => ns.contains y && !ps.any (·.name == y) then
        throw ⟨p, s!"theorem `{n}` mentions `{y}`, which has no table at elaboration; state it with `{y}` a " ++
          s!"parameter: `theorem {n}({y}{(Y.ty.map (s!" : {OExp.arrow ·}")).getD ""}, …)`"⟩
      -- every term of the chain at the statement's type, the parameters at their declared ones (§3)
      let ((), st) ← (do
        let (_, env') ← bindSig env ps
        let (_, s, t) := (← elabE env' none e).plain
        for (q, x, what) in (p, f, "its right side") :: steps.map fun (q, _, x, _) => (q, x, "this step") do
          let (_, s', t') := (← elabE env' none x).plain
          let mc ← Lean.getMCtx
          try unify q "" s' s; unify q "" t' t
          catch _ => throw ⟨q, s!"theorem `{n}`: {what} {x.show} is {zonk mc s'} ⟶ {zonk mc t'}, " ++
            s!"the statement's {e.show} is {zonk mc s} ⟶ {zonk mc t}"⟩
        : M Unit).run { specs, objs := env.objs }
      specs := st.specs
      -- `on A`: each link of the chain (the statement itself when there is none) evaluated as a `check`
      if let some a := on then
        let mut x := e
        for (q, k, y) in if steps.isEmpty then [(p, eq, f)] else steps.map fun (q, k, y, _) => (q, k, y) do
          let (c, sp) ← checkOf env q (.comp a x) (.comp a y) k specs; specs := sp; cs := cs ++ [c]; x := y
  -- each in order, the ones before it called in its body, so a form its body gives one is built here (`callDef`)
  let mut mine : List (String × Def) := []
  for (env₀, p, n, qs, e, ty, vs, d) in pend do
    let c := Parse.constOf own n
    -- a constant already built at its key (`read`'s `seed`) is not built again, as `callDef` finds it in `specs`
    unless specs.any (·.key == c) do
      let (o, sp) ← once { env₀ with defs := mine ++ env₀.defs } p n qs e ty vs c c (qs.map fun _ => (none, none)) [] specs
      specs := sp ++ o.toList
    mine := (n, wrap n (callDef env₀ p n qs e ty vs c emitter calls d)) :: mine
  pure (env, ds, pr, cs, specs, rt, io)

/-- What the program `own` declares, `prog`, read after the programs `homes` its names reach (their definitions
    and objects), each read in order with its own resolver `res h` (module design §2.3), its definitions in scope
    for the next by constant. A definition whose constant `calls` holds is called, not expanded. With no `res`, a
    text read outside any Lean scope: each program sees those before it unqualified (`Parse.openAll`). `seed`: the
    constants this read builds, already built by an earlier read of the same text, so not elaborated again. -/
def read (calls : Lean.Name → Option Once) (homes : List (Lean.Name × Program)) (prog : Program)
    (own : Lean.Name := .anonymous)
    (res : Lean.Name → String → Found := fun h => Parse.openAll (homes.takeWhile (·.1 != h)))
    (seed : List Once := []) : EM Read := do
  let mut ext : List (Lean.Name × Def) := []
  let mut xo : List (Lean.Name × ObjInfo) := []
  -- the constants a call builds at a form no registered constant takes (`callDef`), which `own` emits
  let mut specs : List Once := seed
  -- the imports' run-time names and the statements `n.io` runs for them, each by its constant (`rtName`)
  let mut rt : Rt := []
  let mut io : List Io := []
  for (h, hp) in homes do
    let env : Env := { res := res h, ext, extObjs := xo, objs := xo.map fun (c, i) => (c.toString, i) }
    let (e, _, _, _, sp, rt', io') ←
      (walk hp env (fun k => useDef (Parse.constOf h k) true) h calls false own specs true rt).adapt (Err.inProg h.toString)
    specs := sp
    let cn (y : String) : String := if rt.any (·.1 == y) then y else (Parse.constOf h y).toString
    io := io ++ io'.map (·.rename cn)
    rt := rt'.map fun (y, P, ys) => (cn y, { P with name := cn P.name }, ys.map (·.map cn))
    for d in hp do
      if let some (k, x) := Parse.extOf h d then
        match x.obj, e.objs.lookup x.const.toString, e.defs.lookup k with
        | true, some i, _ => xo := (x.const, i) :: xo
        | false, _, some df => ext := (x.const, df) :: ext
        | _, _, _ => pure ()
  let env : Env := { res := res own, ext, extObjs := xo, objs := xo.map fun (c, i) => (c.toString, i) }
  let (e, ds, ps, cs, os, _, io') ← walk prog env (fun k => useDef (Parse.constOf own k) false) own calls true own specs
    false rt
  pure (ds, ps, cs, e.objs, os, io ++ io')

/-! ### Constants as the `Expr` that builds them (`tmE`), and the registry -/

open Lean Meta

/-- A term that needs no keys and reads no fixed-point variable: computed once, its slot of the share table
    (`Tm.number`). -/
def closed {A B : Obj} (t : Tm A B) : Bool := !t.dem && t.fv.isEmpty

/-- The constant `c : ty := v`, compiled, with the heartbeats a `def` command of its own would have: one
    `rel_program` command adds them all, and a program's count of constants is no measure of any one's cost.
    Regular hints, as `def` gives: an opaque `c` makes the kernel unfold the other side of `c =?= v` first. -/
def addConst (c : Name) (ty v : Lean.Expr) : MetaM Unit := withCurrHeartbeats do
  -- equal subterms as one object: `tmE` rebuilds an object's `oE` at each node, and every traversal after this
  -- (`getMaxHeight`, the compiler, the kernel) visits each object once instead of once per occurrence
  let v := ShareCommon.shareCommon' v
  let hints := .regular (getMaxHeight (← getEnv) v + 1)
  addAndCompile (.defnDecl { name := c, levelParams := [], type := ty, value := v, hints, safety := .safe })


/-- The bytes `b` as hex text, two lowercase digits a byte (`Gen.unhex` reads it back). -/
def hex (b : ByteArray) : String :=
  -- ASCII bytes then one UTF-8 check: `String.push` per digit dominated the expansion's profile
  let d (x : UInt8) : UInt8 := if x < 10 then 48 + x else 87 + x
  String.fromUTF8! (b.foldl (fun o x => (o.push (d (x / 16))).push (d (x % 16))) (.emptyWithCapacity (2 * b.size)))

/-- An atom column rebuilt from its `foR` payload as it is (`Gen.atom`), a boolean one included; a symbol, general or
    `pos` payload is not rebuilt, and says so. -/
def atomE (t : Rel.QAtomicType) (n : USize) (x : Arr t n) : Except String Lean.Expr :=
  match x.enc with
  | .foR m p => pure (g ``Gen.atom #[toExpr t, uE n, mkStrLit (hex m), mkStrLit (hex p)])
  | _ => throw s!"a column of {n} rows in a symbol, general or pos payload cannot be rebuilt"

/-- `rfl : Obj.band A B = o`, the proof `Gen.optV`/`Gen.sumV` take. -/
def bandRfl (o : Option Rel.QAtomicType) : Lean.Expr :=
  mkApp2 (mkConst ``Eq.refl [1]) (toTypeExpr (Option Rel.QAtomicType)) (toExpr o)

/-- A column rebuilt from its parts: each atom column from its payload (`atomE`), the rest by `Vals`'s shape. -/
def valsE : (A : Obj) → (n : USize) → Vals A n → Except String Lean.Expr
  | .atom t, n, x => atomE t n x
  | .prod a b, n, x => do
    pure (g ``Gen.pairV #[oE a, oE b, uE n, ← valsE a n x.1, ← valsE b n x.2])
  | .arr b, n, ⟨m, lo, hi, p⟩ => do
    pure (g ``Gen.arrV #[oE b, uE n, uE m, ← atomE .i64 n lo, ← atomE .i64 n hi, ← valsE b m p])
  -- the `Obj.band` fact is `rfl` at the closed objects the term names, checked when the term is added
  | .sum a b, n, s => match s.view with
    | .opt (t := t) _ x => match x.1 with
      | .foR m p => pure (g ``Gen.optV #[oE a, oE b, toExpr t, bandRfl (some t), uE n, mkStrLit (hex m), mkStrLit (hex p)])
      | _ => throw s!"a nullable column of {n} rows in a symbol, general or pos payload cannot be rebuilt"
    | .gen _ l r tag idx x y => do
      pure (g ``Gen.sumV #[oE a, oE b, bandRfl none, uE n, uE l, uE r, ← atomE .u1 n tag, ← atomE .i64 n idx,
        ← valsE a l x, ← valsE b r y])
  | .one, n, _ => pure (g ``Gen.oneV #[uE n])

def relE {A B : Obj} (R : Tab A B) : Except String Lean.Expr := do
  pure (g ``Gen.relV #[oE A, oE B, uE R.n, ← valsE A R.n R.key, ← valsE B R.n R.val])

/-- `x` and `y` are the same columns: of one object and one length, column by column the same payload (`encEq`). -/
def valsEq : (A : Obj) → {n : USize} → Vals A n → (C : Obj) → {m : USize} → Vals C m → Bool
  | .atom t, n, x, .atom u, m, y => decide (t = u) && decide (n = m) && encEq x.enc y.enc
  | .prod a b, _, x, .prod c d, _, y => valsEq a x.1 c y.1 && valsEq b x.2 d y.2
  | .arr b, n, ⟨_, lo, hi, p⟩, .arr d, m, ⟨_, lo', hi', q⟩ =>
    decide (n = m) && encEq lo.enc lo'.enc && encEq hi.enc hi'.enc && valsEq b p d q
  | .sum a b, n, s, .sum c d, m, s' => match s.view, s'.view with
    | .opt (t := t) _ x, .opt (t := u) _ y => decide (t = u) && decide (n = m) && encEq x.1 y.1
    | .gen _ _ _ tag idx x y, .gen _ _ _ tag' idx' x' y' =>
      decide (n = m) && encEq tag.enc tag'.enc && encEq idx.enc idx'.enc && valsEq a x c x' && valsEq b y d y'
    | _, _ => false
  | .one, _, _, .one, _, _ => true
  | _, _, _, _, _, _ => false

/-- `t` and `u`, of one constructor, agree in their fields that are not terms; a call's constant compared by its
    registry key (`key`), since each module names the constant it built `emitter ++ key`. A `callCv`'s converse
    constant is its constant's converse's (`convOf`), so it follows the constant. A row field by field, as
    `ToExpr Prim` rebuilds it, so `emit`'s check of `tmE` sees a field written wrong. -/
def Tm.fieldsEq (key : Lean.Name → Lean.Name) {A B C D : Obj} (t : Tm A B) (u : Tm C D) : Bool :=
  match t with
  | .val R => match u with | .val S => valsEq _ R.key _ S.key && valsEq _ R.val _ S.val | _ => false
  | .uni (A := A) U => match u with | .uni (A := C) V => valsEq A U C V | _ => false
  | .prim r => match u with
    | .prim r' => r.sym == r'.sym && r.sig == r'.sig && r.conv == r'.conv && r.written == r'.written &&
      r.prelude == r'.prelude && r.mono == r'.mono && r.dem == r'.dem && r.num == r'.num && r.ord == r'.ord &&
      match r.aop, r'.aop with | .ok a, .ok b => a == b | .error a, .error b => a == b | _, _ => false
    | _ => false
  | .atPos k => match u with | .atPos k' => k == k' | _ => false
  | .share k _ => match u with | .share k' _ => k == k' | _ => false
  | .var d k => match u with | .var d' k' => d == d' && k == k' | _ => false
  | .call ks c os _ => match u with | .call ks' c' os' _ => ks == ks' && key c == key c' && os == os' | _ => false
  | .callCv ks c _ os .. => match u with
    | .callCv ks' c' _ os' .. => ks == ks' && key c == key c' && os == os' | _ => false
  | .nu k .. => match u with | .nu k' .. => k == k' | _ => false
  | .mu k w n _ => match u with | .mu k' w' n' _ => k == k' && w == w' && n == n' | _ => false
  | .hylo k w _ => match u with | .hylo k' w' _ => k == k' && w == w' | _ => false
  | _ => true

/-- The first node, from the root, where the bodies `t`, `u` of one registry key differ, as its path of
    constructors (`ctor`); `none` when they are the same definition: per node its constructor, objects and other
    fields (`Tm.fieldsEq`), then its parts (`Tm.parts`, a `share`'s term, a call's body) in order. A call's body is
    entered: a `callOf` call has no registry key, so its name does not determine its body. -/
partial def Tm.diffAt (key : Lean.Name → Lean.Name) (ctor : Nat → String) (path : List String := []) :
    Res → Res → Option String
  | ⟨A, B, t⟩, ⟨C, D, u⟩ =>
    let p := path ++ [ctor t.ctorIdx]
    if t.ctorIdx != u.ctorIdx then some s!"{" / ".intercalate p} against `{ctor u.ctorIdx}`"
    else if !(A == C && B == D) then some s!"{" / ".intercalate p}: {repr A} ⟶ {repr B} against {repr C} ⟶ {repr D}"
    else if !Tm.fieldsEq key t u then some s!"{" / ".intercalate p}: its fields differ"
    else (t.inner.zip u.inner).findSome? fun (x, y) => Tm.diffAt key ctor p x y

-- a row that differs only in a flag is another row: `emit`'s check of `tmE` sees `ToExpr Prim` swap two fields
#guard (Tm.diffAt id toString [] ⟨.long, .long, .prim consRow⟩ ⟨.long, .long, .prim { consRow with mono := false }⟩).isSome

/-- An entry of the registry (module design §2.3): a definition elaborated once, its constant (`once`); a program's
    homes, the programs its names reach, in the order they are read (`read`); a program's scope, its namespace and
    `open`s, which its names resolve in; a definition or object of the program `home`. -/
inductive RegEntry
  | call (c : Name) (o : Once)
  | chain (n : Name) (ns : List Name)
  | prog (n : Name) (ns : Name) (opens : List OpenDecl)
  | ext (e : Ext) (home : Name)
  deriving Inhabited

/-- The registry, written only by `rel_program`: the constants a use may call (`walk`), each program's homes,
    the programs in the order they were defined (imported ones first) with their scopes, and every definition and
    object by its constant, with its program. -/
structure Registry where
  calls : List (Name × Once) := []
  chains : List (Name × List Name) := []
  progs : Array (Name × Name × List OpenDecl) := #[]
  exts : Std.HashMap Name (Ext × Name) := {}
  /-- Each `call` whose key `calls` already held, in the order added (`add`). -/
  again : Array Once := #[]

instance : Inhabited Registry := ⟨{}⟩

/-- A key is held once, by the `Once` registered first; one registered again goes to `again`. `callDef` builds a
    key only when the registry lacks it, so it comes again only from two imports, neither importing the other, that
    each built it under its own constant (`emitter ++ key`). Two constants are kept since Lean refuses to import
    one name declared by two modules. `Registry.call?` checks their bodies. -/
def Registry.add (r : Registry) : RegEntry → Registry
  | .call c o => if (r.calls.lookup c).isSome then { r with again := r.again.push o } else { r with calls := (c, o) :: r.calls }
  | .chain n ns => { r with chains := (n, ns) :: r.chains }
  | .prog n ns os => { r with progs := r.progs.push (n, ns, os) }
  | .ext e h => { r with exts := r.exts.insert e.const (e, h) }

initialize relRegistry : SimplePersistentEnvExtension RegEntry Registry ←
  registerSimplePersistentEnvExtension {
    addEntryFn := Registry.add
    addImportedFn := fun ess => ess.foldl (fun r es => es.foldl Registry.add r) {} }

open Lean Meta in
/-- The `Once` a call by each key reads, the first registered (`Registry.add`). A key registered again is the same
    definition when its `Once` agrees with the first in every field but the constant, bodies compared by `Tm.diffAt`;
    else the error names the key, both constants and the first node that differs. -/
def Registry.call? (r : Registry) : MetaM (Lean.Name → Option Once) := do
  unless r.again.isEmpty do
    let ctors := (← getConstInfoInduct ``Tm).ctors
    let ctor (i : Nat) := toString ((ctors.getD i .anonymous).componentsRev.headD .anonymous)
    let keys : Std.HashMap Lean.Name Lean.Name :=
      (r.calls.map (·.2) ++ r.again.toList).foldl (fun m o => m.insert o.const o.key) {}
    let key (c : Lean.Name) := keys.getD c c
    for o' in r.again do
      let some o := r.calls.lookup o'.key
        | throwError "rel registry: internal: `{o'.key}` registered again but never first"
      let why := if o.gen != o'.gen || o.params != o'.params || o.tst != o'.tst || o.kf != o'.kf
        then some "their object variables, parameters or forms differ" else Tm.diffAt key ctor [] o.res o'.res
      if let some d := why then
        throwError "rel registry: the key `{o.key}` is held by `{o.const}` and by `{o'.const}`, built by two \
          modules neither importing the other, with different bodies: at {d}"
  pure (r.calls.lookup ·)

end Expand

end Rel.Lang
