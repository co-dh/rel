import Lean
import Rel.Run.Lang.GenK
import Rel.Run.Lang.Elab
import Rel.Run.Lang.Parse
import Rel.Run.ValEq

/-! The expander of `rel_program n`: each closed definition `x ≜ …` becomes the Lean definition
    `n.x : Except String (Tab A B)`, a composition of `GenK` ops run in the empty context (`Rel.runE`), or the
    message of the op that failed. At elaboration time the program is elaborated (`elabE`, `build`) to its core term `Tm`, as a run does; the term is then read into a
    Lean `Expr` constructor by constructor. Every closed sub-term (no keys, no fixed-point variable) becomes one
    constant `n.c.<i>`, structurally equal ones the same constant, so it is computed once; a fixed point's body is a Lean `fun X => …`; a closed `≫`/`∩`/`−`/`\` runs as a bit-matrix plan. -/

namespace Rel.Lang

open Tab Rel.Alg

/-- An object variable left in an object. -/
def OTy.poly : OTy → Bool
  | .mv _ => true
  | .prod a b | .sum a b => a.poly || b.poly
  | .arr a => a.poly
  | .base _ => false

def objInfo (env : Env) (n : String) : ObjDef → EM ObjInfo
  | .elems ws => pure { ty := .base n, elems := ws, uni := some ⟨_, col ((List.range ws.length).map Int64.ofNat)⟩, seg := true }
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
      let r ← if imported then tryCatch (d.apply p as) reword else d.apply p as
      -- the body's positions are its program's: at the use, so what `build` raises later is at the use
      -- a prelude definition with a row of its own runs as that row's constant
      -- given relations, not families, as its parameters are
      let row := prims.find? (·.prelude == some c)
      let rels := as.filterMap fun | .rel a s _ => some (a, s) | _ => none
      match c, r, row with
      | _, .rel q s t, some x =>
        if rels.length == as.length && as.length == x.sig.1.length then
          pure (.rel (.prim x ((x.sig.1.zip rels).map fun ((_, f), (a, s')) => x.pass p f a s') s t none) s t)
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
  let ps := (← R.canon).toList.mergeSort fun (x, y) (x', y') => ((cmpEl objs s A x x').then (cmpEl objs t B y y')) != .gt
  pure ("{" ++ ", ".intercalate (ps.map fun (x, y) => s!"({showEl objs false s A x}, {showEl objs false t B y})") ++ "}")

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

/-- What a program reads: its closed definitions, its prints (text and term), its checks, its objects, and its
    definitions elaborated once. -/
abbrev Read := List (String × Res) × List (String × Top) × List Chk × Objs × List Once

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
    settleOpen env' p r.plain.1
    pure (r, os) : M (Arg × List (Obj × Obj × Bool))).run { fixes := nv + qs.length, specs, objs }
  pure (os, r, st)

/-! ### A row of `prims` at its objects -/

open Lean in deriving instance ToExpr for Rel.Obj
open Lean in deriving instance ToExpr for MVarId
open Lean in deriving instance ToExpr for OTy

open Lean in def oE (A : Obj) : Lean.Expr := toExpr A
open Lean in def uE (n : USize) : Lean.Expr := mkApp (mkConst ``USize.ofNat) (toExpr n.toNat)
open Lean in def bE (b : Bool) : Lean.Expr := toExpr b
open Lean in def g (n : Lean.Name) (as : Array Lean.Expr) : Lean.Expr := mkAppN (mkConst n) as

/-- The row a spine of `arg`s is headed by, and its relations in order. -/
def primOf : {A B : Obj} → Tm A B → Option (Prim × List Res)
  | _, _, .prim r => some (r, [])
  | _, _, .arg f x => (primOf f).map fun (r, xs) => (r, xs ++ [⟨_, _, x⟩])
  | _, _, _ => none

/-- The type `Gen.Fn t.dem A B` of a code of `t : Tm A B`. -/
def fnTy (t : Res) : Lean.Expr := g ``Gen.Fn #[bE t.2.2.dem, oE t.1, oE t.2.1]

/-- The wrappers a row's constant runs under (`GenK.ofVals` …), tried in order. -/
def primWrappers : List Lean.Name :=
  [``GenK.ofVals, ``GenK.after, ``GenK.elems, ``GenK.testVals, ``GenK.testAfter, ``GenK.stepAfter, ``GenK.ofRel]

open Lean Meta in
/-- `c` at fresh metavariables: those whose type `sel` picks are `hs` in order (each given with its type), and `ok`
    holds of all of them and the type; none when a type differs or one is left open. The one rule by which `primE`
    fits a wrapper and a row's constant. -/
def fitConst (c : Lean.Name) (sel : Lean.Expr → MetaM Bool) (hs : Array (Lean.Expr × Lean.Expr))
    (ok : Array Lean.Expr → Lean.Expr → MetaM Bool) : MetaM (Option Lean.Expr) := withoutModifyingState do
  let k ← mkConstWithFreshMVarLevels c
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
    fits: the wrapper's `Fn` parts are `xs`, its function's explicit binders the constant's that are relations (not
    `objOrSize`), every other solved by unifying the types. The constant is the row's
    `kernRows` operator. -/
def primE (r : Prim) (A B : Obj) (xs : Array (Lean.Expr × Lean.Expr)) : MetaM (Option Lean.Expr) := do
  let some c := kernRows.lookup r.sym | return none
  primWrappers.findSomeM? fun w => fitConst w (fun t => pure (t.isAppOf ``Gen.Fn)) xs fun ws wty => do
    let some f := ws.back? | return false
    unless ← isDefEq wty (g ``Gen.Fn #[bE true, oE A, oE B]) do return false
    let v? ← forallTelescope (← instantiateMVars (← inferType f)) fun ys body => do
      let es ← ys.filterM fun y => return (← getFVarLocalDecl y).binderInfo.isExplicit
      let some v ← fitConst c (fun t => return !(← objOrSize t)) (← es.mapM fun y => return (y, ← inferType y))
          fun _ ty => isDefEq ty body | return none
      some <$> mkLambdaFVars ys v
    let some v := v? | return false
    isDefEq f v

open Lean Meta in
/-- Each row in `t` fits its constant at its objects (`primE`), its relations variables of their types. A row at an
    object variable's placeholder (`varObj`) that its constant reads at `.long` (`sum` at `[β]`) does not, and that
    is how `once` finds the variable a number object. -/
partial def primsFit {A B : Obj} (t : Tm A B) : MetaM Bool := do
  let some (r, as) := primOf t | t.parts.allM fun ⟨_, _, c⟩ => primsFit c
  let ts := as.toArray.map fnTy
  withLocalDeclsDND (ts.map (`x, ·)) fun xs => do
    pure (← primE r A B (xs.zip ts)).isSome <&&> as.allM fun ⟨_, _, c⟩ => primsFit c

/-- The placeholders of a constant of `n` with `k` object variables in `env`: atoms no object in scope is stored at,
    one per variable, or the definition is refused by name. A refusal of the definition, not of one form of it, so
    `callDef` checks it where its fallback to the expansion cannot swallow it. -/
def placeholdersFor (env : Env) (p : Pos) (n : String) (k : Nat) : Except Err (List Rel.QAtomicType) := do
  let ph := placeholdersOf env.objs
  if ph.length < k then
    throw ⟨p, s!"`{n}` has {k} object variables, and only {ph.length} atoms no object in scope is stored at " ++
      s!"stand for them ({repr ph})"⟩
  pure ph

/-- `n(qs) ≜ e : ty` built once (`elabOnce`); a body that needs keys stays a plan on them, and one that builds no
    relation but tests on pairs is its pair test (`test`, §a). A variable is generic (`varObj`) when the body builds
    with it an object of its own, else `.long`, a number object (`succ`, `sum` …). A body that does not build so is
    an error. `k` its registry key, `c` its constant, `fs` its parameters' forms; with the constants built so far
    and on the way (`specs`). -/
def once (env : Env) (p : Pos) (n : String) (qs : List Param) (e : Expr) (ty : OExp × OExp) (vs : List String)
    (k c : Lean.Name) (fs : List Form) (nb : List (Bool × Bool)) (specs : List Once) : EM (Once × List Once) := do
  -- per variable: generic over its object, and given its universe; one the call puts an unbounded number object at
  -- is `num`, one it puts an initial segment of ℕ at is `seg` (`nb`), so a row with a `dfn` there runs fused
  -- (`build`), as it does outside a body
  let ph ← liftExcept (placeholdersFor env p n vs.length)
  let run (fl : List (Bool × Bool)) : EM (Once × List Once) := do
    let objs := vs.zipIdx.map (fun (v, k) =>
      let (gen, uni) := fl.getD k (false, true)
      let obj := if gen then (varObj ph k).getD .long else .long
      let (num, seg) := nb.getD k (false, false)
      (v, ({ ty := .base v, uniVar := if uni then some k else none, obj, num, seg, ovar := true } : ObjInfo))) ++ env.objs
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
  let mut out ← run fl
  -- with every variable `.long` the body built above, so one whose own object fails the build is a number object;
  -- one that builds without its universe takes the routes run on demand or tested on pairs, which every object has,
  -- where its universe would refuse a call at an array (§a)
  for i in List.range vs.length do
    for b in [(true, false), (true, true)] do
      -- a body that built stays built: a pair test runs nowhere (`build`'s `.call`)
      if let some o := (← tryCatch (some <$> run (fl.set i b)) fun _ => pure none) then if o.1.tst ≤ out.1.tst then fl := fl.set i b; out := o; break
  pure out

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
        -- use is the expansion, which reads the arguments where `build` has every object solved
        let mc ← Lean.getMCtx
        if [zonk mc a, zonk mc a'].any (!·.mvs.isEmpty) then return r
        let (ix', k?) ← idxClass ix j?; ix := ix'
        -- the first form the argument (a family: its relation from the index) builds in: closed, run on demand,
        -- tested on pairs; else closed, whose build reports why
        let st ← get; let mc ← Lean.getMCtx
        let bx := build st.objs mc p x
        let f : Option Bool :=
          if (build st.objs mc p (Pre.close p x a why)).toOption.isSome then none
          else if bx.toOption.isSome then some false
          else if (test st.objs mc p x).toOption.isSome then some true else none
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
          | .ok (o, specs) => modify (fun st => { st with specs := specs ++ [o] }); pure (some o)
          | .error _ => pure none
      -- the arguments that need keys on demand where the body builds so (it composes them with what bounds them),
      -- else closed on their sources' universes, where a body that reads them whole needs them
      let (o?, ys) ← if fsL == fs then pure (← get? fs, xs) else match ← get? fsL with
        | some o => pure (some o, xsL)
        | none => pure (← get? fs, xs)
      let some o := o? | return r
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
    settleOpen env p r.plain.1; settleOpen env p r'.plain.1
    pure (r, r') : M (Arg × Arg)).run { specs, objs := env.objs }
  let mc ← Lean.getMCtx
  let (⟨A, B, R⟩, s, t) ← top env mc p e r
  let (⟨A', B', S⟩, s', t') ← top env mc p f r'
  if h : A' = A ∧ B' = B then pure ((p, e.show, f.show, eq, s, t, ⟨A, B, R, h.1 ▸ h.2 ▸ S⟩), st.specs)
  else throw ⟨p, s!"check: the sides have types {s} ⟶ {t} and {s'} ⟶ {t'}"⟩

/-- The declarations of `prog`, in order, from the environment `env`: each closed definition (no keys) with its
    core term, each `print` and `check` with its terms; nothing evaluated: a definition is in scope as its built
    term. A parametric definition is called where `calls` gives its constant `own.x`; else, when `emitting`, it is
    built once for `emit` (`once`) after the program is read, and called in the bodies built after it; else
    expanded at each use. `specs`: the constants built so far at the forms calls take (`callDef`), `emitter` the
    program that emits those built here; returned with the ones built here. -/
def walk (prog : Program) (env : Env) (wrap : String → Def → Def) (own : Lean.Name) (calls : Lean.Name → Option Once)
    (emitting : Bool) (emitter : Lean.Name) (specs : List Once) (imported : Bool := false) :
    EM (Env × List (String × Res) × List (String × Top) × List Chk × List Once) := do
  let mut env := env
  let mut specs := specs
  let mut pend : List (Env × Pos × String × List Param × Expr × (OExp × OExp) × List String × Def) := []
  let mut ds : List (String × Res) := []
  let mut pr : List (String × Top) := []
  let mut cs : List Chk := []
  for d in prog do
    -- an imported program's prints, checks and theorems ran where it was defined; only its scope is read here
    if imported && (match d with | .print .. | .check .. | .«theorem» .. => true | _ => false) then continue
    match d with
    | .obj _ n od =>
      -- an imported program's object is its constant's, so the importer's types name the same object (§2.3);
      -- an alias stays the object it stands for
      if imported then
        let c := (Parse.constOf own n).toString
        let i ← objInfo env c od
        env := { env with objs := (n, i) :: (c, i) :: env.objs }
      else env := { env with objs := (n, ← objInfo env n od) :: env.objs }
    | .defn p n ps b ty =>
      let missing := ps.any (·.ty.isNone) || match b with | .rel _ => ty.isNone | .test .. => false
      if missing then throw ⟨p, s!"`{n}` has no type; it is {← (inferSig env n ps b).run' {}}"⟩
      match ps, b, ty with
      | [], .rel e, ty =>
        let rigid := match ty with | some (a, b) => (a.vars ++ b.vars).map fun v => (v, OTy.base v) | none => []
        let (r, st) ← (do
          let r ← elabE env none e
          if let some ty := ty then let (_, s, t) := r.plain; declared env p n rigid ty s t
          settleOpen env p r.plain.1
          pure r).run { specs, objs := env.objs }
        specs := st.specs
        let mc ← Lean.getMCtx; let (q, s, t) := r.plain
        let s := zonk mc s; let t := zonk mc t
        let each := wrap n (mkDef env n p [] (.rel e) ty)
        if !rigid.isEmpty || s.poly || t.poly then env := { env with defs := (n, each) :: env.defs }; continue
        let q := if (uniOf env.objs s).isSome then Pre.close p q s noLeft else q
        let res@⟨_, _, tm⟩ ← match build env.objs mc p q, test env.objs mc p q with
          | .ok r, _ => pure r
          | .error _, .ok _ => env := { env with defs := (n, each) :: env.defs }; continue
          | .error e, .error _ => throw e
        env := { env with defs := (n, wrap n { arity := 0, apply := fun _ _ => pure (.rel (.tm res) s t) }) :: env.defs }
        if !tm.dem then ds := ds ++ [(n, res)]
      | qs, b, ty =>
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
    | .print p e =>
      let (r, st) ← (do let r ← elabE env none e; settleOpen env p r.plain.1; pure r).run { specs, objs := env.objs }
      specs := st.specs
      pr := pr ++ [(e.show, ← top env (← Lean.getMCtx) p e r)]
    | .check p e f eq => let (c, sp) ← checkOf env p e f eq specs; specs := sp; cs := cs ++ [c]
    | .«theorem» p n ps e f eq on _ steps =>
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
    let (o, sp) ← once { env₀ with defs := mine ++ env₀.defs } p n qs e ty vs c c (qs.map fun _ => (none, none)) [] specs
    specs := sp ++ [o]
    mine := (n, wrap n (callDef env₀ p n qs e ty vs c emitter calls d)) :: mine
  pure (env, ds, pr, cs, specs)

/-- What the program `own` declares, `prog`, read after the programs `homes` its names reach (their definitions
    and objects), each read in order with its own resolver `res h` (module design §2.3), its definitions in scope
    for the next by constant. A definition whose constant `calls` holds is called, not expanded. With no `res`, a
    text read outside any Lean scope: each program sees those before it unqualified (`Parse.openAll`). -/
def read (calls : Lean.Name → Option Once) (homes : List (Lean.Name × Program)) (prog : Program)
    (own : Lean.Name := .anonymous)
    (res : Lean.Name → String → Found := fun h => Parse.openAll (homes.takeWhile (·.1 != h))) : EM Read := do
  let mut ext : List (Lean.Name × Def) := []
  let mut xo : List (Lean.Name × ObjInfo) := []
  -- the constants a call builds at a form no registered constant takes (`callDef`), which `own` emits
  let mut specs : List Once := []
  for (h, hp) in homes do
    let env : Env := { res := res h, ext, extObjs := xo, objs := xo.map fun (c, i) => (c.toString, i) }
    let (e, _, _, _, sp) ← (walk hp env (fun k => useDef (Parse.constOf h k) true) h calls false own specs true).adapt
      (Err.inProg h.toString)
    specs := sp
    for d in hp do
      if let some (k, x) := Parse.extOf h d then
        match x.obj, e.objs.lookup x.const.toString, e.defs.lookup k with
        | true, some i, _ => xo := (x.const, i) :: xo
        | false, _, some df => ext := (x.const, df) :: ext
        | _, _, _ => pure ()
  let env : Env := { res := res own, ext, extObjs := xo, objs := xo.map fun (c, i) => (c.toString, i) }
  let (e, ds, ps, cs, os) ← walk prog env (fun k => useDef (Parse.constOf own k) false) own calls true own specs
  pure (ds, ps, cs, e.objs, os)

/-! ### The core term as an `Expr` -/

open Lean Meta


/-- A term that needs no keys and reads no fixed-point variable: computed once, its own constant (`share`). -/
def closed {A B : Obj} (t : Tm A B) : Bool := !t.dem && t.fv.isEmpty

/-- `t` with each closed sub-term `R` wrapped as `.share k R`, `k` the next number: `code` keeps each number's
    code and `Tm.fv` stops there (a share is closed), so building and proving a closed sub-term never rebuilds it. -/
partial def number : {A B : Obj} → Tm A B → StateM Nat (Tm A B)
  | _, _, .share _ R => number R
  | _, _, t => do w (← t.mapM fun c => number c)
where w {A B : Obj} (t : Tm A B) : StateM Nat (Tm A B) :=
  if closed t then modifyGet fun k => (.share k t, k + 1) else pure t

/-- The kernel twin of the constant `c` of a definition elaborated once: its parameters and result are code
    (`Rel`), not plans, built on the kernel path where its body is on it (`emit`). -/
def kernelTwin (c : Name) : Name := c ++ `kernel

/-- The constant of each closed value, and the code of each numbered sub-term (`number`). -/
abbrev RM := (StateT (Std.HashMap Lean.Expr Name × Std.HashMap Nat Lean.Expr) MetaM)

/-- The constant `c : ty := v`, compiled, with the heartbeats a `def` command of its own would have: one
    `rel_program` command adds them all, and a program's count of constants is no measure of any one's cost.
    Regular hints, as `def` gives: an opaque `c` makes the kernel unfold the other side of `c =?= v` first. -/
def addConst (c : Name) (ty v : Lean.Expr) : MetaM Unit := withCurrHeartbeats do
  let hints := .regular (getMaxHeight (← getEnv) v + 1)
  addAndCompile (.defnDecl { name := c, levelParams := [], type := ty, value := v, hints, safety := .safe })


/-- The bytes `b` as hex text, two lowercase digits a byte (`Gen.unhex` reads it back). -/
def hex (b : ByteArray) : String :=
  -- ASCII bytes then one UTF-8 check: `String.push` per digit dominated the expansion's profile
  let d (x : UInt8) : UInt8 := if x < 10 then 48 + x else 87 + x
  String.fromUTF8! (b.foldl (fun o x => (o.push (d (x / 16))).push (d (x % 16))) (.emptyWithCapacity (2 * b.size)))

/-- An atom column rebuilt from its `foR` payload as it is (`Gen.atom`), a boolean one included; a symbol, general or
    ALP payload is not rebuilt, and says so. -/
def atomE (t : Rel.QAtomicType) (n : USize) (x : Arr t n) : Except String Lean.Expr :=
  let ofFoR (m p : ByteArray) := pure (g ``Gen.atom #[toExpr t, uE n, mkStrLit (hex m), mkStrLit (hex p)])
  match x.enc, t.width with
  | .foR m p, _ => ofFoR m p
  -- an old kernel's dense answer, encoded at its exit; goes with the old layer (W5)
  | .bytes b, some w => let r := Rel.Kernel.Coc.encode w.toUSize b; ofFoR r.1 r.2
  | _, _ => throw s!"a column of {n} rows in a symbol, general or ALP payload cannot be rebuilt"

/-- A column rebuilt from its parts: each atom column from its payload (`atomE`), the rest by `Vals`'s shape. -/
def valsE : (A : Obj) → (n : USize) → Vals A n → Except String Lean.Expr
  | .atom t, n, x => atomE t n x
  | .prod a b, n, x => do
    pure (g ``Gen.pairV #[oE a, oE b, uE n, ← valsE a n x.1, ← valsE b n x.2])
  | .arr b, n, ⟨m, lo, hi, p⟩ => do
    pure (g ``Gen.arrV #[oE b, uE n, uE m, ← atomE .i64 n lo, ← atomE .i64 n hi, ← valsE b m p])
  | .sum a b, n, ⟨l, r, tag, idx, x, y⟩ => do
    pure (g ``Gen.sumV #[oE a, oE b, uE n, uE l, uE r, ← atomE .u1 n tag, ← atomE .i64 n idx,
      ← valsE a l x, ← valsE b r y])

def relE {A B : Obj} (R : Tab A B) : Except String Lean.Expr := do
  pure (g ``Gen.relV #[oE A, oE B, uE R.n, ← valsE A R.n R.key, ← valsE B R.n R.val])

def liftE {α : Type} (x : Except String α) : RM α := match x with
  | .ok a => pure a
  | .error e => throwError "rel_program expansion: {e}"


mutual

/-- `t`'s code, `Gen.Fn d A B`: a closed `t` is its constant (`share`), any other its node; a numbered sub-term's
    is built once. -/
partial def code (pre : Name) (ph : List Lean.Expr) (ρ : List (Nat × Lean.Expr)) {A B : Obj} (t : Tm A B) : RM Lean.Expr := do
  if let .share k R := t then
    if let some e := (← get).2[k]? then return e
    let e ← code pre ph ρ R
    modify fun (m, cs) => (m, cs.insert k e); return e
  if closed t then
    let v ← node pre ph ρ t
    -- at a placeholder of the constant being built (`Once.ph`, here `ph`) the value lives under its binders: not shared
    if (v.find? ph.contains).isSome then return v
    -- a term demanding nothing of its context (`dem = false`) has one table, so it is computed once
    return mkConst (← share pre A B (if !t.dem then g ``GenK.memo #[oE A, oE B, v] else v))
  else node pre ph ρ t

/-- The constant of the closed code `v : Rel A B`: one per structurally equal value, so a closed term with
    `dem = false` (wrapped in `GenK.memo` by `code`) is computed once and any other runs on the context it is given. -/
partial def share (pre : Name) (A B : Obj) (v : Lean.Expr) : RM Name := do
  if let some c := (← get).1[v]? then return c
  let i := (← get).1.size
  let c := pre ++ `c ++ Name.mkSimple s!"c{i}"
  addConst c (mkApp2 (mkConst ``Rel.Rel) (oE A) (oE B)) v
  modify fun (m, cs) => (m.insert v c, cs); pure c

/-- A call, its constant's kernel twin applied to its arguments' code: a `Rel`. -/
partial def spine (pre : Name) (ph : List Lean.Expr) (ρ : List (Nat × Lean.Expr)) {A B : Obj} : Tm A B → RM Lean.Expr
  | .share _ f => spine pre ph ρ f
  | .arg f x => do return mkApp (← spine pre ph ρ f) (← code pre ph ρ x)
  | .call _ c os _ | .callCv _ c _ os .. => do return mkAppN (mkConst (kernelTwin c)) (os.map oE).toArray
  | _ => throwError "rel_program expansion: internal: a call's head is not a constant"

/-- `φ`'s body as `fun X => …`, the variable `k` read as `X : Tab A B` (`GenK.nu`, `GenK.mu`). -/
partial def body (pre : Name) (ph : List Lean.Expr) (ρ : List (Nat × Lean.Expr)) (A B : Obj) (k : Nat) (b : Tm A B) :
    RM Lean.Expr := do
  withLocalDeclD `X (mkApp2 (mkConst ``Rel.Tab) (oE A) (oE B)) fun x => do
    mkLambdaFVars #[x] (← code pre ph ((k, x) :: ρ) b)

/-- `t`'s own node, its `GenK` body with its parts by `code`. -/
partial def node (pre : Name) (ph : List Lean.Expr) (ρ : List (Nat × Lean.Expr)) {A B : Obj} (t : Tm A B) : RM Lean.Expr := do
  let c {X Y : Obj} (u : Tm X Y) := code pre ph ρ u
  match A, B, t with
  | A, B, .val R => return g ``GenK.val #[oE A, oE B, ← liftE (relE R)]
  | A, _, .uni (m := m) U => return g ``GenK.uni #[oE A, uE m, ← liftE (valsE A m U)]
  | A, B, .zero => return g ``GenK.zero #[oE A, oE B]
  | A, _, .id => return g ``GenK.id #[oE A]
  | A, B, .top V => return g ``GenK.top #[oE A, oE B, ← c V]
  | .prod A B, _, .outl => return g ``GenK.outl #[oE A, oE B]
  | .prod A B, _, .outr => return g ``GenK.outr #[oE A, oE B]
  | A, C, .comp (B := B) R S => return g ``GenK.comp #[oE A, oE B, oE C, bE S.dem, ← c R, ← c S]
  | B, A, .conv R => return g ``GenK.conv #[oE A, oE B, ← c R]
  | A, B, .meet R S => return g ``GenK.meet #[oE A, oE B, bE R.dem, bE S.dem, ← c R, ← c S]
  | A, B, .join R S => return g ``GenK.join #[oE A, oE B, bE R.dem, bE S.dem, ← c R, ← c S]
  | A, B, .diff R S => return g ``GenK.diff #[oE A, oE B, bE R.dem, bE S.dem, ← c R, ← c S]
  | A, _, .dom (B := B) R => return g ``GenK.dom #[oE A, oE B, bE R.dem, ← c R]
  | B, _, .ran (A := A) R => return g ``GenK.ran #[oE A, oE B, ← c R]
  | B, C, .ldiv (A := A) R S UB UC => return g ``GenK.ldiv #[oE A, oE B, oE C, ← c R, ← c S, ← c UB, ← c UC]
  | A, B, .rdiv (C := C) R S UA UB => return g ``GenK.rdiv #[oE A, oE B, oE C, ← c R, ← c S, ← c UA, ← c UB]
  | A, .prod B C, .pair R S => return g ``GenK.pair #[oE A, oE B, oE C, bE R.dem, bE S.dem, ← c R, ← c S]
  | .prod A C, .prod B D, .prod R S => return g ``GenK.prod #[oE A, oE B, oE C, oE D, ← c R, ← c S]
  | A, .arr B, .lam R => return g ``GenK.lam #[oE A, oE B, bE R.dem, ← c R]
  | .arr A, .arr B, .E R => return g ``GenK.E #[oE A, oE B, bE R.dem, ← c R]
  | _, B, .est Q => return g ``GenK.est #[oE B, ← c Q]
  | _, .arr B, .thin Q => return g ``GenK.thin #[oE B, ← c Q]
  | A, .arr B, .nil => return g ``GenK.nil #[oE A, oE B]
  | .arr B, _, .atPos k => return g ``GenK.atPos #[oE B, toExpr k]
  | _, _, .own R => c R
  | _, _, .succ U => return g ``GenK.succ #[← c U]
  | _, _, .arith k U => return g ``GenK.arith #[toExpr k, ← c U]
  | _, _, .leq U => return g ``GenK.leq #[← c U]
  | _, _, .lt U => return g ``GenK.lt #[← c U]
  | .arr Y, V, .foldr e S => return g ``GenK.foldr #[oE Y, oE V, bE S.dem, ← c e, ← c S]
  | .arr Y, V, .fold e S => return g ``GenK.fold #[oE Y, oE V, bE S.dem, ← c e, ← c S]
  | _, _, .share _ R => c R
  | .prod I (.arr Y), V, .foldI e S =>
    return g ``GenK.foldI #[oE I, oE Y, oE V, bE e.dem, bE S.dem, ← c e, ← c S]
  | .prod I A, B, .flat R => return g ``GenK.flat #[oE I, oE A, oE B, bE R.dem, ← c R]
  | A, B, .var _ v => match ρ.lookup v with
    -- by what the binder holds: a kernel twin's parameter (code), a fixed point's variable (a `Tab`)
    | some x => do
      let ty ← inferType x
      if ty.isAppOf ``Rel.Rel then return x
      if ty.isAppOf ``Rel.Tab then
        return g ``GenK.const #[oE A, oE B, mkApp3 (mkConst ``Except.ok [0, 0]) (mkConst ``String) ty x]
      throwError "rel_program expansion: internal: the variable {v} is bound to neither code nor a table: {ty}"
    | none => throwError "rel_program expansion: internal: the variable {v} is not bound here"
  | A, B, .nu v S b => return g ``GenK.nu #[oE A, oE B, ← c S, ← body pre ph ρ A B v b]
  -- `μ` and hylo also take their text: they throw the message naming it
  | A, B, .mu v w n b => return g ``GenK.mu #[oE A, oE B, toExpr w, toExpr n, ← body pre ph ρ A B v b]
  | A, B, .hylo v w b => do
    -- children read in no shape bound no recursion: running `𝟘` for them would compute something else
    let some ch := b.kids v A
      | throwError "rel_program expansion: {w}: the hylo's body reads its variable in a shape that gives no children (Tm.kids)"
    return g ``GenK.hylo #[oE A, oE B, toExpr w, bE ch.dem, bE b.dem, ← c ch, ← body pre ph ρ A B v b]
  | A, B, t@(.prim _) | A, B, t@(.arg ..) => match primOf t with
    | some (r, as) => do
      let xs ← as.toArray.mapM fun x => return (← code pre ph ρ x.2.2, fnTy x)
      let some e ← primE r A B xs
        | throwError "rel_program expansion: row `{r.sym}` at {oE A} → {oE B} given {xs.size} relations fits none of its wrappers {primWrappers}"
      pure e
    | none => spine pre ph ρ t
  | _, _, t@(.call ..) | _, _, t@(.callCv ..) => spine pre ph ρ t

end

/-- `k` under one local of each type `tys`, closed over them: `(∀ xs, ty, fun xs => v)` of `k`'s `(ty, v)`. -/
def lams (tys : List Lean.Expr) (k : Array Lean.Expr → RM (Lean.Expr × Lean.Expr)) (xs : Array Lean.Expr := #[]) :
    RM (Lean.Expr × Lean.Expr) :=
  match tys with
  | [] => do let (t, v) ← k xs; pure (← mkForallFVars xs t, ← mkLambdaFVars xs v)
  | ty :: tys => withLocalDeclD `x ty fun x => lams tys k (xs.push x)

/-- `x` and `y` are the same columns: of one object, column by column the same vector (`valEq`). -/
def valsEq : (A : Obj) → {n : USize} → Vals A n → (C : Obj) → {m : USize} → Vals C m → Bool
  | .atom _, _, x, .atom _, _, y => valEq x.1 y.1
  | .prod a b, _, x, .prod c d, _, y => valsEq a x.1 c y.1 && valsEq b x.2 d y.2
  | .arr b, _, ⟨_, lo, hi, p⟩, .arr d, _, ⟨_, lo', hi', q⟩ =>
    valEq lo.1 lo'.1 && valEq hi.1 hi'.1 && valsEq b p d q
  | .sum a b, _, ⟨_, _, tag, idx, x, y⟩, .sum c d, _, ⟨_, _, tag', idx', x', y'⟩ =>
    valEq tag.1 tag'.1 && valEq idx.1 idx'.1 && valsEq a x c x' && valsEq b y d y'
  | _, _, _, _, _, _ => false

/-- `t` and `u`, of one constructor, agree in their fields that are not terms; a call's constant compared by its
    registry key (`key`), since each module names the constant it built `emitter ++ key`. A `callCv`'s converse
    constant is its constant's converse's (`convOf`), so it follows the constant. -/
def Tm.fieldsEq (key : Lean.Name → Lean.Name) {A B C D : Obj} (t : Tm A B) (u : Tm C D) : Bool :=
  match t with
  | .val R => match u with | .val S => valsEq _ R.key _ S.key && valsEq _ R.val _ S.val | _ => false
  | .uni (A := A) U => match u with | .uni (A := C) V => valsEq A U C V | _ => false
  | .prim r => match u with | .prim r' => r.sym == r'.sym | _ => false
  | .atPos k => match u with | .atPos k' => k == k' | _ => false
  | .share k _ => match u with | .share k' _ => k == k' | _ => false
  | .var d k => match u with | .var d' k' => d == d' && k == k' | _ => false
  | .call ks c os _ => match u with | .call ks' c' os' _ => ks == ks' && key c == key c' && os == os' | _ => false
  | .callCv ks c _ os .. => match u with
    | .callCv ks' c' _ os' .. => ks == ks' && key c == key c' && os == os' | _ => false
  | .arith k _ => match u with | .arith k' _ => k == k' | _ => false
  | .nu k .. => match u with | .nu k' .. => k == k' | _ => false
  | .mu k w n _ => match u with | .mu k' w' n' _ => k == k' && w == w' && n == n' | _ => false
  | .hylo k w _ => match u with | .hylo k' w' _ => k == k' && w == w' | _ => false
  | _ => true

/-- The first node, from the root, where the bodies `t`, `u` of one registry key differ, as its path of
    constructors (`ctor`); `none` when they are the same definition: per node its constructor, objects and other
    fields (`Tm.fieldsEq`), then its parts (`Tm.parts`, a `share`'s term) in order. A call's body is not entered:
    it is its key's, compared at that key. -/
partial def Tm.diffAt (key : Lean.Name → Lean.Name) (ctor : Nat → String) (path : List String := []) :
    Res → Res → Option String
  | ⟨A, B, t⟩, ⟨C, D, u⟩ =>
    let p := path ++ [ctor t.ctorIdx]
    let parts {X Y : Obj} : Tm X Y → List Res | .share _ R => [⟨_, _, R⟩] | t => t.parts
    if t.ctorIdx != u.ctorIdx then some s!"{" / ".intercalate p} against `{ctor u.ctorIdx}`"
    else if !(A == C && B == D) then some s!"{" / ".intercalate p}: {repr A} ⟶ {repr B} against {repr C} ⟶ {repr D}"
    else if !Tm.fieldsEq key t u then some s!"{" / ".intercalate p}: its fields differ"
    else ((parts t).zip (parts u)).findSome? fun (x, y) => Tm.diffAt key ctor p x y

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

def pairT (a b : Lean.Expr) : Lean.Expr := mkApp2 (mkConst ``Prod [0, 0]) a b
def listT (a : Lean.Expr) : Lean.Expr := mkApp (mkConst ``List [0]) a

/-- The objects `objs` as a print reads them (`infoOf`). -/
def objsE (objs : Objs) : MetaM Lean.Expr := do
  let ty := pairT (mkConst ``String) (mkConst ``ObjInfo)
  mkListLit ty (objs.map fun (x, i) => mkApp4 (mkConst ``Prod.mk [0, 0]) (mkConst ``String) (mkConst ``ObjInfo)
    (toExpr x) (g ``infoOf #[toExpr i.ty, toExpr i.elems, toExpr i.range]))

/-- The Lean definitions of what the program `n` reads (`read`): `n.x` for each closed definition, its
    sub-terms' constants `n.c.c<i>`, `n.expanded` (the definitions with their objects), `n.objs`, `n.printed`
    (each `print`'s line and ok bit), `n.prints` (the lines), `n.failures` (`failures`: each `check` that does not
    hold, and each term that threw) and `n.ok`, that there is none. -/
def emit (n : Name) (r : Read) : MetaM Unit := do
  let (ds, ps, cs, objs, os) := r
  -- one numbering over the whole program, as the code of each number is kept across it
  let ((ds, ps, cs), fs) := Prod.fst <| (do
    let fs ← os.mapM fun o => do let ⟨A, B, t⟩ := o.res; return { o with res := ⟨A, B, ← number t⟩ }
    let ds ← ds.mapM fun (x, ⟨A, B, t⟩) => return (x, ⟨A, B, ← number t⟩)
    let ps ← ps.mapM fun (x, ⟨A, B, t⟩, s, u) => return (x, ⟨A, B, ← number t⟩, s, u)
    let cs ← cs.mapM fun (p, x, y, eq, s, u, ⟨A, B, R, S⟩) =>
      return (p, x, y, eq, s, u, ⟨A, B, ← number R, ← number S⟩)
    pure ((ds, ps, cs), fs) : StateM Nat ((List (String × Res) × List (String × Top) × List Chk) × List Once)).run 0
  addConst (n ++ `objs) (mkConst ``Objs) (← objsE objs)
  let os := mkConst (n ++ `objs)
  -- a closed term's table: its code run in the empty context `{}`, which knows neither side; each side a `none`
  -- at its field's type, read off the field's default (which has no executable code of its own)
  let app (A B : Obj) (t : Lean.Expr) : MetaM Lean.Expr := do
    let none' (f : Name) := return mkApp (mkConst ``Option.none [0]) (← inferType (g f #[oE A, oE B])).appArg!
    pure (g ``Rel.Rel.runE #[oE A, oE B, t,
      g ``Rel.Known.mk #[oE A, oE B, ← none' ``Rel.Known.dom._default, ← none' ``Rel.Known.ran._default]])
  -- each definition elaborated once whose body has a kernel body at every node: its kernel twin
  -- `n.x.kernel : (A₁ … : Obj) → Rel U₁ → … → Rel R₁ → … → Rel A B` (`kernelTwin`), generic over the objects of its
  -- generic variables, then code in and out, the universes it reads then its parameters; `n.x.conv.kernel` its
  -- converse, when its body has one (`convTm`)
  let ((), st₀) ← (do
    for o@{ const := c, gen, params := qs, res := ⟨A, B, t⟩, .. } in fs do
      let nv := gen.length
      let reads := (List.range nv).map t.fv.contains
      let vo (k : Nat) : Obj := if gen.getD k false then (varObj o.ph k).getD .long else .long
      let rk := (List.range nv).filter (reads.getD · false)
      let gk := (List.range nv).filter (gen.getD · false)
      let mk (k : Name) (X Y : Obj) (u : Tm X Y) : RM Unit := do
        let pl (X Y : Obj) := mkApp2 (mkConst ``Rel.Rel) (oE X) (oE Y)
        let (ty, v) ← lams (gk.map fun _ => mkConst ``Obj) fun xs => do
          -- each placeholder `varObj k` becomes its binder
          let sub (z : Lean.Expr) := z.replace fun s =>
            (gk.zip xs.toList).findSome? fun (k, a) => if (varObj o.ph k).map toExpr == some s then some a else none
          lams ((rk.map fun k => sub (pl (vo k) (vo k))) ++ qs.map fun (P, Q, _) => sub (pl P Q)) fun ys => do
            let ρ := o.binds.zip ys.toList
            pure (sub (pl X Y), sub (← code n (o.ph.map (oE <| .atom ·)) ρ u))
        addConst k ty v
      -- each twin's numbered codes live under its own binders: built with an empty number cache, dropped after
      let twin (k : Name) (X Y : Obj) (u : Tm X Y) : RM Unit := do
        let env ← getEnv
        if u.onKernel fun c => env.contains (kernelTwin c) then
          let saved := (← get).2
          modify fun (m, _) => (m, {}); mk (kernelTwin k) X Y u; modify fun (m, _) => (m, saved)
      if let some (c', ⟨X, Y, u⟩) := convOf o then twin c' X Y u
      twin c A B t : RM Unit).run ({}, {})
  -- the registry holds each body as elaborated, not numbered: a call copies it (`callTm`), and the numbers are this
  -- program's
  for o in r.2.2.2.2 do modifyEnv (relRegistry.addEntry · (.call o.key o))
  -- every node of every term the program runs has a `GenK` body, a call one where its constant has a kernel twin
  let env ← getEnv
  let tw (c : Name) := env.contains (kernelTwin c)
  let off := ds.flatMap (fun (_, ⟨_, _, t⟩) => t.offKernel tw) ++ ps.flatMap (fun (_, ⟨_, _, t⟩, _, _) => t.offKernel tw)
    ++ cs.flatMap fun (_, _, _, _, _, _, ⟨_, _, R, S⟩) => R.offKernel tw ++ S.offKernel tw
  unless off.isEmpty do
    let ctors := (← getConstInfoInduct ``Tm).ctors
    let kinds := (off.map fun (i, c) =>
      let k := toString ((ctors.getD i .anonymous).componentsRev.headD .anonymous)
      if c.isEmpty then k else s!"{k} {c}").eraseDups
    throwError "rel_program {n}: these nodes have no kernel body (GenK), so the program cannot run: {kinds}"
  let ((entries, printed, checked, errs), _) ← (do
    let mut es := []
    for (x, ⟨A, B, t⟩) in ds do
      let v ← code n [] [] t
      let k := Parse.constOf n x
      unless !t.dem do throwError "rel_program expansion: internal: `{x}` needs keys"
      addConst k (mkApp2 (mkConst ``Except [0, 0]) (mkConst ``String) (mkApp2 (mkConst ``Tab) (oE A) (oE B))) (← app A B v)
      es := es ++ [g ``Gen.entry #[toExpr x, oE A, oE B, mkConst k]]
    -- each term's error message, so `failures` names the op that could not run
    let one (x : String) {A B : Obj} (t : Tm A B) : RM Lean.Expr := do
      pure (mkApp4 (mkConst ``Prod.mk [0, 0]) (mkConst ``String) (mkApp (mkConst ``Option [0]) (mkConst ``String))
        (toExpr x) (g ``Rel.Rel.err #[oE A, oE B, ← code n [] [] t]))
    let errs := (← ds.mapM fun (x, ⟨_, _, t⟩) => one x t) ++ (← ps.mapM fun (x, ⟨_, _, t⟩, _, _) => one x t) ++
      (← cs.mapM fun (_, x, _, _, _, _, ⟨_, _, R, _⟩) => one x R) ++
      (← cs.mapM fun (_, _, y, _, _, _, ⟨_, _, _, S⟩) => one y S)
    let ps ← ps.mapM fun (x, ⟨A, B, t⟩, s, u) => do
      pure (g ``printText #[oE A, oE B, os, toExpr x, toExpr s, toExpr u, ← app A B (← code n [] [] t)])
    let cs ← cs.mapM fun (p, x, y, eq, s, u, ⟨A, B, R, S⟩) => do
      pure (g ``checkErr #[oE A, oE B, os, toExpr p, toExpr x, toExpr y, toExpr eq, toExpr s, toExpr u,
        ← app A B (← code n [] [] R), ← app A B (← code n [] [] S)])
    pure (es, ps, cs, errs) : RM (List Lean.Expr × List Lean.Expr × List Lean.Expr × List Lean.Expr)).run st₀
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

end Expand

end Rel.Lang
