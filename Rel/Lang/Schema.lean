import Rel.Run.Lang.Tm

/-! A frame's schema in its type (PLAN D.11, `doc/dataframe-design.zh.typ` §1.2): `Schema` names the columns of a row
    object, and every term on a frame is a `Tm S.obj …`. No new `Obj` constructor: `S.obj` is a definition, so kernels,
    storage and `rep` see the plain nested `prod`; the names live only in `Schema`, so two schemas with the same field
    objects and other names have one `Obj`.

    - `col S "price" : Tm S.obj T true` is the composition of `outl`/`outr` that reaches the field `("price", T)`.
    - `select`, `exclude`, `rename`, `derive`, `join`: each a function on `S` giving its result schema `T` together
      with the term `S.obj ⟶ T.obj` (`To`), or the error that refuses it.
    - Every name is decided at elaboration (`schema_ok`, `ok`): a missing column, a name twice in a schema, an empty
      schema is an elaboration error naming it, never a default. -/

namespace Rel.Lang

/-- A frame's row type: its columns' names and objects, in `.d` column order. -/
abbrev Schema := List (String × Obj)

namespace Schema

def names (S : Schema) : List String := S.map (·.1)

/-- `S` as an error message writes it: its column names. -/
def shown (S : Schema) : String := s!"[{", ".intercalate S.names}]"

def noColumn : String := "a schema with no column has no object (`Obj` has no unit)"

/-- `S` has a column and no name twice: what every function here accepts and returns. -/
def check (S : Schema) : Except String Unit :=
  if S.isEmpty then .error noColumn else
  match S.names.find? fun n => S.names.count n > 1 with
  | some n => .error s!"column '{n}' appears twice in schema {S.shown}"
  | none => pure ()

/-- The object of `R`, a schema reversed: its head is the last column. -/
def objR : List (String × Obj) → Obj
  | [] => .long
  | [f] => f.2
  | f :: g :: R => .prod (objR (g :: R)) f.2

-- Left-nested, `(A×B)×C`, as `.rel` reads `A×B×C` (`oProd` is left-associative); one column is its own object. `Obj`
-- has no unit, so the empty schema is refused by `check` and its `.long` here is never read.
def obj (S : Schema) : Obj := objR S.reverse

/-- The column `n` of `R` (reversed, as `objR`): `outr` at the last column, `outl` then the column in the rest, `𝟙`
    where it is the only column. -/
def colR (n : String) : (R : List (String × Obj)) → Option ((B : Obj) × Tm (objR R) B true)
  | [] => none
  | [f] => if f.1 = n then some ⟨f.2, .id⟩ else none
  | f :: g :: R => if f.1 = n then some ⟨f.2, .outr⟩ else (colR n (g :: R)).map fun p => ⟨p.1, .comp .outl p.2⟩

/-- The column `n` of `S` with its object, or the error naming `n` and `S`'s columns. -/
def col? (S : Schema) (n : String) : Except String ((B : Obj) × Tm S.obj B true) := do
  S.check
  (colR n S.reverse).elim (.error s!"no column '{n}' in schema {S.shown}") .ok

/-- The message of `e` where it is an error. -/
def errOf {α : Type} : Except String α → Option String
  | .error m => some m
  | .ok _ => none

open Lean Meta in
unsafe def errOfExprImpl (e : Lean.Expr) : MetaM (Option String) := do
  evalExpr (Option String) (mkApp (mkConst ``Option [levelZero]) (mkConst ``String)) (← mkAppM ``errOf #[e])

open Lean Meta in
/-- `errOf e`, `e` a closed `Except String α` run at elaboration. -/
@[implemented_by errOfExprImpl] opaque errOfExpr (e : Lean.Expr) : MetaM (Option String)

open Lean Meta Elab Tactic in
/-- Proves `e.isOk = true` for a closed `e : Except String α` by running `e` at elaboration: its error is this
    tactic's error, word for word; an `ok` is then proved by `decide`. -/
elab "schema_ok" : tactic => do
  let t ← instantiateMVars (← getMainTarget)
  let some (_, l, _) := t.eq? | throwError "schema_ok: the goal {t} is not `e.isOk = true`"
  let_expr Except.isOk _ _ e := l | throwError "schema_ok: the goal {t} is not `e.isOk = true`"
  if let some m ← errOfExpr e then throwError m
  evalTactic (← `(tactic| decide))

/-- The value of `e`, which `h`, decided at elaboration, says is not an error. -/
def ok {α : Type} : (e : Except String α) → (h : e.isOk = true := by schema_ok) → α
  | .ok a, _ => a
  | .error _, h => nomatch h

/-- The column `n` of `S`: `col S "price" : Tm S.obj T true` exists iff `("price", T) ∈ S`, at most once. -/
def col (S : Schema) (n : String) (h : (S.col? n).isOk = true := by schema_ok) : Tm S.obj (ok (S.col? n) h).1 true :=
  (ok (S.col? n) h).2

/-- The fields of `R` (reversed, as `objR`), each read from `A` by `get` at its name and checked to be at the field's
    object, paired as `objR R` nests them. -/
def tupleR {A : Obj} (get : String → Except String ((B : Obj) × Tm A B true)) :
    (R : List (String × Obj)) → Except String (Tm A (objR R) true)
  | [] => .error noColumn
  | [f] => field f
  | f :: g :: R => return .pair (← tupleR get (g :: R)) (← field f)
where
  field (f : String × Obj) : Except String (Tm A f.2 true) := do
    let ⟨B, t⟩ ← get f.1
    if h : B = f.2 then pure (h ▸ t) else .error s!"column '{f.1}' is read at another object than its schema's"

/-- A frame function's result on rows `A`: its schema `T` and the term `A ⟶ T.obj`, or the error that refuses it. -/
abbrev To (A : Obj) := Except String ((T : Schema) × Tm A T.obj true)

/-- The schema `T`, checked, with its fields read from `A` by `get`. -/
def build {A : Obj} (T : Schema) (get : String → Except String ((B : Obj) × Tm A B true)) : To A := do
  T.check; return ⟨T, ← tupleR get T.reverse⟩

/-- The columns `ns` of `S`, in the order of `ns`. -/
def select (S : Schema) (ns : List String) : To S.obj := do
  build (← ns.mapM fun n => return (n, (← S.col? n).1)) S.col?

/-- `S` without the columns `ns`, each of which must be one of `S`'s. -/
def exclude (S : Schema) (ns : List String) : To S.obj := do
  for n in ns do discard (S.col? n)
  build (S.filter fun f => !ns.contains f.1) S.col?

/-- `S` with its column `a` named `b`; `b` already a column of `S` is refused as a name twice. -/
def rename (S : Schema) (a b : String) : To S.obj := do
  discard (S.col? a)
  build (S.map fun f => (if f.1 = a then b else f.1, f.2)) fun n => S.col? (if n = b then a else n)

/-- `S` with the column `n` computed by `e` added last. -/
def derive (S : Schema) (n : String) {B : Obj} {d : Bool} (e : Tm S.obj B d) : To S.obj :=
  build (S ++ [(n, B)]) fun m => if m = n then pure ⟨B, .comp .id e⟩ else S.col? m

/-- The names `S` and `S'` share, in `S`'s order: the key a natural join matches on. -/
def common (S S' : Schema) : List String := S.names.filter S'.names.contains

/-- The natural join on a pair of rows: the pairs whose common columns agree, `dom(⟨π₁ k, π₂ k'⟩ dom(π₁ ∩ π₂))`, as
    one row of `S`'s columns then `S'`'s others. No common column (a cross product) and a common column at two objects
    are refused. -/
def join (S S' : Schema) : To (.prod S.obj S'.obj) := do
  let ks := common S S'
  if ks.isEmpty then throw s!"no common column in schemas {S.shown} and {S'.shown}"
  if let some n := ks.find? fun n => S.lookup n != S'.lookup n then
    throw s!"column '{n}' is at two objects in schemas {S.shown} and {S'.shown}"
  let ⟨K, k⟩ ← S.select ks
  let ⟨K', k'⟩ ← S'.select ks
  if h : K' = K then
    let eq : Tm (.prod S.obj S'.obj) (.prod S.obj S'.obj) true :=
      .dom (.comp (.pair (.comp .outl k) (.comp .outr (h ▸ k'))) (.dom (.meet .outl .outr)))
    let ⟨T, t⟩ ← build (S ++ S'.filter fun f => !ks.contains f.1) fun m =>
      if S.names.contains m then (S.col? m).map fun p => ⟨p.1, .comp .outl p.2⟩
      else (S'.col? m).map fun p => ⟨p.1, .comp .outr p.2⟩
    return ⟨T, .comp eq t⟩
  else throw s!"the common columns of schemas {S.shown} and {S'.shown} differ"

end Schema

end Rel.Lang
