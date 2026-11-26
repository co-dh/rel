module

public import Lean
public import Rel.Kernel.Op
public import Rel.Run.Core
public import Rel.Kernel.Cast
public import Rel.Run.Cast

-- exposed: every def body is a spec a downstream `rfl`/`decide`/`simp` may unfold (PLAN W.8)
@[expose] public section

/-! The Rel language's surface syntax (`doc/rel-lang-design.md` §c, §h): objects, terms, declarations, each node
    with its source line and column. The builtin operators are one table, `Op.table`, read by the parser (symbol,
    arity), the elaborator (typing, lifted row) and the expander (the `Gen` op), each by the `Op` constructor; a
    builtin run on the keys in demand, given relations or none, is a row of `prims` with its type and relation
    parameters. -/

namespace Rel.Lang

deriving instance DecidableEq for Rel.Obj

/-- A source position: line and column, both from 1. -/
structure Pos where
  line : Nat := 0
  col : Nat := 0
  deriving Repr, BEq, Inhabited, Lean.ToExpr

instance : ToString Pos := ⟨fun p => s!"line {p.line}, col {p.col}"⟩

/-- What an error says and whose fault it is: `user` is a refusal of the program's text, which a caller may answer
    with a fallback; `internal` is a broken invariant of the elaborator, which no caller may swallow. -/
inductive Msg
  | user (s : String)
  | internal (s : String)
  deriving Repr, Inhabited

/-- The same kind, its text rewritten: a rewrap of an error keeps whether it is internal. -/
def Msg.map (f : String → String) : Msg → Msg
  | .user s => .user (f s)
  | .internal s => .internal (f s)

def Msg.isInternal : Msg → Bool | .internal _ => true | .user _ => false

instance : ToString Msg := ⟨fun | .user s => s | .internal s => s!"internal: {s}"⟩
instance : Coe String Msg := ⟨.user⟩

/-- A front-end error: where, and what was found against what was expected. -/
structure Err where
  pos : Pos
  msg : Msg
  deriving Repr, Inhabited

/-- A catch-all site falls back only on a refusal of the program's text: an internal error goes on. -/
def Err.user {m : Type → Type} [Monad m] [MonadExceptOf Err m] {α : Type} (e : Err) (k : m α) : m α :=
  if e.msg.isInternal then throw e else k

/-- Line 0 is no place in the program: an error of the prelude's own text says where in its message. -/
instance : ToString Err := ⟨fun e => if e.pos.line == 0 then s!"{e.msg}" else s!"{e.pos}: {e.msg}"⟩

/-- An error raised re-reading the program `n` a program imports: where in `n` it is. -/
def Err.inProg (n : String) (e : Err) : Err := ⟨default, e.msg.map (s!"in the program `{n}`, {e.pos}: " ++ ·)⟩

/-- A definition or object of a program, as the registry records it (`Expand.relRegistry`) and the resolver gives
    it: its constant `n.x`, its arity, whether it is an infix operator `_x_`, an object, a theorem. -/
structure Ext where
  const : Lean.Name
  arity : Nat := 0
  isInfix : Bool := false
  obj : Bool := false
  thm : Bool := false
  deriving Repr, Inhabited

/-- What a written name (`AC3`, `csp.AC3`, `≠`) resolves to in Lean's scope (the current namespace and `open`s),
    kept to the registry: one entry; or an error, `inScope` when the name is a Rel name all the same (several
    entries: ambiguous), not when Lean gives only constants that are no Rel definition; or nothing. -/
inductive Found
  | ext (e : Ext)
  | bad (inScope : Bool) (msg : String)
  | none
  deriving Inhabited

/-- An object as written: a declared name, `A×B`, `A+B`, `[A]`; in a parameter's type also an object
    variable `α`, instantiated at each use (§e). -/
inductive OExp
  | name (p : Pos) (n : String)
  | var (p : Pos) (n : String)
  | prod (a b : OExp)
  | sum (a b : OExp)
  | list (a : OExp)
  /-- `⟨θ ↦ A⟩`: the object `A` once per element of the finite object `θ`, laid out as `Schema.objAt` lays a schema's
      columns; `θ` may be an object variable, whose elements are read at each use (F1). -/
  | each (p : Pos) (o a : OExp)
  deriving Repr, Inhabited, BEq

/-- The builtin operators of §b. A constant (arity 0) may take its objects, `⊤(A,B)`; the others take relations.
    `arith k` is the qlean kernel's integral value verb `k` on pairs of numbers (`Alg.arith`): one constructor, so
    every verb is typed, lifted and run by one path; `prim s` the row `s` of `prims`. `inl`, `inr`, `mem` (`∋`) are
    `Tm` constructors; `map` runs as its row (`Op.row`), kept a constructor for `Calc.toTerm`'s reading as a relator. -/
inductive Op
  | id | zero | top | outl | outr | inl | inr | mem | leq | lt | succ | arith (k : UInt8)
  | alpha | prim (s : String)
  | lam | E | map
  /-- `hylo(c, S)`: an unfold by `c : A ⟶ G(A)` then a fold by `S : G(B) ⟶ B`, `μX : c G(X) S`; `fold` is a
      name programs define (Party), so the builtin is `hylo`. -/
  | hylo
  /-- `at(i)`, the element at position `i` from `0`; `i` a number literal, read by `Embed.atomOf`. -/
  | index (i : Nat)
  deriving Repr, BEq, Inhabited

/-- The builtin infix operators: `∩ ∪ − / \ ÷ ×`, one level with composition and the declared ones (`_⇒_`),
    left to right (§c). `÷` is symmetric division, the definition `R/S ∩ (S/R)°` (`Pre.symDiv`). -/
inductive Bin
  | meet | join | diff | rdiv | ldiv | symDiv | prod
  deriving Repr, BEq, Inhabited

def Bin.table : List (Char × Bin) :=
  [('∩', .meet), ('∪', .join), ('−', .diff), ('/', .rdiv), ('\\', .ldiv), ('÷', .symDiv), ('×', .prod)]

def Bin.sym (o : Bin) : String := ((Bin.table.find? (·.2 == o)).map (·.1.toString)).getD "?"

/-- A side of a literal's row: a word, a pair of sides, or an array of sides, nested to any depth (§c). -/
inductive Tup
  | leaf (w : String)
  | pair (a b : Tup)
  | arr (ts : List Tup)
  deriving Repr, Inhabited

/-- The same kind of side, whatever is inside: the elaborator compares the parts position by position. -/
def Tup.like : Tup → Tup → Bool
  | .leaf _, .leaf _ | .pair .., .pair .. | .arr _, .arr _ => true
  | _, _ => false

/-- `t` as the parser reads it back: an array of two or more items juxtaposed, else bracketed; `item`: `t` stands
    next to others, so an array there is always bracketed. -/
def Tup.render (item : Bool) : Tup → String
  | .leaf w => w
  | .pair a b => s!"({a.render false}, {b.render false})"
  | .arr ts => let s := " ".intercalate (ts.map (Tup.render true)); if item || ts.length < 2 then s!"[{s}]" else s

def Tup.show (t : Tup) : String := t.render false

/-- The bytes `32…126` but `"` and `\`, which q writes as themselves inside a char's quotes. -/
def charPlain (c : Nat) : Bool := 32 ≤ c && c < 127 && c != 34 && c != 92

/-- A byte as q writes a char: `"a"` for a `charPlain` byte, else `"\ooo"`, its three octal digits; `charOf` reads it
    back, the text form of the atom `char` (`Elab.qForm`). -/
def charText (b : UInt8) : String :=
  let n := b.toNat
  if charPlain n then s!"\"{Char.ofNat n}\"" else s!"\"\\{n / 64}{n / 8 % 8}{n % 8}\""

/-- The byte whose `charText` has the bytes `f`; none for any other text. -/
def charOf : List UInt8 → Option Int
  | [34, c, 34] => if charPlain c.toNat then some c.toNat else none
  | [34, 92, a, b, c, 34] =>
    if 48 ≤ a && a ≤ 51 && [b, c].all (fun d => 48 ≤ d && d ≤ 55) then
      some (64 * (a.toNat - 48) + 8 * (b.toNat - 48) + (c.toNat - 48))
    else none
  | _ => none

/-- A string literal (Lean's, its escapes decoded) as the array of its UTF-8 bytes, each a char word (`charText`):
    a text `[C]` is an array of `C`s, so `"NY"` is the literal `["N" "Y"]` of the object of `char`s it is used at. -/
def Tup.ofText (s : String) : Tup := .arr (s.toUTF8.toList.map (.leaf ∘ charText))

/-- The char word of a one-character string literal `"0"` (`.arr` of one `charText` word): as q reads it, a `char`
    where the literal's object is one, and the text `[C]` where the context fixes nothing else (`Elab.litTy`). -/
def Tup.char? : Tup → Option String
  | .arr [.leaf w] => if (charOf w.toUTF8.toList).isSome then some w else none
  | _ => none

/-- The words of the elements of the range `lo…hi`, ascending. -/
def rangeWords (lo hi : Int) : List String := (List.range (hi + 1 - lo).toNat).map fun k : Nat => toString (lo + k)

/-- A term of §c. `name` is a program's definition or parameter; `op` a builtin with its objects and arguments;
    `app` a program's operator applied. Composition is juxtaposition. -/
inductive Expr
  | name (p : Pos) (n : String)
  | op (p : Pos) (o : Op) (objs : List OExp) (args : List Expr)
  | app (p : Pos) (n : String) (args : List Expr)
  | comp (a b : Expr)
  | bin (p : Pos) (o : Bin) (a b : Expr)
  /-- `a n b`: the definition declared `_n_` (§c). -/
  | inf (p : Pos) (n : String) (a b : Expr)
  | conv (p : Pos) (a : Expr)
  | compl (p : Pos) (a : Expr)
  | pair (p : Pos) (a b : Expr)
  | junc (p : Pos) (a b : Expr)
  | fold (p : Pos) (right : Bool) (r : Expr)
  /-- A table; `ty` the declared type of the input whose `where` table it is (`Expand.bindIns`), which its objects
      are unified with as a typed definition's are. -/
  | lit (p : Pos) (ps : List (Tup × Tup)) (ty : Option (OExp × OExp) := none)
  /-- `col S "c"`: the column `c` of the schema `S`, `S ⟶ C` where `("c", C) ∈ S` (`Schema.col?`). -/
  | col (p : Pos) (s : OExp) (c : String)
  /-- `μX : φ` (`least`) or `νX : φ`: the least or the greatest `X` with `X = φ(X)`; the body reaches to the
      closing parenthesis or the end of the declaration. -/
  | fix (p : Pos) (least : Bool) (x : String) (body : Expr)
  /-- `body where x ≜ e`: the item `e` computed once, `x` in `body` its parameter (`Elab.callOf`). -/
  | whr (p : Pos) (x : String) (e body : Expr)
  /-- `⟨v ∈ V ↦ body⟩`: `body` at each element `w` of the object `V` (`v` the literal `{(∗,w)} : 1 ⟶ V`), the results
      nested pairs left to right. `V` may be an object variable: the elements are read at each use, where the call
      has solved it (`Elab.elabE`; F1). -/
  | each (p : Pos) (v : String) (o : OExp) (body : Expr)
  deriving Repr, Inhabited

/-- The position a term starts at. -/
def Expr.pos : Expr → Pos
  | .name p _ | .op p .. | .app p .. | .bin p .. | .inf p .. | .conv p _ | .compl p _ | .pair p .. | .junc p .. | .fold p ..
  | .lit p .. | .fix p .. | .col p .. | .each p .. => p
  | .comp a _ | .whr _ _ _ a => a.pos

open Lean Elab Term in
/-- Each atom by its name, the name of its `QAtomicType` constructor (`f64`, `datetime`), read from the inductive's own
    constructor list: `obj F : f64` names an atom as Lean does, with no second spelling to keep in step. -/
def atomNames : List (Lean.Name × Rel.QAtomicType) := by_elab do
  let .inductInfo i ← getConstInfo ``Rel.QAtomicType | throwError "Rel.QAtomicType is no inductive type"
  let (n, t) := (Lean.mkConst ``Lean.Name, Lean.mkConst ``Rel.QAtomicType)
  Meta.mkListLit (Lean.mkApp2 (Lean.mkConst ``Prod [0, 0]) n t) (i.ctors.map fun c =>
    Lean.mkApp4 (Lean.mkConst ``Prod.mk [0, 0]) n t (toExpr (Lean.Name.mkSimple c.getString!)) (Lean.mkConst c))

/-- The atom the counting rows (`length`, `succ`, the positions of `positions`, `asc`) run on. -/
def intAtoms : List QAtomicType := [.i64]
/-- The atoms a sum (`sum`, `sums`) runs at (`Lang.sumDen`): `i64` added exactly; a float atom added left to right
    (q's order) in `f64` and rounded once to the atom. -/
def sumAtoms : List QAtomicType := [.i64, .f32, .f64]
/-- The float atoms, whose verbs run on `f64` words: those `fval` reads. -/
def floatAtoms : List QAtomicType := [.f32, .f64]

/-- How a row runs on demand (§a, `Tm.dem`): `keys` always; `whole` its table made from its relations' whole tables
    (`GenK.ofRel`), so a closed `asc(P)` runs whole at a source with no universe; `arg` its relations run on the keys
    in demand (`dom`). A row of `whole` or `arg` given its relations needs keys exactly where one of them does.
    `bounds` is lazy on `Known` (both sides, or `pairs`) and never asks the elaborator for keys, so a row given its
    relation is closed (`cmpRelRow`, `GenK.cmp`). -/
inductive PrimDem | keys | whole | arg | bounds
  deriving Inhabited, BEq, DecidableEq, Repr

instance : Lean.ToExpr PrimDem where
  toExpr d := Lean.mkConst (match d with
    | .keys => ``PrimDem.keys | .whole => ``PrimDem.whole | .arg => ``PrimDem.arg | .bounds => ``PrimDem.bounds)
  toTypeExpr := Lean.mkConst ``PrimDem

/-- A builtin run on the keys in demand: `sym` as written (`written`), or the prelude's definition, the constant
    `prelude`, run as it (`Expand.useDef`), or neither: a converse only (`convTm`), or an `Op` of its own that
    `Calc.toTerm` reads over any allegory (`Op.row`); `sig` its relation parameters (each `X ⟶ Y` and its form:
    `some true` an order `Q : B ⟶ B` taken as its pair test `τ(Q)`, §a) and its type `A ⟶ B`, object variables
    (`ℕ` too: a declared number object is stored as `.long`, F6) instantiated by the elaborator; `conv` the row of
    its converse; `aop` its AOP reading (`Calc.builtins`) or why it has none; `mono`: it reads its parameters
    monotonically (§e's fixed points); `prelude` and `aop` named unchecked (`Test` and `Calc` check them). A row
    that is the fused form of a definition (§4) carries its text in `prelude`; `build` runs the row or the text by the
    `.prim` rule (no `q` → row; no universe → row; initial segment or `native` atom → `Prim.cut`; else `Pre.textAt`). -/
structure Prim where
  sym : String
  sig : List ((OExp × OExp) × Option Bool) × OExp × OExp
  conv : Option String := none
  written : Bool := true
  prelude : Option Lean.Name := none
  aop : Except String Lean.Name := .error "it is not written"
  mono : Bool := true
  /-- Whether it runs on demand (`Tm.dem`, `PrimDem`). -/
  dem : PrimDem := .keys
  /-- Its number object variables, each with the atoms it runs at (`length`'s `ℕ` at `intAtoms`, `sum`'s and `sums`'s
      values at `sumAtoms`, a unary float verb's at `floatAtoms`): an object of any other atom is refused as `succ`
      refuses one (`Elab.numObj`), never left to fail inside its definition. -/
  num : List (String × List QAtomicType) := []
  /-- The atoms of its `num` variables at which it has no definition and runs as itself (`sum`'s `floatAtoms`: it
      rounds once, which no fold of `plus` does); a theorem's hypothesis about its definition reads this field. -/
  native : List QAtomicType := []
  /-- Its object variables whose canon order it reads as their value order (`sums`'s positions): each must be an
      object of an atom stored as an integer (`QAtomicType.intOrd`), refused by name elsewhere (`Elab.build`). -/
  ord : List String := []
  /-- Its meaning commutes with keying (`Prim.KeyLifts`): given families over `I`, it runs once on them keyed at the
      objects `I×v` (`Elab.appliedRowL`). Set only beside a proof: `Prim.keyLifts_ok` lists every row that sets it. -/
  keyLift : Bool := false
  deriving Inhabited

def consRow : Prim :=
  { sym := "cons", sig := ([], .prod (.var {} "B") (.list (.var {} "B")), .list (.var {} "B")),
    conv := "uncons", aop := .ok `Freyd.Alg.RelSet.ListRel.cons }

-- `F(R)` is written as its `Op`, which `Calc.toTerm` reads as a relator
def mapRow : Prim :=
  { sym := "F", sig := ([((.var {} "A", .var {} "B"), some false)], .list (.var {} "A"), .list (.var {} "B")),
    written := false }
-- `length = ⦇[0, π₁ succ]⦈`, `sum = ⦇[0, plus]⦈` (§4, `prelude`): each step kept in the object, as `succ`,
-- `plus` keep theirs
def lengthRow : Prim :=
  { sym := "length", num := [("ℕ", intAtoms)], sig := ([], .list (.var {} "E"), .var {} "ℕ"),
    prelude := `Rel.Programs.prelude.length,
    aop := .ok `Freyd.Alg.RelSet.ListRel.length }
def sumRow : Prim :=
  { sym := "sum", num := [("ℕ", sumAtoms)], native := floatAtoms, sig := ([], .list (.var {} "ℕ"), .var {} "ℕ"),
    prelude := `Rel.Programs.prelude.sum,
    aop := .ok `Freyd.Alg.RelSet.ListRel.sum }
/-- `asc(P)`: q's `asc` of the set `dom P`, `j ↦` its `j`-th smallest element in `Obj.lt` order; not `mono`: a
    larger `P` renumbers. Its definition `(dom(P) Λ(> dom(P)) length)°` is `Tm.ascDef`, proved equal to the row's
    meaning where `dom P` has a sorted list (`Tm.ascDef_den`). -/
def ascRow : Prim :=
  { sym := "asc", num := [("ℕ", intAtoms)], sig := ([((.var {} "B", .var {} "B"), some false)], .var {} "ℕ", .var {} "B"),
    mono := false, prelude := `Rel.Programs.prelude.asc, aop := .error "AOP declares no numbering of a set by its order", dem := .whole }
/-- `Rᴵ`: the family `R : I ⟶ A×B` as one relation `I×A ⟶ B`, the fused form of its definition
    `⟨π₁R,π₂⟩dom(π₁π₁ ∩ π₂)π₁π₂` (`prelude`), `R` run on the keys in demand (`Tab.flat`). -/
def flatRow : Prim :=
  { sym := "flat", sig := ([((.var {} "I", .prod (.var {} "A") (.var {} "B")), some false)],
      .prod (.var {} "I") (.var {} "A"), .var {} "B"),
    prelude := `Rel.Programs.prelude.flat, written := false,
    aop := .error "AOP declares no family read as one relation of the key and the source" }
/-- `⦇e,S⦈` given a family (§e): `e : I ⟶ V×V`, `S : (I×V)×E ⟶ I×V` as one relation `I×[E] ⟶ V`, the fused form
    of its definition `(π₁π₁° ∩ π₂⦇ran⟨𝟙,eπ₂⟩, S ∩ π₁π₁π₁°⦈)π₂` (`prelude`), one fold per (key, array) in demand
    (`GenK.foldI`). -/
def foldIRow : Prim :=
  { sym := "foldI", sig := ([((.var {} "I", .prod (.var {} "V") (.var {} "V")), some false),
      ((.prod (.prod (.var {} "I") (.var {} "V")) (.var {} "E"), .prod (.var {} "I") (.var {} "V")), some false)],
      .prod (.var {} "I") (.list (.var {} "E")), .var {} "V"),
    prelude := `Rel.Programs.prelude.foldI, written := false,
    aop := .error "AOP declares no fold of a family read as one relation of the key and the list" }
/-- `star(R) ≜ μX : 𝟙 ∪ R X`, the prelude's, run as its fused form `Tab.star` (semi-naive, on the keys in demand, so
    also on an object with no universe, where the closed `μ` cannot run). -/
def starRow : Prim :=
  { sym := "star", sig := ([((.var {} "B", .var {} "B"), some false)], .var {} "B", .var {} "B"),
    prelude := `Rel.Programs.prelude.star, keyLift := true }
/-- `dom(R) = 𝟙 ∩ R R°`, the fused form of its definition `⟨𝟙,R⟩π₁` (`prelude`), `R` run on the keys in demand
    (`GenK.dom`); `B` named by its parameter only (`Prim.objs`). -/
def domRow : Prim :=
  { sym := "dom", sig := ([((.var {} "A", .var {} "B"), some false)], .var {} "A", .var {} "A"), conv := "dom",
    prelude := `Rel.Programs.prelude.dom, written := false, dem := .arg, aop := .error "a row of the allegory, not of AOP's catalogue" }
/-- `ran(R) = 𝟙 ∩ R° R`, the fused form of its definition `dom(R°)` (`prelude`), one column sorted where the
    definition sorts two (`GenK.ran`); `A` named by its parameter only (`Prim.objs`). -/
def ranRow : Prim :=
  { sym := "ran", sig := ([((.var {} "A", .var {} "B"), none)], .var {} "B", .var {} "B"), conv := "ran",
    prelude := `Rel.Programs.prelude.ran, written := false, dem := .arg, aop := .error "a row of the allegory, not of AOP's catalogue" }
/-- `[] : A ⟶ [B]`, every source to the empty list, the fused form of its definition `Λ(𝟘)` (`prelude`), a
    constant column (`GenK.nil`). -/
def nilRow : Prim :=
  { sym := "nil", sig := ([], .var {} "A", .list (.var {} "B")),
    prelude := `Rel.Programs.prelude.nil, written := false, aop := .error "a row of the allegory, not of AOP's catalogue" }
/-- `est(Q) ≜ ∋ − (⟨∋,∋⟩(𝟙 − cor(Q ∪ 𝟙))π₁)` (`Tm.estDef`, division-free) given `Q` as its pair test
    (`Tab.est`): the row runs it fused. -/
def estRow : Prim :=
  { sym := "est", sig := ([((.var {} "B", .var {} "B"), some true)], .list (.var {} "B"), .var {} "B"),
    prelude := `Rel.Programs.prelude.est,
    written := false, aop := .error "a row of the allegory, not of AOP's catalogue" }
/-- `front(Q) ≜ Λ(∋ − ∋ (Q − Q°))` given `Q` as its pair test (`Tab.front`); not `mono`: a larger `Q` drops
    more elements. -/
def frontRow : Prim :=
  { sym := "front", sig := ([((.var {} "B", .var {} "B"), some true)], .list (.var {} "B"), .list (.var {} "B")),
    prelude := `Rel.Programs.prelude.front, written := false, mono := false,
    aop := .error "a row of the allegory, not of AOP's catalogue" }
/-- The value verb `s` of `arithOps`, `N×N ⟶ N` on a number atom, no universe inside (§3.5): `build` cuts it to a
    bounded object's universe `U` as `(U×U) s U` (`Tm.cut2`), so it is never written. -/
def arithRow (s : String) : Prim :=
  { sym := s, sig := ([], .prod (.var {} "N") (.var {} "N"), .var {} "N"), num := [("N", intAtoms ++ floatAtoms)],
    written := false, aop := .error "AOP declares no arithmetic on atoms" }
/-- `succ : N ⟶ N` on `i64`, no universe inside: cut to `U` as `U succ U` (`Tm.cut1`). -/
def succRow : Prim :=
  { sym := "succ", sig := ([], .var {} "N", .var {} "N"), num := [("N", intAtoms)], written := false,
    aop := .error "AOP declares no successor on atoms" }
/-- `mix : N ⟶ N` on `i64`: each counter to splitmix64's output there (`Op.mixWord`), the random source of the
    frame library (dataframe F8); a pure hash, so a program reading it is a relation like any other. -/
def mixRow : Prim :=
  { sym := "mix", sig := ([], .var {} "N", .var {} "N"), num := [("N", [.i64])],
    aop := .error "AOP declares no hash on atoms" }
/-- `at : [B]×ν ⟶ B`, q's index `xs[k]` on `i64`: the pair `(xs, k)` to the element at a nonneg `k` below the length (`atOn`).
    Not written: the surface `at(k)` (op table `.index k`) elaborates to `⟨𝟙, ⊤ {k}⟩ at` (`indexAt`). -/
def indexRow : Prim :=
  { sym := "at", sig := ([], .prod (.list (.var {} "B")) (.var {} "N"), .var {} "B"), num := [("N", [.i64])],
    written := false, aop := .error "AOP declares no indexing of a list by a number" }
/-- The order test `s` of `cmpOps`, the coreflexive `N×N ⟶ N×N` on the pairs in order, no universe inside. -/
def cmpRow (s : String) : Prim :=
  { sym := s, sig := ([], .prod (.var {} "N") (.var {} "N"), .prod (.var {} "N") (.var {} "N")), written := false,
    num := [("N", (atomNames.map (·.2)).filter (·.ordNum.isSome))], native := floatAtoms,
    prelude := some (.str `Rel.Programs.prelude s), aop := .error "AOP declares no order on atoms" }
-- the row's fused atoms, `num` minus `native`, are the integer-stored ones (`Tm.lt_row_den`'s hypothesis)
#guard (atomNames.map (·.2)).all fun t => (t.ordNum.isSome && !floatAtoms.contains t) == t.intOrd
/-- `≤`, `<` on a universe `U : N ⟶ N`, the row `cmpRow` given `U` as `⟨dom U, ⊤(dom U)⟩ cmpRow π₂`
    (`Tm.cmpDef`), run fused by `GenK.cmpRel`: closed, or on the pairs a meet hands it. Its symbol is the surface one,
    distinct from the test row's `lt`/`le`. -/
def cmpRelRow (strict : Bool) : Prim :=
  { sym := ordSym strict, sig := ([((.var {} "N", .var {} "N"), some false)], .var {} "N", .var {} "N"),
    written := false, dem := .bounds, aop := .error "AOP declares no order on atoms" }

/-- Every builtin run on the keys in demand: adding one is adding its row. -/
def prims : List Prim :=
  [{ sym := "τ", sig := ([], .var {} "A", .list (.var {} "A")),
     prelude := `Rel.Programs.prelude.τ, aop := .ok `Freyd.Alg.singletonMap }, consRow, mapRow,
   -- `filter(p)`, `takewhile(p)` given one relation run as their mask forms (`rep_filterC`, `rep_takewhileC`, `elems_test`);
   -- not `mono`: a larger `p` keeps more elements, a different list, not a superset of pairs (`rowDens`)
   { sym := "filter", sig := ([((.var {} "B", .var {} "B"), some false)], .list (.var {} "B"), .list (.var {} "B")),
     mono := false, prelude := `Rel.Programs.prelude.filter },
   { sym := "takewhile",
     sig := ([((.var {} "B", .var {} "B"), some false)], .list (.var {} "B"), .list (.var {} "B")),
     mono := false, prelude := `Rel.Programs.prelude.takewhile },
   { sym := "thinL", sig := ([((.var {} "B", .var {} "B"), some true)], .list (.var {} "B"), .list (.var {} "B")),
     mono := false, prelude := `Rel.Programs.prelude.thinL, aop := .ok `Freyd.Alg.RelSet.ListRel.thinL },
   { sym := "merge",
     sig := ([((.var {} "B", .var {} "B"), some true)], .prod (.list (.var {} "B")) (.list (.var {} "B")),
       .list (.var {} "B")),
     mono := false, prelude := `Rel.Programs.prelude.merge, aop := .ok `Freyd.Alg.RelSet.ListRel.merge },
   { sym := "loop",
     sig := ([((.prod (.var {} "X") (.var {} "Y"), .var {} "X"), some false)],
       .prod (.var {} "X") (.list (.var {} "Y")), .var {} "X"),
     prelude := `Rel.Programs.prelude.loop, aop := .error "AOP declares no iteration to a fixed point from the left" },
   { sym := "uncons", sig := ([], .list (.var {} "B"), .prod (.var {} "B") (.list (.var {} "B"))),
     conv := "cons", written := false },
   lengthRow, sumRow,
   { sym := "inits", sig := ([], .list (.var {} "B"), .list (.list (.var {} "B"))),
     prelude := `Rel.Programs.prelude.inits, aop := .ok `Freyd.Alg.RelSet.ListRel.initsR },
   -- the prelude's folds run as their slice forms (`rep_tailsC`, `rep_prefixC`, `rep_suffixC`, `rep_concatC`)
   { sym := "tails", sig := ([], .list (.var {} "B"), .list (.list (.var {} "B"))),
     prelude := `Rel.Programs.prelude.tails },
   { sym := "prefix", sig := ([], .list (.var {} "B"), .list (.var {} "B")),
     prelude := `Rel.Programs.prelude.prefix },
   { sym := "suffix", sig := ([], .list (.var {} "B"), .list (.var {} "B")),
     prelude := `Rel.Programs.prelude.suffix },
   { sym := "concat", sig := ([], .list (.list (.var {} "B")), .list (.var {} "B")),
     prelude := `Rel.Programs.prelude.concat },
   { sym := "cat", sig := ([], .prod (.list (.var {} "B")) (.list (.var {} "B")), .list (.var {} "B")),
     prelude := `Rel.Programs.prelude.cat, conv := "uncat", aop := .ok `Freyd.Alg.RelSet.ListRel.cat },
   { sym := "uncat", sig := ([], .list (.var {} "B"), .prod (.list (.var {} "B")) (.list (.var {} "B"))),
     conv := "cat", written := false },
   { sym := "zip", sig := ([], .prod (.list (.var {} "A")) (.list (.var {} "B")),
       .list (.prod (.var {} "A") (.var {} "B"))),
     aop := .ok `Freyd.Alg.RelSet.Pointfree.zip },
   { sym := "snoc", sig := ([], .prod (.list (.var {} "B")) (.var {} "B"), .list (.var {} "B")), conv := "unsnoc",
     prelude := `Rel.Programs.prelude.snoc,
     aop := .error "AOP's `snoc` is on snoc lists (`SL.snoc`), not on the cons lists `[α]` reads as" },
   { sym := "unsnoc", sig := ([], .list (.var {} "B"), .prod (.list (.var {} "B")) (.var {} "B")),
     conv := "snoc", written := false },
   { sym := "setify", sig := ([], .list (.var {} "B"), .list (.var {} "B")),
     prelude := `Rel.Programs.prelude.setify, aop := .ok `Freyd.Alg.RelSet.ListRel.setify },
   -- `positions(p)`: dataframe §3.1's `where(dom(xs ≫ p))`, named so because `where` is a keyword (§c). Its `dfn` is
   -- `(𝟙 − dom(s (𝟙 − dom(length)))) Λ(s length)`, `s` the prefixes ending just before a passing element: their lengths
   -- are the positions, `Λ` lists them ascending; the guard keeps `xs` only where every length is in `ℕ`'s universe,
   -- so at an initial segment the text is the row cut to it (`Prim.cut`), where `ℕ` has no universe a text still runs
   { sym := "positions", num := [("ℕ", intAtoms)],
     sig := ([((.var {} "B", .var {} "B"), some false)], .list (.var {} "B"), .list (.var {} "ℕ")),
     prelude := `Rel.Programs.prelude.positions,
     mono := false, aop := .error "AOP declares no positions of the elements of a list that pass a test" },
   ascRow,
   -- `sums(x)`: q's `sums` per key, `x : κ×ν ⟶ γ`, the key the source's first component; the fused form of
   -- `agg(dom(x) (𝟙 × ≥) dom(x), F(x) ⦇[0, plus]⦈)` (`rowDens`). Not `mono`: a larger `x` changes the sums. Its
   -- definition is, as `asc`'s, no text `build` runs. The positions `P` and the values `V` are two objects: only
   -- `V` is summed, so only `V` is a number object (`num`); `P` is only ordered (`ord`)
   { sym := "sums", num := [("V", sumAtoms)], ord := ["P"],
     sig := ([((.prod (.var {} "K") (.var {} "P"), .var {} "V"), some false)], .prod (.var {} "K") (.var {} "P"),
       .var {} "V"),
     mono := false, aop := .error "AOP declares no prefix sums per key", dem := .whole },
   flatRow,
   -- `x $ F`: each value of `x : A ⟶ N` to the same number at `F`'s atom (`QAtomicType.embed`, typed base S6), written
   -- as its own infix form, which names the target object
   { sym := "$", sig := ([], .var {} "N", .var {} "F"), written := false,
     aop := .error "AOP declares no change of a number's representation" },
   -- `ymd`: a text `[C]` to the day it spells (`Db.Csv.ymd`: `yyyy.mm.dd` or `yyyy-mm-dd`) at a date object `D`;
   -- no row where it spells none (`Tab.ymd`)
   { sym := "ymd", num := [("C", [.char]), ("D", [.date])], sig := ([], .list (.var {} "C"), .var {} "D"),
     aop := .error "AOP declares no reading of a text as a day" },
   foldIRow, starRow, domRow, ranRow, nilRow, estRow, frontRow] ++
  -- `sqrt`, `neg`, …, `xexp`: each a relation `F ⟶ D` (`F×F ⟶ D` where its `Op` reads two operands) from a float
  -- object `F` (`num` its float atoms) to an object `D` of the row's answer atom (`floatOps`), one row per name
  (floatOps.map fun (s, o, u) =>
    { sym := s, sig := ([], if o.readsAcc then .prod (.var {} "F") (.var {} "F") else .var {} "F", .var {} "D"),
      num := [("F", floatAtoms), ("D", [u])],
      aop := .error "AOP declares no floating-point function" }) ++
  -- the value verbs (`arithOps`), `succ`, the order tests `lt` `le` (`cmpOps`): rows on atoms, no universe inside;
  -- `build` writes each, cut to a bounded object's universe `U` as `⟨π₁U, π₂U⟩ row U` (§3.5), so none is written
  arithOps.map (arithRow ·.1) ++ [succRow, mixRow, indexRow] ++ cmpOps.map (cmpRow ·.1) ++ cmpOps.map (cmpRelRow ·.2)

def Prim.find?(s : String) : Option Prim := prims.find? (·.sym == s)

/-- The one table of builtins: symbol and arity. A program may not define or take as a parameter a name
    in it (§c). -/
def Op.table : List (String × Op × Nat) :=
  [("𝟙", .id, 0), ("𝟘", .zero, 0), ("⊤", .top, 0), ("π₁", .outl, 0),
   ("π₂", .outr, 0), ("inl", .inl, 0), ("inr", .inr, 0), ("∋", .mem, 0), ("≤", .leq, 0), ("<", .lt, 0), ("succ", .succ, 0),
   ("plus", .arith Rel.Kernel.Ew.add, 0), ("times", .arith Rel.Kernel.Ew.mul, 0),
   ("minus", .arith Rel.Kernel.Ew.sub, 0), ("div", .arith Rel.Kernel.Ew.idiv, 0),
   ("mod", .arith Rel.Kernel.Ew.imod, 0), ("max", .arith Rel.Kernel.Ew.greater, 0),
   ("min", .arith Rel.Kernel.Ew.lesser, 0),
   -- q's `%` by its word and its glyph; `Op.sym` prints the first
   ("divide", .arith Rel.Kernel.Ew.divide, 0), ("%", .arith Rel.Kernel.Ew.divide, 0), ("α", .alpha, 0),
   -- `Λ(R) ≜ (𝟙÷∋)E(R)` (Elab.singletonImage); `E(R) ≜ (∋R)÷∋`.
   ("Λ", .lam, 1), ("E", .E, 1),
   ("F", .map, 1),
   ("hylo", .hylo, 2),
   ("at", .index 0, 0)] ++
  (prims.filter fun r => r.written && r.prelude.isNone).map fun r => (r.sym, .prim r.sym, r.sig.1.length)

-- `at(i)` prints with its position, which no table row holds
def Op.sym : Op → String
  | .index i => s!"at({i})"
  | .prim s => s
  | o => ((Op.table.find? (·.2.1 == o)).map (·.1)).getD "?"

/-- Each name of `σ` replaced by its term: a `where` item put in place in its body (§c). -/
partial def Expr.subst (σ : List (String × Expr)) : Expr → Expr
  | .name p n => (σ.lookup n).getD (.name p n)
  | .op p o os as => .op p o os (as.map (·.subst σ))
  | .app p n as => .app p n (as.map (·.subst σ))
  | .comp a b => .comp (a.subst σ) (b.subst σ)
  | .bin p o a b => .bin p o (a.subst σ) (b.subst σ)
  | .inf p n a b => .inf p n (a.subst σ) (b.subst σ)
  | .conv p a => .conv p (a.subst σ)
  | .compl p a => .compl p (a.subst σ)
  | .pair p a b => .pair p (a.subst σ) (b.subst σ)
  | .junc p a b => .junc p (a.subst σ) (b.subst σ)
  | .fold p d r => .fold p d (r.subst σ)
  | .lit p ps ty => .lit p ps ty
  | .col p s c => .col p s c
  -- `x` is bound in the body, so an outer `x` is not replaced there
  | .fix p l x b => .fix p l x (b.subst (σ.filter (·.1 != x)))
  | .whr p x e b => .whr p x (e.subst σ) (b.subst (σ.filter (·.1 != x)))
  | .each p v o b => .each p v o (b.subst (σ.filter (·.1 != v)))

/-- Every name `e` mentions, bound or free, operators applied included: a variable not among them captures nothing
    in `e`. -/
partial def Expr.names : Expr → List String
  | .name _ n => [n]
  | .op _ _ _ as => as.flatMap (·.names)
  | .app _ n as => n :: as.flatMap (·.names)
  | .comp a b | .bin _ _ a b | .pair _ a b | .junc _ a b => a.names ++ b.names
  | .fold _ _ r => r.names
  | .inf _ n a b => n :: (a.names ++ b.names)
  | .conv _ a | .compl _ a => a.names
  | .lit .. | .col .. => []
  | .fix _ _ x b => x :: b.names
  | .whr _ x e b => x :: (e.names ++ b.names)
  | .each _ v _ b => v :: b.names

/-- Whether `e` compares by an order, `<`, `≤`, `asc` or the prelude's `>`, `≥`: at `sym` such a term reads the
    program's dictionary (`Elab.symOrd`), so a definition of one mentions it where it is declared (`Expand.walk`). -/
partial def Expr.ordered : Expr → Bool
  | .name _ n => n == ">" || n == "≥"
  | .op _ o _ as => (match o with | .lt | .leq | .prim "asc" => true | _ => false) || as.any (·.ordered)
  | .app _ n as => n == ">" || n == "≥" || n == ascRow.sym || as.any (·.ordered)
  | .comp a b | .bin _ _ a b | .pair _ a b | .junc _ a b | .inf _ _ a b => a.ordered || b.ordered
  | .fold _ _ r => r.ordered
  | .conv _ a | .compl _ a => a.ordered
  | .lit .. | .col .. => false
  | .fix _ _ _ b => b.ordered
  | .whr _ _ e b => e.ordered || b.ordered
  | .each _ _ _ b => b.ordered

/-- A body: a relation, or a test `e ⊑ f` (§e). -/
inductive Body
  | rel (e : Expr)
  | test (e f : Expr)
  deriving Repr, Inhabited

/-- A parameter and its declared type `S : A ⟶ B`, its objects possibly object variables (§e). Every parameter of
    a run program declares one (`none` is a parse that `run` refuses, naming the inferred type); a family given
    to it is lifted (§e). -/
structure Param where
  name : String
  ty : Option (OExp × OExp)
  deriving Repr, Inhabited

open Lean in deriving instance ToExpr for Rel.QAtomicType

/-- An object declaration's right side: named elements, a signed number range `lo ≤ hi`, or a derived object. -/
inductive ObjDef
  | elems (ws : List String)
  /-- Named elements at the atom `t`, `ws[i]` the text of the word stored as `codes[i]` (as an `Int64`): `obj V from
      "dir" c`, the distinct values of a column on disk kept as stored (F1), not re-encoded `0…n−1` as `elems` is. -/
  | coded (t : Rel.QAtomicType) (ws : List String) (codes : List Int)
  | range (lo hi : Int)
  | alias (o : OExp)
  /-- `schema S = {k : K, v : N}`: the `Schema` of these columns, the object `Schema.obj` of it (`Expand.objInfo`). -/
  | schema (cs : List (String × OExp))
  /-- `obj N` with no right side: an unbounded number object, every `Int64` its element and `𝟙` its universe, so
      nothing of it is materialised and `<`, `succ`, the value verbs on it are bounded by their context (§0).
      `obj F : f64`: the same at the atom `t` (`atomNames`), every element of `t` an element of `F`. -/
  | num (t : Rel.QAtomicType := .i64)
  deriving Repr, Inhabited

/-- The words of its elements in order, where the declaration lists them: the one reading both a program's own
    finite objects (`Parse.after`) and an imported one's (`Parse.S.finExt`) go through. -/
def ObjDef.words : ObjDef → Option (List String)
  | .elems ws | .coded _ ws _ => some ws
  | .range lo hi => some (rangeWords lo hi)
  | _ => none

/-- A `calc` step's reason (`doc/rel-mss-proof-design.md` §3): `:= n(R, …)` cites the theorem `n` at the
    arguments `args` (none when it has no parameters), `:= ≜ n` unfolds or folds back the definition `n`. The
    cited theorem as the resolver found it: `c`, the registry's constant, or none for the program's own `n`. -/
inductive Why
  | thm (p : Pos) (n : String) (c : Option Lean.Name) (args : List Expr)
  | unfold (p : Pos) (n : String)
  deriving Repr, Inhabited

inductive Decl
  | obj (p : Pos) (n : String) (d : ObjDef)
  /-- `ty`: the declared type `A ⟶ B`, required on a relation and absent on a test (§e). -/
  | defn (p : Pos) (n : String) (ps : List Param) (b : Body) (ty : Option (OExp × OExp))
  /-- `binds`: the `where` items, each an input of the program and the table that stands for it here (IO design A.4). -/
  | print (p : Pos) (e : Expr) (binds : List (String × Expr))
  | check (p : Pos) (e f : Expr) (eq : Bool) (binds : List (String × Expr)) (proof : Option Lean.Name)
  /-- `input n : A ⟶ B from p`: a relation with no body, a parameter of the statements after it that mention it
      (IO design A.2); read from the table directory `path`, or the CSV file `path` when `csv` is its separator (`,` CSV, `\t` TSV). -/
  | input (p : Pos) (n : String) (ty : OExp × OExp) (csv : Option UInt8) (path : String)
  /-- `dictionary n : A ⟶ B`: the program's symbol dictionary `sym ⟶ text` as a run-time name, as an input is, bound
      by `n.io` to the dictionary grown by the inputs before it (`Table.dictRel`); `A` a `sym` object, `B` a text. -/
  | dict (p : Pos) (n : String) (ty : OExp × OExp)
  /-- `output n to path`: the table of the definition or input `n` written to `path` (`csv`: as one CSV file, its fields separated by that byte). -/
  | output (p : Pos) (n : String) (csv : Option UInt8) (path : String)
  /-- `theorem n(ps) on A : e = f := calc` (`⊑` when `eq` is false), each step `_ = x := why` with its line; no
      steps: the proof is owed to Lean. `on A`: each step is also evaluated as `check A x = A y` (§3). -/
  | «theorem» (p : Pos) (n : String) (ps : List Param) (e f : Expr) (eq : Bool) (on : Option Expr)
      -- each hypothesis after `if`: `e = f` or `e ⊑ f` (`some (eq, f)`), or a test applied, `t(R)` (`none`)
      (hyps : List (Expr × Option (Bool × Expr))) (steps : List (Pos × Bool × Expr × Why))
  deriving Repr, Inhabited

abbrev Program := List Decl

/-! ### Printing, in the syntax the parser reads: a composite on the right of an operator in parentheses -/

/-- `o` printed; `inner` parenthesises a product or sum, as an operand of `×`, `+` needs. -/
def OExp.render (inner : Bool) : OExp → String
  | .name _ n | .var _ n => n
  | .prod a b => let s := s!"{a.render true}×{b.render true}"; if inner then s!"({s})" else s
  | .sum a b => let s := s!"{a.render true}+{b.render true}"; if inner then s!"({s})" else s
  | .list a => s!"[{a.render false}]"
  | .each _ o a => s!"⟨{o.render false} ↦ {a.render false}⟩"

def OExp.show (o : OExp) : String := o.render false

/-- The object variables of `o`, in order, each once. -/
def OExp.vars : OExp → List String
  | .var _ n => [n]
  | .name .. => []
  | .prod a b | .sum a b => (a.vars ++ b.vars).eraseDups
  | .list a => a.vars
  | .each _ o a => (o.vars ++ a.vars).eraseDups

/-- The object variables of a row's parameters and type, in order, each once. -/
def Prim.vars (r : Prim) : List String :=
  ((r.sig.1.flatMap fun ((x, y), _) => x.vars ++ y.vars) ++ r.sig.2.1.vars ++ r.sig.2.2.vars).eraseDups

/-- The row's source is a variable nothing else in its signature names (`nil : A ⟶ [B]`): a use no context fixes
    starts at the object `1` (`settleOpen`). Kernel rows (`$`, `sqrt`) have the same signature shape but their source is
    fixed by the atoms they run at, so only a prelude definition (`nil`, a constant relation) is open. -/
def Prim.openSrc (r : Prim) : Bool :=
  match r.sig.2.1 with
  | .var _ v => r.prelude.isSome && r.sig.1.isEmpty && !(r.sig.2.2.vars.contains v)
  | _ => false

/-- The object variables a `⟨θ ↦ A⟩` in `o` takes its elements from: those of each `θ`, which a use must solve before
    the elements are known. -/
def OExp.eachVars : OExp → List String
  | .name .. | .var .. => []
  | .prod a b | .sum a b => a.eachVars ++ b.eachVars
  | .list a => a.eachVars
  | .each _ o a => o.vars ++ o.eachVars ++ a.eachVars

/-- Whether `o` has a `⟨θ ↦ A⟩`. -/
def OExp.hasEach : OExp → Bool
  | .name .. | .var .. => false
  | .prod a b | .sum a b => a.hasEach || b.hasEach
  | .list a => a.hasEach
  | .each .. => true

/-- The same for the term `e`: its objects and its own `⟨v ∈ V ↦ …⟩`. -/
partial def Expr.eachVars : Expr → List String
  | .name .. => []
  | .op _ _ os as => os.flatMap OExp.eachVars ++ as.flatMap (·.eachVars)
  | .app _ _ as => as.flatMap (·.eachVars)
  | .comp a b | .bin _ _ a b | .pair _ a b | .junc _ a b | .inf _ _ a b | .whr _ _ a b => a.eachVars ++ b.eachVars
  | .fold _ _ r | .conv _ r | .compl _ r | .fix _ _ _ r => r.eachVars
  | .lit _ _ ty => (ty.map fun (a, b) => a.eachVars ++ b.eachVars).getD []
  | .col _ s _ => s.eachVars
  | .each _ _ o b => o.vars ++ o.eachVars ++ b.eachVars

/-- The row's name as a leaf of an error: `sym`, with `( )` when it takes relations. -/
def Prim.leaf (r : Prim) : String := if r.sig.1.isEmpty then r.sym else s!"{r.sym}( )"

/-- A definition's head and type as `typesOf` prints it and the parser reads it back:
    `n(R : A ⟶ B, …) : C ⟶ D`, each type given as its text; a test has no type of its own (§e). -/
def sigText (n : String) (ps : List (String × Option String)) (ty : Option String) : String :=
  let h := if ps.isEmpty then n else
    n ++ "(" ++ ", ".intercalate (ps.map fun (q, t) => match t with | some t => s!"{q} : {t}" | none => q) ++ ")"
  match ty with | some t => s!"{h} : {t}" | none => h

def OExp.arrow (ty : OExp × OExp) : String := s!"{ty.1.show} ⟶ {ty.2.show}"

/-- A definition's declaration as written: `sigText` of its declared types. -/
def sigOf (n : String) (ps : List Param) (ty : Option (OExp × OExp)) : String :=
  sigText n (ps.map fun q => (q.name, q.ty.map OExp.arrow)) (ty.map OExp.arrow)

/-- The level a left operand prints at: `1` for a fixed point, whose body would read on past the operator. -/
def Expr.lhs : Expr → Nat
  | .fix .. => 1
  | _ => 0

/-- `e` printed at the level `l`,parenthesised as §c's one level needs: `0` anywhere or the left operand of a
    composite or infix term, `1` its right operand or the operand of `∼` (a composite or infix term in
    parentheses), `2` under `°` (a complement too). `full` puts every composite and infix term in parentheses:
    the parser guards compare it with the reading written out. -/
partial def Expr.render (l : Nat) (full : Bool := false) : Expr → String
  | .name _ n => n
  | .op _ o objs args =>
    let os := if objs.isEmpty then "" else "(" ++ ", ".intercalate (objs.map OExp.show) ++ ")"
    let as := if args.isEmpty then "" else "(" ++ ", ".intercalate (args.map (Expr.render 0 full)) ++ ")"
    o.sym ++ os ++ as
  | .app _ n args => n ++ "(" ++ ", ".intercalate (args.map (Expr.render 0 full)) ++ ")"
  | .comp (.bin _ .symDiv (.op _ .id [] []) (.op _ .mem [] [])) (.op _ .E [] [a]) =>
    let s := if full then s!"(𝟙 ÷ ∋) E({a.render 0 full})" else s!"(𝟙÷∋)E({a.render 0 full})"
    if full || l ≥ 1 then s!"({s})" else s
  | .comp a b => let s := s!"{a.render a.lhs full} {b.render 1 full}"; if full || l ≥ 1 then s!"({s})" else s
  | .bin _ o a b => let s := s!"{a.render a.lhs full} {o.sym} {b.render 1 full}"; if full || l ≥ 1 then s!"({s})" else s
  | .inf _ n a b => let s := s!"{a.render a.lhs full} {n} {b.render 1 full}"; if full || l ≥ 1 then s!"({s})" else s
  | .conv _ a => s!"{a.render 2 full}°"
  | .compl _ a => let s := s!"∼{a.render 1 full}"; if l ≥ 2 then s!"({s})" else s
  | .pair _ a b => s!"⟨{a.render 0 full}, {b.render 0 full}⟩"
  | .junc _ a b => s!"[{a.render 0 full}, {b.render 0 full}]"
  | .fold _ d r => s!"⦇{r.render 0 full}⦈{if d then "ʳ" else ""}"
  | .lit _ ps _ => "{" ++ ", ".intercalate (ps.map fun (a, b) => (Tup.pair a b).show) ++ "}"
  | .col _ s c => s!"col {s.render true} {c.quote}"
  | .fix _ least x b =>
    let s := s!"{if least then "μ" else "ν"}{x} : {b.render 0 full}"; if full || l ≥ 1 then s!"({s})" else s
  -- printed as its expansion, the item in place, so a message reads the term as written in use
  | .whr _ x e b => (b.subst [(x, e)]).render l full
  | .each _ v o b => s!"⟨{v} ∈ {o.show} ↦ {b.render 0 full}⟩"

def Expr.show (e : Expr) : String := e.render 0

-- here, not in `Grammar` (meta): `Tm.number`'s proofs in `GenSound` run `Expand.tmE`, which reads these instances
deriving instance Lean.ToExpr for OExp
deriving instance Lean.ToExpr for Op
deriving instance Lean.ToExpr for Bin
deriving instance Lean.ToExpr for Tup
deriving instance Lean.ToExpr for Expr
deriving instance Lean.ToExpr for Body
deriving instance Lean.ToExpr for Param
deriving instance Lean.ToExpr for ObjDef
deriving instance Lean.ToExpr for Why
deriving instance Lean.ToExpr for Decl

end Rel.Lang
