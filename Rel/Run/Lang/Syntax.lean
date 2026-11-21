import Lean
import Rel.Kernel.Op
import Rel.Run.Core
import Rel.Kernel.Cast
import Rel.Run.Cast

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

/-- A front-end error: where, and what was found against what was expected. -/
structure Err where
  pos : Pos
  msg : String
  deriving Repr, Inhabited

/-- Line 0 is no place in the program: an error of the prelude's own text says where in its message. -/
instance : ToString Err := ⟨fun e => if e.pos.line == 0 then e.msg else s!"{e.pos}: {e.msg}"⟩

/-- An error raised re-reading the program `n` a program imports: where in `n` it is. -/
def Err.inProg (n : String) (e : Err) : Err := ⟨default, s!"in the program `{n}`, {e.pos}: {e.msg}"⟩

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
  deriving Repr, Inhabited

/-- The builtin operators of §b. A constant (arity 0) may take its objects, `⊤(A,B)`; the others take relations.
    `arith k` is the qlean kernel's integral value verb `k` on pairs of numbers (`Alg.arith`): one constructor, so
    every verb is typed, lifted and run by one path; `prim s` the row `s` of `prims`. `inl`, `inr`, `map` run as
    their rows too (`Op.row`), kept as constructors for `Calc.toTerm`'s readings over any allegory. -/
inductive Op
  | id | zero | top | outl | outr | inl | inr | leq | lt | succ | arith (k : UInt8)
  | nil | alpha | prim (s : String)
  | dom | ran | lam | E | est | thin | map
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
  deriving Repr, Inhabited

/-- The position a term starts at. -/
def Expr.pos : Expr → Pos
  | .name p _ | .op p .. | .app p .. | .bin p .. | .inf p .. | .conv p _ | .compl p _ | .pair p .. | .junc p .. | .fold p ..
  | .lit p .. | .fix p .. | .col p .. => p
  | .comp a _ => a.pos

/-- The atom the counting rows (`length`, `sum`, `sums`, `succ`) run on. -/
def intAtoms : List QAtomicType := [.i64]
/-- The float atoms, whose verbs run on `f64` words: those `fval` reads. -/
def floatAtoms : List QAtomicType := [.f32, .f64]

/-- A builtin run on the keys in demand: `sym` as written (`written`), or the prelude's definition, the constant
    `prelude`, run as it (`Expand.useDef`), or neither: a converse only (`convTm`), or an `Op` of its own that
    `Calc.toTerm` reads over any allegory (`Op.row`); `sig` its relation parameters (each `X ⟶ Y` and its form:
    `some true` an order `Q : B ⟶ B` taken as its pair test `τ(Q)`, §a) and its type `A ⟶ B`, object variables
    (`ℕ` too: a declared number object is stored as `.long`, F6) instantiated by the elaborator; `conv` the row of
    its converse; `aop` its AOP reading (`Calc.builtins`) or why it has none; `mono`: it reads its parameters
    monotonically (§e's fixed points); `prelude` and `aop` named unchecked (`Test` and `Calc` check them). A row
    that is the fused form of a definition (§4) is keyed in `Elab.dfns`, which builds the definition. -/
structure Prim where
  sym : String
  sig : List ((OExp × OExp) × Option Bool) × OExp × OExp
  conv : Option String := none
  written : Bool := true
  prelude : Option Lean.Name := none
  aop : Except String Lean.Name := .error "it is not written"
  mono : Bool := true
  /-- Its table is made from its relations' whole tables (`GenK.ofRel`): it needs no keys where they need none
      (`Tm.dem`), so a closed `asc(P)` runs whole at a source with no universe. -/
  whole : Bool := false
  /-- Its object variables that must be number objects, each with the atoms it admits: those its constant reads at
      `.long` (`sums`'s positions `ℕ` and values `V`, `length`'s and `sum`'s `ℕ`) at `i64`, a unary float verb's at the
      float atoms; refused as `succ` refuses one (`Elab.numObj`), never left to fail inside its definition. -/
  num : List (String × List QAtomicType) := []
  deriving Inhabited

def consRow : Prim :=
  { sym := "cons", sig := ([], .prod (.var {} "B") (.list (.var {} "B")), .list (.var {} "B")),
    conv := "uncons", aop := .ok `Freyd.Alg.RelSet.ListRel.cons }

def memRow : Prim :=
  { sym := "∋", sig := ([], .list (.var {} "B"), .var {} "B"), aop := .ok `Freyd.Alg.PowerAllegory.eps }

-- `inl`, `inr`, `F(R)` are written as their `Op`s, which `Calc.toTerm` reads as a coproduct's injections and a relator
def inlRow : Prim :=
  { sym := "inl", sig := ([], .var {} "A", .sum (.var {} "A") (.var {} "B")), conv := "inl°", written := false }
def inrRow : Prim :=
  { sym := "inr", sig := ([], .var {} "B", .sum (.var {} "A") (.var {} "B")), conv := "inr°", written := false }
-- the injections' converses, which `[R,S] = inl°R ∪ inr°S` runs on the sum values in demand (`convTm`)
def inlConvRow : Prim :=
  { sym := "inl°", sig := ([], .sum (.var {} "A") (.var {} "B"), .var {} "A"), conv := "inl", written := false }
def inrConvRow : Prim :=
  { sym := "inr°", sig := ([], .sum (.var {} "A") (.var {} "B"), .var {} "B"), conv := "inr", written := false }
def mapRow : Prim :=
  { sym := "F", sig := ([((.var {} "A", .var {} "B"), some false)], .list (.var {} "A"), .list (.var {} "B")),
    written := false }
-- `length = ⦇[0, π₁ succ]⦈`, `sum = ⦇[0, plus]⦈ʳ` (§4, `Elab.dfns`): each step kept in the object, as `succ`,
-- `plus` keep theirs
def lengthRow : Prim :=
  { sym := "length", num := [("ℕ", intAtoms)], sig := ([], .list (.var {} "E"), .var {} "ℕ"),
    aop := .ok `Freyd.Alg.RelSet.ListRel.length }
def sumRow : Prim :=
  { sym := "sum", num := [("ℕ", intAtoms)], sig := ([], .list (.var {} "ℕ"), .var {} "ℕ"),
    aop := .ok `Freyd.Alg.RelSet.ListRel.sum }
/-- `Rᴵ`: the family `R : I ⟶ A×B` as one relation `I×A ⟶ B`, the fused form of its definition
    `⟨π₁R,π₂⟩dom(π₁π₁ ∩ π₂)π₁π₂` (`Elab.dfns`), `R` run on the keys in demand (`Tab.flat`). -/
def flatRow : Prim :=
  { sym := "flat", sig := ([((.var {} "I", .prod (.var {} "A") (.var {} "B")), some false)],
      .prod (.var {} "I") (.var {} "A"), .var {} "B"),
    written := false, aop := .error "AOP declares no family read as one relation of the key and the source" }

/-- Every builtin run on the keys in demand: adding one is adding its row. -/
def prims : List Prim :=
  [{ sym := "τ", sig := ([], .var {} "A", .list (.var {} "A")),
     aop := .ok `Freyd.Alg.singletonMap }, consRow, memRow, inlRow, inrRow, mapRow,
   -- `filter(p)`, `takewhile(p)` given one relation run as their mask forms (`rep_filterC`, `rep_takewhileC`, `elems_test`);
   -- not `mono`: a larger `p` keeps more elements, a different list, not a superset of pairs (`rowDens`)
   { sym := "filter", sig := ([((.var {} "B", .var {} "B"), some false)], .list (.var {} "B"), .list (.var {} "B")),
     mono := false, prelude := `Rel.Programs.prelude.filter },
   { sym := "takewhile",
     sig := ([((.var {} "B", .var {} "B"), some false)], .list (.var {} "B"), .list (.var {} "B")),
     mono := false, prelude := `Rel.Programs.prelude.takewhile },
   { sym := "thinL", sig := ([((.var {} "B", .var {} "B"), some true)], .list (.var {} "B"), .list (.var {} "B")),
     mono := false, aop := .ok `Freyd.Alg.RelSet.ListRel.thinL },
   { sym := "merge",
     sig := ([((.var {} "B", .var {} "B"), some true)], .prod (.list (.var {} "B")) (.list (.var {} "B")),
       .list (.var {} "B")),
     mono := false, aop := .ok `Freyd.Alg.RelSet.ListRel.merge },
   { sym := "loop",
     sig := ([((.prod (.var {} "X") (.var {} "Y"), .var {} "X"), some false)],
       .prod (.var {} "X") (.list (.var {} "Y")), .var {} "X"),
     aop := .error "AOP declares no iteration to a fixed point from the left" },
   { sym := "uncons", sig := ([], .list (.var {} "B"), .prod (.var {} "B") (.list (.var {} "B"))),
     conv := "cons", written := false },
   lengthRow, sumRow,
   { sym := "inits", sig := ([], .list (.var {} "B"), .list (.list (.var {} "B"))),
     aop := .ok `Freyd.Alg.RelSet.ListRel.initsR },
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
     conv := "uncat", aop := .ok `Freyd.Alg.RelSet.ListRel.cat },
   { sym := "uncat", sig := ([], .list (.var {} "B"), .prod (.list (.var {} "B")) (.list (.var {} "B"))),
     conv := "cat", written := false },
   { sym := "zip", sig := ([], .prod (.list (.var {} "A")) (.list (.var {} "B")),
       .list (.prod (.var {} "A") (.var {} "B"))),
     aop := .ok `Freyd.Alg.RelSet.Pointfree.zip },
   { sym := "snoc", sig := ([], .prod (.list (.var {} "B")) (.var {} "B"), .list (.var {} "B")), conv := "unsnoc",
     aop := .error "AOP's `snoc` is on snoc lists (`SL.snoc`), not on the cons lists `[α]` reads as" },
   { sym := "unsnoc", sig := ([], .list (.var {} "B"), .prod (.list (.var {} "B")) (.var {} "B")),
     conv := "snoc", written := false },
   { sym := "setify", sig := ([], .list (.var {} "B"), .list (.var {} "B")),
     aop := .ok `Freyd.Alg.RelSet.ListRel.setify },
   -- `positions(p)`: dataframe §3.1's `where(dom(xs ≫ p))`, named so because `where` is a keyword (§c); it makes
   -- positions, numbers of `ℕ`, so it has no `dfn` until `rank` can be written and no use where `ℕ` has a universe
   { sym := "positions", num := [("ℕ", intAtoms)],
     sig := ([((.var {} "B", .var {} "B"), some false)], .list (.var {} "B"), .list (.var {} "ℕ")),
     mono := false, aop := .error "AOP declares no positions of the elements of a list that pass a test" },
   -- `asc(P)`: q's `asc` of the set `dom P`, `j ↦` its `j`-th smallest element in `Obj.lt` order; not `mono`: a
   -- larger `P` renumbers. Its definition `(dom(P) Λ(> P) length)°` is no `Elab.dfns` row: `>` on any object
   -- (`Obj.lt`) has no term (`lt` is on ℕ's universe only), and no law proves `ascDen` equal to it
   { sym := "asc", num := [("ℕ", intAtoms)], sig := ([((.var {} "B", .var {} "B"), some false)], .var {} "ℕ", .var {} "B"),
     mono := false, aop := .error "AOP declares no numbering of a set by its order", whole := true },
   -- last, so the rows before keep their positions (`Rows.lean`'s numbering)
   inlConvRow, inrConvRow,
   -- `sums(x)`: q's `sums` per key, `x : κ×ν ⟶ γ`, the key the source's first component; the fused form of
   -- `agg(dom(x) (𝟙 × ≥) dom(x), F(x) ⦇[0, plus]⦈)` (`rowDens`). Not `mono`: a larger `x` changes the sums. Its
   -- definition is, as `asc`'s, no `Elab.dfns` row. The positions `ℕ` and the values `V` are two objects: only
   -- `V` is summed, so only `V` is a number object (`num`)
   { sym := "sums", num := [("ℕ", intAtoms), ("V", intAtoms)],
     sig := ([((.prod (.var {} "K") (.var {} "ℕ"), .var {} "V"), some false)], .prod (.var {} "K") (.var {} "ℕ"),
       .var {} "V"),
     mono := false, aop := .error "AOP declares no prefix sums per key", whole := true },
   flatRow,
   -- `x $ F`: each value of `x : A ⟶ N` to the same number at `F`'s atom (`QAtomicType.embed`, typed base S6), written
   -- as its own infix form, which names the target object
   { sym := "$", sig := ([], .var {} "N", .var {} "F"), written := false,
     aop := .error "AOP declares no change of a number's representation" }] ++
  -- `sqrt`, `neg`, …: each a relation `F ⟶ F` on a float object `F` (`num` its float atoms), one row per name
  unaryOps.map fun (s, _) =>
    { sym := s, sig := ([], .var {} "F", .var {} "F"), num := [("F", floatAtoms)],
      aop := .error "AOP declares no floating-point function" }

def Prim.find?(s : String) : Option Prim := prims.find? (·.sym == s)

/-- The one table of builtins: symbol and arity. A program may not define or take as a parameter a name
    in it (§c). -/
def Op.table : List (String × Op × Nat) :=
  [("𝟙", .id, 0), ("𝟘", .zero, 0), ("⊤", .top, 0), ("π₁", .outl, 0),
   ("π₂", .outr, 0), ("inl", .inl, 0), ("inr", .inr, 0), ("≤", .leq, 0), ("<", .lt, 0), ("succ", .succ, 0),
   ("plus", .arith Rel.Kernel.Ew.add, 0), ("times", .arith Rel.Kernel.Ew.mul, 0),
   ("minus", .arith Rel.Kernel.Ew.sub, 0), ("div", .arith Rel.Kernel.Ew.idiv, 0),
   ("mod", .arith Rel.Kernel.Ew.imod, 0), ("max", .arith Rel.Kernel.Ew.greater, 0),
   ("min", .arith Rel.Kernel.Ew.lesser, 0),
   -- q's `%` by its word and its glyph; `Op.sym` prints the first
   ("divide", .arith Rel.Kernel.Ew.divide, 0), ("%", .arith Rel.Kernel.Ew.divide, 0), ("nil", .nil, 0), ("α", .alpha, 0),
   ("dom", .dom, 1), ("ran", .ran, 1), ("Λ", .lam, 1), ("E", .E, 1),
   ("est", .est, 1), ("thin", .thin, 1), ("F", .map, 1),
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

open Lean Elab Term in
/-- Each atom by its name, the name of its `QAtomicType` constructor (`f64`, `datetime`), read from the inductive's own
    constructor list: `obj F : f64` names an atom as Lean does, with no second spelling to keep in step. -/
def atomNames : List (Lean.Name × Rel.QAtomicType) := by_elab do
  let .inductInfo i ← getConstInfo ``Rel.QAtomicType | throwError "Rel.QAtomicType is no inductive type"
  let (n, t) := (Lean.mkConst ``Lean.Name, Lean.mkConst ``Rel.QAtomicType)
  Meta.mkListLit (Lean.mkApp2 (Lean.mkConst ``Prod [0, 0]) n t) (i.ctors.map fun c =>
    Lean.mkApp4 (Lean.mkConst ``Prod.mk [0, 0]) n t (toExpr (Lean.Name.mkSimple c.getString!)) (Lean.mkConst c))

open Lean in deriving instance ToExpr for Rel.QAtomicType

/-- An object declaration's right side: named elements, a signed number range `lo ≤ hi`, or a derived object. -/
inductive ObjDef
  | elems (ws : List String)
  | range (lo hi : Int)
  | alias (o : OExp)
  /-- `schema S = {k : K, v : N}`: the `Schema` of these columns, the object `Schema.obj` of it (`Expand.objInfo`). -/
  | schema (cs : List (String × OExp))
  /-- `obj N` with no right side: an unbounded number object, every `Int64` its element and `𝟙` its universe, so
      nothing of it is materialised and `<`, `succ`, the value verbs on it are bounded by their context (§0).
      `obj F : f64`: the same at the atom `t` (`atomNames`), every element of `t` an element of `F`. -/
  | num (t : Rel.QAtomicType := .i64)
  deriving Repr, Inhabited

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
  | check (p : Pos) (e f : Expr) (eq : Bool) (binds : List (String × Expr))
  /-- `input n : A ⟶ B from p`: a relation with no body, a parameter of the statements after it that mention it
      (IO design A.2); read from the table directory `path`, or the CSV file `path` when `csv`. -/
  | input (p : Pos) (n : String) (ty : OExp × OExp) (csv : Bool) (path : String)
  /-- `output n to path`: the table of the definition or input `n` written to `path` (`csv`: as one CSV file). -/
  | output (p : Pos) (n : String) (csv : Bool) (path : String)
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

def OExp.show (o : OExp) : String := o.render false

/-- The object variables of `o`, in order, each once. -/
def OExp.vars : OExp → List String
  | .var _ n => [n]
  | .name .. => []
  | .prod a b | .sum a b => (a.vars ++ b.vars).eraseDups
  | .list a => a.vars

/-- The object variables of a row's parameters and type, in order, each once. -/
def Prim.vars (r : Prim) : List String :=
  ((r.sig.1.flatMap fun ((x, y), _) => x.vars ++ y.vars) ++ r.sig.2.1.vars ++ r.sig.2.2.vars).eraseDups

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
def Expr.render (l : Nat) (full : Bool := false) : Expr → String
  | .name _ n => n
  | .op _ o objs args =>
    let os := if objs.isEmpty then "" else "(" ++ ", ".intercalate (objs.map OExp.show) ++ ")"
    let as := if args.isEmpty then "" else "(" ++ ", ".intercalate (args.map (Expr.render 0 full)) ++ ")"
    o.sym ++ os ++ as
  | .app _ n args => n ++ "(" ++ ", ".intercalate (args.map (Expr.render 0 full)) ++ ")"
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

def Expr.show (e : Expr) : String := e.render 0

end Rel.Lang
