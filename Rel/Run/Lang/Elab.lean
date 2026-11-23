module

public import Rel.Run.Struct
public import Rel.Run.SetOps
public import Rel.Run.Lang.Syntax
public import Rel.Run.Lang.Tm
public import Rel.Run.Lang.Schema
public import Rel.Kernel.Db.Csv

-- exposed: every def body is a spec a downstream `rfl`/`decide`/`simp` may unfold (PLAN W.8)
@[expose] public section

/-! The elaborator of the Rel language (`doc/rel-lang-design.md` §a, §e): names resolved, every term typed
    `A ⟶ B` over the declared objects, definitions expanded, a body whose declared parameter is given a family
    lifted by the rows of §e. Two passes: `elabE` types the surface term into `Pre` with object variables,
    unified as it goes; `build` reads the solved objects and gives `Tm`, the core term, indexed by its source,
    target and whether it runs on demand, so its expansion (`Expand`) has no error path. -/

namespace Rel.Lang

open Tab Rel.Alg
open Rel.Kernel (need needSize)

/-! ### Objects as the program names them -/

/-- The declared object `n` as Lean's unifier sees it: one constant per name, so `isDefEq` tells `X` from `N` though
    both are stored as `.long` (F6); irreducible, so the unifier never reads a name as its storage. -/
@[irreducible] def _root_.Rel.Obj.named (_ : String) : Obj := .long

/-- An object up to its declared names: `X` and `N` are both `long` and still different objects. `[A]` is
    `arr`. `mv` is an object variable of the inference, a Lean metavariable of type `Obj`. -/
inductive OTy
  | base (n : String)
  | prod (a b : OTy)
  | sum (a b : OTy)
  | arr (a : OTy)
  | mv (m : Lean.MVarId)
  deriving BEq, Inhabited

/-- `o` as an `Obj` term: a declared object its constant `Obj.named`, a variable its metavariable. -/
def OTy.toExpr : OTy → Lean.Expr
  | .base n => .app (.const ``Obj.named []) (Lean.mkStrLit n)
  | .prod a b => Lean.mkApp2 (.const ``Obj.prod []) a.toExpr b.toExpr
  | .sum a b => Lean.mkApp2 (.const ``Obj.sum []) a.toExpr b.toExpr
  | .arr a => .app (.const ``Obj.arr []) a.toExpr
  | .mv m => .mvar m

/-- An `Obj` term read back: the unifier only assigns `toExpr`'s forms to the variables, so no other form occurs;
    one would print as itself. -/
def OTy.ofExpr : Lean.Expr → OTy
  | .app (.const ``Obj.named _) (.lit (.strVal n)) => .base n
  | .app (.app (.const ``Obj.prod _) a) b => .prod (ofExpr a) (ofExpr b)
  | .app (.app (.const ``Obj.sum _) a) b => .sum (ofExpr a) (ofExpr b)
  | .app (.const ``Obj.arr _) a => .arr (ofExpr a)
  | .mvar m => .mv m
  | e => .base s!"{e}"

/-- The object `n` as a program writes it: another program's object, named by its constant
    (`Rel.Programs.prelude.«1»`), by that constant's last component (`1`), read by Lean's name-literal parser; a name
    that is no constant as it is. -/
def nameShown (n : String) : String :=
  match Lean.Syntax.decodeNameLit ("`" ++ n) with | some (.str _ s) => s | _ => n

/-- `o` as the program writes it (printing only: a base object by `nameShown`). -/
def OTy.exp : OTy → OExp
  | .base n => .name {} (nameShown n)
  | .prod a b => .prod a.exp b.exp
  | .sum a b => .sum a.exp b.exp
  -- `[A]` is an array; printed as the array the interpreter holds
  | .arr a => .list a.exp
  | .mv m => .var {} (match m.name with | .num _ k => s!"?{k}" | n => s!"?{n}")

instance : ToString OTy := ⟨(·.exp.show)⟩

/-! ### An element of an atom: how a literal word is stored and printed back -/

/-- How an element of the atom `t` is written: `(width, float, signed)`, `t`'s layout in the kernels' own table
    (`Kernel.ascLayout`); none where no literal column is built (`Arr.ofFn` takes no `u1`, whose elements are bits,
    and `sym`, `general` have no width). `obj F : t` declares an object at such a `t` only. -/
def litLayout (t : Rel.QAtomicType) : Option (Nat × Bool × Bool) := if t == .u1 then none else Kernel.ascLayout t

/-- The atom `t` by its name (`atomNames`). -/
def atomName (t : Rel.QAtomicType) : String :=
  match atomNames.find? (·.2 == t) with | some (n, _) => n.toString | none => s!"{repr t}"

/-- `A` as a program writes it, each atom `t` the object named by it (`atomName`), and the atoms it names: where
    `schema S from` puts a column. -/
def oexpOf : Obj → OExp × List Rel.QAtomicType
  | .atom t => (.name {} (atomName t), [t])
  | .prod a b => let (x, s) := oexpOf a; let (y, u) := oexpOf b; (.prod x y, s ++ u)
  | .sum a b => let (x, s) := oexpOf a; let (y, u) := oexpOf b; (.sum x y, s ++ u)
  | .arr a => let (x, s) := oexpOf a; (.list x, s)
  | .one => (.name {} "1", [])

/-- The bits of the float of `w` bytes nearest `±m·10^e` (`s` false) or `±m·10^(-e)` (`s` true): `OfScientific`,
    the reader of Lean's own float literals; `neg` its sign, so `-0.0` is the negative zero. -/
def floatBits (w : Nat) (neg : Bool) (m : Nat) (s : Bool) (e : Nat) : UInt64 :=
  -- Clinger's fast path: `m` and `10^e` exact in the float, so one rounded `*` or `/`, where `OfScientific` builds
  -- `m·5^e` or `m·2^k` as a `Nat`, a GMP number past `2^63`. `m` is exact when it converts back to itself (below
  -- `2^63`, where the rounded value cannot saturate `toUInt64`), not only below `2^53`: `1.5e16` is `15·10^15`
  if w == 4 then
    let x : Float32 := if m >>> 63 == 0 && m.toUInt64.toFloat32.toUInt64 == m.toUInt64 && e ≤ 10 then
        let (a, p) := (m.toUInt64.toFloat32, ((10 : UInt64) ^ e).toFloat32); if s then a / p else a * p
      else OfScientific.ofScientific m s e
    (if neg then -x else x).toBits.toUInt64
  else
    let x : Float := if m >>> 63 == 0 && m.toUInt64.toFloat.toUInt64 == m.toUInt64 && e ≤ 22 then
        let (a, p) := (m.toUInt64.toFloat, ((5 : UInt64) ^ e).toFloat.scaleB e); if s then a / p else a * p
      else OfScientific.ofScientific m s e
    (if neg then -x else x).toBits

/-- The float of `w` bytes with bits `b` as its sign and `M`, `E`, its value `±M·2^E`; none at an infinity or a NaN
    (every exponent bit set). The fields are cut from the word as words: `b.toNat` of a negative float is past `2^63`. -/
def floatParts (w : Nat) (b : UInt64) : Option (Bool × Nat × Int) :=
  let (mb, eb) : UInt64 × UInt64 := if w == 4 then (23, 8) else (52, 11)
  let (fr, ex, neg) := (b &&& ((1 <<< mb) - 1), (b >>> mb) &&& ((1 <<< eb) - 1), (b >>> (mb + eb)) &&& 1 == 1)
  let bias : Int := ((1 <<< (eb - 1)) - 1 : UInt64).toNat
  if ex == (1 <<< eb) - 1 then none
  else if ex == 0 then some (neg, fr.toNat, 1 - bias - mb.toNat)
  else some (neg, (fr ||| (1 <<< mb)).toNat, ex.toNat - bias - mb.toNat)

/-- A number word's sign, `-`, which `Embed.wNeg` writes before the token, and its token. -/
def wordSign (w : String) : Bool × String :=
  match w.toList with | '-' :: cs => (true, String.ofList cs) | cs => (false, String.ofList cs)

/-- A number word's sign (`wordSign`) and its token as Lean reads a number
    literal: a whole number `k` as `(k, false, 0)`, a scientific one (`2.5`, `1e-3`, `1.5e10`) by
    `Syntax.decodeScientificLitVal?`, `m·10^(∓e)` as `(m, s, e)`. -/
def numParts (w : String) : Option (Bool × Nat × Bool × Nat) :=
  let (neg, d) := wordSign w
  match d.toNat? with
  | some k => some (neg, k, false, 0)
  | none => (Lean.Syntax.decodeScientificLitVal? d).map fun (m, s, e) => (neg, m, s, e)

/-- The atoms with a text form of q's besides the integer: a `date` written `2024.01.15`, a `datetime`
    `2024.01.15D12:30:00.5`, read by the CSV's reader of the atom (`Db.Csv.ymd`, `Db.Csv.stamp`, C.3) at the day's
    separator `.`, as the CSV: days, nanoseconds since 1970-01-01, proleptic Gregorian, years 0001–9999; a
    `char` written `"a"` or `"\ooo"`, a byte of a string literal (`charText`, `Tup.ofText`). The reader gives the
    word sign-extended to 64 bits, as `Db.Csv.intWord`; each is in its atom's range (`stamp` checks `i64`'s). -/
def qForm : Rel.QAtomicType → Option (String × (List UInt8 → Option UInt64))
  | .date => some ("day yyyy.mm.dd", fun f => (Db.Csv.ymd f).map (·.toInt64.toUInt64))
  | .datetime => some ("time yyyy.mm.ddDhh:mm:ss[.f]", Db.Csv.stamp)
  | .char => some ("char \"a\"", fun f => (charOf f).map (·.toInt64.toUInt64))
  | _ => none

/-- The word `w` stored at the atom `t` of the object `n` (`litLayout`): a float of `t`'s width read as Lean reads a
    float literal, a whole number included (`numParts`), normalised where it is produced (`QAtomicType.nonCanonical`: `-0.0`
    and a `-1e-400` that rounds to it are `0.0`); an integer in `t`'s range, written as one or in `t`'s `qForm`. An
    error names `w` and `n` where it is neither, or where it is no finite float: no literal writes an infinity or a NaN
    (NaN has no row). -/
def wordAt (p : Pos) (n : String) (t : Rel.QAtomicType) (w : String) : Except Err UInt64 :=
  let no := s!"'{w}' is not an element of {n}, an object of {atomName t}"
  match litLayout t with
  | none => throw ⟨p, s!"{n} is an object of {atomName t}, which has no literal"⟩
  | some (b, true, _) => match numParts w with
    | some (neg, m, s, e) =>
      -- a literal writes no NaN, so the one non-canonical word it can produce is the negative zero
      let x := if t.nonCanonical (floatBits b neg m s e) then floatBits b false m s e else floatBits b neg m s e
      if (floatParts b x).isSome then pure x else throw ⟨p, s!"{no}: it is beyond the range of {atomName t}"⟩
    | none => throw ⟨p, no⟩
  | some (b, false, sg) =>
    -- sign and magnitude (`Db.Csv.intWord`): an `Int` past `±2^31` is a GMP number
    let (neg, d) := wordSign w
    match d.toNat?, (qForm t).bind (·.2 (Db.Csv.bytes w)) with
    | some k, _ => match Db.Csv.intWord b sg neg k with
      | some x => pure x
      | none => let (lo, hi) : Int × Int := if sg then (-2 ^ (8 * b - 1), 2 ^ (8 * b - 1)) else (0, 2 ^ (8 * b))
        throw ⟨p, s!"{no}: it is not in {lo}…{hi - 1}"⟩
    | none, some x => pure x
    | none, none => throw ⟨p, match qForm t with
      | some (f, _) => s!"{no}: it is no integer and no {f} of the years 0001–9999 in the range of {atomName t}"
      | none => no⟩

/-- `D·10^k` with the trailing zeros of `D` moved into `k`. -/
def stripZeros : Nat → Nat → Int → Nat × Int
  | f + 1, D, k => if D % 10 == 0 && D != 0 then stripZeros f (D / 10) (k + 1) else (D, k)
  | 0, D, k => (D, k)

/-- The float of `w` bytes with bits `b` printed as the shortest decimal that reads back to `b` (`numParts`,
    `floatBits`): of the nearest decimals `D·10^k` with 1, 2, … significant digits, the first that reads back to the
    same bits (the longest, 9 or 17 digits, always does). Plain with a point where the leading digit's place is
    `10^-7 … 10^20` (`2.5`, `-0.0`, `100.0`), else with an exponent (`1.5e-8`, `1e21`). An infinity or a NaN, which
    no literal writes, prints as q prints it (`0w`, `-0w`, `0n`). -/
def floatText (w : Nat) (b : UInt64) : String :=
  match floatParts w b with
  | none => if b.toNat % 2 ^ (if w == 4 then 23 else 52) != 0 then "0n"
    else if b.toNat / 2 ^ (8 * w - 1) % 2 == 1 then "-0w" else "0w"
  | some (neg, 0, _) => if neg then "-0.0" else "0.0"
  | some (neg, M, E) =>
    let (num, den) : Nat × Nat := if E ≥ 0 then (M * 2 ^ E.toNat, 1) else (M, 2 ^ (-E).toNat)
    -- the place of the leading digit: `10^L ≤ num/den < 10^(L+1)`
    let L : Int := if num ≥ den then ((Nat.toDigits 10 (num / den)).length : Int) - 1
      else -((((Array.range 400).find? fun j => num * 10 ^ (j + 1) ≥ den).getD 400 : Nat) + 1 : Int)
    let near (d : Nat) : Nat × Int :=
      let k := L - d + 1
      let (a, c) := if k ≥ 0 then (num, den * 10 ^ k.toNat) else (num * 10 ^ (-k).toNat, den)
      ((2 * a + c) / (2 * c), k)
    let mx := if w == 4 then 9 else 17
    -- the `mx`-digit one is not read back: it always reads back, and has no exact `floatBits` fast path
    let (D, k) := (((Array.range (mx - 1)).map (near ∘ (· + 1))).find? fun (D, k) => floatBits w neg D (k < 0) k.natAbs == b).getD (near mx)
    let (D, k) := stripZeros 20 D k
    let s := toString D
    let P : Int := (s.length : Int) - 1 + k
    let zeros (j : Nat) := String.ofList (List.replicate j '0')
    let body :=
      if -7 ≤ P ∧ P < 21 then
        if k ≥ 0 then s ++ zeros k.toNat ++ ".0"
        else if P ≥ 0 then String.ofList (s.toList.take (P.toNat + 1)) ++ "." ++ String.ofList (s.toList.drop (P.toNat + 1))
        else "0." ++ zeros ((-P).toNat - 1) ++ s
      else (if s.length == 1 then s else String.ofList (s.toList.take 1) ++ "." ++ String.ofList (s.toList.drop 1)) ++ s!"e{P}"
    (if neg then "-" else "") ++ body

/-- The stored word of an element of the atom `t`, as `Arr.ofFn` takes it (a symbol is its 8-byte id); none at `general`, which has none. -/
def elWord : (t : Rel.QAtomicType) → (Obj.atom t).El → Option UInt64
  | .u1, x => some (if (x : Bool) then 1 else 0)
  | .u8, x | .char, x => some (x : UInt8).toUInt64
  | .i16, x => some (x : Int16).toUInt16.toUInt64
  | .i32, x | .date, x => some (x : Int32).toUInt32.toUInt64
  | .i8, x => some (x : Int8).toUInt8.toUInt64
  | .i64, x | .datetime, x => some (x : Int64).toUInt64
  | .f32, x => some (x : UInt32).toUInt64
  | .f64, x | .sym, x => some (x : UInt64)
  | .general, _ => none

/-- The word `x` of the atom `t` printed as `wordAt` reads it back: a float by `floatText`, a temporal atom as q
    shows it (`Db.Csv.cell`, the CSV's one text of the atom; an out-of-range one as its integer), an integer by its
    value at `t`'s width and sign. -/
def wordText (t : Rel.QAtomicType) (x : UInt64) : String :=
  match (qForm t).bind fun _ => Db.Csv.cell (t, []) x with
  | some s => String.ofList (s.map (Char.ofNat ·.toNat))
  | none => match litLayout t with
    | some (b, true, _) => floatText b x
    -- cut and negated as words: `x.toNat` of a negative one is past `2^63`, a GMP number
    | some (b, false, sg) => let u := x &&& Column.ones (8 * b)
      if sg && u >>> (8 * b - 1).toUInt64 != 0 then s!"-{(0 - u) &&& Column.ones (8 * b)}" else toString u
    | none => "?"

/-- A declared object: what it stands for, and, for a base object, its elements and universe. -/
structure ObjInfo where
  ty : OTy
  elems : List String := []
  /-- The code each of `elems` is stored as, in order: `0…n−1` for `obj V = {…}`, the stored values for a disk one. -/
  codes : List Int64 := []
  range : Option (Int × Int) := none
  uni : Option ((m : USize) × Arr .i64 m) := none
  /-- An unbounded number object (`ObjDef.num`): every `Int64` an element, `𝟙` its universe. -/
  num : Bool := false
  /-- Its universe is an initial segment `0…k` of ℕ (a range from `0`, or named elements, coded `0…n−1`; or an
      object variable a call puts one at): there a row's `dfn` is its fused row cut to the universe (`build`). -/
  seg : Bool := false
  /-- An object variable of a definition elaborated once: its universe is the variable `k`, an argument of the
      definition's constant. -/
  uniVar : Option Nat := none
  /-- An object variable of a definition elaborated once: a numeral there is the number, which each call checks its
      object holds (`build`'s `.call`). -/
  ovar : Bool := false
  /-- An object variable whose number checks (`numObj`, `$`'s `castOK`) are left to each use: the definition's
      verdict build (`Expand.once`), which is never emitted; each use builds the expansion, where they run. -/
  deferred : Bool := false
  /-- How it is stored: `.long` for a declared object (F6), `.atom t` for one declared `obj F : t`; `varObj k` for the
      object variable `k` of a constant generic over it. -/
  obj : Obj := .long
  /-- A schema's columns (`schema S = {…}`), `ty` their `Schema.objAt`; none for any other object. -/
  cols : Schema OTy := []

/-- The atoms a placeholder may be: every atom but `.long`'s, which the number verbs fix (`Tm.instObj.fixed`). -/
def varAtoms : List Rel.QAtomicType := [.general, .u1, .u8, .i16, .i32, .f32, .f64, .char, .sym,
  .i8, .date, .datetime]

/-- The atoms at the leaves of `A`. -/
def _root_.Rel.Obj.atoms : Obj → List Rel.QAtomicType
  | .atom t => [t]
  | .prod a b | .sum a b => a.atoms ++ b.atoms
  | .arr b => b.atoms
  | .one => []

/-- The placeholders of a constant built where `objs` are declared: the `varAtoms` none of them is stored at, so
    no object its body can name is taken for one of its variables (`Obj.inst`), whatever atom it is stored at. -/
def placeholdersOf (objs : List (String × ObjInfo)) : List Rel.QAtomicType :=
  varAtoms.filter fun t => !objs.any fun (_, i) => i.obj.atoms.contains t

/-- The placeholder of the object variable `k` among `ph`; none past `ph`. -/
def varObj (ph : List Rel.QAtomicType) (k : Nat) : Option Obj := ph[k]?.map .atom

deriving instance Repr for Rel.Obj

/-- `A` with the placeholder `ph[k]` of each object variable `k` replaced by `σ[k]`, kept where `σ` has none. An
    atom outside `varAtoms` is no placeholder whatever `ph` holds, so `.long` is kept by every `ph`. -/
def _root_.Rel.Obj.inst (ph : List Rel.QAtomicType) (σ : List Obj) : Obj → Obj
  | .atom t => match varAtoms.idxOf? t with
    | none => .atom t
    | some _ => match ph.idxOf? t with | some k => σ.getD k (.atom t) | none => .atom t
  | .prod a b => .prod (a.inst ph σ) (b.inst ph σ)
  | .arr b => .arr (b.inst ph σ)
  | .sum a b => .sum (a.inst ph σ) (b.inst ph σ)
  | .one => .one

/-- `t`, built at the placeholders, at the objects `σ` (`Obj.inst`): a definition's body at a call's objects. A
    node whose objects are fixed (a table, a universe, the number verbs at `.long`) keeps them, else the error
    names them. -/
def Tm.instObj (ph : List Rel.QAtomicType) (σ : List Obj) : {A B : Obj} → Tm A B →
    Except String (Tm (A.inst ph σ) (B.inst ph σ))
  | _, _, .val R => fixed (.val R)
  | _, _, .uni U => fixed (.uni U)
  | _, _, .zero => pure .zero
  | _, _, .id => pure .id
  | _, _, .top V => return .top (← V.instObj ph σ)
  | _, _, .outl => pure .outl
  | _, _, .outr => pure .outr
  | _, _, .comp R S => return .comp (← R.instObj ph σ) (← S.instObj ph σ)
  | _, _, .conv R => return .conv (← R.instObj ph σ)
  | _, _, .meet R S => return .meet (← R.instObj ph σ) (← S.instObj ph σ)
  | _, _, .join R S => return .join (← R.instObj ph σ) (← S.instObj ph σ)
  | _, _, .diff R S => return .diff (← R.instObj ph σ) (← S.instObj ph σ)
  | _, _, .ldiv R S U V => return .ldiv (← R.instObj ph σ) (← S.instObj ph σ) (← U.instObj ph σ) (← V.instObj ph σ)
  | _, _, .rdiv R S U V => return .rdiv (← R.instObj ph σ) (← S.instObj ph σ) (← U.instObj ph σ) (← V.instObj ph σ)
  | _, _, .pair R S => return .pair (← R.instObj ph σ) (← S.instObj ph σ)
  | _, _, .lam R => return .lam (← R.instObj ph σ)
  | _, _, .mem => pure .mem
  | _, _, .inl => pure .inl
  | _, _, .inr => pure .inr
  | _, _, .prim r => pure (.prim r)
  | _, _, .own R => return .own (← R.instObj ph σ)
  | _, _, .leq t U => do fixed (.leq t (← back (← U.instObj ph σ)))
  | _, _, .lt t U => do fixed (.lt t (← back (← U.instObj ph σ)))
  | _, _, .foldr e S => return .foldr (← e.instObj ph σ) (← S.instObj ph σ)
  | _, _, .fold e S => return .fold (← e.instObj ph σ) (← S.instObj ph σ)
  | _, _, .share k R => return .share k (← R.instObj ph σ)
  | _, _, .var d k => pure (.var d k)
  | _, _, .call ks c os b => return .call ks c (os.map (·.inst ph σ)) (← b.instObj ph σ)
  | _, _, .callCv ks c c' os b u => return .callCv ks c c' (os.map (·.inst ph σ)) (← b.instObj ph σ) (← u.instObj ph σ)
  | _, _, .arg f x => return .arg (← f.instObj ph σ) (← x.instObj ph σ)
  | _, _, .nu k S b => return .nu k (← S.instObj ph σ) (← b.instObj ph σ)
  | _, _, .mu k w n b => return .mu k w n (← b.instObj ph σ)
  | _, _, .hylo k w b => return .hylo k w (← b.instObj ph σ)
where
  /-- `t` at objects `X ⟶ Y` that `σ` must keep: decided, as `Obj.inst` reads `varAtoms` by search. -/
  fixed {X Y : Obj} (t : Tm X Y) : Except String (Tm (X.inst ph σ) (Y.inst ph σ)) :=
    if h : X.inst ph σ = X ∧ Y.inst ph σ = Y then pure (cast (by rw [h.1, h.2]) t) else
      throw s!"a table, a universe or a number verb at {repr X} ⟶ {repr Y}, objects the call changes"
  /-- `fixed` backwards: a part of such a node. -/
  back {X Y : Obj} (t : Tm (X.inst ph σ) (Y.inst ph σ)) : Except String (Tm X Y) :=
    if h : X.inst ph σ = X ∧ Y.inst ph σ = Y then pure (cast (by rw [h.1, h.2]) t) else
      throw s!"a table, a universe or a number verb at {repr X} ⟶ {repr Y}, objects the call changes"

abbrev Objs := List (String × ObjInfo)

/-- The universe of an object, when every base object in it has one (§a): `cross` of a product's, the two
    sides of a sum's; an `arr` has none. Whether it has one is decided here; its values are built when a reader
    forces the thunk, so an object whose universe is past `crossMax` costs nothing until a term reads it. -/
def uniOf (objs : Objs) : OTy → Option ((A : Obj) × Thunk (Except String ((m : USize) × Vals A m)))
  | .base n => do
    let i ← objs.lookup n; let ⟨m, U⟩ ← i.uni
    match i.obj with | .one => pure ⟨.one, .pure (.ok ⟨m, ()⟩)⟩ | _ => pure ⟨.long, .pure (.ok ⟨m, U⟩)⟩
  | .prod a b => do
    let ⟨A, ua⟩ ← uniOf objs a; let ⟨B, ub⟩ ← uniOf objs b
    pure ⟨.prod A B, .mk fun _ => do
      let ⟨_, Ua⟩ ← ua.get; let ⟨_, Ub⟩ ← ub.get
      let ⟨_, x, y⟩ ← (Vals.cross Ua Ub).mapError (s!"the universe of {a} × {b}: {·}")
      pure ⟨_, (x, y)⟩⟩
  | .sum a b => do
    let ⟨A, ua⟩ ← uniOf objs a; let ⟨B, ub⟩ ← uniOf objs b
    pure ⟨.sum A B, .mk fun _ => do
      let ⟨_, Ua⟩ ← ua.get; let ⟨_, Ub⟩ ← ub.get
      -- the values of `inl` on `Ua` and of `inr` on `Ub`: `ran(inl) ∪ ran(inr)`
      let U ← (show Except String (Tab (.sum A B) (.sum A B)) from do
        Tab.union (← Tab.ran (← Tab.inl (B := B) Ua)) (← Tab.ran (← Tab.inr (A := A) Ub))).mapError
        (s!"the universe of {a} + {b}: {·}")
      pure ⟨_, U.key⟩⟩
  | _ => none

/-- The rounds a `μ` runs at most when an object of it has no universe: Kleene rounds from `𝟘` stop at the least
    fixed point whatever the object, but an array object may grow every round; a run that reaches the cap fails. -/
def muCap : Nat := 1024

/-- The element count of `uniOf objs o`, read off the declared universes without building the product's. -/
def uniSize (objs : Objs) : OTy → Option Nat
  | .base n => do let ⟨m, _⟩ ← (← objs.lookup n).uni; pure m.toNat
  | .prod a b => do pure ((← uniSize objs a) * (← uniSize objs b))
  | .sum a b => do pure ((← uniSize objs a) + (← uniSize objs b))
  | _ => none

/-! ### The typed surface term -/

/-- A term typed but not yet built: the core operators, object variables on the constants. `close` marks a
    place whose term is read whole — no left context, or an operator that is not local (§a): its term runs on
    its source's universe when it needs keys, `why` naming that operator in the error when there is none.
    `tm` is a built term, a definition's. -/
inductive Pre
  | tm (r : Res)
  | zero (a b : OTy)
  | id (a : OTy)
  | top (p : Pos) (a b : OTy) (tgt : Option Pre)
  | outl (a b : OTy)
  | outr (a b : OTy)
  | comp (p q : Pre)
  | conv (p : Pre)
  | meet (p q : Pre)
  | join (p q : Pre)
  | diff (p q : Pre)
  | dom (p : Pre)
  | ran (p : Pre)
  | ldiv (pos : Pos) (p q : Pre) (b c : OTy)
  | rdiv (pos : Pos) (p q : Pre) (a b : OTy)
  | pair (p q : Pre)
  | prod (p q : Pre)
  | lam (p : Pre)
  | nil (a b : OTy)
  | mem (b : OTy)
  | inl (a b : OTy)
  | inr (a b : OTy)
  /-- The row `r` of `prims` at `s ⟶ t`, an instance of its type, given the relations `args` (`Prim.inst`); a row
      of `dfns` is the fused form of its definition, which `build` cuts to `t`'s universe. -/
  | prim (r : Prim) (args : List Pre) (s t : OTy)
  | own (p : Pre)
  | succ (pos : Pos) (n : OTy)
  | arith (pos : Pos) (k : UInt8) (n : OTy)
  | leq (pos : Pos) (n : OTy)
  | lt (pos : Pos) (n : OTy)
  | fold (right : Bool) (e s : Pre)
  /-- A literal; `gd` the generic definition whose body holds it (`Env.gdef`), where its numerals' objects are
      the call's, checked at each call. -/
  | lit (pos : Pos) (a b : OTy) (ps : List (Tup × Tup)) (gd : Option String)
  | close (pos : Pos) (p : Pre) (a : OTy) (why : String)
  /-- The variable `k` of a fixed point `X : a ⟶ b`, at the place `pos` it is used; or a constant's parameter,
      its argument's form (`Form`): closed (`none`), run on demand (`some false`), tested on pairs and never run
      (`some true`). -/
  | var (pos : Pos) (k : Nat) (a b : OTy) (tst : Option Bool)
  /-- `μX : body` (`least`) or `νX : body`, `X` the variable `k` written `x`; `S` the meet of `body`'s conjuncts that
      do not mention `X`, a `ν`'s start. -/
  | fix (pos : Pos) (least : Bool) (k : Nat) (x : String) (S : Option Pre) (body : Pre) (a b : OTy)
  /-- `hylo(c, S)`, `c` at `pos`, where a cycle of `c` is reported: `body` the `μX : c G(X) S` it is, `X` the variable
      `k`; its children, `c` then `G`'s membership, are `Tm.kids` of the built body. -/
  | hylo (pos : Pos) (k : Nat) (body : Pre) (a b : OTy)
  /-- The constant `c` at `pos`, at the objects `us` of its object variables, each with whether `c` is generic
      over it and whether `c` reads its universe, and the arguments `args`, each passed as its pair test where
      `ts` says so (`Form`); `body` the constant's body at its placeholders `ph` (`Once.ph`), `ks` the variables the
      arguments bind (`Once.binds`), `cv` its converse's constant and body (`Tm.callCv`); `tst`: `c` is the pair test
      of a body that only tests (§a). `alt` the definition's body expanded at the use, which every analysis reads and
      `build` does not. -/
  | call (pos : Pos) (c : Lean.Name) (us : List (OTy × Bool × Bool)) (args : List Pre) (ts : List Bool) (alt : Pre)
      (a b : OTy)
      (ks : List Nat) (ph : List Rel.QAtomicType) (body : Res) (cv : Option (Lean.Name × Res)) (tst : Bool)
  /-- The definition `c`'s body elaborated at the use once, each parameter the variable of `ks` (`Tm.call`), applied to
      `args`, each built once (`Code.args`): `cl` with every parameter read closed, `od` with every one run on
      demand. `alt` the expansion, the arguments put in place of the variables, which every analysis reads and
      `build` runs where the call does not build. -/
  | callE (pos : Pos) (c : String) (ks : List Nat) (args : List Pre) (alt cl od : Pre) (a b : OTy)

instance : Inhabited Pre := ⟨.id (.base "")⟩

/-- `R/S : a ⟶ b` with its operands read whole (`close`), as `/` elaborates. -/
def Pre.rdivWhole (pos : Pos) (r s : Pre) (a b : OTy) : Pre :=
  let w := "R/S reads its operands whole outside a meet with a term run on demand"
  .rdiv pos (.close pos r a w) (.close pos s b w) a b

/-- Symmetric division `R÷S : a ⟶ b` is its definition `R/S ∩ (S/R)°` (architecture §1), not a node of its own: `x`
    to `y` when `R x` and `S y` are one image, within the universes (`Tm.symDiv_den`). -/
def Pre.symDiv (pos : Pos) (r s : Pre) (a b : OTy) : Pre :=
  .meet (.rdivWhole pos r s a b) (.conv (.rdivWhole pos s r b a))

/-- `[R,S] : a + b ⟶ _` is its definition `inl°R ∪ inr°S` (architecture §1, §7), not a node of its own: each part
    runs on the values of its summand in demand (`Tab.inlConv`), and is covered by the laws of `∪`, `≫` and the rows. -/
def Pre.junc (r s : Pre) (a b : OTy) : Pre :=
  .join (.comp (.conv (.inl a b)) r) (.comp (.conv (.inr a b)) s)

/-- A fold's base `0` at the number object `n`, the coreflexive `⟨𝟙,𝟙⟩minus ∩ 𝟙`: `x − x` kept where it is `x`;
    none where `0` is not in `n` (`minus` keeps its result there). -/
def Pre.zero0 (p : Pos) (n : OTy) : Pre := .meet (.comp (.pair (.id n) (.id n)) (.arith p Rel.Kernel.Ew.sub n)) (.id n)

/-- `⦇[0, S]⦈` (`right`: `⦇[0, S]⦈ʳ`) at `n`, as the fold and `foldParts` elaborate it: the start `ran(0)`. -/
def Pre.fold0 (p : Pos) (right : Bool) (n : OTy) (s : Pre) : Pre :=
  .fold right (.close p (.ran (.close p (Pre.zero0 p n) n "ran( ) reads its argument whole")) n
    "the fold's start is read whole") s

/-- The `why` of a top-level term's `close`. -/
def noLeft : String := "the term here needs keys and has no left context"

/-! ### Object variables -/

/-- The form of an argument at a call (module design §5 M): closed (`none`), run on the keys in demand
    (`some false`), tested on pairs (`some true`, its pair test, §a); or a family whose index is the class `i` among
    the call's indices (§e). Part of the constant's signature. -/
abbrev Form := Option Bool × Option Nat

/-- What a call needs of a constant (the registry), read off its `Once` by `sigOf`. -/
structure Sig where
  /-- The constant. -/
  const : Lean.Name
  /-- Per object variable, whether it is generic over it and whether it reads its universe. -/
  vars : List (Bool × Bool)
  /-- Whether it is a pair test. -/
  tst : Bool
  /-- Whether a family result `I ⟶ a×b` is its keyed form `I×a ⟶ b` (`keyed`). -/
  kf : Bool
  deriving Inhabited, Repr, BEq

/-- A definition elaborated once at its arguments' forms (`once`). Not an extension of `Sig`: a `Sig` is computed
    from it (`sigOf`), its universes read and converse taken from the body. -/
structure Once where
  /-- Its registry key (`formKey`). -/
  key : Lean.Name
  /-- Its constant. -/
  const : Lean.Name
  /-- Per object variable whether the constant is generic over it (the variables' universes are the term
      variables `0 … n-1`). -/
  gen : List Bool
  /-- The atoms its variables are built at (`placeholdersOf`), the `k`-th the variable `k`'s: none is an atom an
      object its body names is stored at. -/
  ph : List Rel.QAtomicType
  /-- Its parameters' objects and demand bits as the constant takes them (the variables from `n` on). -/
  params : List (Obj × Obj × Bool)
  /-- Its parameters' forms (`Form`'s first part): `convOf` reads which run on demand. -/
  forms : List (Option Bool)
  /-- Its body. -/
  res : Res
  /-- Whether that body is its pair test (it builds no relation, §a). -/
  tst : Bool
  /-- Whether it is a family's keyed form. -/
  kf : Bool

/-- The variables of `o`'s body its arguments bind, in the order a call gives them (`callArgs`): the universes it
    reads, then its parameters. -/
def Once.binds (o : Once) : List Nat :=
  (List.range o.gen.length).filter o.res.2.2.fv.contains ++ (List.range o.params.length).map (o.gen.length + ·)

/-- A use at `p` of the generic definition `n : sig` (`mkDef`): its object variables at the use, `us`, and its
    expansion's nodes `xs`, whose number checks run once the context has solved `us` (`settleUses`). -/
structure Use where
  p : Pos
  n : String
  sig : String
  us : List (String × OTy)
  xs : List Pre

structure St where
  /-- The uses whose object variables the context solves after they return, an expected type at the use: a
      variable only the definition's result names (`mkDef`), checked once the term is elaborated (`settleUses`). -/
  uses : List Use := []
  /-- The fixed points so far: the next one's variable. -/
  fixes : Nat := 0
  /-- The constants built so far at the forms the program's calls take, in the order `emit` adds them. -/
  specs : List Once := []
  /-- The objects of the program elaborating, where a call tries its arguments' forms (`callDef`): a definition's
      own scope does not hold the caller's objects nor the universes of its object variables. -/
  objs : Objs := []
  /-- The argument each variable of a call's body (`callOf`) stands for, outer calls' variables put in place: a
      call in that body picks its arguments' forms by what they compute (`Expand.callDef`), as its expansion does. -/
  args : List (Nat × Pre) := []

/-- Elaboration outside a term: the program's error, over Lean's metavariables. -/
abbrev EM := ExceptT Err Lean.Meta.MetaM

/-- The elaborator: its object variables are Lean's metavariables, solved by Lean's unifier (`unify`). -/
abbrev M := StateT St EM

-- `throw`, `try … catch` here are the program's `Err`, not the `Exception` of the `MetaM` under it
instance (priority := high) : MonadExcept Err EM := { throw := throwThe Err, tryCatch := tryCatchThe Err }
instance (priority := high) : MonadExcept Err M := { throw := throwThe Err, tryCatch := tryCatchThe Err }

def fresh : M OTy := do
  let m ← Lean.mkFreshMVarId
  discard <| Lean.Meta.mkFreshExprMVarWithId m (some (.const ``Obj []))
  pure (.mv m)

/-- `o` with every solved variable replaced, as the metavariable context `mc` has them. -/
def zonk (mc : Lean.MetavarContext) (o : OTy) : OTy := .ofExpr (Lean.instantiateMVarsCore mc o.toExpr).1

/-- `x` and `y` made one object by Lean's unifier, which leaves the variables as they were when it fails. -/
def defEq (x y : OTy) : M Bool := Lean.Meta.isDefEq x.toExpr y.toExpr

/-- The parts of `x` and `y` that unify, unified: what a failed `defEq` of the whole rolled back. -/
partial def defEqParts : OTy → OTy → M Unit
  | .prod a b, .prod c d | .sum a b, .sum c d => do defEqParts a c; defEqParts b d
  | .arr a, .arr c => defEqParts a c
  | a, c => discard (defEq a c)

/-- Unify `x` (found) with `y` (expected); the error names both with every part that does unify filled in
    (`defEqParts`), so a mismatch shows the objects that differ, never the variables left open by the rollback. -/
def unify (p : Pos) (what : String) (x y : OTy) : M Unit := do
  unless ← defEq x y do
    defEqParts x y
    let mc ← Lean.getMCtx
    throw ⟨p, s!"{what}: found {zonk mc x}, expected {zonk mc y}"⟩

/-- Where a match that fails part way goes back to: the elaborator's state and Lean's metavariables. -/
def save : M (St × Lean.Meta.SavedState) := return (← get, ← Lean.Meta.saveState)

def restore (s : St × Lean.Meta.SavedState) : M Unit := do set s.1; s.2.restore

/-! ### Fixed points: where the variable occurs -/

/-- How a term reads one of its parts: monotonically, antitonically (`what` names the place), or neither (`op`,
    an operator not monotonic in its argument). -/
inductive Pol
  | mono
  | anti (what : String)
  | not (op : String)

/-- `x` with its positions through `fp` and its parts through `f`, one level down, `f` told how `x` reads each
    part, or `none` for a copy of a part `x` reads elsewhere: a call's arguments (in `alt`), a `ν`'s start (the
    conjuncts of its body). Every walk over `Pre` is an instance (`parts`, `at`, `nilSrcs`). -/
def Pre.traverse {m : Type → Type} [Monad m] (fp : Pos → m Pos) (f : Option Pol → Pre → m Pre) (x : Pre) :
    m Pre :=
  let mo := f (some .mono)
  match x with
  | .top q a b t => return .top (← fp q) a b (← t.mapM mo)
  | .comp x y => return .comp (← mo x) (← mo y)
  | .conv x => return .conv (← mo x)
  | .meet x y => return .meet (← mo x) (← mo y)
  | .join x y => return .join (← mo x) (← mo y)
  | .diff x y => return .diff (← mo x) (← f (some (.anti "the right operand of −")) y)
  | .dom x => return .dom (← mo x)
  | .ran x => return .ran (← mo x)
  | .ldiv q x y b c => return .ldiv (← fp q) (← f (some (.anti "the left operand of \\")) x) (← mo y) b c
  | .rdiv q x y a b => return .rdiv (← fp q) (← mo x) (← f (some (.anti "the right operand of /")) y) a b
  | .pair x y => return .pair (← mo x) (← mo y)
  | .prod x y => return .prod (← mo x) (← mo y)
  | .lam x => return .lam (← f (some (.not "Λ")) x)
  | .own x => return .own (← mo x)
  | .prim r xs s t => return .prim r (← xs.mapM (f (some (if r.mono then .mono else .not r.sym)))) s t
  | .succ q n => return .succ (← fp q) n
  | .arith q k n => return .arith (← fp q) k n
  | .leq q n => return .leq (← fp q) n
  | .lt q n => return .lt (← fp q) n
  | .fold d e s => return .fold d (← mo e) (← mo s)
  | .lit q a b ps gd => return .lit (← fp q) a b ps gd
  | .close q x a why => return .close (← fp q) (← mo x) a why
  | .var q k a b t => return .var (← fp q) k a b t
  | .fix q l k x S y a b => return .fix (← fp q) l k x (← S.mapM (f none)) (← mo y) a b
  | .hylo q k x a b => return .hylo (← fp q) k (← mo x) a b
  | .call q c us xs ts alt a b ks ph t cv tst =>
    return .call (← fp q) c us (← xs.mapM (f none)) ts (← mo alt) a b ks ph t cv tst
  | .callE q c ks xs alt cl od a b =>
    -- `cl` and `od` read no variable but `ks` (the call binds every name in scope), so a walk stops at them
    return .callE (← fp q) c ks (← xs.mapM (f none)) (← mo alt) cl od a b
  | x => pure x

/-- The parts of `x`, each with how `x` reads it. A definition's body is expanded at its use, so the prelude's
    and the program's definitions need no rule of their own. -/
def Pre.parts (x : Pre) : List (Pre × Pol) :=
  (Id.run ((x.traverse (m := StateM (List (Pre × Pol))) pure fun pol y => do
    if let some pol := pol then modify (· ++ [(y, pol)])
    pure y).run [])).2

/-- `Pre.rewrite`, each node visited once per address: an expansion holds each argument once per use (`callOf`'s
    `alt`), so nested definitions share subterms and a walk of the tree is exponential in the nesting. -/
unsafe def Pre.rewriteShared (fp : Pos → Pos) (g : Pre → Option Pre) (x : Pre) : Pre :=
  (go x).run' {}
where go (y : Pre) : StateM (Std.HashMap USize Pre) Pre := do
  if let some z := (← get)[ptrAddrUnsafe y]? then return z
  let z ← match g y with | some z => pure z | none => y.traverse (pure ∘ fp) fun _ c => go c
  modifyGet fun m => (z, m.insert (ptrAddrUnsafe y) z)

/-- `x` with each node `g` names replaced, every other rebuilt from its parts with its positions through `fp`. -/
@[implemented_by Pre.rewriteShared]
partial def Pre.rewrite (fp : Pos → Pos) (g : Pre → Option Pre) (x : Pre) : Pre :=
  match g x with | some z => z | none => Id.run (x.traverse (pure ∘ fp) fun _ y => pure (y.rewrite fp g))

/-- `x` with every position `p`: a prelude body at its use, so an error `build` raises in it is at the use (§c). -/
def Pre.at (p : Pos) (x : Pre) : Pre := x.rewrite (fun _ => p) fun _ => none

/-- The source of each `nil` in `x`, a definition's body at its use included. -/
partial def Pre.nilSrcs : Pre → List OTy
  | .nil a _ => [a]
  | x => x.parts.flatMap (·.1.nilSrcs)

/-- `x` and every node under it, a call's expansion included. -/
partial def Pre.nodes (x : Pre) : List Pre := x :: x.parts.flatMap (·.1.nodes)

/-- Each literal in `x`, a generic definition's body's (`Env.gdef`) with the definition's name last; its expansion
    at a use included. -/
partial def Pre.lits : Pre → List (Pos × OTy × OTy × List (Tup × Tup) × Option String)
  | .lit p a b ps d => [(p, a, b, ps, d)]
  | x => x.parts.flatMap (·.1.lits)

/-- Where the variable `k` first occurs in `x`. -/
partial def Pre.occ (k : Nat) : Pre → Option Pos
  | .var p j _ _ _ => if j == k then some p else none
  | x => x.parts.findSome? (·.1.occ k)

/-- Whether `x` reads a parameter run on demand (`Form` `some false`), its argument at a call or a definition's
    expansion included. Its `Tm.var true k` is no converse of itself (`convTm` takes a variable for a pair test's). -/
partial def Pre.onDemand : Pre → Bool
  | .var _ _ _ _ (some false) => true
  | x => (x.traverse (m := StateM Bool) pure (fun _ y => do modify (· || y.onDemand); pure y) |>.run false).2

/-- The first occurrence of `X`, the variable `k` of `fx` (`μX`, `νX`), where the body is not monotonic in it:
    under an operator that is not, or under an odd number of antitone places, `why` the last of them. -/
partial def Pre.polarity (k : Nat) (fx x : String) (pos : Bool) (why : String) : Pre → Option Err
  | .var p j _ _ _ =>
    if j == k && !pos then
      some ⟨p, s!"{fx}: {x} occurs in {why} at {p.line}:{p.col} (antitone); {x} must occur only in monotonic positions"⟩
    else none
  | y => y.parts.findSome? fun (z, pol) => match pol with
    | .mono => z.polarity k fx x pos why
    | .anti w => z.polarity k fx x (!pos) w
    | .not op => (z.occ k).map fun p => ⟨p,
      s!"{fx}: {x} occurs under {op} at {p.line}:{p.col}; {op} is not monotonic in its argument, so the fixed point need not exist"⟩

def Pre.conjuncts : Pre → List Pre
  | .meet x y => x.conjuncts ++ y.conjuncts
  | x => [x]

/-- The meet of the top-level conjuncts of `x` that do not mention the variable `k`: `X ⊑ φ(X) ⊑ S`, so the
    greatest fixed point lies below `S`, and `ν`'s rounds start there. -/
def Pre.bound (k : Nat) (x : Pre) : Option Pre :=
  match x.conjuncts.filter (·.occ k |>.isNone) with
  | [] => none
  | c :: cs => some (cs.foldl .meet c)

/-- `x` with each variable `.var p k a b t` replaced by `g p k a b t`. -/
def Pre.mapVar (g : Pos → Nat → OTy → OTy → Option Bool → Pre) : Pre → Pre :=
  Pre.rewrite (fun q => q) fun | .var p k a b t => some (g p k a b t) | _ => none

/-- `x` with each variable of a call's body (`St.args`) the argument it stands for: what `x` computes. -/
def St.expand (st : St) (x : Pre) : Pre := x.mapVar fun p k a b t => (st.args.lookup k).getD (.var p k a b t)

/-! ### Elaboration: environments and the lifted rows of §e -/

/-- An elaborated argument or result: one relation `s ⟶ t`, or a family `i ⟶ a×b` read as its fibres `a ⟶ b`. -/
inductive Arg
  | rel (p : Pre) (s t : OTy)
  | fam (p : Pre) (i a b : OTy)

instance : Inhabited Arg := ⟨.rel default default default⟩

/-- A definition: its arity, and its expansion at given arguments (§e: substituted, lifted when a declared
    parameter is given a family). -/
structure Def where
  arity : Nat
  apply : Pos → List Arg → M Arg

structure Env where
  objs : Objs := []
  defs : List (String × Def) := []
  params : List (String × Arg) := []
  /-- The resolver (module design §2.3), and the other programs' definitions and objects by constant: where a name
      the program does not define goes. -/
  res : String → Found := fun _ => .none
  ext : List (Lean.Name × Def) := []
  extObjs : List (Lean.Name × ObjInfo) := []
  /-- The definition generic over objects whose body this is: a numeral literal in it takes its object from the
      context, an object variable the call decides (`litTy`), not from the declared objects. -/
  gdef : Option String := none
  /-- The object variables of the definition whose body this is, at this use's objects: a body may name them
      (`x $ φ`), as its parameters' types do. -/
  ovars : List (String × OTy) := []

/-- The definition `n`: the program's, else the one the resolver gives. -/
def Env.def? (env : Env) (n : String) : Option Def :=
  (env.defs.lookup n).orElse fun _ => match env.res n with | .ext e => if e.obj || e.thm then none else env.ext.lookup e.const | _ => none

/-- The infix operator `n`: the program's `_n_`, else the registered infix the resolver gives. -/
def Env.infix? (env : Env) (n : String) : Option Def :=
  (env.defs.lookup s!"_{n}_").orElse fun _ => match env.res n with | .ext e => if e.isInfix then env.ext.lookup e.const else none | _ => none

/-- The object `n`: the program's, else the registered object the resolver gives. -/
def Env.obj? (env : Env) (n : String) : Option ObjInfo :=
  (env.objs.lookup n).orElse fun _ => match env.res n with | .ext e => if e.obj then env.extObjs.lookup e.const else none | _ => none

/-- The object `1` in scope, the source a `nil` no context fixes starts at (`settleNil`). -/
def Env.one (env : Env) : OTy := ((env.obj? "1").map (·.ty)).getD (.base "1")

/-- `o` as the program wrote it, resolved: an alias stands for its definition, a variable for its object in `vs`,
    one use's instantiation (§e). -/
def oty (env : Env) (vs : List (String × OTy) := []) : OExp → M OTy
  | .name p n => match env.obj? n with
    | some i => pure i.ty
    | none => throw ⟨p, s!"unknown object '{n}'"⟩
  | .var p n => match (vs.lookup n).orElse fun _ => env.ovars.lookup n with
    | some o => pure o
    | none => throw ⟨p, s!"the object variable '{n}' is not instantiated here"⟩
  | .prod a b => return .prod (← oty env vs a) (← oty env vs b)
  | .sum a b => return .sum (← oty env vs a) (← oty env vs b)
  | .list a => return .arr (← oty env vs a)

/-- A solved object's `Obj`: a declared base object as `ObjInfo.obj` stores it (`long` but for `obj F : t`), an
    object variable likewise. -/
def objOf (objs : Objs) (dp : Pos) : OTy → Except Err Obj
  | .base n => pure ((objs.lookup n).elim .long (·.obj))
  | .prod a b => return .prod (← objOf objs dp a) (← objOf objs dp b)
  | .sum a b => return .sum (← objOf objs dp a) (← objOf objs dp b)
  | .arr a => return .arr (← objOf objs dp a)
  | .mv _ => throw ⟨dp, "an object is not determined; write the constant's objects, as in ⊤(A,B) or 𝟙(A)"⟩

/-- `col S "c"`: the term `Schema.col?` gives at `S`'s columns as `Obj`s, typed `S ⟶ C` at the program's objects. -/
def colOf (env : Env) (p : Pos) (s : OExp) (c : String) : Except Err (Res × OTy × OTy) := do
  let (n, i) ← match s with
    | .name _ n => pure (n, env.obj? n)
    | _ => pure (s.show, none)
  let some i := i.filter (!·.cols.isEmpty) | throw ⟨p, s!"`col` reads a column of a schema; `{n}` is no schema"⟩
  let S ← i.cols.mapM fun (k, o) => return (k, ← objOf env.objs p o)
  match Schema.col? S c, i.cols.lookup c with
  | .ok ⟨B, t⟩, some b => pure (⟨_, B, t⟩, i.ty, b)
  | .error m, _ => throw ⟨p, s!"schema `{n}`: {m}"⟩
  | .ok _, none => throw ⟨p, s!"internal: schema `{n}` has the column '{c}' as an `Obj` and not as an object"⟩

/-! ### The lifted rows of §e, each shape stated once -/

/-- The operators a lifted row is written in: at `Pre` a shape builds the row, at `Pat` it recognises one (`keyed`).
    `Pre`'s own constructors are not enough: a `match` pattern cannot repeat an object, and a row's objects repeat.
    `ω`, `π` are what an object and a place are at `τ`. -/
class Shape (τ : Type) where
  ω : Type
  π : Type
  comp : τ → τ → τ
  pair : τ → τ → τ
  meet : τ → τ → τ
  join : τ → τ → τ
  diff : τ → τ → τ
  dom : τ → τ
  id : ω → τ
  outl : ω → ω → τ
  outr : ω → ω → τ
  prod : ω → ω → ω
  top : π → ω → ω → Option τ → τ
  close : π → τ → ω → String → τ

instance : Shape Pre := ⟨OTy, Pos, .comp, .pair, .meet, .join, .diff, .dom, .id, .outl, .outr, .prod, .top, .close⟩

/-- What recognising a row binds, each at its first occurrence: the place `q`, the parts `R`, `S`, the objects
    `a`–`d`. A row that does not mention a hole leaves it unbound. -/
structure Holes where
  q : Option Pos := none
  R : Option Pre := none
  S : Option Pre := none
  a : Option OTy := none
  b : Option OTy := none
  c : Option OTy := none
  d : Option OTy := none

abbrev Pat := StateT Holes Option Unit

/-- A shape as a recogniser. An object a row writes as `a×b` binds `a`, `b` when the term's is a product and is not
    checked otherwise, as a place the row reads its objects from elsewhere. -/
instance : Shape (Pre → Pat) where
  ω := OTy → Pat
  π := Pos → Pat
  comp f g := fun | .comp x y => do f x; g y | _ => failure
  pair f g := fun | .pair x y => do f x; g y | _ => failure
  meet f g := fun | .meet x y => do f x; g y | _ => failure
  join f g := fun | .join x y => do f x; g y | _ => failure
  diff f g := fun | .diff x y => do f x; g y | _ => failure
  dom f := fun | .dom x => f x | _ => failure
  id o := fun | .id x => o x | _ => failure
  outl o o' := fun | .outl x y => do o x; o' y | _ => failure
  outr o o' := fun | .outr x y => do o x; o' y | _ => failure
  prod o o' := fun | .prod x y => do o x; o' y | _ => pure ()
  top q o o' t := fun
    | .top q' x y t' => do q q'; o x; o' y; match t, t' with | none, none => pure () | some f, some z => f z | _, _ => failure
    | _ => failure
  close q f o _ := fun | .close q' x y _ => do q q'; f x; o y | _ => failure

section Shapes

open Shape

variable {τ : Type} [Shape τ]

/-- `RS` lifted, `R : I ⟶ a×b`, `S` keyed: `⟨𝟙,R⟩⟨π₂π₁,⟨π₁,π₂π₂⟩S⟩`, each row `(a,b)` of `R` at its key `i` joined
    with `S` on `(i,b)`. Not `⟨R,S⟩` cut to the agreeing middles, which pairs every row of `R` with every row of `S`
    at a key. -/
def compSh (I a b : ω τ) (R S : τ) : τ :=
  let ab := prod a b
  comp (pair (Shape.id I) R) (pair (comp (outr I ab) (outl a b)) (comp (pair (outl I ab) (comp (outr I ab) (outr a b))) S))

/-- `⟨R,S⟩` lifted: `⟨R,S⟩dom(π₁π₁ ∩ π₂π₁)⟨π₁π₁,⟨π₁π₂,π₂π₂⟩⟩`, pairs of rows of one source. -/
def pairSh (a b c : ω τ) (R S : τ) : τ :=
  let ab := prod a b; let ac := prod a c
  comp (comp (pair R S) (dom (meet (comp (outl ab ac) (outl a b)) (comp (outr ab ac) (outl a c)))))
    (pair (comp (outl ab ac) (outl a b)) (pair (comp (outl ab ac) (outr a b)) (comp (outr ab ac) (outr a c))))

/-- `R×S` lifted: `⟨R,S⟩⟨⟨π₁π₁,π₂π₁⟩,⟨π₁π₂,π₂π₂⟩⟩`. -/
def prodSh (a b a' b' : ω τ) (R S : τ) : τ :=
  let ab := prod a b; let ab' := prod a' b'
  comp (pair R S) (pair (pair (comp (outl ab ab') (outl a b)) (comp (outr ab ab') (outl a' b')))
    (pair (comp (outl ab ab') (outr a b)) (comp (outr ab ab') (outr a' b'))))

/-- A family then a closed `C`: `F⟨π₁,π₂C⟩`, each row's value carried by `C`. -/
def thenSh (a b : ω τ) (F C : τ) : τ := comp F (pair (outl a b) (comp (outr a b) C))

/-- `dom(F)` lifted: `F⟨π₁,π₁⟩`. -/
def domSh (a b : ω τ) (F : τ) : τ := comp F (pair (outl a b) (outl a b))

/-- `⊤` as a family: `D⊤`, `⊤ : I ⟶ a×b`. -/
def topSh (q : π τ) (I a b : ω τ) : τ := top q I (prod a b) none

/-- A closed `C : a ⟶ b` as a family, `D⊤⟨𝟙,C⟩`, `⊤ : I ⟶ a` onto `V`. -/
def constSh (q : π τ) (I a : ω τ) (V : Option τ) (C : τ) : τ := comp (top q I a V) (pair (Shape.id a) C)

/-- `constSh` onto `dom(C')`, `C` read whole there. -/
def closedSh (q : π τ) (I a : ω τ) (C' C : τ) : τ := constSh q I a (some (close q (dom C') a "a closed term in a lifted body")) C

/-- A row `X : I×a ⟶ I×b` keeping each key as a family: `⟨𝟙,⊤⟩⟨π₂,Xπ₂⟩`, `⊤ : I ⟶ a` onto `a`'s universe, as the
    lifted `𝟙` is (`liftConst`). -/
def rowSh (q : π τ) (I a b : ω τ) (X : τ) : τ :=
  comp (pair (Shape.id I) (top q I a none)) (pair (outr I a) (comp X (outr I b)))

end Shapes

/-- A row of §e: its shape at the index `I`, the place `q`, the parts `R S` and the objects `a b c d`, and its keyed
    form from the holes recognising it binds, `K` keying a part at its objects, `a b` the family's. -/
structure LiftRow where
  shape : {τ : Type} → [S : Shape τ] → S.ω → S.π → τ → τ → S.ω → S.ω → S.ω → S.ω → τ
  keyed : (Pre → OTy → OTy → Pre) → OTy → OTy → Holes → Option Pre

/-- The holes `x` binds when it has `r`'s shape. -/
def LiftRow.match? (r : LiftRow) (x : Pre) : Option Holes :=
  (r.shape (τ := Pre → Pat) (fun _ => pure ())
    (fun v => modify fun h => { h with q := h.q <|> some v })
    (fun v => modify fun h => { h with R := h.R <|> some v }) (fun v => modify fun h => { h with S := h.S <|> some v })
    (fun v => modify fun h => { h with a := h.a <|> some v }) (fun v => modify fun h => { h with b := h.b <|> some v })
    (fun v => modify fun h => { h with c := h.c <|> some v }) (fun v => modify fun h => { h with d := h.d <|> some v })
    x).run {} |>.map (·.2)

section Rows

open Pre

variable (I : OTy) (p : Pos)

/-- A closed `C : a ⟶ b` as a family: `D⊤⟨𝟙,C⟩`, `⊤ : I ⟶ a` onto `dom(C)`; `⊤` itself is `D⊤`, `𝟙` is
    `D⊤⟨𝟙,𝟙⟩` (§e). -/
def liftConst (C : Pre) (a b : OTy) : Pre × OTy × OTy :=
  match C with
  | .top _ _ _ none => (topSh p I a b, a, b)
  | .id _ => (constSh p I a none (.id a), a, b)
  | C => (closedSh p I a C C, a, b)

/-- A result as a family over `I`. -/
def famOf : Arg → M (Pre × OTy × OTy)
  | .fam q i a b => do unify p "the index of a family" i I; pure (q, a, b)
  | .rel q s t => pure (liftConst I p q s t)

/-- The rows whose fibre at a source reads only that source, in the order `keyed` tries them. -/
def liftRows : List LiftRow := [
  ⟨fun _ _ R S _ _ _ _ => Shape.join R S, fun K a b h => return join (K (← h.R) a b) (K (← h.S) a b)⟩,
  ⟨fun _ _ R S _ _ _ _ => Shape.meet R S, fun K a b h => return meet (K (← h.R) a b) (K (← h.S) a b)⟩,
  ⟨fun _ _ R S _ _ _ _ => Shape.diff R S, fun K a b h => return diff (K (← h.R) a b) (K (← h.S) a b)⟩,
  -- `D⊤`, `⊤ : I ⟶ a×b`: `D⊤`, `⊤ : I×a ⟶ b`
  ⟨fun I q _ _ a b _ _ => topSh q I a b, fun _ _ _ h => return top (← h.q) (.prod I (← h.a)) (← h.b) none⟩,
  -- a closed `C` onto `V = dom(C')`: `dom(π₂C')π₂C`, so `C'` too runs on the sources in demand, not on its universe
  ⟨fun I q R S a _ _ _ => closedSh q I a R S, fun _ a _ h => return comp (dom (comp (outr I a) (← h.R))) (comp (outr I a) (← h.S))⟩,
  -- a closed `C` onto `V`: `π₂VC`, `C` run on the sources `π₂V` meets
  ⟨fun I q R S a _ _ _ => constSh q I a (some R) S, fun _ a _ h => return comp (comp (outr I a) (← h.R)) (← h.S)⟩,
  ⟨fun I q _ S a _ _ _ => constSh q I a none S, fun _ a _ h => return comp (outr I a) (← h.S)⟩,
  -- `RS` lifted, and `X⦇R⦈` lifted, `G : I×b ⟶ c` keyed: `⟨π₁,Rᴵ⟩G`
  ⟨fun I _ R S a b _ _ => compSh I a b R S, fun K _ _ h => do
    let a ← h.a; return comp (pair (outl I a) (K (← h.R) a (← h.b))) (← h.S)⟩,
  -- `⟨R,S⟩` lifted: `⟨Rᴵ,Sᴵ⟩`
  ⟨fun _ _ R S a b c _ => pairSh a b c R S, fun K _ _ h => do
    let a ← h.a; return pair (K (← h.R) a (← h.b)) (K (← h.S) a (← h.c))⟩,
  -- `R×S` lifted: `⟨⟨π₁,π₂π₁⟩Rᴵ,⟨π₁,π₂π₂⟩Sᴵ⟩` on `I×(a×a')`
  ⟨fun _ _ R S a b a' b' => prodSh a b a' b' R S, fun K _ _ h => do
    let a ← h.a; let a' ← h.c; let s := OTy.prod a a'
    return pair (comp (pair (outl I s) (comp (outr I s) (outl a a'))) (K (← h.R) a (← h.b)))
      (comp (pair (outl I s) (comp (outr I s) (outr a a'))) (K (← h.S) a' (← h.d)))⟩,
  -- `F` then `C`: `FᴵC`
  ⟨fun _ _ F C a b _ _ => thenSh a b F C, fun K _ _ h => return comp (K (← h.R) (← h.a) (← h.b)) (← h.S)⟩,
  -- `dom(F)` lifted: `dom(Fᴵ)π₂`
  ⟨fun _ _ F _ a b _ _ => domSh a b F, fun K _ _ h => do let a ← h.a; return comp (dom (K (← h.R) a (← h.b))) (outr I a)⟩,
  -- a keyed row (`appliedRowL`): `Xπ₂`
  ⟨fun I q X _ a b _ _ => rowSh q I a b X, fun _ _ b h => return comp (← h.R) (outr I b)⟩]

/-- The family `R : I ⟶ a×b` as one relation of the key and the source, `Rᴵ : I×a ⟶ b`, run on the pairs
    (key, source) in demand (§e, cost of the keyed fold). A row whose fibre at a source reads only that source
    is keyed through its parts, so a closed part runs on the sources in demand, not on its domain at every key.
    Any other family is read whole at each key and cut to the source, `⟨π₁R,π₂⟩dom(π₁π₁ ∩ π₂)π₁π₂`: every part
    runs on the keys in demand, so `I` needs no universe (a converse or `ran` here would close over all of `I`). -/
partial def keyed (R : Pre) (a b : OTy) : Pre :=
  ((liftRows I).findSome? fun r => r.match? R >>= r.keyed (keyed · · ·) a b).getD
    (.prim flatRow [R] (.prod I a) b)

def lComp : Pre × OTy × OTy → Pre × OTy × OTy → M (Pre × OTy × OTy)
  | (R, a, b), (S, b', c) => do
    unify p "the middle object of a composition" b' b
    pure (compSh I a b R (keyed I S b c), a, c)

def lThen : Pre × OTy × OTy → Pre × OTy × OTy → M (Pre × OTy × OTy)
  | (F, a, b), (C, s, t) => do
    unify p "the middle object of a composition" s b
    pure (thenSh a b F C, a, t)

def lConv : Pre × OTy × OTy → Pre × OTy × OTy
  | (R, a, b) => (comp R (pair (outr a b) (outl a b)), b, a)

def lDom : Pre × OTy × OTy → Pre × OTy × OTy
  | (R, a, b) => (domSh a b R, a, a)

def lRan : Pre × OTy × OTy → Pre × OTy × OTy
  | (R, a, b) => (comp R (pair (outr a b) (outr a b)), b, b)

/-- `∼R` lifted: `D⊤ − R`, `⊤ : I ⟶ a×b`. -/
def lCompl : Pre × OTy × OTy → Pre × OTy × OTy
  | (R, a, b) => (diff (topSh p I a b) R, a, b)

/-- `∩ ∪ −` lifted: the same operator on the two families. -/
def lSame (op : Pre → Pre → Pre) : Pre × OTy × OTy → Pre × OTy × OTy → M (Pre × OTy × OTy)
  | (R, a, b), (S, a', b') => do
    unify p "the source of the right operand" a' a; unify p "the target of the right operand" b' b
    pure (op R S, a, b)

def lLdiv (R S : Pre × OTy × OTy) : M (Pre × OTy × OTy) := do
  unify p "the source of `\\`'s right operand" S.2.1 R.2.1
  pure (lCompl I p (← lComp I p (lConv R) (lCompl I p S)))

/-- `R/S = (S°\R°)°` lifted, through `lLdiv`, as the unlifted `rdiv` is: one definition of the division. -/
def lRdiv (R S : Pre × OTy × OTy) : M (Pre × OTy × OTy) := do
  unify p "the target of `/`'s right operand" S.2.2 R.2.2
  return lConv (← lLdiv I p (lConv S) (lConv R))

def lPair : Pre × OTy × OTy → Pre × OTy × OTy → M (Pre × OTy × OTy)
  | (R, a, b), (S, a', c) => do
    unify p "the source of the pair's second part" a' a
    pure (pairSh a b c R S, a, .prod b c)

def lProd : Pre × OTy × OTy → Pre × OTy × OTy → Pre × OTy × OTy
  | (R, a, b), (S, a', b') => (prodSh a b a' b' R S, .prod a a', .prod b b')

/-- `[R,S]` lifted: `R⟨π₁inl,π₂⟩ ∪ S⟨π₁inr,π₂⟩`, the row `R(inl×𝟙) ∪ S(inr×𝟙)` with no universe. -/
def lJunc : Pre × OTy × OTy → Pre × OTy × OTy → M (Pre × OTy × OTy)
  | (R, a, c), (S, b, c') => do
    unify p "the target of the case's second part" c' c
    pure (join (comp R (pair (comp (outl a c) (Pre.inl a b)) (outr a c)))
      (comp S (pair (comp (outl b c) (Pre.inr a b)) (outr b c))), .sum a b, c)

/-- `Λ(R)` lifted on the sources `S : I ⟶ a` of each key, `Rπ₁` (`dom`) when none: `⟨𝟙,S⟩⟨π₂,Λ(Rᴵ)⟩`. `Λ` takes
    `S = ⊤` onto `a`'s universe, being total; `E` and `front` take `dom`, as their `a = [x]` has no universe. -/
def lLam (S : Option Pre) : Pre × OTy × OTy → Pre × OTy × OTy
  | (R, a, b) => (comp (pair (id I) (S.getD (comp R (outl a b)))) (pair (outr I a) (lam (keyed I R a b))), a, .arr b)

/-- `X⦇e,S⦈` lifted, `X : I ⟶ a×[x]`, `e : I ⟶ v×v`, `S : I ⟶ (v×x)×v`: `⟨𝟙,X⟩⟨π₂π₁,⟨π₁,π₂π₂⟩⦇e,S'⦈ᴵ⟩`, where
    `⦇e,S'⦈ᴵ : I×[x] ⟶ v` left-folds each array at its key, carrier `I×v`, `S' ≜ ⟨π₁π₁,⟨π₁π₂,π₂⟩⟩⟨π₁,Sᴵ⟩`. -/
def lFold : Pre × OTy × OTy → Pre × OTy × OTy → Pre × OTy × OTy → M (Pre × OTy × OTy)
  | (X, a, xs), (e, v, v'), (S, vx, w) => do
    unify p "the fold's start, a coreflexive" v' v
    let x ← fresh
    unify p "the source of the fold's step" vx (.prod v x)
    unify p "the target of the fold's step" w v
    unify p "the arrays a fold runs on" xs (.arr x)
    let iv := OTy.prod I v; let vx := OTy.prod v x
    let S' := comp (pair (comp (outl iv x) (outl I v)) (pair (comp (outl iv x) (outr I v)) (outr iv x)))
      (pair (outl I vx) (keyed I S vx v))
    pure (compSh I a (.arr x) X (.prim foldIRow [e, S'] (.prod I (.arr x)) v), a, v)

end Rows

/-- A row that has no lifting (§e). -/
def notLiftable {α : Type} (p : Pos) (what : String) (why := "it runs one relation on every array (§e)") : M α :=
  throw ⟨p, s!"{what} given a family is not liftable: {why}"⟩

/-- The front-end form of a result: a family outside its body is a relation `i ⟶ a×b`. -/
def Arg.plain : Arg → Pre × OTy × OTy
  | .rel q s t => (q, s, t)
  | .fam q i a b => (q, i, .prod a b)

def Arg.isFam : Arg → Bool
  | .fam .. => true
  | _ => false

/-- The row `r` at fresh objects for its constant's object variables: its parameters' types and forms, and its
    type, and the objects of its variables (`Prim.vars` order). -/
def Prim.inst (env : Env) (r : Prim) : M (List ((OTy × OTy) × Option Bool) × OTy × OTy × List OTy) := do
  let vs ← r.vars.mapM fun v => return (v, ← fresh)
  let ps ← r.sig.1.mapM fun ((x, y), f) => return ((← oty env vs x, ← oty env vs y), f)
  pure (ps, ← oty env vs r.sig.2.1, ← oty env vs r.sig.2.2, vs.map (·.2))

/-- The row `o` runs as: `prim s` the row `s`, `inl`, `inr`, `map` theirs (`Prim.written`); none for an operator
    with a term of its own. -/
def Op.row (p : Pos) : Op → M (Option Prim)
  | .prim s => match Prim.find? s with
    | some r => pure (some r)
    | none => throw ⟨p, s!"internal: no row `{s}` in `prims`"⟩
  | .map => pure (some mapRow)
  | .est => pure (some estRow)
  | .front => pure (some frontRow)
  | _ => pure none

/-- `at(k) : [b] ⟶ b` is its definition `⟨𝟙, ⊤ {k}⟩ at` (`indexRow`): the pair of the array and the constant index `k`,
    `⊤` to the one-row coreflexive `{(k,k)}`. The index object is no declared one (`objOf` stores an unlisted name as
    `.long`, and no program can write this name), so `at(k)` needs no number object in scope. -/
def indexAt (p : Pos) (k : Nat) (b : OTy) : Pre :=
  let n : OTy := .base "at(k)"
  let v := Int64.ofNat k
  .comp (.pair (.id (.arr b)) (.top p (.arr b) n (some (.tm ⟨.long, .long, .val ⟨1, col [v], col [v]⟩⟩))))
    (.prim indexRow [] (.prod (.arr b) n) b)

/-- A constant: fresh objects for its type, the explicit ones `(A,B)` unified with source and target. -/
def constant (env : Env) (p : Pos) (o : Op) (objs : List OExp) : M Arg := do
  let a ← fresh; let b ← fresh
  let row ← match ← o.row p with
    | some r => do
      let (ps, s, t, _) ← r.inst env
      unless ps.isEmpty do throw ⟨p, s!"{r.sym} takes {ps.length} arguments, found 0"⟩
      pure (some (.prim r [] s t, s, t))
    | none => pure none
  let (q, s, t) : Pre × OTy × OTy := row.getD <| match o with
    | .id => (.id a, a, a)
    | .zero => (.zero a b, a, b)
    | .top => (.top p a b none, a, b)
    | .outl => (.outl a b, .prod a b, a)
    | .outr => (.outr a b, .prod a b, b)
    | .leq => (.leq p a, a, a)
    | .lt => (.lt p a, a, a)
    | .succ => (.succ p a, a, a)
    | .arith k => (.arith p k a, .prod a a, a)
    | .nil => (.nil a b, a, .arr b)
    | .mem => (.mem a, .arr a, a)
    | .inl => (.inl a b, a, .sum a b)
    | .inr => (.inr b a, a, .sum b a)
    | .alpha => (.junc (.nil a b) (.prim consRow [] (.prod b (.arr b)) (.arr b)) a (.prod b (.arr b)),
        .sum a (.prod b (.arr b)), .arr b)
    | .index k => (indexAt p k b, .arr b, b)
    | _ => (.id a, a, a)
  match objs with
  | [] => pure ()
  -- `x $ F` names the one object no other constant takes alone, its target
  | [x] => do
    let tgt := o == .prim "$"
    unify p s!"the {if tgt then "target" else "object"} of {o.sym}" (if tgt then t else s) (← oty env [] x)
  | [x, y] => do unify p s!"the source of {o.sym}" s (← oty env [] x); unify p s!"the target of {o.sym}" t (← oty env [] y)
  | _ => throw ⟨p, s!"{o.sym} takes at most two objects, found {objs.length}"⟩
  pure (.rel q s t)

/-- Whether the declared object `i`, named `n`, holds the word `w`, by its own reader: one of its named elements, a
    number in its range, or (`obj F : t`, `obj N` at `i64`) a word `wordAt` reads at its atom; else why not. -/
def ObjInfo.member (i : ObjInfo) (n w : String) : Except String Unit :=
  if i.elems.contains w then pure () else
  match i.range, i.num, i.obj with
  | some (lo, hi), _, _ => match w.toInt? with
    | some k => if lo ≤ k ∧ k ≤ hi then pure () else throw s!"{w} is not in {n} = {lo}…{hi}"
    | none => throw s!"'{w}' is not an element of {n}"
  | none, true, .atom t => match wordAt {} n t w with | .ok _ => pure () | .error e => throw e.msg
  | _, _, _ => throw s!"'{w}' is not an element of {n}"

/-- The declared objects holding all the words `ws` (`ObjInfo.member`), each once: an imported object is in scope
    under its name and its constant, one object (`Expand.walk`). -/
def holders (objs : Objs) (ws : List String) : List OTy :=
  ((objs.filter fun (n, i) => ws.all fun w => (i.member n w).toBool).map (·.2.ty)).eraseDups

/-- Why no declared object holds all the words `ws`: each object's reader on the first word it refuses. -/
def refusals (objs : Objs) (ws : List String) : String :=
  let rs := objs.foldl (fun (acc : List (OTy × String)) (n, i) => if acc.any (·.1 == i.ty) then acc else
    match (ws.findSome? fun w => match i.member n w with | .error e => some e | .ok _ => none) with
    | some e => acc ++ [(i.ty, e)] | none => acc) []
  s!"no declared object has the elements {ws}" ++ (if rs.isEmpty then "" else s!" ({"; ".intercalate (rs.map (·.2))})")

/-- The atoms the value verbs (`plus`, …) and the orders `≤`, `<` run on (`stepAt`, `ltAt`): `i64`, and every float
    atom, whose verbs are computed on `f64` words (`fval`). -/
def valueAtom (t : QAtomicType) : Bool := intAtoms.contains t || floatAtoms.contains t

/-- The name and atom of `o`, a number object `op` computes on: a declared object stored at an atom `ok` admits
    (`valueAtom` for the value verbs and orders, `i64` alone for `succ` and `sums`); an object variable whose checks
    are left to each use (`ObjInfo.deferred`) admits every atom. -/
def numObj (objs : Objs) (mc : Lean.MetavarContext) (p : Pos) (o : OTy) (op : String) (ok : QAtomicType → Bool) :
    Except Err (String × QAtomicType) :=
  match zonk mc o with
  | .base n =>
    -- an object declared at no atom is stored at `i64` (S1); at an atom `op` has no step for, `op` is refused, never
    -- run on the bits
    let t := match objs.lookup n with | some { obj := .atom t, ovar := false, .. } => t | _ => .i64
    if ok t || (objs.lookup n).any (·.deferred) then pure (n, t) else
      let ats := ", ".intercalate ((atomNames.filter (ok ·.2)).map (atomName ·.2))
      -- the atoms `op` runs at that `t` casts to without loss (`castOK`): the program casts (`$`), explicitly
      let tos := (atomNames.filter fun a => ok a.2 && t.castOK a.2).map (atomName ·.2)
      let cast := if tos.isEmpty then "" else s!"; cast first, `x $ F` with `F` an object of {", ".intercalate tos}"
      throw ⟨p, s!"{op} on {n}: {n} is an object of {atomName t}, and {op} runs on objects of {ats} only{cast}"⟩
  | o => throw ⟨p, s!"{op} runs on a declared object, found {o}"⟩

/-- The object the variable `v` of the pattern `e` stands for in `o`, `o` of `e`'s form; none where `e` has no `v`. -/
def OExp.varAt (v : String) : OExp → OTy → Option OTy
  | .var _ n, o => if n == v then some o else none
  | .prod a b, .prod x y | .sum a b, .sum x y => (a.varAt v x).orElse fun _ => b.varAt v y
  | .list a, .arr x => a.varAt v x
  | _, _ => none

/-- The atoms the arithmetic verb `k` runs on: the value atoms, `%` (`divide`) on floats only, as it has no integer
    step (`intStep`); `max`, `min` on every ordered atom too, the order picking an operand. -/
def arithOk (k : UInt8) (t : QAtomicType) : Bool :=
  (valueAtom t && (k != Rel.Kernel.Ew.divide || t != .i64)) ||
    (k == Rel.Kernel.Ew.greater || k == Rel.Kernel.Ew.lesser) && t.ordNum.isSome

/-- The number objects the node `x` itself computes on, each with its operator and the atoms it admits: `build`
    refuses any other (`numObj`), and `settleLit` settles a literal's open object by them. -/
def Pre.numsAt (mc : Lean.MetavarContext) : Pre → List (OTy × String × (QAtomicType → Bool))
  | .prim r _ s t => r.num.filterMap fun (v, ok) =>
    ((r.sig.2.2.varAt v (zonk mc t)).orElse fun _ => r.sig.2.1.varAt v (zonk mc s)).map (·, r.sym, ok.contains)
  | .succ _ n => [(n, "succ", (· == .i64))]
  | .arith _ k n => [(n, (Op.arith k).sym, arithOk k)]
  | .leq _ n => [(n, "≤", (·.ordNum.isSome))]
  | .lt _ n => [(n, "<", (·.ordNum.isSome))]
  | _ => []

/-- `numsAt` of `x` and of its parts, a definition's body at its use included. -/
partial def Pre.nums (mc : Lean.MetavarContext) (x : Pre) : List (OTy × String × (QAtomicType → Bool)) :=
  x.numsAt mc ++ x.parts.flatMap (·.1.nums mc)

/-- Why the rows `ts` of a literal's position do not determine its object: they are none (an empty array's
    elements), or several declared objects hold their words. -/
def litOpen (objs : Objs) (p : Pos) (ts : List Tup) : Err :=
  let ws := ts.filterMap fun | .leaf w => some w | _ => none
  if ts.isEmpty then ⟨p, s!"the object of {(Tup.arr []).show} cannot be read off an empty array: write nil(A,[O])"⟩
  else ⟨p, s!"the elements {ws} are in {holders objs ws}; write the literal after its object"⟩

/-- The object of a literal's position, `ts` the sides there, one per row or array element (§c): a word's is the
    one declared object holding all the words, a pair's the product of its parts', an array's `[O]`, `O` the
    object of the elements of all its arrays together. Where the rows do not determine it (`litOpen`) it is an
    open object, which the context fixes as it fixes `nil`'s; `litCol` reports one still open at `build`. In the
    body of a generic definition `gd` numerals are open first: their object may be an object variable, which each
    call puts an object at, so the declared objects decide only what the context leaves open (`settleOpen`). -/
partial def litTy (objs : Objs) (gd : Option String) (p : Pos) (ts : List Tup) : M OTy := do
  let t := ts.headD default
  if let some r := ts.find? (!·.like t) then
    throw ⟨p, s!"the rows of a literal nest alike: found {r.show}, expected the form of {t.show}"⟩
  match ts, t with
  | [], _ => fresh
  | _, .leaf _ =>
    let ws := ts.filterMap fun | .leaf w => some w | _ => none
    if gd.isSome && ws.all (numParts · |>.isSome) then fresh else
    match holders objs ws with
    | [o] => pure o
    | [] => throw ⟨p, refusals objs ws⟩
    | _ => fresh
  | _, .pair .. =>
    pure (.prod (← litTy objs gd p (ts.map fun | .pair a _ => a | r => r))
      (← litTy objs gd p (ts.map fun | .pair _ b => b | r => r)))
  -- one-character strings only: a `char` or a text, which the context decides (`Tup.char?`, `settleLit`)
  | _, .arr _ => if ts.all (·.char?.isSome) then fresh else
    pure (.arr (← litTy objs gd p (ts.flatMap fun | .arr es => es | _ => [])))

/-- The object `o` of a literal's position `ts` that the context left open: of the declared objects holding its
    words (`litTy`'s rule), the one every number verb `ns` at `o` runs on (`Pre.nums`, `numObj`): `{(2024.01.15,1)}`
    beside `length`'s count is `D ⟶ N`, though a date object also holds `1`. Still open where several are left;
    an error where its words are held by none, or by none the verbs run on. -/
partial def settleLit (objs : Objs) (ns : List (OTy × String × (QAtomicType → Bool))) (p : Pos) (d : Option String)
    (ts : List Tup) (o : OTy) : M Unit := do
  let mc ← Lean.getMCtx
  match zonk mc o, ts with
  | _, [] => pure ()
  | .mv m, .leaf _ :: _ =>
    let ws := ts.filterMap fun | .leaf w => some w | _ => none
    let vs := ns.filter fun (n, _) => zonk mc n == .mv m
    let hs := holders objs ws
    match hs.filter fun h => vs.all fun (_, op, ok) => (numObj objs mc p h op ok).toBool with
    | [h] => unify p "the literal's object" o h
    | [] =>
      let who := match d with | some d => s!"`{d}`: " | none => ""
      if hs.isEmpty then throw ⟨p, s!"{who}{refusals objs ws}, and no object variable is put at them"⟩
      throw ⟨p, s!"{who}the elements {ws} are in {hs}, and {", ".intercalate (vs.map (·.2.1)).eraseDups} runs on none of them"⟩
    | _ => pure ()
  | .prod x y, .pair .. :: _ => do
    settleLit objs ns p d (ts.map fun | .pair a _ => a | r => r) x
    settleLit objs ns p d (ts.map fun | .pair _ b => b | r => r) y
  | .arr x, .arr _ :: _ => settleLit objs ns p d (ts.flatMap fun | .arr es => es | _ => []) x
  -- one-character strings no context read as `char`s (`litTy`): texts, as every other string
  | .mv _, .arr _ :: _ => do
    unify p "the literal's object" o (.arr (← litTy objs d p (ts.flatMap fun | .arr es => es | _ => [])))
    settleLit objs ns p d ts o
  | _, _ => pure ()

/-- What no context fixed once the terms `xs`, which share their objects (a check's two sides), are elaborated: a
    `nil`'s source starts at `1`, B&dM's `nil : 1 ⟶ [A]`, `Env.one` (§e); a literal's open object is settled by its
    words and the number verbs at it (`settleLit`). -/
def settleOpen (env : Env) (p : Pos) (xs : List Pre) : M Unit := do
  xs.forM fun x => x.nilSrcs.forM fun a => do
    if let .mv _ := zonk (← Lean.getMCtx) a then unify p "nil's source" a env.one
  let ns := xs.flatMap (·.nums (← Lean.getMCtx))
  xs.forM fun x => x.lits.forM fun (q, a, b, ps, d) => do
    settleLit env.objs ns q d (ps.map (·.1)) a; settleLit env.objs ns q d (ps.map (·.2)) b

/-- The argument `q : s ⟶ _` of row `r` in the form `f` its parameter takes it: a pair test is tested on the pairs
    the row compares (`build`, `param`), not read whole. -/
def Prim.pass (r : Prim) (p : Pos) (f : Option Bool) (q : Pre) (s : OTy) : Pre := match f with
  | some true => .close p q s s!"{r.sym}( )"
  | some false => q
  | none => .close p q s s!"{r.sym}( ) reads its argument whole"

/-- A row applied to relations: each unified with its parameter's type and passed in its form (`Form`): a pair
    test, run on demand, or read whole. -/
def appliedRow (env : Env) (p : Pos) (r : Prim) (qs : List (Pre × OTy × OTy)) : M Arg := do
  let (ps, s, t, _) ← r.inst env
  unless ps.length == qs.length do throw ⟨p, s!"{r.sym}: wrong number of arguments, found {qs.length}"⟩
  let xs ← (ps.zip qs).mapM fun (((x, y), f), (q, s', t')) => do
    unify p s!"the source of {r.sym}'s argument" s' x; unify p s!"the target of {r.sym}'s argument" t' y
    pure (r.pass p f q s')
  pure (.rel (.prim r xs s t) s t)

/-- A builtin applied to relations, every argument one relation. -/
def applied (env : Env) (p : Pos) (o : Op) (as : List (Pre × OTy × OTy)) : M Arg := do
  if let some r ← o.row p then return ← appliedRow env p r as
  match as with
  | [(q, s, t)] => do
    match o with
    | .dom => pure (.rel (.dom q) s s)
    | .ran => pure (.rel (.ran (.close p q s "ran( ) reads its argument whole")) t t)
    | .lam => pure (.rel (.lam q) s (.arr t))
    | .E => pure (.rel (.lam (.comp (.mem s) q)) (.arr s) (.arr t))  -- `E(R) ≜ Λ(∋ R)`
    | _ => throw ⟨p, s!"{o.sym} takes {(Op.table.find? (·.2.1 == o)).map (·.2.2) |>.getD 0} arguments, found 1"⟩
  | as => throw ⟨p, s!"{o.sym}: wrong number of arguments, found {as.length}"⟩

/-- A row given families over `I`: each argument `R : I ⟶ a×b` keyed, `⟨π₁,Rᴵ⟩ : I×a ⟶ I×b`, the row run once on
    them at `I×v` for each object variable `v`, and its result a family again (`rowSh`): what the row means at each
    key exactly when its meaning commutes with keying, `Prim.KeyLifts`, which `Prim.keyLifts_ok` proves of every
    row with `keyLift`; any other row has no lifting. `Prim.inst` makes its object variables fresh (`{}`). -/
def appliedRowL (I : OTy) (p : Pos) (r : Prim) (as : List Arg) : M Arg := do
  unless r.keyLift do
    notLiftable p s!"{r.sym}( )" "no theorem proves its meaning commutes with keying (`Prim.KeyLifts`, `keyLift`)"
  let ks := (← as.mapM (famOf I p)).map fun (R, a, b) => (Pre.pair (.outl I a) (keyed I R a b), OTy.prod I a, OTy.prod I b)
  let (q, s, t) := (← appliedRow {} p r ks).plain
  let a ← fresh; let b ← fresh
  unify p s!"the source of {r.sym} at the keys" s (.prod I a); unify p s!"the target of {r.sym} at the keys" t (.prod I b)
  pure (.fam (rowSh p I a b q) I a b)

/-- A builtin applied with a family among its arguments, by the rows of §e; a row by `appliedRowL`. -/
def appliedL (I : OTy) (p : Pos) (o : Op) (as : List Arg) : M Arg := do
  if let some x ← o.row p then return ← appliedRowL I p x as
  let fs ← as.mapM (famOf I p)
  let r ← match o, fs with
    | .dom, [R] => pure (lDom R)
    | .ran, [R] => pure (lRan R)
    | .lam, [R] => pure (lLam I (some (.top p I R.2.1 none)) R)
    | .E, [R] => do let b ← fresh; pure (lLam I none (← lComp I p (liftConst I p (.mem b) (.arr b) b) R))
    | o, _ => notLiftable p s!"{o.sym}( )"
  pure (.fam r.1 I r.2.1 r.2.2)

/-- `⦇R⦈`, `R : 1 + E×V ⟶ V`, as the kernel's start `ran(inl R)` and step `inr R`, given `R` elaborated (`.inr`) or
    `R` written `[a,S]` with `a`, `S` elaborated (`.inl`): then `ran(a)` and `S` by `inl[a,S] = a`, `inr[a,S] = S`, so
    no injection runs. The parts come elaborated because `elabE` recurses only on subterms. -/
def foldParts (env : Env) (m : Option OTy) (p : Pos) : (Arg × Arg) ⊕ Arg → M (Arg × Arg)
  | .inl (a, s) => base a s
  | .inr x => do
    let inj (o : Op) : M Arg := do
      let i ← constant env p o []
      match m, x with
      | some I, .fam .. => let q ← lComp I p (← famOf I p i) (← famOf I p x); pure (.fam q.1 I q.2.1 q.2.2)
      | _, _ =>
        let (q, s, t) := i.plain; let (q', s', t') := x.plain
        unify p "the source of ⦇R⦈'s algebra R, 1 + E×V" s' t; pure (.rel (.comp q q') s t')
    base (← inj .inl) (← inj .inr)
where
  base (a s : Arg) : M (Arg × Arg) := do
    let (src, tgt) := match a with | .rel _ s t | .fam _ _ s t => (s, t)
    unify p "the target of ⦇R⦈'s base inl R, the target of its step inr R" tgt (match s with | .rel _ _ t | .fam _ _ _ t => t)
    -- a base `a : B ⟶ V` means the book's `⊤a`, `⊤ : 1 ⟶ B`, as `ran(⊤a) = ran(a)` is the kernel's start
    -- either way; so `1` is its source only where nothing else fixed one, as `settleNil` does for `nil`: a base on
    -- one object, a coreflexive on `V` (`sum`'s `0`), is its own start
    let mc ← Lean.getMCtx
    match zonk mc src, zonk mc tgt with
    | .mv i, .mv j => if i != j then unify p "the source of ⦇R⦈'s base inl R" src env.one
    | .mv _, _ => unify p "the source of ⦇R⦈'s base inl R" src env.one
    | _, _ => pure ()
    match m, a with
    | some I, .fam .. => pure (← appliedL I p .ran [a], s)
    | _, _ => pure (← applied env p .ran [a.plain], s)

/-- A binary operator on one relation each side. -/
def binary (p : Pos) (o : Bin) : Pre × OTy × OTy → Pre × OTy × OTy → M Arg
  | (q, s, t), (r, s', t') => do
    match o with
    | .meet | .join | .diff => do
      unify p s!"the source of {o.sym}'s right operand" s' s; unify p s!"the target of {o.sym}'s right operand" t' t
      let x := match o with
        | .meet => Pre.meet q r | .join => .join q r | _ => .diff q r
      pure (.rel x s t)
    | .rdiv => do
      unify p "the target of `/`'s right operand" t' t
      pure (.rel (Pre.rdivWhole p q r s s') s s')
    | .symDiv => do
      unify p "the target of `÷`'s right operand" t' t
      pure (.rel (Pre.symDiv p q r s s') s s')
    | .ldiv => do
      unify p "the source of `\\`'s right operand" s' s
      let w := "R\\S reads its operands whole outside a meet with a term run on demand"
      pure (.rel (.ldiv p (.close p q s w) (.close p r s w) t t') t t')
    -- `R×S = ⟨π₁R,π₂S⟩`: `build` runs it as that pair when an operand runs on demand
    | .prod => pure (.rel (.prod (.close p q s "R×S") (.close p r s' "R×S")) (.prod s s') (.prod t t'))

/-- A binary operator with a family on a side, by the rows of §e. -/
def binaryL (I : OTy) (p : Pos) (o : Bin) (x y : Arg) : M Arg := do
  let R ← famOf I p x; let S ← famOf I p y
  let r ← match o with
    | .meet => lSame p Pre.meet R S
    | .join => lSame p Pre.join R S
    | .diff => lSame p Pre.diff R S
    | .rdiv => lRdiv I p R S
    -- `R/S ∩ (S/R)°` lifted part by part, as `Pre.symDiv` is outside a family
    | .symDiv => lSame p Pre.meet (← lRdiv I p R S) (lConv (← lRdiv I p S R))
    | .ldiv => lLdiv I p R S
    | .prod => pure (lProd R S)
  pure (.fam r.1 I r.2.1 r.2.2)

/-- A defined operator's result where it is used, given the arguments `as`: a family stays one inside a lifted
    body of the same index when an argument is a family of that body; applied to closed terms only, it is a
    closed relation `i ⟶ a×b`, which enters the body by the closed row (§e, mixed terms), as it does outside. -/
def settle (m : Option OTy) (p : Pos) (as : List Arg) : Arg → M Arg
  | .fam q i a b => match m, as.any Arg.isFam with
    | some I, true => do unify p "the index of a family" i I; pure (.fam q i a b)
    | _, _ => pure (.rel q i (.prod a b))
  | r => pure r

/-- `hylo(c, S)`'s functor `G`, read off `c : a ⟶ t` (`t = G(a)`) and `S : s ⟶ b` (`s = G(b)`) along `×`, `+`,
    `[ ]`: a place where `t` is `a` and `s` is `b` (or not known yet) is `G`'s argument, one where they are one object
    a constant. Its terms: `G(X) : t ⟶ G(b)`, `X` the variable `k` (`F` on `[ ]`, `⟨π₁·,π₂·⟩` on `×`, `[· inl,· inr]`
    on `+`, `𝟙` where `G` is constant), the object `G(b)`, and whether `G` reads `X` there (`false` where `G` is
    constant); the terms `μX : c G(X) S` would elaborate to as written. `G`'s membership is `Tm.kids` of them. -/
partial def hyloG (p : Pos) (k : Nat) (a b : OTy) (t s : OTy) : M (Pre × OTy × Bool) := do
  let any := match s with | .mv _ => true | _ => false
  if t == a && (s == b || any) then return (.var p k a b none, b, true)
  match t, s with
  | .prod t₁ t₂, .prod s₁ _s₂ | .prod t₁ t₂, s₁@(.mv _) =>
    let s₂ := match s with | .prod _ s₂ => s₂ | _ => s₁
    let (g₁, u₁, m₁) ← hyloG p k a b t₁ s₁; let (g₂, u₂, m₂) ← hyloG p k a b t₂ s₂
    if !m₁ && !m₂ then return (.id t, t, false)
    return (.pair (.comp (.outl t₁ t₂) g₁) (.comp (.outr t₁ t₂) g₂), .prod u₁ u₂, true)
  | .sum t₁ t₂, .sum s₁ _s₂ | .sum t₁ t₂, s₁@(.mv _) =>
    let s₂ := match s with | .sum _ s₂ => s₂ | _ => s₁
    let (g₁, u₁, m₁) ← hyloG p k a b t₁ s₁; let (g₂, u₂, m₂) ← hyloG p k a b t₂ s₂
    if !m₁ && !m₂ then return (.id t, t, false)
    return (.junc (.comp g₁ (.inl u₁ u₂)) (.comp g₂ (.inr u₁ u₂)) t₁ t₂,
      .sum u₁ u₂, true)
  | .arr t₁, .arr s₁ | .arr t₁, s₁@(.mv _) =>
    let (g₁, u₁, m₁) ← hyloG p k a b t₁ s₁
    if !m₁ then return (.id t, t, false)
    return (.prim mapRow [g₁] (.arr t₁) (.arr u₁), .arr u₁, true)
  | _, _ =>
    if t == s || any then return (.id t, t, false)
    throw ⟨p, s!"hylo(c, S): c's target and S's source differ at {t} against {s}, which is neither {a} against {b} \
      (the recursion) nor one object (a constant); G is read off them"⟩

/-- The body `body` of `c` elaborated once, each name of `bs` in it a variable of its own (`St.fixes`), applied to
    the argument `bs` gives it (`Pre.callE`), so each argument is computed once however often the body reads it. An
    argument or a body that is a family is the expansion (`bs` put in place), which §e lifts by its shape. -/
def callOf (env : Env) (p : Pos) (c : String) (bs : List (String × Arg)) (body : Env → M Arg) : M Arg := do
  let rels := bs.filterMap fun | (n, .rel q s t) => some (n, q, s, t) | _ => none
  -- a variable is bound to itself, read in its own form: copying it recomputes nothing
  let own : Pre → Option Nat := fun | .var _ k _ _ _ => some k | _ => none
  if bs.isEmpty || rels.length != bs.length || rels.all (own ·.2.1 |>.isSome) then
    return ← body { env with params := bs }
  let ks ← rels.mapM fun (_, q, _) => match own q with
    | some k => pure k
    | none => modifyGet fun s => (s.fixes, { s with fixes := s.fixes + 1 })
  let σ := (ks.zip (rels.map (·.2.1))).filter fun (_, q) => (own q).isNone
  modify fun st => { st with args := st.args ++ σ.map fun (k, q) => (k, st.expand q) }
  let r ← body { env with params := (rels.zip ks).map fun ((n, q, s, t), k) =>
    (n, if (own q).isSome then .rel q s t else .rel (.var p k s t none) s t) }
  let alt (q : Pre) := q.mapVar fun p' k a b t => (σ.lookup k).getD (.var p' k a b t)
  let form (q : Pre) (f : Option Bool) :=
    q.mapVar fun p' k a b t => .var p' k a b (if (σ.lookup k).isSome then f else t)
  pure <| match r with
    | .rel q s t => .rel (.callE p c ks (rels.map (·.2.1)) (alt q) (form q none) (form q (some false)) s t) s t
    | .fam q i s t => .fam (alt q) i s t

mutual

/-- Elaborate `e` in the mode `m`: plain, or the body of a definition lifted to the index `I`. -/
def elabE (env : Env) (m : Option OTy) : Expr → M Arg
  | .name p n => do
    match env.params.lookup n with
    -- a fixed point's variable at the place it is used, which its errors name
    | some (.rel (.var _ k a b x) s t) => pure (.rel (.var p k a b x) s t)
    | some a => pure a
    | none => match env.def? n with
      | some d =>
        if d.arity == 0 then (do settle m p [] (← d.apply p []))
        else throw ⟨p, s!"'{n}' takes {d.arity} arguments, found none"⟩
      | none => throw ⟨p, s!"unknown name '{n}'"⟩
  -- `μX : c G(X) S` as written out by hand, `G` read off the types of `c` and `S`, and the children `c ∈_G`
  | .op p .hylo _ [c, s] => do
    if m.isSome then notLiftable p "hylo( )"
    let (qc, a, t) := (← elabE env none c).plain; let (qs, s', b) := (← elabE env none s).plain
    let k ← modifyGet fun st => (st.fixes, { st with fixes := st.fixes + 1 })
    let mc ← Lean.getMCtx
    let (gx, gb, _) ← hyloG p k (zonk mc a) (zonk mc b) (zonk mc t) (zonk mc s')
    unify p "the source of hylo's algebra S, G(B)" s' gb
    pure (.rel (.hylo c.pos k (.comp (.comp qc gx) qs) a b) a b)
  | .op p o objs args => do
    let as ← elabArgs env m args
    if args.isEmpty then constant env p o objs
      else match m with
        | some I => if as.any Arg.isFam then appliedL I p o as else applied env p o (as.map Arg.plain)
        | none => applied env p o (as.map Arg.plain)
  | .app p n args => do
    let as ← elabArgs env m args
    match env.def? n with
    | some d =>
      if d.arity != as.length then throw ⟨p, s!"'{n}' takes {d.arity} arguments, found {as.length}"⟩
      settle m p as (← d.apply p as)
    | none => throw ⟨p, s!"unknown name '{n}'"⟩
  -- `R n S`: the definition declared `_n_`, given `R` and `S` (§c)
  | .inf p n a b => do
    let x ← elabE env m a; let y ← elabE env m b
    match env.infix? n with
    | some d => settle m p [x, y] (← d.apply p [x, y])
    | none => throw ⟨p, s!"unknown infix operator '{n}'"⟩
  | .comp a b => do
    let x ← elabE env m a
    let p := b.pos
    -- `Xest(Q)`, `Xfront(Q)` with `Q` a family: `est`, `front` run one `Q` on every array, so the rows of §e
    -- work on `G ≜ X∋`, the values of each key; a closed `Q` takes the closed row below
    let q? ← match m, b with
      | some _, .op _ .est [] [qe] | some _, .op _ .front [] [qe] => do
        let y ← elabE env m qe; pure (if y.isFam then some y else none)
      | _, _ => pure none
    let est := match b with | .op _ .est _ _ => true | _ => false
    -- `X⦇R⦈` with `R` a family: the fold keyed by the index, on the arrays `X` gives each key (§e)
    let fold? ← match m, b with
      | some _, .fold _ false r => do
        let (y, z) ← foldParts env m p (← match r with
          | .junc _ a s => do pure (.inl (← elabE env m a, ← elabE env m s))
          | r => do pure (.inr (← elabE env m r)))
        pure (if y.isFam || z.isFam then some (y, z) else none)
      | _, _ => pure none
    if let (some I, some (y, z)) := (m, fold?) then
      let r ← lFold I p (← famOf I p x) (← famOf I p y) (← famOf I p z)
      return .fam r.1 I r.2.1 r.2.2
    match m, q? with
    | some I, some q => do
      let e ← fresh
      let G ← lThen p (← famOf I p x) (.mem e, .arr e, e)
      let Q ← famOf I p q
      let r ← if est then do lSame p Pre.meet G (← lLdiv I p (lConv G) (lConv Q))
        else do pure (lLam I none (← lSame p Pre.diff G (← lComp I p G (← lSame p Pre.diff Q (lConv Q)))))
      pure (.fam r.1 I r.2.1 r.2.2)
    | _, _ =>
      let y ← elabE env m b
      match m, x.isFam || y.isFam with
      | some I, true =>
        let r ← match x, y with
          | .fam .., .rel q s t => lThen p (← famOf I p x) (q, s, t)
          | _, _ => do lComp I p (← famOf I p x) (← famOf I p y)
        pure (.fam r.1 I r.2.1 r.2.2)
      | _, _ =>
        let (q, s, t) := x.plain; let (r, s', t') := y.plain
        unify p "the source of the right factor of a composition" s' t
        pure (.rel (.comp q r) s t')
  | .bin p o a b => do
    let x ← elabE env m a; let y ← elabE env m b
    match m, x.isFam || y.isFam with
    | some I, true => binaryL I p o x y
    | _, _ => binary p o x.plain y.plain
  | .conv p a => do
    -- `build` pushes the converse to the leaves when the term runs on demand (`convTm`)
    match ← elabE env m a with
    | .fam q i s t => let r := lConv (q, s, t); pure (.fam r.1 i r.2.1 r.2.2)
    | .rel q s t => pure (.rel (.conv (.close p q s "R°")) t s)
  | .compl p a => do
    match ← elabE env m a with
    | .fam q i s t => let r := lCompl i p (q, s, t); pure (.fam r.1 i r.2.1 r.2.2)
    | .rel q s t => pure (.rel (.diff (.top p s t none) q) s t)
  | .pair p a b => do
    let x ← elabE env m a; let y ← elabE env m b
    match m, x.isFam || y.isFam with
    | some I, true => let r ← lPair p (← famOf I p x) (← famOf I p y); pure (.fam r.1 I r.2.1 r.2.2)
    | _, _ =>
      let (q, s, t) := x.plain; let (r, s', t') := y.plain
      unify p "the source of the pair's second part" s' s
      pure (.rel (.pair q r) s (.prod t t'))
  | .junc p a b => do
    let x ← elabE env m a; let y ← elabE env m b
    match m, x.isFam || y.isFam with
    | some I, true => let r ← lJunc p (← famOf I p x) (← famOf I p y); pure (.fam r.1 I r.2.1 r.2.2)
    | _, _ =>
      let (q, s, t) := x.plain; let (r, s', t') := y.plain
      unify p "the target of the case's second part" t' t
      pure (.rel (.junc q r s s') (.sum s s') t)
  | .fold p d r => do
    let (x, y) ← foldParts env m p (← match r with
      | .junc _ a s => do pure (.inl (← elabE env m a, ← elabE env m s))
      | r => do pure (.inr (← elabE env m r)))
    if x.isFam || y.isFam then
      throw ⟨p, "⦇R⦈ given a family is not liftable on its own: its arrays come from its left, X⦇R⦈ (§e), a left fold"⟩
    let (q, v, v') := x.plain; let (r, ev, w) := y.plain
    unify p "the fold's start, a coreflexive" v' v
    let e ← fresh
    unify p "the source of the fold's step" ev (if d then .prod e v else .prod v e)
    unify p "the target of the fold's step" w v
    pure (.rel (.fold d (.close p q v "the fold's start is read whole") r) (.arr e) v)
  | .lit p ps ty => do
    let a ← litTy env.objs env.gdef p (ps.map (·.1)); let b ← litTy env.objs env.gdef p (ps.map (·.2))
    if let some (A, B) := ty then
      unify p "the table's source" a (← oty env [] A); unify p "the table's target" b (← oty env [] B)
    pure (.rel (.lit p a b ps env.gdef) a b)
  -- a built term, as a closed definition is (`walk`)
  | .col p s c => do let (r, a, b) ← MonadExcept.ofExcept (colOf env p s c); settle m p [] (.rel (.tm r) a b)
  -- `X : a ⟶ b` in scope in the body, which has that type and is monotonic in `X`; `ν` from the conjuncts
  -- without `X`, `μ` from `𝟘` on any object, its rounds capped at run time (`muCap`)
  -- the item elaborated once and computed once: a parameter of the term it scopes over, which binds every name in
  -- scope as its parameters too (`callOf`), so the call's body reads no variable of the caller
  | .whr p x e b => do
    let a ← elabE env m e
    callOf env p x ((x, a) :: env.params) fun env' => elabE env' m b
  | .fix p least x b => do
    let fx := s!"{if least then "μ" else "ν"}{x}"
    if m.isSome then notLiftable p fx
    let a ← fresh; let c ← fresh
    let k ← modifyGet fun s => (s.fixes, { s with fixes := s.fixes + 1 })
    let (q, s, t) := (← elabE { env with params := (x, .rel (.var p k a c none) a c) :: env.params } none b).plain
    unify p s!"the source of {fx}'s body" s a; unify p s!"the target of {fx}'s body" t c
    if let some e := q.polarity k fx x true "" then throw e
    let S := q.bound k
    if !least && S.isNone then
      throw ⟨p, s!"{fx} needs a bound: write S ∩ φ with S not mentioning {x} (⊤(A,B) for the whole object)"⟩
    pure (.rel (.fix p least k x S q a c) a c)

def elabArgs (env : Env) (m : Option OTy) :
    List Expr → M (List Arg)
  | [] => pure []
  | e :: es => do let a ← elabE env m e; pure (a :: (← elabArgs env m es))

end

/-- A declared type matched against an argument's: the variables' objects so far, no match, or a variable met
    at two objects. -/
inductive Match
  | ok (vs : List (String × OTy))
  | no
  | clash (n : String) (o o' : OTy)

/-- `t` as `mk a b`, an unsolved variable solved to that form; none when `t` is another object. -/
def split (_p : Pos) (mk : OTy → OTy → OTy) (t : OTy) : M (Option (OTy × OTy)) := do
  let a ← fresh; let b ← fresh
  if ← defEq t (mk a b) then let mc ← Lean.getMCtx; pure (some (zonk mc a, zonk mc b)) else pure none

def Match.bind (r : Match) (k : List (String × OTy) → M Match) : M Match :=
  match r with | .ok vs => k vs | r => pure r

/-- First-order matching of the declared `o` against `t`, extending the instantiation `vs`: a variable takes
    the object it meets, once; a declared object unifies. -/
def pmatch (env : Env) (p : Pos) (vs : List (String × OTy)) : OExp → OTy → M Match
  | .var _ n, t => match vs.lookup n with
    | none => pure (.ok ((n, t) :: vs))
    | some o => do
      if ← defEq t o then pure (.ok vs) else let mc ← Lean.getMCtx; pure (.clash n (zonk mc o) (zonk mc t))
  | .prod x y, t => do match ← split p .prod t with
    | some (a, b) => (← pmatch env p vs x a).bind (pmatch env p · y b)
    | none => pure .no
  | .sum x y, t => do match ← split p .sum t with
    | some (a, b) => (← pmatch env p vs x a).bind (pmatch env p · y b)
    | none => pure .no
  | .list x, t => do match ← split p (fun a _ => .arr a) t with
    | some (a, _) => pmatch env p vs x a
    | none => pure .no
  | o@(.name ..), t => do
    let O ← oty env [] o
    pure (if ← defEq t O then .ok vs else .no)

/-- `x ⟶ y` matched against `s ⟶ t`. -/
def both (env : Env) (p : Pos) (vs : List (String × OTy)) (x y : OExp) (s t : OTy) : M Match := do
  (← pmatch env p vs x s).bind (pmatch env p · y t)

/-- Bind a parameter to its argument: one relation, or, for a declared `S : A ⟶ B` given `I ⟶ A×B`, a family
    with the index `I` (§e). `vs` is the use's instantiation of the object variables so far. -/
def bind (env : Env) (p : Pos) (P : Param) (a : Arg) (vs : List (String × OTy)) :
    M ((String × Arg) × Option OTy × List (String × OTy)) := do
  match P.ty, a with
  | none, .rel .. => pure ((P.name, a), none, vs)
  | none, .fam .. =>
    throw ⟨p, s!"parameter '{P.name}' is given a family but declares no type; write '{P.name} : A ⟶ B'"⟩
  | some (x, y), a => do
    let sv ← save; let mc := sv.2.meta.mctx
    let decl := s!"'{P.name} : {x.show} ⟶ {y.show}'"
    let clash (r : Match) (s t : OTy) : M Unit := match r with
      | .clash n o o' => throw ⟨p, s!"`{n}` in the type of '{P.name}' is both {o} and {o'}: {decl} given {s} ⟶ {t}"⟩
      | _ => pure ()
    match a with
    | .fam q i s t =>
      match ← both env p vs x y s t with
      | .ok vs => pure ((P.name, .fam q i (← oty env vs x) (← oty env vs y)), some i, vs)
      | r => do restore sv; clash r (zonk mc s) (zonk mc t); throw ⟨p, s!"{decl} given a family of fibre {zonk mc s} ⟶ {zonk mc t}"⟩
    | .rel q s t =>
      -- one relation `A ⟶ B` first; failing that, a family `I ⟶ A×B` (§e)
      let r ← both env p vs x y s t
      if let .ok vs := r then return ((P.name, a), none, vs)
      restore sv
      let r' ← match ← split p .prod t with
        | some (u, v) => both env p vs x y u v
        | none => pure .no
      if let .ok vs := r' then return ((P.name, .fam q s (← oty env vs x) (← oty env vs y)), some s, vs)
      restore sv
      let s := zonk mc s; let t := zonk mc t
      clash r s t; clash r' s t
      throw ⟨p, s!"{decl} given {s} ⟶ {t}: neither {x.show} ⟶ {y.show} nor a family I ⟶ {x.render true}×{y.render true}"⟩

/-- The projection of `(I₀×I₁)×…×Iₙ`, left-nested over the factors `ix`, onto the factor `k`. -/
def proj (ix : Array OTy) (k : Nat) : Pre := go (ix.size - 1)
where
  pre (m : Nat) : OTy := (ix.toList.take (m + 1)).tail.foldl .prod (ix.toList.headD default)
  go : Nat → Pre
    | 0 => .id (pre 0)
    | m + 1 =>
      if m + 1 == k then .outr (pre m) (ix.toList.getD (m + 1) default)
      else if m + 1 > k then .comp (.outl (pre m) (ix.toList.getD (m + 1) default)) (go m)
      else .id (pre (m + 1))

/-! ### Declared types -/

def OTy.mvs : OTy → List Lean.MVarId
  | .mv k => [k]
  | .prod a b | .sum a b => a.mvs ++ b.mvs
  | .arr a => a.mvs
  | .base _ => []

def OTy.bases : OTy → List String
  | .base n => [n]
  | .prod a b | .sum a b => a.bases ++ b.bases
  | .arr a => a.bases
  | .mv _ => []

/-- Let-generalisation of the body `x` of the definition `n`: each object it made (a metavariable numbered from `k`
    on) that is still open and that neither a use nor the result reaches (`keep`) becomes the object variable `n#i`.
    No use determines it, so every use has it at the one object a constant builds a variable at, `.long` (`objOf`
    of a name no declaration holds), and its number checks run there (`numObj`, `numCheck`). A literal's or a
    `nil`'s open object is left to `settleOpen`; a `check` is no definition, so an object open there is refused. -/
def generalise (n : String) (p : Pos) (k : Nat) (keep : List OTy) (x : Pre) : M Unit := do
  let mc ← Lean.getMCtx
  let held := (keep ++ x.nilSrcs ++ x.lits.flatMap fun (_, a, b, _) => [a, b]).flatMap fun o => (zonk mc o).mvs
  let own := mc.decls.toList.filter fun (m, d) =>
    d.index ≥ k && !mc.eAssignment.contains m && d.type == .const ``Obj [] && !held.contains m
  (own.mergeSort (·.2.index ≤ ·.2.index)).zipIdx.forM fun ((m, _), i) => unify p "" (.mv m) (.base s!"{n}#{i}")

/-- The letters an inferred type names its open objects by: `α`…`ω` without `ο` and `π`, which read as `o`, `π₁`. -/
def varNames : List String := ("αβγδεζηθικλμνξρστυφχψω".toList).map Char.toString

/-- `o` with each unsolved variable of `os` named an object variable, `α β …` by first occurrence, skipping the
    names `os` already holds: an inferred type as a declaration writes it. -/
def gen (os : List OTy) (o : OTy) (avoid : List String := []) : OTy :=
  let used := avoid ++ os.flatMap OTy.bases
  let σ := (os.flatMap OTy.mvs).eraseDups.zip (varNames.filter (!used.contains ·))
  let rec go : OTy → OTy
    | .mv k => match σ.lookup k with | some n => .base n | none => .mv k
    | .prod a b => .prod (go a) (go b)
    | .sum a b => .sum (go a) (go b)
    | .arr a => .arr (go a)
    | o => o
  go o

/-- The body's type `s ⟶ t` against the declared `ty` of `n`, its variables the parameters' at this use (`vs`)
    and fresh otherwise: the declared type determines the objects the body leaves open (§e). -/
def declared (env : Env) (p : Pos) (n : String) (vs : List (String × OTy)) (ty : OExp × OExp) (s t : OTy) :
    M Unit := do
  let vs ← (ty.1.vars ++ ty.2.vars).foldlM (fun vs v => do
    if (vs.lookup v).isSome then pure vs else pure ((v, ← fresh) :: vs)) vs
  let a ← oty env vs ty.1; let b ← oty env vs ty.2
  let mc ← Lean.getMCtx
  try
    unify p "" s a
    unify p "" t b
  catch _ => do
    let s := zonk mc s; let t := zonk mc t
    throw ⟨p, s!"`{n}` is declared {OExp.arrow ty}, but its body is {gen [s, t] s} ⟶ {gen [s, t] t}"⟩

/-- The parameters `ps` with their objects, each declared one's object variables rigid and an undeclared type
    fresh, and `env` with them in scope: a signature read with no use (`inferSig`, a theorem's statement). -/
def bindSig (env : Env) (ps : List Param) : M (List (String × OTy × OTy) × Env) := do
  let bs ← ps.mapM fun P => do
    match P.ty with
    | some (x, y) =>
      let vs := (x.vars ++ y.vars).map fun v => (v, OTy.base v)
      pure (P.name, ← oty env vs x, ← oty env vs y)
    | none => pure (P.name, ← fresh, ← fresh)
  pure (bs, { env with params := bs.map fun (q, s, t) => (q, .rel (.zero s t) s t) })

/-- The type of `n`, as `typesOf` prints it: each parameter's (declared, its variables kept as written, or
    inferred) and the body's, open objects named as variables; what a definition missing one should write. -/
def inferSig (env : Env) (n : String) (ps : List Param) (b : Body) : M String := do
  let (bs, env') ← bindSig env ps
  let r ← match b with
    | .rel e => do let (_, s, t) := (← elabE env' none e).plain; pure (some (s, t))
    | .test e f => do let _ ← elabE env' none e; let _ ← elabE env' none f; pure none
  let mc ← Lean.getMCtx
  let os := (bs.flatMap fun (_, s, t) => [s, t]) ++ (match r with | some (s, t) => [s, t] | none => [])
  let os := os.map (zonk mc)
  -- a variable is not a name in scope (§e), nor the one being defined
  let avoid := n :: env.defs.map (·.1)
  let arr (s t : OTy) := s!"{gen os (zonk mc s) avoid} ⟶ {gen os (zonk mc t) avoid}"
  pure (sigText n ((ps.zip bs).map fun (P, q, s, t) => (q, some ((P.ty.map OExp.arrow).getD (arr s t))))
    (r.map fun (s, t) => arr s t))

/-- The class of a family argument's index `j?` among the distinct indices `ix` so far, by first occurrence, and
    `ix` with it (§e); `none` for a relation. A definition (`mkDef`) and a call of it (`Expand.callDef`) both number
    by it, so the call lines up with the definition. -/
def idxClass (ix : Array OTy) : Option OTy → M (Array OTy × Option Nat)
  | none => pure (ix, none)
  | some j => do
    for h : k in [0:ix.size] do
      if ← defEq j (ix[k]'h.upper) then return (ix, some k)
    pure (ix.push j, some ix.size)

section Num

variable (objs : Objs) (mc : Lean.MetavarContext) (dp : Pos)

def internal {α : Type} (what : String) : Except Err α := throw ⟨dp, s!"internal: {what}"⟩

/-- The element `w` of the declared base object `o`: its position among the named elements, or the number. -/
def code (p : Pos) (o : OTy) (w : String) : Except Err Int64 :=
  match zonk mc o with
  | .base n => match objs.lookup n with
    | some i =>
      -- a numeral at an object variable whose checks are left to each use: that build is never emitted, and each use
      -- reads the word at the object it puts there (`numCheck`), so no code is read here
      if i.deferred && (numParts w).isSome then pure 0 else
      -- a number object's words are `wordAt`'s at its atom; one at another atom than `i64` holds no long (`litCol`)
      if i.num then match i.obj with
        | .long => (wordAt p n .i64 w).map (·.toInt64)
        | o => throw ⟨p, s!"{w} at {n}, an object of {repr o}: no long"⟩
      else match i.range, (i.elems.idxOf? w).bind (i.codes[·]?), w.toInt? with
      | some (lo, hi), _, some k => if lo ≤ k ∧ k ≤ hi then pure (Int64.ofInt k)
          else throw ⟨p, s!"{w} is not in {n} = {lo}…{hi}"⟩
      | none, some k, _ => pure k
      | none, none, some k =>
        -- each call checks its object holds the number (`build`'s `.call`)
        if i.ovar then
          if i.obj == .long then pure (Int64.ofInt k)
          else throw ⟨p, s!"the number {w} at {n}, an object variable its constant is generic over"⟩
        else throw ⟨p, s!"'{w}' is not an element of {n}"⟩
      | _, _, _ => throw ⟨p, s!"'{w}' is not an element of {n}"⟩
    | none => throw ⟨p, s!"unknown object '{n}'"⟩
  | o => throw ⟨p, s!"a literal relates elements of declared objects, found {o}"⟩

/-- The column of a literal's side of object `o`, its `n` rows' sides `rows`: a long column of codes at a leaf,
    the pair of the two parts' columns at a product, at an array the column of all its elements row after row
    as the payload, row `i` the slice `[lo i, hi i)`. `o` is zonked. -/
def litCol (p : Pos) (n : USize) (o : OTy) (rows : List Tup) : Except Err ((A : Obj) × Vals A n) :=
  match o with
  | .prod x y => do
    let ⟨A, u⟩ ← litCol p n x (rows.map fun | .pair r _ => r | r => r)
    let ⟨B, v⟩ ← litCol p n y (rows.map fun | .pair _ r => r | r => r)
    pure ⟨.prod A B, (u, v)⟩
  | .arr x => do
    let ts ← rows.mapM fun
      | .arr es => pure es
      | r => throw ⟨p, s!"a literal's element of {o} is an array, found {r.show}"⟩
    let es := ts.flatten
    needSize es.length "literal array cells" (fun _ => internal dp "literal array cells") fun m => do
    let ⟨B, v⟩ ← litCol p m x es
    let ends := (ts.foldl (fun (k, acc) t => (k + t.length, (k + t.length) :: acc)) (0, ([] : List Nat))).2.reverse
    let hi := ends.map Int64.ofNat; let lo := (ends.zip ts).map fun (e, t) => Int64.ofNat (e - t.length)
    if h : lo.length.toUSize = n ∧ hi.length.toUSize = n then
      (let l : Arr .i64 n := h.1 ▸ col lo; let r : Arr .i64 n := h.2 ▸ col hi; pure ⟨.arr B, ⟨_, l, r, v⟩⟩)
    else internal dp "literal array rows"
  | .mv _ => throw (litOpen objs p rows)
  -- a sum only the context gives, to an empty array's elements: no rows to read
  | .sum x y =>
    if h : n = 0 ∧ rows.isEmpty then h.1 ▸ (do
      let ⟨A, u⟩ ← litCol p 0 x []; let ⟨B, v⟩ ← litCol p 0 y []
      let _ := (u, v)
      match Vals.none (.sum A B) with
      | .ok z => pure ⟨.sum A B, z⟩
      | .error s => throw ⟨p, s!"an empty literal of {o}: {s}"⟩ : Except Err ((A : Obj) × Vals A 0))
    else throw ⟨p, s!"a literal relates elements of declared objects, found {o}"⟩
  | o => do
    -- a one-character string at a word's object is its `char` (`Tup.char?`)
    let rows := rows.map fun r => r.char?.elim r .leaf
    -- an object declared at another atom (`obj F : f64`): each word stored at that atom (`wordAt`)
    if let .base m := o then if let some { ovar := false, obj := .atom t, .. } := objs.lookup m then
      if t != .i64 then
        let ws ← rows.mapM fun
          | .leaf w => wordAt p m t w
          | r => throw ⟨p, s!"a literal's element of {o} is a word, found {r.show}"⟩
        let a := ws.toArray
        if h : a.size = n.toNat ∧ (t ≠ .u1 ∧ t.width.isSome) then
          return ⟨.atom t, Arr.ofFn t n (fun i => a[i.val]'(by have := i.isLt; omega)) h.2⟩
        else return ← internal dp s!"literal rows at {atomName t}"
    let cs ← rows.mapM fun
      | .leaf w => code objs mc p o w
      | r => throw ⟨p, s!"a literal's element of {o} is a word, found {r.show}"⟩
    -- an object stored at `1` (one element, `ObjInfo.obj`): each word checked by `code` above, no column
    if let .base m := o then if let some { obj := .one, .. } := objs.lookup m then return ⟨.one, ()⟩
    if h : cs.length.toUSize = n then (let c : Arr .i64 n := h ▸ col cs; pure ⟨.long, c⟩) else internal dp "literal rows"

/-- The number checks of the node `x` at its solved objects: the number objects it computes on (`numsAt`, read by
    `settleLit` too), `$`'s `castOK`, and a literal's words read at its objects (`litCol`). `build` runs them; a use of a generic definition runs them on its expansion
    first, so the error names the use and the objects its variables were given (`mkDef`). An object the use has not
    solved yet is checked when `build` reaches it. -/
def numCheck (x : Pre) : Except Err Unit := do
  x.numsAt mc |>.forM fun (o, op, ok) =>
    if (zonk mc o).mvs.isEmpty then discard (numObj objs mc dp o op ok) else pure ()
  match x with
  | .prim r _ s t => do
    -- `$` is typed by unification at any two objects; which atoms it joins is `castOK`'s, read off their formats
    if r.sym == "$" && (zonk mc s).mvs.isEmpty && (zonk mc t).mvs.isEmpty then
      let A ← objOf objs dp (zonk mc s); let B ← objOf objs dp (zonk mc t)
      let nm : Obj → String := fun | .atom a => atomName a | _ => "no atom"
      let dfr (o : OTy) : Bool := match zonk mc o with | .base n => (objs.lookup n).any (·.deferred) | _ => false
      unless dfr s || dfr t || (match A, B with | .atom a, .atom b => QAtomicType.castOK a b | _, _ => false) do
        throw ⟨dp, s!"$ from {zonk mc s} ({nm A}) to {zonk mc t} ({nm B}): not every {nm A} value is a {nm B} \
          value, and $ keeps a number's value"⟩
  | .lit p a b ps _ =>
    [(a, ps.map (·.1)), (b, ps.map (·.2))].forM fun (o, rows) =>
      if (zonk mc o).mvs.isEmpty then discard (litCol objs mc dp p rows.length.toUSize (zonk mc o) rows) else pure ()
  | _ => pure ()

/-- The number checks of the use `u` at the objects the use solved its variables to (`numCheck`), the error naming
    the use and each variable's object; a variable nothing at the use solved is refused, naming it and the definition. -/
def Use.check (u : Use) : Except Err Unit := do
  let us := u.us.map fun (v, o) => (v, zonk mc o)
  if let some (v, _) := us.find? (!·.2.mvs.isEmpty) then
    throw ⟨u.p, s!"`{u.n}` at this use: nothing here fixes its object variable '{v}' \
      (`{u.n}` : {u.sig}); give the use an expected type: a typed definition, a check against a typed term, or a \
      composition that fixes {v}"⟩
  if let .error e := u.xs.forM (numCheck objs mc u.p) then
    throw ⟨u.p, s!"`{u.n}` at this call, where {", ".intercalate (us.map fun (v, o) => s!"{v} is {o}")}: {e.msg}"⟩

end Num

/-- The uses waiting on their objects (`St.uses`) checked, now that the term around them is elaborated and its
    open objects settled (`settleOpen`, a definition's `generalise`). -/
def settleUses : M Unit := do
  let st ← get; let mc ← Lean.getMCtx
  st.uses.forM fun u => match u.check st.objs mc with | .error e => throw e | .ok _ => pure ()
  set { st with uses := [] }

/-- A definition with parameters: its body elaborated at each use, lifted when a declared parameter is given
    a family, its result checked against the declared type `ty`; a test `e ⊑ f` is the coreflexive
    `D − dom(R − S)` of the keys whose fibres pass. -/
def mkDef (env : Env) (n : String) (dp : Pos) (ps : List Param) (body : Body) (ty : Option (OExp × OExp)) :
    Def where
  arity := ps.length
  apply p args := do
    let k := (← Lean.getMCtx).mvarCounter
    -- one instantiation of the object variables per use, shared by the parameters left to right (§e)
    let (bs, vs) ← (ps.zip args).foldlM (fun (bs, vs) (P, a) => do
      let (b, j, vs) ← bind env p P a vs; pure (bs ++ [(b, j)], vs)) ([], [])
    -- every variable of the declared types is in scope in the body (`x $ φ`); one the parameters leave open is fresh,
    -- fixed by the body or the declared result (`declared`)
    let tys := ty.toList ++ ps.filterMap (·.ty)
    let vs ← (tys.flatMap fun (x, y) => x.vars ++ y.vars).foldlM (fun vs v => do
      if (vs.lookup v).isSome then pure vs else pure ((v, ← fresh) :: vs)) vs
    let check (s t : OTy) : M Unit := match ty with
      | some ty => declared env p n vs ty s t
      | none => pure ()
    -- the distinct indices `I₀ … Iₙ` of the family arguments, and each family's place among them (§e, mixed terms)
    let (ix, pl) ← bs.foldlM (fun (ix, pl) (_, j?) => do
      let (ix, k?) ← idxClass ix j?; pure (ix, pl ++ [k?])) (#[], ([] : List (Option Nat)))
    -- several indices: the body runs at `(I₀×I₁)×…`, each family re-keyed by its projection
    let idx := ix.toList.head?.map fun i => ix.toList.tail.foldl .prod i
    let bound := (bs.zip pl).map fun (((n, a), _), k?) => match a, k?, idx with
      | .fam q _ s t, some k, some P => if ix.size > 1 then (n, .fam (.comp (proj ix k) q) P s t) else (n, a)
      | _, _, _ => (n, a)
    let gdef := if tys.any (fun (x, y) => !(x.vars ++ y.vars).isEmpty) then some n else none
    let env' := { env with params := bound, ovars := vs, gdef }
    let r : Arg ← match body, idx with
    | .rel e, none => do
      let r ← callOf env' p n bound fun env'' => elabE env'' none e
      let (_, s, t) := r.plain; check s t; pure r
    | .rel e, some I => do
      let r ← famOf I p (← elabE env' (some I) e)
      check r.2.1 r.2.2
      pure (.fam r.1 I r.2.1 r.2.2)
    | .test _ _, none => throw ⟨p, s!"the test defined at {dp} needs a family; write `check` for one relation"⟩
    | .test e f, some I => do
      let R ← famOf I p (← elabE env' (some I) e)
      let S ← famOf I p (← elabE env' (some I) f)
      let (d, _) ← lSame p Pre.diff R S
      pure (.rel (.diff (.id I) (.dom d)) I I)
    let keep := vs.map (·.2) ++ (r :: args).flatMap fun | .rel _ s t => [s, t] | .fam _ i s t => [i, s, t]
    generalise n p k keep r.plain.1
    -- a literal written in this body (`Pre.lits`' last part, not one an argument brings) whose open object no use
    -- reaches is read against the objects the definition sees (`settleLit`), as the body's other names are: the
    -- caller's objects are not in its scope, so a use cannot make it ambiguous
    let mc ← Lean.getMCtx
    let reach := keep.flatMap fun o => (zonk mc o).mvs
    let ns := r.plain.1.nums mc
    r.plain.1.lits.forM fun (q, a, b, ps, d) => if gdef.isNone || d != gdef then pure () else
      [(a, ps.map (·.1)), (b, ps.map (·.2))].forM fun (o, ts) =>
        if (zonk mc o).mvs.any reach.contains then pure () else settleLit env.objs ns q d ts o
    -- the number checks a generic body leaves to its uses (`ObjInfo.deferred`), on this expansion once the use has
    -- solved its variables, so the error names the use and each variable's object; a variable the use's expected
    -- type fixes (one only the result names) is solved after this returns, so its use waits (`settleUses`)
    let mc ← Lean.getMCtx
    let u : Use := ⟨p, n, (ty.map OExp.arrow).getD "", vs.reverse, r.plain.1.nodes⟩
    if gdef.isSome then
      if u.us.all fun (_, o) => (zonk mc o).mvs.isEmpty then
        if let .error e := u.check (← get).objs mc then throw e
      else modify fun st => { st with uses := st.uses ++ [u] }
    pure r

/-! ### Build: the solved objects, the core term -/

/-- The swap `A×B ⟶ B×A`, `⟨π₂,π₁⟩`. -/
def swapTm {A B : Obj} : Tm (.prod A B) (.prod B A) := .pair .outr .outl

/-- `τ(R) = dom(π₂ ∩ π₁R)` for `R` that runs: the pairs `(a,b)` in demand with `a R b`. -/
def pairTest {A B : Obj} (t : Tm A B) : Tm (.prod A B) (.prod A B) :=
  .dom (.meet .outr (.comp .outl t))

/-- `t°` read through one projection of its source `A₁×A₂`: `Zπ₁°` (`.inl Z`) or `Zπ₂°` (`.inr Z`), `Z` run
    on demand. It does not run alone, but a meet with the other projection does (`Proj.meet`). -/
abbrev Proj (B A₁ A₂ : Obj) := Tm B A₁ ⊕ Tm B A₂

/-- `P` before `Zπᵢ°`: `(PZ)πᵢ°`. -/
def Proj.pre {C B A₁ A₂ : Obj} (p : Tm C B) : Proj B A₁ A₂ → Proj C A₁ A₂
  | .inl z => .inl (.comp p z)
  | .inr z => .inr (.comp p z)

/-- `Xπᵢ° ∩ Yπⱼ°`: across the two projections the pair `⟨X,Y⟩`, which runs (`Gen.rpair_eq_meet_proj`); on
    one, `(X∩Y)πᵢ°` (`Gen.meet_comp_conv_graph`). -/
def Proj.meet {B A₁ A₂ : Obj} : Proj B A₁ A₂ → Proj B A₁ A₂ → Tm B (.prod A₁ A₂) ⊕ Proj B A₁ A₂
  | .inl x, .inr y => .inl (.pair x y)
  | .inr x, .inl y => .inl (.pair y x)
  | .inl x, .inl y => .inr (.inl (.meet x y))
  | .inr x, .inr y => .inr (.inr (.meet x y))

mutual

/-- `R°` for `R` run on demand (§a), itself run on demand: pushed to the leaves by `(RS)° = S°R°`,
    `(R∩S)° = R°∩S°` (and `∪`, `−`), `⟨R,S⟩° = π₁R° ∩ π₂S°`, a coreflexive is its own converse, and a builtin
    by its named converse (`cons° = uncons`), and the prelude's `perm` as its own (`Tm.own`). A side that reads
    its source through one projection is met with one through the other (`convProj`), so `(R×S)° = R°×S°`. A
    closed part is conversed whole. The error is the leaf whose converse does not run on demand. -/
def convTm {A B : Obj} (t : Tm A B) : Except String (Tm B A) :=
  if t.dem = false then pure (.conv t) else
  match t with
  | .val R => pure (.conv (.val R))
  -- a parameter tested on pairs is a coreflexive, its own converse
  | .var _ k => pure (.var true k)
  | .nu k S b => pure (.conv (.nu k S b))
  | .mu k w n b => pure (.conv (.mu k w n b))
  | .uni U => pure (.uni U)
  | .zero => pure .zero
  | .conv R => pure R
  | .ldiv R S U V => pure (.conv (.ldiv R S U V))
  | .rdiv R S U V => pure (.conv (.rdiv R S U V))
  | .leq t U => pure (.conv (.leq t U))
  | .lt t U => pure (.conv (.lt t U))
  | .id => pure .id
  | .own R => pure (.own R)
  | .comp R S => do let s ← convTm S; let r ← convTm R; pure (.comp s r)
  | .meet R S => match convTm R, convTm S with
    | .ok r, .ok s => pure (.meet r s)
    | r, s => do
      let l := match r, s with | .error l, _ => l | _, .error l => l | _, _ => ""
      match A, R, S with
      | .prod _ _, R, S => match convProj R, convProj S with
        | .ok x, .ok y => match Proj.meet x y with | .inl p => pure p | .inr _ => throw l
        | _, _ => throw l
      | _, _, _ => throw l
  | .join R S => do let r ← convTm R; let s ← convTm S; pure (.join r s)
  | .diff R S => do let r ← convTm R; let s ← convTm S; pure (.diff r s)
  -- `⟨R,S⟩° = π₁R° ∩ π₂S°`; with one side's converse only, the other is tested on the pairs it gives:
  -- `⟨π₁R°,π₂⟩τ(S)π₁`, `⟨π₁,π₂S°⟩τ(R°)π₂`
  | .pair R S => match convTm R, convTm S with
    | .ok r, .ok s => pure (.meet (.comp .outl r) (.comp .outr s))
    | .ok r, .error _ => pure (.comp (.pair (.comp .outl r) .outr) (.comp (pairTest S) .outl))
    | .error _, .ok s =>
      pure (.comp (.pair .outl (.comp .outr s)) (.comp swapTm (.comp (pairTest R) (.comp swapTm .outr))))
    -- neither runs: each side read through one projection, `⟨π₁P, π₂Q⟩° = ⟨π₁P°, π₂Q°⟩`, i.e. `(P×Q)° = P°×Q°`
    | .error l, .error _ => match A, R, S with
      | .prod _ _, R, S => match convProj R, convProj S with
        | .ok x, .ok y => match Proj.meet (Proj.pre .outl x) (Proj.pre .outr y) with
          | .inl p => pure p
          | .inr _ => throw l
        | _, _ => throw l
      | _, _, _ => throw l
  | .share _ R => convTm R
  -- a row by its converse's row (`cons° = uncons`); any other row's converse is lazy (§0): `(c, a) ∈ r°` is `a r c`,
  -- run by `GenK.conv` on the side its context knows, as `<` is, so no row's converse is refused
  | .prim r => match r.conv.bind Prim.find? with
    | some r' => pure (.prim r')
    | none => pure (.conv (.prim r))
  -- a constant's plan on demand: its converse constant at the same arguments; with none, read whole on its
  -- source's universe
  | .callCv ks c c' os b u => pure (.callCv ks c' c os u b)
  | .call _ c .. => throw s!"`{c}`"
  -- a closed spine under a demand argument (a whole row, `Tm.whole`) has no converse spine: `convTm f` gives `f°`
  -- a spine whose row has no converse row is conversed lazily whole, `(r x)°`, as `GenK.conv` runs it
  | .arg f x => if f.dem then do
      match ← convTm f with | .conv _ => pure (.conv (.arg f x)) | f' => pure (.arg f' x)
    else throw "a whole row's closed spine"
  | .top _ => throw "⊤"
  | .outl => throw "π₁"
  | .outr => throw "π₂"
  | .lam _ => throw "Λ( )"
  | .mem => throw "∋"
  | .inl => pure (.conv .inl)
  | .inr => pure (.conv .inr)
  | .hylo .. => throw "hylo( )"
  | .foldr .. => throw "⦇e,S⦈ʳ"
  | .fold .. => throw "⦇e,S⦈"

/-- `t° = Zπᵢ°` (`Proj`): `π₁° = 𝟙π₁°`, `(RS)° = S°(Zπᵢ°)`, and a meet or pair of two on one projection
    (`Proj.meet`). The error is only that `t` is not of that form: the caller reports its own leaf. -/
def convProj {A₁ A₂ B : Obj} (t : Tm (.prod A₁ A₂) B) : Except String (Proj B A₁ A₂) :=
  match t with
  | .outl => pure (.inl .id)
  | .outr => pure (.inr .id)
  | .comp R S => do let s ← convTm S; pure (Proj.pre s (← convProj R))
  | .share _ R => convProj R
  | .meet R S => do match Proj.meet (← convProj R) (← convProj S) with
    | .inr z => pure z
    | .inl _ => throw "a meet across both projections"
  | .pair R S => do match Proj.meet (Proj.pre .outl (← convProj R)) (Proj.pre .outr (← convProj S)) with
    | .inr z => pure z
    | .inl _ => throw "a pair across both projections"
  | _ => throw "not read through one projection"

end

/-- `convTm t`, `t` built from `q`: a `t` on demand reading a parameter run on demand has none, since `convTm` takes
    a variable for a pair test's, its own converse, and such a parameter `R : A ⟶ B` is not (`Pre.onDemand`); a
    closed `t` is conversed whole. -/
def convPre {A B : Obj} (q : Pre) (t : Tm A B) : Except String (Tm B A) :=
  if t.dem && q.onDemand then throw "a parameter run on demand" else convTm t

/-- A pair test: `τ(R) : A×B ⟶ A×B`, the coreflexive on the pairs `(a,b)` in demand with `a R b`. -/
abbrev Cor := (A : Obj) × (B : Obj) × Tm (.prod A B) (.prod A B)

/-- `R ∩ S` with `S` run on demand and `R` tested: `⟨𝟙,S⟩τ(R)π₂`; `R − S` is this with `𝟙 − τ(S)`. -/
def onPairs {A B : Obj} (s : Tm A B) (c : Tm (.prod A B) (.prod A B)) : Tm A B :=
  .comp (.pair .id s) (.comp c .outr)

/-- `τ(R/S) = 𝟙 − dom(⟨π₁,π₂S⟩(𝟙 − τ(R)))`, `R : A ⟶ C`, `S : B ⟶ C`: no `c` with `b S c` and not `a R c`. -/
def divTest {A B C : Obj} (c : Tm (.prod A C) (.prod A C)) (s : Tm B C) :
    Tm (.prod A B) (.prod A B) :=
  .diff .id (.dom (.comp (.pair .outl (.comp .outr s)) (.diff .id c)))

/-- The column of the one word `0` of the ordered atom `t` (`wordsFoR`, a kernel's answer form): `t`'s literal zero,
    `ofBits t 0` (`zeroCol_row`). -/
def zeroCol (t : QAtomicType) (h : t.ordNum.isSome) : Arr t 1 :=
  Arr.mk _ ((Rel.Verify.wordsFoR_closed #[0] (n := 1) (by simp)).2.2
    (by cases t <;> first | rfl | exact absurd h (by decide)) fun _ i hi => by
      obtain rfl : i = 0 := by simp at hi; omega
      decide +revert) (Rel.Verify.hasNul_wordsFoR #[0])

/-- The fold base `0`: the literal zero of the atom `t` (`zeroCol`) where it is in the universe `u`, `ran(u {0})`,
    closed, since the fold reads its start whole. A word, not `⟨𝟙,𝟙⟩ minus ∩ 𝟙`: one base at every atom, a float's too. -/
def zeroTm {t : QAtomicType} (h : t.ordNum.isSome) (u : Tm (.atom t) (.atom t)) : Tm (.atom t) (.atom t) :=
  .ran (.comp u (.uni (A := .atom t) (zeroCol t h)))

/-- A row's definition (§4): `⦇[0, π₁ succ]⦈` (`lengthRow`'s) and `⦇[0, plus]⦈` (`sumRow`'s, at its atom `t`), the
    base `0` on the universe `u₀`, the step on `u`; `⟨π₁R,π₂⟩dom(π₁π₁ ∩ π₂)π₁π₂` (`flatRow`'s, of the family `R`);
    `⟨𝟙,R⟩π₁` (`domRow`'s, not `𝟙 ∩ R R°`, whose `R°` an on-demand `R` often cannot run), `dom(R°)` (`ranRow`'s),
    `Λ(𝟘)` (`nilRow`'s), `∋ ∩ (∈ \ (Q ∪ 𝟙)°)` (`estRow`'s) and `Λ(∋ − ∋ (Q − Q°))` (`frontRow`'s), of the order `Q`,
    whose fused rows read it as its pair test `τ(Q)` (`pairTest`).
    Indexed by the term, so the law takes it apart by `cases`; `dfns` builds it from the row's own relations and
    target universe. -/
inductive DfnCut : {A B : Obj} → Tm A B → Type
  | length {E : Obj} (u₀ u : Tm .long .long) :
    DfnCut (A := .arr E) (B := .long) (.fold (zeroTm (t := .i64) rfl u₀) (.comp .outl (Tm.cut1 succRow u)))
  | sum {t : QAtomicType} (h : t.ordNum.isSome) (hf : t ∉ floatAtoms) (u₀ u : Tm (.atom t) (.atom t)) :
    DfnCut (A := .arr (.atom t)) (B := .atom t) (.fold (zeroTm h u₀) (Tm.cut2 (arithRow "plus") u))
  -- at a float atom `sum` rounds once (`Lang.sumDen`), no fold of `plus` (rounding each step): its definition is
  -- the row cut to the universe, `F(u) sum u`
  | fsum {t : QAtomicType} (u : Tm (.atom t) (.atom t)) :
    DfnCut (A := .arr (.atom t)) (B := .atom t) (.comp (.comp (.arg (.prim mapRow : Tm (.arr (.atom t))
      (.arr (.atom t))) u) (.prim sumRow : Tm (.arr (.atom t)) (.atom t))) u)
  | flat {I A B : Obj} (R : Tm I (.prod A B)) :
    DfnCut (A := .prod I A) (B := B)
      (.comp (.pair (.comp .outl R) .outr) (.comp (.dom (.meet (.comp .outl .outl) .outr)) (.comp .outl .outr)))
  | foldI {I E V : Obj} (e : Tm I (.prod V V)) (S : Tm (.prod (.prod I V) E) (.prod I V)) :
    DfnCut (A := .prod I (.arr E)) (B := V)
      (.comp (.meet (.comp .outl (.conv .outl)) (.comp .outr (.fold (.ran (.pair .id (.comp e .outr)))
        (.meet S (.comp .outl (.comp .outl (.conv .outl))))))) .outr)
  | dom {A B : Obj} (R : Tm A B) : DfnCut (A := A) (B := A) (.comp (.pair .id R) .outl)
  | ran {A B : Obj} (R : Tm A B) : DfnCut (A := B) (B := B) (.dom (.conv R))
  | nil {A B : Obj} : DfnCut (A := A) (B := .arr B) (.lam .zero)
  -- `∈ \ (Q ∪ 𝟙)°` read under `∋ ∩`, where an array has a column, so the universes `𝟙` are never read
  | est {B : Obj} (Q : Tm B B) :
    DfnCut (A := .arr B) (B := B) (.meet .mem (.ldiv (.conv .mem) (.conv (.join Q .id)) .id .id))
  | front {B : Obj} (Q : Tm B B) : DfnCut (A := .arr B) (B := .arr B) (.lam (.diff .mem (.comp .mem (.diff Q (.conv Q)))))

/-- The universes of the base and of the step, where the law needs them; none where it holds on every object. -/
def DfnCut.uni {A B : Obj} {d : Tm A B} : DfnCut d → Option (Tm B B × Tm B B)
  | .length u₀ u | .sum _ _ u₀ u => some (u₀, u)
  | .fsum u => some (u, u)
  | .flat _ | .foldI _ _ | .dom _ | .ran _ | .nil | .est _ | .front _ => none

/-- The row the definition is the fused form of. -/
def DfnCut.fused {A B : Obj} {d : Tm A B} : DfnCut d → Tm A B
  | .length _ _ => .prim lengthRow
  | .sum _ _ _ _ | .fsum _ => .prim sumRow
  | .flat R => .arg (.prim flatRow) R
  | .foldI e S => .arg (.arg (.prim foldIRow) e) S
  | .dom R => .dom R
  | .ran R => .ran R
  | .nil => .nil
  | .est Q => .est (pairTest Q)
  | .front Q => .front (pairTest Q)

/-- The row cut to its universe: `sum`'s tests its elements in it first (`F(u)`), as `plus` does; a row whose law
    needs no universe, itself. -/
def DfnCut.cut {A B : Obj} {d : Tm A B} : DfnCut d → Tm A B
  | .length _ u => .comp (.prim lengthRow) u
  | @DfnCut.sum t _ _ _ u => .comp (.comp (.arg (.prim mapRow : Tm (.arr (.atom t)) (.arr (.atom t))) u)
    (.prim sumRow : Tm (.arr (.atom t)) (.atom t))) u
  | @DfnCut.fsum t u => .comp (.comp (.arg (.prim mapRow : Tm (.arr (.atom t)) (.arr (.atom t))) u)
    (.prim sumRow : Tm (.arr (.atom t)) (.atom t))) u
  | .flat R => .arg (.prim flatRow) R
  | .foldI e S => .arg (.arg (.prim foldIRow) e) S
  | .dom R => .dom R
  | .ran R => .ran R
  | .nil => .nil
  | .est Q => .est (pairTest Q)
  | .front Q => .front (pairTest Q)

/-- The rows that are the fused form of a definition (§4), keyed by `sym`: each builds the `DfnCut` of its
    definition from the row's built relations and the universe `u` of its target (base and step both on it), at
    the row's objects `A ⟶ B`; none at other objects. `build` runs `c.fused` or `c.cut`, never the definition, and
    `Tm.dfnCut_den` proves each equal to it: no read-back of a built term decides which runs. -/
def dfns : List (String × ((A B : Obj) → List Res → Tm B B → Option ((d : Tm A B) × DfnCut d))) :=
  [("length", fun A B _ u => match A, B, u with | .arr _, .long, u => some ⟨_, .length u u⟩ | _, _, _ => none),
   ("sum", fun A B _ u => match A, B, u with
     | .arr (.atom t), .atom t', u =>
       if h : t' = t then by
         obtain rfl := h
         exact if hf : t' ∈ floatAtoms then some ⟨_, .fsum u⟩
           else if ho : t'.ordNum.isSome then some ⟨_, .sum ho hf u u⟩ else none
       else none
     | _, _, _ => none),
   ("flat", fun A B xs _ => match A, xs with
     | .prod I A, [⟨I', AB, R⟩] => if h : I' = I ∧ AB = .prod A B then some ⟨_, .flat (h.1 ▸ h.2 ▸ R)⟩ else none
     | _, _ => none),
   ("foldI", fun A B xs _ => match A, xs with
     | .prod I (.arr E), [⟨I', VV, e⟩, ⟨IVE, IV, S⟩] =>
       if h : I' = I ∧ VV = .prod B B ∧ IVE = .prod (.prod I B) E ∧ IV = .prod I B then
         some ⟨_, .foldI (h.1 ▸ h.2.1 ▸ e) (h.2.2.1 ▸ h.2.2.2 ▸ S)⟩ else none
     | _, _ => none),
   ("dom", fun A B xs _ => match xs with
     | [⟨A', _, R⟩] => if h : A' = A ∧ B = A then by obtain ⟨rfl, rfl⟩ := h; exact some ⟨_, .dom R⟩ else none
     | _ => none),
   ("ran", fun A B xs _ => match xs with
     | [⟨_, B', R⟩] => if h : A = B' ∧ B = B' then by obtain ⟨rfl, rfl⟩ := h; exact some ⟨_, .ran R⟩ else none
     | _ => none),
   ("nil", fun A B _ _ => match B with
     | .arr E => some ⟨_, DfnCut.nil (A := A) (B := E)⟩
     | _ => none),
   ("est", fun A B xs _ => match A, xs with
     | .arr E, [⟨E', E'', Q⟩] => if h : E' = E ∧ E'' = E ∧ B = E then by
         obtain ⟨rfl, rfl, rfl⟩ := h; exact some ⟨_, .est Q⟩ else none
     | _, _ => none),
   ("front", fun A B xs _ => match A, xs with
     | .arr E, [⟨E', E'', Q⟩] => if h : E' = E ∧ E'' = E ∧ B = .arr E then by
         obtain ⟨rfl, rfl, rfl⟩ := h; exact some ⟨_, .front Q⟩ else none
     | _, _ => none)]

/-- The converses a program states as theorems `c° = c'` (no parameters, no hypotheses), `(c, c')` in order: the
    definitions' source of `convOf`, read off the declarations, never kept as a second list. -/
def convs (prog : Program) : List (String × String) :=
  prog.filterMap fun | .«theorem» _ _ [] (.conv _ (.name _ c)) (.name _ c') true _ [] _ => some (c, c') | _ => none

/-- The name of the converse of `c`: a row's `Prim.conv`, or a definition's `c'` from `cs = convs prelude`
    (§5.2 of `doc/tm-minimal-design.zh.typ`); `none` where the converse is no named one. Not `Expand.convOf`,
    which builds a converse body. -/
def convOf (cs : List (String × String)) (c : String) : Option String := (Prim.find? c).bind (·.conv) <|> cs.lookup c

section Build

variable (objs : Objs) (mc : Lean.MetavarContext) (dp : Pos)

def toObj (o : OTy) : Except Err Obj := objOf objs dp (zonk mc o)

/-- `t` at the objects `A ⟶ B`: the cast is the equality `build` decided. -/
def at? {A B : Obj} (r : Res) : Except Err (Tm A B) :=
  match r with
  | ⟨A', B', t⟩ => if h : A' = A ∧ B' = B then pure (h.1 ▸ h.2 ▸ t) else internal dp "objects disagree"

/-- `r` at `A ⟶ B` as a closed term: the old index `false`, now `t.dem = false`, which the type no longer states. -/
def closed? {A B : Obj} (r : Res) : Except Err (Tm A B) := do
  let t ← at? dp (A := A) (B := B) r
  if t.dem then internal dp "a term that needs keys where none are supplied" else pure t

/-- `𝟙` on the universe of `o`, or the error that `o` has none: a declared one's literal (`uniOf`), an unbounded
    number object's `𝟙` itself; else built from its parts, an object variable's being the universe its constant is
    given (`uniVar`). -/
def uniPart (o : OTy) (A : Obj) : Except Err (Option (Tm A A)) := do
  if let some ⟨A', U⟩ := uniOf objs o then
    -- the one reader that forces the universe: a product past `crossMax` fails the definition that reads it
    let ⟨_, U⟩ ← U.get.mapError fun e => (⟨dp, e⟩ : Err)
    return ← if h : A' = A then pure (some (.uni (h ▸ U))) else internal dp "universe objects disagree"
  match o, A with
  -- an object variable's universe is its constant's argument even where the call puts an unbounded object (`num`)
  | .base n, _ => match objs.lookup n with
    | some { uniVar := some k, .. } => pure (some (.var false k))
    | some { num := true, .. } => pure (some .id)
    | _ => pure none
  | .prod a b, .prod A B => do
    let (some u, some v) := (← uniPart a A, ← uniPart b B) | pure none
    -- `⊤(u)` reads `u` whole, so a part on demand (an unbounded `𝟙`) gives `u × v` on demand
    pure (some (if u.dem || v.dem then u.prod v else u.prodUni v))
  | .sum a b, .sum A B => do
    let (some u, some v) := (← uniPart a A, ← uniPart b B) | pure none
    -- `ran(u inl)` hands the values in demand to `inl`'s range, where it cannot run; a part on demand (an unbounded
    -- `𝟙`) gives `dom(inl° u inl ∪ inr° v inr)`, which hands them to `inl°`'s domain, split by tag
    if u.dem || v.dem then
      pure (some (.dom (B := .sum A B) (.join (.comp (B := A) (.conv .inl) (.comp (B := A) u .inl))
        (.comp (B := B) (.conv .inr) (.comp (B := B) v .inr)))))
    else pure (some (.join (.ran (.comp u .inl)) (.ran (.comp v .inr))))
  | _, _ => pure none

/-- `o` is an unbounded number object (`ObjInfo.num`): a declared one, or an object variable a call puts one at. -/
def unbounded (objs : Objs) : OTy → Bool
  | .base n => (objs.lookup n).any (·.num)
  | _ => false

/-- `o`'s universe is an initial segment `0…k` of ℕ (`ObjInfo.seg`). -/
def initSeg (objs : Objs) : OTy → Bool
  | .base n => (objs.lookup n).any (·.seg)
  | _ => false

/-- `uniPart`, or the error naming the whole object `o` that has no universe. -/
def uniTm (p : Pos) (o : OTy) (A : Obj) (what : String) : Except Err (Tm A A) := do
  match ← uniPart objs dp (zonk mc o) A with
  | some t => pure t
  | none => throw ⟨p, s!"{what}: {zonk mc o} has no universe; compose a set of its elements before it (§a)"⟩

/-- The universe of a number object, for `succ`, the value verbs (`plus`, …), `≤`, `<`: a declared object's,
    or the one a constant is given for an object variable. -/
def numU (p : Pos) (o : OTy) (op : String) (ok : QAtomicType → Bool) :
    Except Err ((t : QAtomicType) × Tm (.atom t) (.atom t)) := do
  let (n, t) ← numObj objs mc p o op ok
  return ⟨t, ← declared n t⟩
where
  -- an object stored at another atom than `i64` is a declared number object, its universe `𝟙` (S1)
  declared (n : String) : (t : QAtomicType) → Except Err (Tm (.atom t) (.atom t))
    | .i64 => match objs.lookup n with
      | some { uni := some ⟨_, U⟩, .. } => pure (.uni (A := .long) U)
      | some { num := true, .. } => pure .id
      | some { uniVar := some k, obj := .atom .i64, .. } => pure (.var false k)
      | i => refuse n i
    | _ => match objs.lookup n with
      | some { num := true, .. } => pure .id
      | i => refuse n i
  refuse {X : Type} (n : String) : Option ObjInfo → Except Err X
    | some { uniVar := some _, .. } => throw ⟨p, s!"{op} on {n}: a number object, which its constant is not generic over"⟩
    | _ => throw ⟨p, s!"{op} on {n}: no universe"⟩

/-- A pair test at the objects `A×B`. -/
def corAt (A B : Obj) : Cor → Except Err (Tm (.prod A B) (.prod A B))
  | ⟨A', B', c⟩ => if h : A' = A ∧ B' = B then pure (h.1 ▸ h.2 ▸ c) else internal dp "pair-test objects disagree"

/-- A built term read whole: closed as it is, or on demand run on the universe of its source `a`. -/
def closeRes (p : Pos) (a : OTy) (why : String) : Res → Except Err Res
  | ⟨A, B, t⟩ => if t.dem then return ⟨A, B, .comp (← uniTm objs mc dp p a A why) t⟩ else pure ⟨A, B, t⟩

/-- The pair test of an order parameter at its object `B`,or the error naming the leaf that is not testable. -/
def paramOf (why : String) : Except Err Cor → Except Err ((B : Obj) × Tm (.prod B B) (.prod B B))
  | .ok ⟨A, B, c⟩ => if h : B = A then pure ⟨A, h ▸ c⟩ else internal dp s!"{why}'s order is not on one object"
  | .error e => throw ⟨e.pos,
    s!"{why} runs its order on the pairs it compares, and the order is not testable on pairs (§a): {e.msg}"⟩

/-- The call node of the constant `c` at `A ⟶ B`, its object variables at `us`: its body `t` (and its converse's)
    at their objects (`Tm.instObj` at its placeholders `ph`), `os` those of the variables it is generic over. A
    variable it is not generic over keeps its placeholder, so `σ` is the identity there. -/
def callTm (pos : Pos) (c : Lean.Name) (us : List (OTy × Bool × Bool)) (ks : List Nat) (ph : List Rel.QAtomicType)
    (t : Res) (cv : Option (Lean.Name × Res)) (A B : Obj) : Except Err (Tm A B) := do
  -- a variable the constant is not generic over was built at `.long`: any other object is refused here, before the
  -- body is put at the call's objects, where it would not fit
  let σ ← us.zipIdx.mapM fun ((u, gen, _), k) => do
    if gen then return ← toObj objs mc dp u
    unless (← toObj objs mc dp u) == .long do
      throw ⟨pos, s!"`{c}`: an object variable is {zonk mc u} here; its constant is not generic over it, a number object"⟩
    pure ((varObj ph k).getD .long)
  let os := (σ.zip us).filterMap fun (o, _, gen, _) => if gen then some o else none
  let inst {X Y : Obj} : Res → Except Err (Tm X Y)
    | ⟨X₀, Y₀, b⟩ => do
      let b ← (b.instObj ph σ).mapError fun e => (⟨pos, s!"`{c}` at the objects of this call: {e}"⟩ : Err)
      if h : X₀.inst ph σ = X ∧ Y₀.inst ph σ = Y then pure (h.1 ▸ h.2 ▸ b)
      else internal dp s!"`{c}`'s body is not at the objects of its call"
  match cv with
  | some (c', u) => return .callCv ks c c' os (← inst t) (← inst u)
  | none => return .call ks c os (← inst t)

/-- The literal `ps` at `a ⟶ b`, a table; in the body of the generic definition `gd` an error is that use's. -/
def litRes (p : Pos) (a b : OTy) (ps : List (Tup × Tup)) (gd : Option String) : Except Err Res :=
  (needSize ps.length "literal rows" (fun _ => internal dp "literal rows") fun n => do
    let ⟨A, k⟩ ← litCol objs mc dp p n (zonk mc a) (ps.map (·.1))
    let ⟨B, v⟩ ← litCol objs mc dp p n (zonk mc b) (ps.map (·.2))
    pure ⟨A, B, .val ⟨n, k, v⟩⟩).mapError fun e => match gd with
      | some d => ⟨e.pos, s!"`{d}` at the objects of this call: {e.msg}"⟩
      | none => e

/-- Each place `t` reads the variable `k` free, as that `var` node: a binder of `k` hides its scope, and a call's
    body is not entered (it reads only its own `ks`, `Code.args`), its arguments are. -/
partial def Tm.reads (k : Nat) : {A B : Obj} → Tm A B → List Res
  | A, B, t@(.var _ j) => if j == k then [⟨A, B, t⟩] else []
  | _, _, .mu j _ _ b | _, _, .hylo j _ b => if j == k then [] else b.reads k
  | _, _, .nu j S b => S.reads k ++ if j == k then [] else b.reads k
  | _, _, t => t.parts.flatMap fun ⟨_, _, c⟩ => c.reads k

/-- The call node of `c` given the body `t` and its arguments `rs`, bound to `ks`, one for one. A call's body sees
    only its `ks` (`Code.args`, `Tm.fv`), so each variable `t` reads beyond them (a universe of the enclosing
    constant, read by `callOf`'s body) is bound to itself, as an argument of its own; one read at two objects is
    refused. -/
def callNode (c : Lean.Name) (ks : List Nat) (rs : List Res) {A B : Obj} (t : Tm A B) :
    Except Err (Tm A B) := do
  let free := t.fv.eraseDups.filter (!ks.contains ·)
  let more ← free.mapM fun k => match t.reads k with
    | r@⟨X, Y, _⟩ :: rest => if rest.all fun ⟨X', Y', _⟩ => X' == X && Y' == Y then pure r
      else internal dp s!"`{c}`'s body reads the variable {k} at two objects"
    | [] => internal dp s!"`{c}`'s body has {k} free but reads it nowhere"
  pure <| (rs ++ more).foldl (fun f ⟨_, _, x⟩ => .arg f x) (Tm.call (ks ++ free) c [] t)

mutual

/-- `Pre` to `Tm` at the solved objects. Every check here holds by `elabE`'s unification except the
    universes, whose absence is the error of §a. -/
def build : Pre → Except Err Res
  | .tm r => pure r
  | .zero a b => return ⟨← toObj objs mc dp a, ← toObj objs mc dp b, .zero⟩
  | .id a => return ⟨_, _, .id (A := ← toObj objs mc dp a)⟩
  | .top p a b tgt => do
    let A ← toObj objs mc dp a; let B ← toObj objs mc dp b
    let V ← match tgt with
      | none => uniTm objs mc dp p b B "⊤'s target"
      | some q => do closed? dp (← build q)
    pure ⟨A, B, .top V⟩
  | .outl a b => return ⟨_, _, .outl (A := ← toObj objs mc dp a) (B := ← toObj objs mc dp b)⟩
  | .outr a b => return ⟨_, _, .outr (A := ← toObj objs mc dp a) (B := ← toObj objs mc dp b)⟩
  | .comp p q => do
    let ⟨A, B, t⟩ ← build p; let ⟨B', C, u⟩ ← build q
    if h : B' = B then pure ⟨A, C, .comp t (h ▸ u)⟩ else internal dp "composition objects disagree"
  -- `R°`: closed, conversed whole; on demand, pushed to the leaves (`convTm`); a leaf whose converse does not
  -- run on demand reads `R` whole on its source's universe
  | .conv (.close _ (.conv (.close _ q _ _)) _ _) => build q
  -- a call's converse is its expansion's, pushed to the leaves as below
  | .conv (.close pos (.callE _ _ _ _ alt _ _ _ _) a w) => build (.conv (.close pos alt a w))
  | .conv (.close pos q a _) => do
    let ⟨A, B, t⟩ ← build q
    match convPre q t with
    -- the lazy converse of the whole `R` (a row with no converse row): nothing inside `R` bounds its source side,
    -- so it is read on its source's universe, the context still bounding its target
    | .ok (.conv t') =>
      if t.dem && !(Tm.conv t').dem then
        (fun U => ⟨B, A, .conv (.comp U t')⟩) <$>
          uniTm objs mc dp pos a A "the lazy converse of a row, R° reads R on its source's universe"
      else pure ⟨B, A, .conv t'⟩
    | .ok u => pure ⟨B, A, u⟩
    | .error leaf => do
      let U ← uniTm objs mc dp pos a A s!"the converse of {leaf} does not run on demand, so R° reads R whole"
      pure ⟨B, A, .conv (.comp U t)⟩
  -- closed, or a converse that runs on demand itself (`Tm.dem`: `inl°`, `inr°`)
  | .conv p => do
    let r ← build p; let ⟨A, B, _⟩ := r; let t ← at? dp (A := A) (B := B) r
    if (Tm.conv t).dem then pure ⟨B, A, .conv t⟩ else pure ⟨B, A, .conv (← closed? dp (A := A) (B := B) r)⟩
  -- a side that cannot run is tested on the pairs the other side gives (`test`)
  | .meet p q => match build p, build q with
    | .ok ⟨A, B, t⟩, .ok s => do let u ← at? dp (A := A) (B := B) s; pure ⟨A, B, .meet t u⟩
    | .error err, .ok ⟨A, B, s⟩ => match test p with
      | .ok c => do pure ⟨A, B, onPairs s (← corAt dp A B c)⟩
      | .error _ => throw err
    | .ok ⟨A, B, s⟩, .error err => match test q with
      | .ok c => do pure ⟨A, B, onPairs s (← corAt dp A B c)⟩
      | .error _ => throw err
    | .error err, .error _ => throw err
  | .join p q => do let ⟨A, B, t⟩ ← build p; let u ← at? dp (A := A) (B := B) (← build q); pure ⟨A, B, .join t u⟩
  | .diff p q => match build p, build q with
    | .ok ⟨A, B, t⟩, .ok s => do let u ← at? dp (A := A) (B := B) s; pure ⟨A, B, .diff t u⟩
    | .ok ⟨A, B, s⟩, .error err => match test q with
      | .ok c => do pure ⟨A, B, onPairs s (.diff .id (← corAt dp A B c))⟩
      | .error _ => throw err
    | .error err, _ => throw err
  | .dom p => do let ⟨A, _, t⟩ ← build p; pure ⟨A, A, .dom t⟩
  | .ran p => do let r ← build p; let ⟨A, B, _⟩ := r; pure ⟨B, B, .ran (← closed? dp (A := A) (B := B) r)⟩
  | .ldiv pos p q b c => do
    let r ← build p; let s ← build q; let ⟨A, B, _⟩ := r; let ⟨_, C, _⟩ := s
    let R ← closed? dp (A := A) (B := B) r; let S ← closed? dp (A := A) (B := C) s
    pure ⟨B, C, .ldiv R S (← uniTm objs mc dp pos b B "R\\S") (← uniTm objs mc dp pos c C "R\\S")⟩
  | .rdiv pos p q a b => do
    let r ← build p; let s ← build q; let ⟨A, C, _⟩ := r; let ⟨B, _, _⟩ := s
    let R ← closed? dp (A := A) (B := C) r; let S ← closed? dp (A := B) (B := C) s
    pure ⟨A, B, .rdiv R S (← uniTm objs mc dp pos a A "R/S") (← uniTm objs mc dp pos b B "R/S")⟩
  | .pair p q => do
    let ⟨A, _, t⟩ ← build p; let s ← build q; let ⟨_, C, _⟩ := s
    let u ← at? dp (A := A) (B := C) s; pure ⟨A, _, .pair t u⟩
  -- `R×S ≜ ⟨π₁R,π₂S⟩` (`Tm.prod`); both operands closed on their sources, it runs closed on `dom R × dom S`, since
  -- the product object may have no universe of its own (`[A]×[A]`); otherwise on demand
  | .prod (.close pp p a w) (.close pq q b w') =>
    let onDemand : Except Err Res := do
      let ⟨A, B, t⟩ ← build p; let ⟨C, D, u⟩ ← build q; pure ⟨.prod A C, .prod B D, t.prod u⟩
    match build (.close pp p a w), build (.close pq q b w') with
    | .ok ⟨A, B, t⟩, .ok ⟨C, D, u⟩ =>
      if t.dem || u.dem then onDemand else pure ⟨.prod A C, .prod B D, .comp ((Tm.dom t).prodUni (.dom u)) (t.prod u)⟩
    | _, _ => onDemand
  | .prod p q => do
    let ⟨A, B, t⟩ ← build p; let ⟨C, D, u⟩ ← build q; pure ⟨.prod A C, .prod B D, t.prod u⟩
  | .lam p => do let ⟨_, _, t⟩ ← build p; pure ⟨_, _, .lam t⟩
  | .nil a b => return ⟨_, _, .nil (A := ← toObj objs mc dp a) (B := ← toObj objs mc dp b)⟩
  | .mem b => return ⟨_, _, .mem (B := ← toObj objs mc dp b)⟩
  | .inl a b => return ⟨_, _, .inl (A := ← toObj objs mc dp a) (B := ← toObj objs mc dp b)⟩
  | .inr a b => return ⟨_, _, .inr (A := ← toObj objs mc dp a) (B := ← toObj objs mc dp b)⟩
  -- the row's objects are checked where `Expand.primE` fits its constant at them (`primsFit`, `node`). A row of
  -- `dfns` means its definition `d` (§4: every step stays in the target object). `Tm.dfnCut_den` proves `d` equal to
  -- the row followed by `𝟙` of the target (`c.cut`) where the universe is every number or `0…k`, and to the row
  -- itself at `𝟙` or where no universe enters (`DfnCut.uni`); at any other universe (one with negatives or not from
  -- `0`, or an object variable no call fixed to one of those) the two differ — `[−3,3,3] sum` on `−3…3` is `𝟘` by
  -- `d`, `3` by the cut — so `d` runs. With no universe, the row runs (the base `0` would need keys none supply).
  | .prim r xs s t => do
    numCheck objs mc dp (.prim r xs s t)
    -- an object whose canon order is not its value order (a float's bits, a symbol's bytes) is refused by name
    r.ord.forM fun v => do
      if let some o := (r.sig.2.2.varAt v (zonk mc t)).orElse fun _ => r.sig.2.1.varAt v (zonk mc s) then
        let ats := ", ".intercalate ((atomNames.filter (·.2.intOrd)).map (atomName ·.2))
        match zonk mc o with
        | .base n => match objs.lookup n with
          | some { obj := .atom a, ovar := false, .. } => unless a.intOrd do
              throw ⟨dp, s!"{r.sym}' position object {n} is an object of {atomName a}; {r.sym} orders positions of {ats}"⟩
          | _ => pure ()
        | o => throw ⟨dp, s!"{r.sym}' position object {o} is no atom; {r.sym} orders positions of {ats}"⟩
    let A ← toObj objs mc dp s; let B ← toObj objs mc dp t
    let row (_ : Unit) : Except Err Res :=
      (r.sig.1.zip xs.attach).foldlM (init := (⟨A, B, .prim r⟩ : Res)) fun ⟨A, B, f⟩ ((_, form), ⟨x, h⟩) => do
        have := List.sizeOf_lt_of_mem h
        if form == some true then let ⟨_, c⟩ ← param x; pure ⟨A, B, .arg f c⟩
        else let ⟨_, _, u⟩ ← build x; pure ⟨A, B, .arg f u⟩
    let some dfn := dfns.lookup r.sym | row ()
    -- relations that do not build alone give no definition: the row runs, a pair-test parameter tested on pairs
    -- (`param`, as `length ≤ length°` on `[N]`), any other rebuilt by `row`, which reports its own error
    let .ok args := xs.attach.mapM fun ⟨x, h⟩ => have := List.sizeOf_lt_of_mem h; build x | row ()
    -- a definition that needs no universe (`DfnCut.uni`, asked with `𝟙` standing for it) is its fused row at every
    -- object: the target's universe is not read, since `uniPart` forces a declared one and may fail on it
    if let some ⟨_, c⟩ := dfn A B args .id then if c.uni.isNone then return ⟨A, B, c.fused⟩
    let o := zonk mc t
    let some u ← uniPart objs dp o B | do
      -- an object variable with no universe may be called at a bounded object, where the uncut row is not `d`
      if let .base n := o then if (objs.lookup n).any fun i => i.ovar && !i.num then
        if (dfn A B args .id).all (·.2.uni.isSome) then
          throw ⟨dp, s!"{r.sym} at the object variable {n} needs its universe: its definition is cut to it (§4)"⟩
      row ()
    -- none at an atom with no literal `0` (`zeroCol`): a placeholder, so the constant stays at `.long` (`Expand.once`)
    let some ⟨d, c⟩ := dfn A B args u | throw ⟨dp, s!"{r.sym}'s definition (dfns) has no form at {repr A} ⟶ {repr B}"⟩
    if unbounded objs o || c.uni.isNone then pure ⟨A, B, c.fused⟩
    else if initSeg objs o then pure ⟨A, B, c.cut⟩
    else pure ⟨A, B, d⟩
  | .own p => do
    let ⟨A, B, t⟩ ← build p
    if h : B = A then pure ⟨A, A, .own (h ▸ t)⟩ else internal dp "perm's objects"
  | .succ p n => do
    let (m, _) ← numObj objs mc p n "succ" (· == .i64)
    return ⟨_, _, Tm.cut1 succRow (← numU.declared objs p "succ" m .i64)⟩
  -- `max`/`min` need no arithmetic: at an ordered atom with no value step they are `τ(≤)π₂ ∪ τ(>)π₁` (`min` the
  -- projections swapped), the order picking an operand; at a value atom the fused verb runs
  | .arith p k n => do
    let ⟨t, U⟩ ← numU objs mc p n (Op.arith k).sym (arithOk k)
    if valueAtom t then
      let some (s, _) := arithOps.find? (·.2 == k) | internal dp s!"no row of arithOps has the verb {k}"
      return ⟨_, _, Tm.cut2 (arithRow s) U⟩
    let le : Tm (.prod (.atom t) (.atom t)) _ := pairTest (.leq t U)
    let gt : Tm (.prod (.atom t) (.atom t)) _ := .comp swapTm (.comp (pairTest (.lt t U)) swapTm)
    let (hi, lo) : Tm (.prod (.atom t) (.atom t)) (.atom t) × Tm (.prod (.atom t) (.atom t)) (.atom t) :=
      if k == Rel.Kernel.Ew.greater then (.outr, .outl) else (.outl, .outr)
    return ⟨_, _, .join (.comp le hi) (.comp gt lo)⟩
  | .leq p n => do let ⟨t, U⟩ ← numU objs mc p n "≤" (·.ordNum.isSome); return ⟨_, _, .leq t U⟩
  | .lt p n => do let ⟨t, U⟩ ← numU objs mc p n "<" (·.ordNum.isSome); return ⟨_, _, .lt t U⟩
  | .fold true e s => do
    let r ← build e; let ⟨V, _, _⟩ := r
    match ← build s with
    | ⟨.prod E V', V'', S⟩ =>
      if h : V' = V ∧ V'' = V then
        pure ⟨.arr E, V, .foldr (← closed? dp (A := V) (B := V) r) (h.1 ▸ (h.2 ▸ S : Tm (.prod E V') V) : Tm (.prod E V) V)⟩
      else internal dp "the fold's objects"
    | _ => internal dp "the fold's step"
  | .fold false e s => do
    let r ← build e; let ⟨V, _, _⟩ := r
    match ← build s with
    | ⟨.prod V' E, V'', S⟩ =>
      if h : V' = V ∧ V'' = V then
        pure ⟨.arr E, V, .fold (← closed? dp (A := V) (B := V) r) (h.1 ▸ (h.2 ▸ S : Tm (.prod V' E) V) : Tm (.prod V E) V)⟩
      else internal dp "the fold's objects"
    | _ => internal dp "the fold's step"
  | .lit p a b ps gd => litRes objs mc dp p a b ps gd
  | .close p q a why => do closeRes objs mc dp p a why (← build q)
  -- the children and the body run on the nodes in demand, no universe read
  | .hylo p k q a b => do
    let A ← toObj objs mc dp a; let B ← toObj objs mc dp b
    let t ← at? dp (A := A) (B := B) (← build q)
    pure ⟨A, B, .hylo k s!"the coalgebra c at {p}" t⟩
  | .var _ k a b none => return ⟨← toObj objs mc dp a, ← toObj objs mc dp b, .var false k⟩
  | .var _ k a b (some false) => return ⟨← toObj objs mc dp a, ← toObj objs mc dp b, .var true k⟩
  -- a parameter given a pair test runs nowhere; `test` reads it
  | .var pos _ _ _ (some true) =>
    throw ⟨pos, "this parameter is tested on the pairs it compares, not run: its argument is a pair test (§a)"⟩
  -- a constant that is a pair test runs nowhere; `test` calls it
  | .call pos c _ _ _ _ _ _ _ _ _ _ true =>
    throw ⟨pos, s!"`{c}` is tested on the pairs it compares, not run: its constant is its pair test (§a)"⟩
  | .call pos c us xs ts q a b ks ph t cv false => do
    -- a variable whose object was open when the call was made (`callDef`) and is unbounded: the constant chose its
    -- rows' forms (`.prim`) without it, so the expansion, built at the call's objects, runs instead
    if us.any fun (u, _, reads) => reads && !u.mvs.isEmpty && unbounded objs (zonk mc u) then return ← build q
    -- a variable the constant is not generic over (built at `.long`) given another object: the constant does not
    -- serve this call, so the expansion runs at the call's objects, every number check at them (monomorphised)
    if us.any fun (u, gen, _) => !gen && (toObj objs mc dp u).toOption != some .long then return ← build q
    -- the constant took a numeral at an object variable as the number; the expansion has it at the call's object
    q.lits.forM fun (p, a, b, ps, d) => if d.isSome then discard (litRes objs mc dp p a b ps d) else pure ()
    let A ← toObj objs mc dp a; let B ← toObj objs mc dp b
    pure ⟨A, B, ← callArgs pos c us xs ts (← callTm objs mc dp pos c us ks ph t cv A B)⟩
  -- each argument built once, the body with every parameter read on demand where an argument needs keys, else
  -- closed; where that does not build (a body reading a parameter whole, an argument only tested), the expansion
  | .callE _ c ks xs alt cl od a b =>
    let viaCall : Except Err Res := do
      let A ← toObj objs mc dp a; let B ← toObj objs mc dp b
      -- a variable bound to itself in its pair-test form is passed as its pair test, as `callArgs` passes one
      let rs ← xs.attach.mapM fun ⟨x, h⟩ => have := List.sizeOf_lt_of_mem h
        match x with
        | .var _ _ _ _ (some true) => do let ⟨A, B, t⟩ ← test x; pure (⟨.prod A B, .prod A B, t⟩ : Res)
        | _ => build x
      -- only an argument given a variable of its own (`callOf`) takes the form chosen here
      let dem := (xs.zip rs).any fun (x, r) => !(x matches .var ..) && r.2.2.dem
      let ⟨A', B', t⟩ ← if dem then build od else build cl
      -- `od` reads every parameter on demand; one whose argument is closed is read whole, as it is given, so the
      -- call needs keys only where its expansion does
      let t := if !dem then t else t.subst (((ks.zip xs).zip rs).filterMap fun ((k, x), ⟨A, B, r⟩) =>
        if !(x matches .var ..) && !r.dem then some (k, ⟨A, B, .var false k⟩) else none)
      let u ← callNode dp (.mkSimple c) ks rs t
      -- `Tm.dem` counts an argument run on demand even where the body closes it: that call is the expansion's
      if u.dem && !t.dem then internal dp s!"`{c}` closes an argument that needs keys"
      if h : A' = A ∧ B' = B then pure ⟨A, B, h.1 ▸ h.2 ▸ u⟩
      else internal dp s!"`{c}`'s body is not at the objects of its call"
    match viaCall with
    | .ok r => pure r
    | .error _ => build alt
  -- the body read whole each round, on its source's universe when it needs keys
  | .fix p least k x S q a b => do
    let A ← toObj objs mc dp a; let B ← toObj objs mc dp b
    let why := s!"{if least then "μ" else "ν"}'s body is read whole each round"
    let body ← closed? dp (A := A) (B := B) (← closeRes objs mc dp p a why (← build q))
    unless body.pol true k do
      -- `Tm.pol` answers a Bool and `Tm.var` holds no position, so the source term gives the first occurrence
      let some o := q.occ k | internal dp s!"{x} is not positive in {if least then "μ" else "ν"}{x} at {p} but does not occur"
      throw ⟨p, s!"{if least then "μ" else "ν"}{x} at {p.line}:{p.col}: {x} first occurs at {o.line}:{o.col}, and the " ++
        s!"body does not use {x} positively (it reads {x} on both sides, or holds it whole)"⟩
    if least then
      -- a chain from `𝟘` on universes of `n` and `m` elements stops within `n·m+1` rounds, so their `cap` never
      -- fails a monotonic body; an array object has no such bound, and `muCap` only guards termination
      let cap := match uniSize objs (zonk mc a), uniSize objs (zonk mc b) with
        | some n, some m => max muCap (n * m + 2)
        | _, _ => muCap
      pure ⟨A, B, .mu k s!"the μ at {p}" cap body⟩
    else match S with
      | some s => do
        let s ← closed? dp (A := A) (B := B) (← closeRes objs mc dp p a why (← build s))
        pure ⟨A, B, .nu k s body⟩
      | none => internal dp "ν without its bound"
termination_by x => (sizeOf x, 0)

/-- The call `f` given, per object variable `u` of its constant, the universe of `u` where the constant reads it,
    then the arguments `xs`, each built (closed or run on demand) or, where `ts` says so, its pair test (`Form`). A
    variable the constant is not generic over is a number object (`.long`). -/
def callArgs (pos : Pos) (c : Lean.Name) (us : List (OTy × Bool × Bool)) (xs : List Pre) (ts : List Bool) {A B : Obj}
    (f : Tm A B) : Except Err (Tm A B) := do
  -- a variable it is not generic over is `.long` here (`callTm` refused any other)
  let f ← us.foldlM (init := f) fun f (u, _, reads) => do
    let U ← toObj objs mc dp u
    if reads then return .arg f (← uniTm objs mc dp pos u U s!"`{c}`") else pure f
  xs.attach.zipIdx.foldlM (init := f) fun f (⟨x, h⟩, i) => do
    have : sizeOf x < sizeOf xs := List.sizeOf_lt_of_mem h
    if ts.getD i false then let ⟨_, _, t⟩ ← test x; return .arg f t
    let ⟨_, _, t⟩ ← build x; pure (.arg f t)
termination_by (sizeOf xs, 3)

/-- `τ(R)`, the pair test of `R : A ⟶ B` (`Cor`), for `R` that cannot enumerate its targets: a term that
    builds is tested as `dom(π₂ ∩ π₁R)`; otherwise by its form — `R/S`, `R\S`, `frac`, `∼`, `−`, `∩`, `∪`, `°`,
    and a composite with a side that runs. The error is `p`'s own build error. -/
def test (p : Pre) : Except Err Cor :=
  match build p with
  | .ok ⟨A, B, t⟩ => pure ⟨A, B, pairTest t⟩
  | .error err => match p with
    | .close _ q _ _ => test q
    | .callE _ _ _ _ alt _ _ _ _ => test alt
    -- a constant that is a pair test, `τ(c(…)) : A×B ⟶ A×B` (`once`)
    -- a parameter given a pair test (`Form`)
    | .var _ k a b (some true) => do pure ⟨← toObj objs mc dp a, ← toObj objs mc dp b, .var true k⟩
    | .call pos c us xs ts _ a b ks ph t _ true => do
      let A ← toObj objs mc dp a; let B ← toObj objs mc dp b
      pure ⟨A, B, ← callArgs pos c us xs ts (← callTm objs mc dp pos c us ks ph t none (.prod A B) (.prod A B))⟩
    | .conv q => do let ⟨A, B, c⟩ ← test q; pure ⟨B, A, .comp swapTm (.comp c swapTm)⟩
    | .top _ a b none => do pure ⟨← toObj objs mc dp a, ← toObj objs mc dp b, .id⟩
    | .meet q r => do let c ← test q; let ⟨A, B, c₁⟩ := c; pure ⟨A, B, .meet c₁ (← corAt dp A B (← test r))⟩
    | .join q r => do let c ← test q; let ⟨A, B, c₁⟩ := c; pure ⟨A, B, .join c₁ (← corAt dp A B (← test r))⟩
    | .diff q r => do let c ← test q; let ⟨A, B, c₁⟩ := c; pure ⟨A, B, .diff c₁ (← corAt dp A B (← test r))⟩
    -- `τ(PT) = dom(⟨π₁P,π₂⟩τ(T))` with `P` run; `τ(TQ) = dom(⟨π₁,π₂Q°⟩τ(T))` with `Q°` run on demand
    | .comp q r => match build q with
      | .ok ⟨A, M, t⟩ => do
        let c ← test r; let ⟨_, B, _⟩ := c
        pure ⟨A, B, .dom (.comp (.pair (.comp .outl t) .outr) (← corAt dp M B c))⟩
      | .error _ => match build r with
        | .ok ⟨M, B, u⟩ => match convPre r u with
          | .ok v => do
            let c ← test q; let ⟨A, _, _⟩ := c
            pure ⟨A, B, .dom (.comp (.pair .outl (.comp .outr v)) (← corAt dp A M c))⟩
          | .error _ => throw err
        | .error _ => throw err
    -- `R/S`, `R : A ⟶ C` tested, `S : B ⟶ C` run on the `b`s
    | .rdiv _ (.close _ q _ _) (.close _ r _ _) _ _ => do
      let c ← test q; let ⟨A, C, _⟩ := c
      let ⟨B, _, s⟩ ← build r
      let s ← at? dp (A := B) (B := C) ⟨B, _, s⟩
      pure ⟨A, B, divTest (← corAt dp A C c) s⟩
    -- `R\S`, `R : A ⟶ B` with `R°` run on the `b`s, `S : A ⟶ C` tested: `τ = 𝟙 − dom(⟨π₁R°,π₂⟩(𝟙 − τ(S)))`
    | .ldiv _ (.close _ q _ _) (.close _ r _ _) _ _ => do
      let ⟨A, B, t⟩ ← build q
      match convPre q t with
      | .ok v => do
        let c ← test r; let ⟨_, C, _⟩ := c
        pure ⟨B, C, .diff .id (.dom (.comp (.pair (.comp .outl v) .outr) (.diff .id (← corAt dp A C c))))⟩
      | .error _ => throw err
    | _ => throw err
termination_by (sizeOf p, 1)

/-- The order (or coreflexive) parameter `Q : B ⟶ B` of `est front filter takewhile thinL merge`
    as its pair test `τ(Q)` (§a), which the operator runs on the pairs it compares: a closed `Q` and a `Q` that
    runs on demand alike, and any `Q` testable on pairs. `why` names the operator; the error names the leaf. -/
def param : Pre → Except Err ((B : Obj) × Tm (.prod B B) (.prod B B))
  | .close _ q _ why => paramOf dp why (test q)
  | q => paramOf dp "an operator" (test q)
termination_by p => (sizeOf p, 2)

end

end Build

end Rel.Lang
