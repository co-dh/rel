import Rel.Run.Lang.Tm
import Rel.Kernel.Db.Own
import Rel.Kernel.Scan
import Rel.Kernel.Gather
import Rel.Kernel.Seen

/-! # A program as kernel calls (`doc/rel-native-design.md` §6), stage 1a: `lit`, `call`, `fail`

A plan is first-order data: instructions over numbered registers, each register defined once, in order. A `call`
names an `@[extern]` kernel by its C symbol; `Plan.run` is what a plan means, calling the same kernels through the
table `kernel%` builds from their declarations, and `relc` (`Rel/Lang/EmitC`) prints the same plan as C. -/

namespace Rel.Lang.Plan

open Lean Elab Term Meta Tab Rel.Kernel

/-- A register's type: the argument and result types of the kernels' `@[extern]` declarations. `nat` is a `Nat`
    (C `size_t`, below `2^63`, where `lean_box` holds it); `obj` a constructor object, `lean_ctor_object`. -/
inductive Ty
  | bytes | size | bit | u8 | str | parts | u64 | i64 | nat | obj
  deriving BEq, Repr, Inhabited, ToExpr

/-- What a register holds: a buffer, a size, a bit, a byte, a string, an array of buffers (a column's parts), a
    64-bit word, unsigned or signed (a kernel's fill or null), a `Nat`, or a constructor object as the runtime lays it
    out: its tag, its object fields in declaration order (a scalar there is boxed, as a field of polymorphic type is),
    and its unboxed scalar fields in declaration order. A kernel's `Enc`, `List`, product, `Option` and `AscKey`
    arguments and answers are `ctor`s (`Reg`), because that is what the C passes. -/
inductive Val
  | bytes (b : ByteArray)
  | size (n : USize)
  | bit (b : Bool)
  | u8 (b : UInt8)
  | str (s : String)
  | parts (bs : Array ByteArray)
  | u64 (x : UInt64)
  | i64 (x : Int64)
  | nat (n : Nat)
  | ctor (tag : Nat) (objs scal : Array Val)
  deriving Inhabited

def Val.ty : Val → Ty
  | .bytes _ => .bytes | .size _ => .size | .bit _ => .bit | .u8 _ => .u8 | .str _ => .str | .parts _ => .parts
  | .u64 _ => .u64 | .i64 _ => .i64 | .nat _ => .nat | .ctor .. => .obj

/-- `v` as `fail` prints it: a scalar or a string as itself, a buffer by its size, an object by its tag. -/
def Val.show : Val → String
  | .bytes b => s!"<{b.size} bytes>"
  | .size n => toString n
  | .bit b => toString b
  | .u8 b => toString b
  | .str s => s
  | .parts bs => s!"<{bs.size} parts>"
  | .u64 x => toString x
  | .i64 x => toString x
  | .nat n => toString n
  | .ctor t .. => s!"<constructor {t}>"

/-- The Lean types a register holds, each with its `Ty`; `kernel%` reads an `@[extern]` signature through it. -/
class Reg (α : Type) where
  ty : Ty
  get? : Val → Option α
  put : α → Val

instance : Reg ByteArray := ⟨.bytes, fun | .bytes b => some b | _ => none, .bytes⟩
instance : Reg USize := ⟨.size, fun | .size n => some n | _ => none, .size⟩
instance : Reg Bool := ⟨.bit, fun | .bit b => some b | _ => none, .bit⟩
instance : Reg UInt8 := ⟨.u8, fun | .u8 b => some b | _ => none, .u8⟩
instance : Reg String := ⟨.str, fun | .str s => some s | _ => none, .str⟩
instance : Reg (Array ByteArray) := ⟨.parts, fun | .parts bs => some bs | _ => none, .parts⟩
instance : Reg UInt64 := ⟨.u64, fun | .u64 x => some x | _ => none, .u64⟩
instance : Reg Int64 := ⟨.i64, fun | .i64 x => some x | _ => none, .i64⟩
instance : Reg Nat := ⟨.nat, fun | .nat n => some n | _ => none, .nat⟩

/-- An enum, which the C ABI passes as its constructor index in a byte. `ofNat` clamps, so the round trip through
    `idx` is what refuses a byte that is no index. -/
def Reg.enum {α : Type} (ofNat : Nat → α) (idx : α → Nat) : Reg α := ⟨.u8, fun
  | .u8 b => let k := ofNat b.toNat; if idx k == b.toNat then some k else none
  | _ => none, fun k => .u8 (idx k).toUInt8⟩

instance : Reg Scan.Kind := Reg.enum Scan.Kind.ofNat Scan.Kind.ctorIdx
instance : Reg Kernel.Op := Reg.enum Kernel.Op.ofNat Kernel.Op.ctorIdx
instance : Reg QAtomicType := Reg.enum QAtomicType.ofNat QAtomicType.ctorIdx

/-- A pair: constructor `0`, its two components boxed object fields. -/
instance {α β : Type} [Reg α] [Reg β] : Reg (α × β) := ⟨.obj, fun
  | .ctor 0 #[a, b] #[] => do pure (← Reg.get? a, ← Reg.get? b)
  | _ => none, fun (a, b) => .ctor 0 #[Reg.put a, Reg.put b] #[]⟩

/-- `none` is constructor `0` with no field (`lean_box(0)`), `some a` constructor `1` holding `a` boxed. -/
instance {α : Type} [Reg α] : Reg (Option α) := ⟨.obj, fun
  | .ctor 0 #[] #[] => some none
  | .ctor 1 #[a] #[] => some <$> Reg.get? a
  | _ => none, fun | none => .ctor 0 #[] #[] | some a => .ctor 1 #[Reg.put a] #[]⟩

/-- A list's cells read back, `[]` constructor `0`, `a :: l` constructor `1` of `a` and `l`. -/
partial def listGet? {α : Type} [Reg α] : Val → Option (List α)
  | .ctor 0 #[] #[] => some []
  | .ctor 1 #[a, l] #[] => do pure ((← Reg.get? a) :: (← listGet? l))
  | _ => none

instance {α : Type} [Reg α] : Reg (List α) :=
  ⟨.obj, listGet?, fun l => l.foldr (fun a r => .ctor 1 #[Reg.put a, r] #[]) (.ctor 0 #[] #[])⟩

/-- An `Enc` is the constructor `Db.ownParts` takes apart: its tag, and its parts as its fields, which they are for
    the forms whose fields are all buffers (`bytes`, `foR`, `alp`) and for `pos`, which has none; `Db.ownEnc` puts
    them back. Every other form (`syms`, `enum`, `gen`) has a field that is no part: `Db.ownParts` refuses it, so it
    is put with no fields and `get?` refuses its tag — a run that reaches one fails naming the register, never reads
    a constructor the C does not hold. -/
instance : Reg Enc := ⟨.obj, fun
  | .ctor 6 #[] #[] => some .pos
  | .ctor k ps #[] => if [0, 2, 3].contains k then
      ps.mapM (fun | .bytes b => some b | _ => none) >>= Db.ownEnc k.toUInt8 else none
  | _ => none, fun e => .ctor e.ctorIdx (match Db.ownParts e with | .ok (some (_, ps)) => ps.map .bytes | _ => #[]) #[]⟩

mutual
/-- `atom t` is constructor `0` of the byte `t`; `cells n c lo hi els` constructor `1` of the objects `lo hi els`
    and the words `n c`, as the runtime lays a constructor out. -/
partial def ascGet? : Val → Option AscKey
  | .ctor 0 #[] #[t] => AscKey.atom <$> Reg.get? t
  | .ctor 1 #[lo, hi, els] #[n, c] => do
    let _ : Reg AscKey := ⟨.obj, ascGet?, ascPut⟩
    pure (.cells (← Reg.get? n) (← Reg.get? c) (← Reg.get? lo) (← Reg.get? hi) (← Reg.get? els))
  | _ => none
partial def ascPut : AscKey → Val
  | .atom t => .ctor 0 #[] #[Reg.put t]
  | .cells n c lo hi els =>
    let _ : Reg AscKey := ⟨.obj, ascGet?, ascPut⟩
    .ctor 1 #[Reg.put lo, Reg.put hi, Reg.put els] #[.size n, .size c]
end

instance : Reg AscKey := ⟨.obj, ascGet?, ascPut⟩
/-- A scan's verb is an enum too: its constructor index in a byte. -/
instance : Reg Scan.Verb := ⟨.u8, fun
  | .u8 0 => some .sums | .u8 1 => some .prds | .u8 2 => some .mins | .u8 3 => some .maxs | .u8 4 => some .fills
  | _ => none,
  fun v => .u8 (match v with | .sums => 0 | .prds => 1 | .mins => 2 | .maxs => 3 | .fills => 4)⟩

/-- A kernel as its `@[extern]` declaration states it (`kernel%`): the C symbol, each argument's type and whether
    it is borrowed (`@&`), the result's types (a product flattened) and each one's path of field indices into the
    answer, whether the answer is an `Except String` (its `error` the run's failure), whether the toolchain declares
    it (so `lean.h` defines its symbol, `static inline`), and the Lean call on registers: a pure kernel's answer, or
    an `IO` kernel's action, which answers no register and runs only at the output edge (`Plan.exec`). -/
structure Kernel where
  sym : String
  args : Array (Ty × Bool)
  res : Array Ty
  paths : Array (List Nat)
  exc : Bool
  std : Bool
  run : (Array Val → Except String (Array Val)) ⊕ (Array Val → IO Unit)

/-- Whether `k` runs in `IO`. -/
def Kernel.io (k : Kernel) : Bool := k.run.isRight

/-- Argument `i` of the kernel `sym`, read from its register as the type the declaration asks for. -/
def arg {α : Type} [Reg α] (sym : String) (vs : Array Val) (i : Nat) : Except String α :=
  match vs[i]?.bind Reg.get? with
  | some a => pure a
  | none => throw s!"{sym}: argument {i} is not a {repr (Reg.ty α)} register"

/-- A result as registers: none for `Unit`, else one; an `Except`'s `error` is the run's failure. -/
class Out (α : Type) where
  out : α → Except String (Array Val)

instance : Out Unit := ⟨fun _ => pure #[]⟩
instance {α : Type} [Reg α] : Out α := ⟨fun a => pure #[Reg.put a]⟩
/-- A product's registers: its components', left first (before `Reg (α × β)`, which would make it one register). -/
instance (priority := high) {α β : Type} [Out α] [Out β] : Out (α × β) :=
  ⟨fun (a, b) => return (← Out.out a) ++ (← Out.out b)⟩
/-- A decision is its bit (`lean_usize_dec_eq` answers a `uint8_t`). -/
instance {p : Prop} : Out (Decidable p) := ⟨fun d => pure #[.bit (@decide p d)]⟩
/-- A kernel's typed failure: its `error` fails the run, its `ok` is its registers. -/
instance (priority := high) {α : Type} [Out α] : Out (Except String α) := ⟨fun r => r >>= Out.out⟩

/-- The `Ty` that `Reg t` answers, read off the instance. -/
def tyOf (t : Lean.Expr) : MetaM Ty := do
  let some inst ← synthInstance? (mkApp (mkConst ``Reg) t)
    | throwError "kernel%: `{t}` is not a register type (`Plan.Reg`)"
  match (← whnfD (mkApp2 (mkConst ``Reg.ty) t inst)).constName? with
  | some ``Ty.bytes => pure .bytes | some ``Ty.size => pure .size | some ``Ty.bit => pure .bit
  | some ``Ty.u8 => pure .u8 | some ``Ty.str => pure .str | some ``Ty.parts => pure .parts
  | some ``Ty.u64 => pure .u64 | some ``Ty.i64 => pure .i64 | some ``Ty.nat => pure .nat
  | some ``Ty.obj => pure .obj
  | _ => throwError "kernel%: `Reg.ty` of `{t}` does not reduce to a `Ty`"

/-- A result's registers' types, as `Out` lays them, each with its path of field indices into the answer: none for
    `Unit`, a product's components' (field `0`, then `1`), a decision's bit, an `Except`'s `ok` value's. -/
partial def resTys (r : Lean.Expr) : MetaM (Array (Ty × List Nat)) := do
  if r.isConstOf ``Unit then return #[]
  if r.isAppOfArity ``Decidable 1 then return #[(.bit, [])]
  if r.isAppOfArity ``Except 2 then return ← resTys r.appArg!
  if r.isAppOfArity ``Prod 2 then
    return (← resTys r.appFn!.appArg!).map (fun (t, p) => (t, 0 :: p)) ++
      (← resTys r.appArg!).map (fun (t, p) => (t, 1 :: p))
  return #[(← tyOf r, [])]

/-- `kernel% f`: the `Kernel` of the `@[extern]` constant `f`, its symbol, `@&` marks and types read off the
    declaration, so the ABI is never written a second time. -/
elab "kernel% " c:ident : term => do
  let n ← realizeGlobalConstNoOverloadWithInfo c
  let some sym := getExternNameFor (← getEnv) `c n | throwError "kernel%: `{n}` has no `@[extern]` C symbol"
  let rec doms : Lean.Expr → List Lean.Expr × Lean.Expr
    | .forallE _ d b _ => let (ds, r) := doms b; (d :: ds, r)
    | e => ([], e)
  let (ds, r) := doms (← getConstInfo n).type
  let args ← ds.toArray.mapM fun d => return (← tyOf d.consumeMData, isMarkedBorrowed d)
  let (io, r) := if r.isAppOfArity ``IO 1 then (true, r.appArg!) else (false, r)
  let exc := r.isAppOfArity ``Except 2
  let rp ← resTys r
  let res := rp.map (·.1)
  if io && !res.isEmpty then
    throwError "kernel%: `{n}` runs in `IO` and answers {res.size} registers; a plan runs `IO` only at its output edge"
  -- the toolchain's own externs are the ones `lean.h` defines; its modules are those of `Init`, `Std`, `Lean`
  let env ← getEnv
  let std := (env.getModuleIdxFor? n >>= (env.header.moduleNames[·.toNat]?)).any ([`Init, `Std, `Lean].contains ·.getRoot)
  let vs := mkIdent `vs
  let as : Array Term ← (List.range ds.length).toArray.mapM fun i =>
    if io then `((← IO.ofExcept (arg $(quote sym) $vs $(quote i)))) else `((← arg $(quote sym) $vs $(quote i)))
  let call ← `($(mkIdent n) $as*)
  let run ← if io then `(Sum.inr fun $vs => do ($call : IO Unit)) else `(Sum.inl fun $vs => do Out.out $call)
  let runE ← elabTermAndSynthesize
    (← `(($run : (Array Val → Except String (Array Val)) ⊕ (Array Val → IO Unit)))) none
  return mkAppN (mkConst ``Kernel.mk) #[toExpr sym, toExpr args, toExpr res, toExpr (rp.map (·.2)), toExpr exc,
    toExpr std, ← instantiateMVars runE]

/-- One step. A `lit` defines one register, a `call` as many as its kernel's results, an `apply` as many as the
    function's, a `global` as many as the global's, an `ite` as many as each branch names, a `fail` none. -/
inductive Instr
  /-- `r = lit v`. -/
  | lit (v : Val)
  /-- `r… = call sym(args)`: the `@[extern]` kernel of C symbol `sym` on the registers `args`. -/
  | call (sym : String) (args : Array Nat)
  /-- `need`'s failing branch: print `msg` and the registers `args`, exit 1. -/
  | fail (msg : String) (args : Array Nat)
  /-- `r… = apply f(args)`: the plan's function number `f`, which must come before the one applying it. -/
  | apply (f : Nat) (args : Array Nat)
  /-- `r… = global g`: the registers the plan's global number `g` computed, once, before `main`. -/
  | global (g : Nat)
  /-- `r… = if c then t else e`: a branch runs after the registers so far, and its registers `rt` (`re`) are the
      results; the two name as many. -/
  | ite (c : Nat) (t : List Instr) (rt : Array Nat) (e : List Instr) (re : Array Nat)
  /-- `r = ctor tag(objs; scal)`: the constructor object of tag `tag`, its object fields the registers `objs` (a
      scalar one boxed), its scalar fields the registers `scal` (`Val.ctor`). -/
  | ctor (tag : Nat) (objs scal : Array Nat)
  /-- `r = proj x.i`: object field `i` of the constructor in register `x`, whose tag must be `tag`, read as a `t`
      (unboxed when `t` is a scalar); any other tag fails the run. -/
  | proj (x tag i : Nat) (t : Ty)
  deriving Inhabited

/-- A function: its parameters' types (registers `0 … k-1`, borrowed), its body, its result registers (owned). A
    global is a function of no parameter. -/
structure Fun where
  params : Array Ty
  body : List Instr
  res : Array Nat
  deriving Inhabited

/-- A plan (§6): functions, each applying only earlier ones, so the call graph has no cycle; globals, computed in
    order before `main`; and `main`. -/
structure Plan where
  funs : Array Fun := #[]
  globals : Array Fun := #[]
  main : List Instr
  deriving Inhabited

/-- What `fail msg args` prints: `msg`, then the registers after `: `, separated by `, `. -/
def failText (msg : String) (vs : List Val) : String :=
  if vs.isEmpty then msg else msg ++ ": " ++ ", ".intercalate (vs.map Val.show)

/-- Register `a`, read by `who`. -/
def reg (rs : Array Val) (who : String) (a : Nat) : Except String Val := match rs[a]? with
  | some v => pure v
  | none => throw s!"plan: {who} reads register {a}, which no earlier instruction defines"

/-- The calls of `IO` kernels a run made, in order: each kernel's symbol and its argument registers. A run is pure;
    these are performed after it, at the output edge (`Plan.exec`). -/
abbrev Writes := Array (String × Array Val)

/-- What a function means, given the globals: its parameters' values to its results', after the writes so far. -/
abbrev Sem := Array (Array Val) → Array Val → Writes → Except String (Array Val × Writes)

mutual
/-- What a block means after the registers `rs` and the writes `ws`: each instruction in order, each kernel looked
    up in `abi`, each function in `fs`, each global in `gs`. -/
def runB (abi : String → Option Kernel) (fs : Array Sem) (gs : Array (Array Val)) :
    List Instr → Array Val → Writes → Except String (Array Val × Writes)
  | [], rs, ws => pure (rs, ws)
  | i :: is, rs, ws => do let (rs, ws) ← runI abi fs gs i rs ws; runB abi fs gs is rs ws

def runI (abi : String → Option Kernel) (fs : Array Sem) (gs : Array (Array Val)) :
    Instr → Array Val → Writes → Except String (Array Val × Writes)
  | .lit v, rs, ws => pure (rs.push v, ws)
  | .call sym as, rs, ws => do
    let some k := abi sym | throw s!"plan: no kernel `{sym}` in the ABI table"
    let vs ← as.mapM (reg rs sym)
    match k.run with
    | .inl f =>
      let out ← f vs
      unless out.size == k.res.size do throw s!"plan: `{sym}` answered {out.size} registers, its declaration {k.res.size}"
      pure (rs ++ out, ws)
    | .inr _ => pure (rs, ws.push (sym, vs))
  | .fail msg as, rs, _ => do throw (failText msg (← as.mapM (reg rs "fail")).toList)
  | .apply f as, rs, ws => do
    let some g := fs[f]? | throw s!"plan: apply f{f}, which is not an earlier function"
    let (out, ws) ← g gs (← as.mapM (reg rs s!"apply f{f}")) ws
    pure (rs ++ out, ws)
  | .global g, rs, ws => do
    let some v := gs[g]? | throw s!"plan: global g{g} read before it is computed"
    pure (rs ++ v, ws)
  | .ite c t rt e re, rs, ws => do
    match ← reg rs "if" c with
    | .bit true => let (xs, ws) ← runB abi fs gs t rs ws; pure (rs ++ (← rt.mapM (reg xs "then")), ws)
    | .bit false => let (xs, ws) ← runB abi fs gs e rs ws; pure (rs ++ (← re.mapM (reg xs "else")), ws)
    | _ => throw s!"plan: if reads register {c}, which is not a bit"
  | .ctor tag os ss, rs, ws => do pure (rs.push (.ctor tag (← os.mapM (reg rs "ctor")) (← ss.mapM (reg rs "ctor"))), ws)
  | .proj x tag i t, rs, ws => do
    match ← reg rs "proj" x with
    | .ctor tag' os _ =>
      unless tag' == tag do throw s!"plan: proj r{x}.{i} reads constructor {tag'}, not {tag}"
      match os[i]? with
      | some v => if v.ty == t then pure (rs.push v, ws) else throw s!"plan: proj r{x}.{i} is a {repr v.ty}, not a {repr t}"
      | none => throw s!"plan: proj r{x}.{i}: constructor {tag} has {os.size} object fields"
    | _ => throw s!"plan: proj reads register {x}, which is not a constructor"
end

/-- What function `f` means where the functions before it mean `fs`. -/
def Fun.sem (abi : String → Option Kernel) (fs : Array Sem) (f : Fun) : Sem := fun gs args ws => do
  let (xs, ws) ← runB abi fs gs f.body args ws; pure (← f.res.mapM (reg xs "result"), ws)

/-- The functions' meanings, each seeing only the ones before it. -/
def sems (abi : String → Option Kernel) (funs : Array Fun) : Array Sem :=
  funs.foldl (fun fs f => fs.push (f.sem abi fs)) #[]

/-- What `p` means, pure (decision D of `doc/rel-native-design.md` §13): the globals in order, then `main`'s
    registers, and the writes to perform. -/
def Plan.run (abi : String → Option Kernel) (p : Plan) : Except String (Array Val × Writes) := do
  let fs := sems abi p.funs
  let (gs, ws) ← p.globals.foldlM (fun (gs, ws) g => do
    let (v, ws) ← g.sem abi fs gs #[] ws; pure (gs.push v, ws)) (#[], #[])
  runB abi fs gs p.main #[] ws

/-- `p` run, then its writes performed in order by their `IO` kernels: the output edge. A run that fails writes
    nothing, where the C has written what came before its `fail`; the gates compare runs that succeed. -/
def Plan.exec (abi : String → Option Kernel) (p : Plan) : IO (Array Val) := do
  let (rs, ws) ← IO.ofExcept (p.run abi)
  for (sym, vs) in ws do
    let some k := abi sym | throw (IO.userError s!"plan: no kernel `{sym}` in the ABI table")
    match k.run with
    | .inr act => act vs
    | .inl _ => throw (IO.userError s!"plan: `{sym}` is no `IO` kernel")
  pure rs

/-! ### Building a plan -/

/-- A plan being built: the current block's instructions, the number of registers defined so far, and the plan's
    functions and globals. -/
abbrev Bld := StateT (Array Instr × Nat × Array Fun × Array Fun) (Except String)

/-- A one-register instruction's register. -/
def emit1 (i : Instr) : Bld Nat := modifyGet fun (is, n, fg) => (n, (is.push i, n + 1, fg))

/-- `r = lit v`: the new register. -/
def lit (v : Val) : Bld Nat := emit1 (.lit v)

/-- An instruction defining `nres` registers: the new registers. -/
def emit (i : Instr) (nres : Nat) : Bld (Array Nat) :=
  modifyGet fun (is, n, fg) => ((List.range' n nres).toArray, (is.push i, n + nres, fg))

/-- `call sym(args)` of a kernel answering `nres` registers: the new registers. -/
def call (sym : String) (args : Array Nat) (nres : Nat) : Bld (Array Nat) := emit (.call sym args) nres

/-- `b` as a block of its own after the registers so far: its instructions and result registers; the functions and
    globals it adds stay. -/
def block (b : Bld (Array Nat)) : Bld (List Instr × Array Nat) := do
  let (is, n, fg) ← get
  let (r, is', _, fg') ← b.run (#[], n, fg)
  set (is, n, fg'); pure (is'.toList, r)

/-- `if c then t else e`, both answering as many registers: the new registers. -/
def ite (c : Nat) (t e : Bld (Array Nat)) : Bld (Array Nat) := do
  let (ti, rt) ← block t; let (ei, re) ← block e
  unless rt.size == re.size do throw s!"if r{c}: the branches answer {rt.size} and {re.size} registers"
  emit (.ite c ti rt ei re) rt.size

/-- The function of parameters `ps` and body `b` (run on the parameter registers), added to the plan: its number. -/
def defFun (ps : Array Ty) (b : Array Nat → Bld (Array Nat)) : Bld Nat := do
  let (is, n, fs, gs) ← get
  let (r, body, _, fs', gs') ← (b (List.range ps.size).toArray).run (#[], ps.size, fs, gs)
  set (is, n, fs'.push ⟨ps, body.toList, r⟩, gs'); pure fs'.size

/-- `apply f(args)`, `f` answering `nres` registers. -/
def apply (f : Nat) (args : Array Nat) (nres : Nat) : Bld (Array Nat) := emit (.apply f args) nres

/-- The global computed by `b`, added to the plan, and its registers read here. -/
def global (b : Bld (Array Nat)) : Bld (Array Nat) := do
  let (is, n, fs, gs) ← get
  let (r, body, _, fs', gs') ← b.run (#[], 0, fs, gs)
  set (is, n, fs', gs'.push ⟨#[], body.toList, r⟩)
  emit (.global gs'.size) r.size

/-- The plan of `main`. -/
def Bld.plan (b : Bld Unit) : Except String Plan := do
  let ((), is, _, fs, gs) ← b.run (#[], 0, #[], #[])
  pure ⟨fs, gs, is.toList⟩

/-- A side's atom columns, each with its path in the side: `""` an atom; `.1`/`.2` a product's; `.lo`/`.hi`/`.e`
    an array's bounds and payload; `.tag`/`.idx`/`.l`/`.r` a sum's tags, positions and two payloads. -/
def cols : (A : Obj) → {n : USize} → Vals A n → String → List (String × QValue)
  | .atom _, _, x, p => [(p, x.1)]
  | .prod a b, _, x, p => cols a x.1 (p ++ ".1") ++ cols b x.2 (p ++ ".2")
  | .arr b, _, ⟨_, lo, hi, f⟩, p => [(p ++ ".lo", lo.1), (p ++ ".hi", hi.1)] ++ cols b f (p ++ ".e")
  | .sum a b, _, ⟨_, _, tag, idx, x, y⟩, p =>
    [(p ++ ".tag", tag.1), (p ++ ".idx", idx.1)] ++ cols a x (p ++ ".l") ++ cols b y (p ++ ".r")

/-- A column as qlean's column writer takes it (`Db.ownFile`): `code`, `attr`, `kind`, `count`, `domain`, `parts`;
    `none` for positions, which have no file. -/
def ownFile (p : String) (v : QValue) : Except String (Option Db.OwnFile) :=
  (Db.ownFile v).mapError fun e => s!"column `{p}`: {e}"

/-- A side's registers: each column's path and its six `ownFile` registers. -/
abbrev Side := List (String × Array Nat)

/-- The side's columns as `lit`s; a positions column has none. -/
def litSide {A : Obj} {n : USize} (x : Vals A n) : Bld Side :=
  (cols A x "").filterMapM fun (p, v) => do
    let some f ← ownFile p v | return none
    return some (p, ← #[.u8 f.code, .u8 f.attr, .u8 f.kind, .size f.count, .str f.domain, .parts f.parts].mapM lit)

/-- The registers of a closed term's value, key side then value side. Stage 1a builds a literal and a converse,
    which swaps the sides and emits nothing; any other node is refused. -/
def ofTm : {A B : Obj} → Tm A B → Bld (Side × Side)
  | _, _, .val R => return (← litSide R.key, ← litSide R.val)
  | _, _, .conv R => return (← ofTm R).swap
  | _, _, .share _ R => ofTm R
  | _, _, _ => throw "a node other than a literal, a converse or a shared term: stage 1a builds only those"

/-! ### Recipes on the five kernels (design §4) -/

/-- `need`'s test on the bit `c`: set, nothing runs; clear, `fail msg args`. -/
def guard (c : Nat) (msg : String) (args : Array Nat) : Bld Unit :=
  discard <| ite c (pure #[]) (do discard <| emit (.fail msg args) 0; pure #[])

/-- `call k(args)`: as many new registers as `k`'s declaration answers, so the count is never written by hand. -/
def callK (k : Kernel) (args : Array Nat) : Bld (Array Nat) := call k.sym args k.res.size

/-- A one-register kernel call. Any other kernel is refused: the run pushes all its results, so every register
    numbered after a one-register `emit1` would be off by the rest. -/
def call1 (k : Kernel) (args : Array Nat) : Bld Nat := do
  unless k.res.size == 1 do throw s!"call1 `{k.sym}`: its declaration answers {k.res.size} registers, not one (`callK`)"
  emit1 (.call k.sym args)

/-- Register `i` of the registers `rs` that `who` answered. -/
def nth (rs : Array Nat) (i : Nat) (who : String) : Bld Nat := match rs[i]? with
  | some r => pure r
  | none => throw s!"{who} answers {rs.size} registers, not {i + 1}"

/-- `r = ctor tag(objs; scal)`. -/
def ctorB (tag : Nat) (objs scal : Array Nat) : Bld Nat := emit1 (.ctor tag objs scal)

/-- `r = proj x.i`, `x` of tag `tag`, read as a `t`. -/
def projB (x tag i : Nat) (t : Ty) : Bld Nat := emit1 (.proj x tag i t)

/-- The list of the registers `rs`, laid out as `Reg (List α)` lays it. -/
def listB (rs : List Nat) : Bld Nat := do rs.foldrM (fun x l => ctorB 1 #[x, l] #[]) (← ctorB 0 #[] #[])

/-- `kscatter` of no row into `n` cells: the column of `n` rows, each the word in register `fill`. -/
def constB (n fill : Nat) : Bld Nat := do
  let e ← lit (Reg.put (wordsFoR #[]))
  call1 (kernel% kscatter) #[← lit (Reg.put Kernel.Op.last), ← lit (.size 0), e, e, n, fill]

/-- `kscan op` at `t` over the `n` rows of the columns `es`, a segment starting at each row `seg` sets: the column and
    the fold result. -/
def scanB (op : Kernel.Op) (t : QAtomicType) (n seg : Nat) (es : List Nat) : Bld (Array Nat) := do
  callK (kernel% kscan) #[← lit (Reg.put op), ← lit (.bit false), ← lit (Reg.put t), ← lit (Reg.put t), n, seg, ← listB es]

/-- `where` (design §4: scan → scatter, no sort): the count `r` (a `size`) and the positions, in order, of the rows the
    `n`-row mask `keep` sets. The inclusive prefix sum `P` (`kscan add`, one segment) numbers the kept rows `1 … r`
    and its fold is `r` (`0` at `n = 0`, where no row is folded); row `i` goes to cell `keep[i] · P[i]` of `r + 1`
    (`kscatter`), a dropped row to the spare cell `0`, which the `kgather` of cells `1 … r` cuts off. -/
def whereB (n keep : Nat) : Bld (Nat × Nat) := do
  let z ← constB n (← lit (.u64 0)); let one ← constB n (← lit (.u64 1))
  let ps ← scanB .add .i64 n z [z, keep]
  let p ← nth ps 0 "kscan"
  let fold ← nth ps 1 "kscan"
  let empty ← call1 (kernel% USize.decEq) #[n, ← lit (.size 0)]
  let r ← call1 (kernel% UInt64.toUSize) #[← nth (← ite empty (do pure #[← lit (.u64 0)])
    (do pure #[← projB fold 1 0 .u64])) 0 "if"]
  let ix ← nth (← scanB .mul .i64 n one [keep, p]) 0 "kscan"
  let r1 ← call1 (kernel% USize.add) #[r, ← lit (.size 1)]
  let ix1 ← call1 (kernel% kscatter) #[← lit (Reg.put Kernel.Op.last), n, ix, ← lit (Reg.put (Ext.Enc.pos : Enc)), r1,
    ← lit (.u64 0)]
  let zr ← constB r (← lit (.u64 0))
  let cut ← nth (← scanB .add .i64 r zr [zr, ← constB r (← lit (.u64 1))]) 0 "kscan"
  pure (r, ← call1 (kernel% kgather) #[r, cut, r1, ix1])

/-- `Alg.arith op` (`add`, `sub`, `mul`) on the `i64` columns `u`, `v` of `n` rows: `s = u op v` wrapped (a `kscan`
    map: every row a segment), the rows kept where no operand and not `s` is null and `s` did not wrap (`kscan` maps
    of compares), `whereB` of them, and the columns gathered there (`kgather`): the count, then `u`, `v`, `s`. -/
def arithB (op : Kernel.Op) (n u v : Nat) : Bld (Array Nat) := do
  let one ← constB n (← lit (.u64 1)); let z ← constB n (← lit (.u64 0))
  let nul ← constB n (← lit (.u64 Alg.nul.toUInt64))
  let m (o : Kernel.Op) (a b : Nat) : Bld Nat := do nth (← scanB o .i64 n one [a, b]) 0 "kscan"
  let s ← m op u v
  -- `s` wrapped iff the sign of `v` disagrees with the side of `u` that `s` lies on; a product iff `s / u ≠ v`
  let exact ← match op with
    | .add => do m .eq (← m .ge v z) (← m .ge s u)
    | .sub => do m .eq (← m .ge v z) (← m .le s u)
    | .mul => do let u0 ← m .eq u z; m .or u0 (← m .eq (← m .div s (← m .add u u0)) v)
    | _ => throw s!"arithB: {repr op} is not `add`, `sub` or `mul`, the arithmetic whose wrap it checks"
  let keep ← m .and (← m .and (← m .ne u nul) (← m .ne v nul)) (← m .and (← m .ne s nul) exact)
  let (r, w) ← whereB n keep
  let g (x : Nat) := call1 (kernel% kgather) #[r, w, n, x]
  return #[r, ← g u, ← g v, ← g s]

/-- Each row's group among the `n` rows of the column `c` of the type in the byte `t`, groups numbered in `asc` order of their keys (design §4,
    group-by = `asc ≫ seen`): `kasc` sorts the rows (the sorted column and the permutation `p`), `kseen` numbers the
    runs of equal keys on the sorted rows (`g`), and `kscatter` writes sorted row `k`'s group to row `p[k]`. -/
def groupIdsB (t n c : Nat) : Bld Nat := do
  let key (e : Nat) : Bld Nat := do listB [← ctorB 0 #[← ctorB 0 #[] #[t], e] #[]]
  let sp ← callK (kernel% kasc) #[n, ← key c]
  let sorted ← projB (← nth sp 0 "kasc") 1 0 .obj
  let kg ← callK (kernel% kseen) #[n, ← key sorted]
  call1 (kernel% kscatter) #[← lit (Reg.put Kernel.Op.last), n, ← nth sp 1 "kasc", ← nth kg 1 "kseen", n, ← lit (.u64 0)]

end Rel.Lang.Plan

