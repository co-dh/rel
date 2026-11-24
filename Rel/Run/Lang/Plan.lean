module

public import Rel.Run.Lang.Tm
public import Rel.Kernel.Db.Own
public import Rel.Kernel.Scan
public import Rel.Kernel.Gather
public import Rel.Kernel.Seen

-- exposed: every def body is a spec a downstream `rfl`/`decide`/`simp` may unfold (PLAN W.8)
@[expose] public section

/-! # A program as kernel calls (`doc/rel-native-design.md` §6), stage 1a: `lit`, `call`, `fail`

A plan is first-order data: instructions over numbered registers, each register defined once, in order. A `call`
names an `@[extern]` kernel by its C symbol; `Plan.run` is what a plan means, calling the same kernels through the
table `kernel%` builds from their declarations, and `relc` (`Rel/Run/Lang/EmitC`) prints the same plan as C. -/

namespace Rel.Lang.Plan

open Lean Elab Term Meta Tab Rel.Kernel

/-- A register's type: the argument and result types of the kernels' `@[extern]` declarations. `nat` is a `Nat`
    (C `size_t`, below `2^63`, where `lean_box` holds it); `obj` a constructor object, `lean_ctor_object`. -/
inductive Ty
  | bytes | size | bit | u8 | str | parts | u64 | i64 | nat | obj
  deriving BEq, Repr, Inhabited

-- `kernel%` runs at elaboration, so its `toExpr` instance is meta
meta section
deriving instance Lean.ToExpr for Ty
end

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
  deriving Inhabited, BEq

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
instance : Reg QAtomicType := Reg.enum QAtomicType.ofNat QAtomicType.ctorIdx

/-- The `Op`s with no field, by constructor index: `Op` is no enum since `cast s t` (S6), so it has no `ofNat`. -/
def nullOps : List Kernel.Op :=
  [.add, .sub, .mul, .div, .mod, .min, .max, .neg, .abs, .eq, .ne, .lt, .le, .gt, .ge, .and, .or, .not, .first, .last,
   .fadd, .fsub, .fmul, .fdiv, .fpow, .fmin, .fmax, .fneg, .fabs, .fsqrt, .fexp, .flog, .fsin, .fcos, .ftan, .fasin,
   .facos, .fatan, .ffloor, .fround, .feq, .fne, .flt, .fle, .fgt, .fge, .f32to64, .rdiv, .rmod, .mix, .null]
-- every index below `cast`'s, the last constructor, holds its own `Op`
#guard nullOps.zipIdx.all (fun (o, i) => o.ctorIdx == i) && nullOps.length == (Kernel.Op.cast .i64 .i64).ctorIdx

/-- An `Op` as the runtime passes it (`@& Op`): a field-less one is `lean_box` of its index, `cast s t` a constructor
    holding the two atom types as `u8` scalars. -/
instance : Reg Kernel.Op := ⟨.obj, fun
  | .ctor k #[] #[] => nullOps[k]?
  | .ctor k #[] #[a, b] => do
    let o := Kernel.Op.cast (← Reg.get? a) (← Reg.get? b)
    if o.ctorIdx == k then some o else none
  | .ctor k #[] #[a] => do
    let o := Kernel.Op.fto (← Reg.get? a)
    if o.ctorIdx == k then some o else none
  | _ => none, fun
  | .cast s t => .ctor (Kernel.Op.cast s t).ctorIdx #[] #[Reg.put s, Reg.put t]
  | .fto t => .ctor (Kernel.Op.fto t).ctorIdx #[] #[Reg.put t]
  | o => .ctor o.ctorIdx #[] #[]⟩

/-- A pair: constructor `0`, its two components boxed object fields. -/
instance {α β : Type} [Reg α] [Reg β] : Reg (α × β) := ⟨.obj, fun
  | .ctor 0 #[a, b] #[] => do pure (← Reg.get? a, ← Reg.get? b)
  | _ => none, fun (a, b) => .ctor 0 #[Reg.put a, Reg.put b] #[]⟩

/-- `none` is constructor `0` with no field (`lean_box(0)`), `some a` constructor `1` holding `a` boxed. -/
instance {α : Type} [Reg α] : Reg (Option α) := ⟨.obj, fun
  | .ctor 0 #[] #[] => some none
  | .ctor 1 #[a] #[] => some <$> Reg.get? a
  | _ => none, fun | none => .ctor 0 #[] #[] | some a => .ctor 1 #[Reg.put a] #[]⟩

/-- A list's cells read back, `[]` constructor `0`, `a :: l` constructor `1` of `a` and `l`. Fields tested by size, not
    matched as `#[a, l]`, and recursion on `sizeOf`, not `partial`: so it has an unfolding equation a proof can use. -/
def listGet? {α : Type} [Reg α] : Val → Option (List α)
  | .ctor 0 os ss => if os.isEmpty && ss.isEmpty then some [] else none
  | .ctor 1 os ss => if h : os.size = 2 ∧ ss.isEmpty then do pure ((← Reg.get? os[0]) :: (← listGet? os[1])) else none
  | _ => none
termination_by v => sizeOf v
decreasing_by have := Array.sizeOf_getElem os 1 (by omega); simp; omega

instance {α : Type} [Reg α] : Reg (List α) :=
  ⟨.obj, listGet?, fun l => l.foldr (fun a r => .ctor 1 #[Reg.put a, r] #[]) (.ctor 0 #[] #[])⟩

/-- An `Enc` is the constructor `Db.ownParts` takes apart: its tag, and its parts as its fields, which they are for
    the forms whose fields are all buffers (`foR`) and for `pos`, which has none; `Db.ownEnc` puts them back. Every
    other form (`syms`, `enum`, `gen`) has a field that is no part: `Db.ownParts` refuses it, so it is put with no
    fields and `get?` refuses its tag — a run that reaches one fails naming the register, never reads a constructor
    the C does not hold. `get?` finds the own-format kind whose constructor has the tag, so no tag is written here. -/
instance : Reg Enc := ⟨.obj, fun
  | .ctor k ps #[] => do
    let bs ← ps.mapM fun | .bytes b => some b | _ => none
    if k == (.pos : Enc).ctorIdx && bs.isEmpty then some .pos
    else (List.range Db.ownNParts.length).findSome? fun i => (Db.ownEnc i.toUInt8 bs).filter (·.ctorIdx == k)
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
    an `IO` kernel's action, which runs only at an edge (`Plan.exec`): a read, answering registers, at the input
    edge (`Plan.input`); a write, answering none, at the output edge. -/
structure Kernel where
  sym : String
  args : Array (Ty × Bool)
  res : Array Ty
  paths : Array (List Nat)
  exc : Bool
  std : Bool
  run : (Array Val → Except String (Array Val)) ⊕ (Array Val → IO (Array Val))

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
meta def tyOf (t : Lean.Expr) : MetaM Ty := do
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
meta partial def resTys (r : Lean.Expr) : MetaM (Array (Ty × List Nat)) := do
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
  -- the toolchain's own externs are the ones `lean.h` defines; its modules are those of `Init`, `Std`, `Lean`
  let env ← getEnv
  let std := (env.getModuleIdxFor? n >>= (env.header.moduleNames[·.toNat]?)).any ([`Init, `Std, `Lean].contains ·.getRoot)
  let vs := mkIdent `vs
  let as : Array Term ← (List.range ds.length).toArray.mapM fun i =>
    if io then `((← IO.ofExcept (arg $(quote sym) $vs $(quote i)))) else `((← arg $(quote sym) $vs $(quote i)))
  let call ← `($(mkIdent n) $as*)
  let run ← if io then `(Sum.inr fun $vs => do IO.ofExcept (Out.out (← $call))) else `(Sum.inl fun $vs => do Out.out $call)
  let runE ← elabTermAndSynthesize
    (← `(($run : (Array Val → Except String (Array Val)) ⊕ (Array Val → IO (Array Val))))) none
  return mkAppN (mkConst ``Kernel.mk) #[toExpr sym, toExpr args, toExpr res, toExpr (rp.map (·.2)), toExpr exc,
    toExpr std, ← instantiateMVars runE]

/-- One step. A `lit` defines one register, a `call` as many as its kernel's results, an `apply` as many as the
    function's, a `global` as many as the global's, an `ite` as many as each branch names, a `fail` none. -/
inductive Instr
  /-- `r = lit v`. -/
  | lit (v : Val)
  /-- `r… = call sym(args)`: the `@[extern]` kernel of C symbol `sym` on the registers `args`. -/
  | call (sym : String) (args : Array Nat)
  /-- `r… = call sym(args)` of an `IO` read at the input edge, unless the file at the path in register `args[0]` (a
      `str`) is absent: then the literal registers `dflt`, as many as the kernel answers. A library's dictionary files
      (`Table.libDict`) are read this way: none yet is the empty dictionary. -/
  | readOpt (sym : String) (args : Array Nat) (dflt : Array Val)
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
  /-- `r = sproj x.i`: scalar field `i` of the constructor in register `x` of tag `tag`, `nobj` object fields and
      scalar fields of the types `ss` in declaration order (`Val.ctor`'s scalars), stored unboxed as the Lean
      compiler lays them out (an `ownMap` answer's count and bytes); any other tag fails the run. -/
  | sproj (x tag nobj : Nat) (ss : Array Ty) (i : Nat)
  /-- `r = part x.i`: part `i` (a `bytes`) of the parts array in register `x` (an `ownMap` answer's), an array of
      fewer parts failing the run. Not a `proj`: the runtime lays an `Array` out with a size and no tag, its elements
      read by `lean_array_get_core`, not as a constructor's fields. -/
  | part (x i : Nat)
  /-- `r… = loop k(init) { body } (out; done)`: the state, first the registers `init`, then rounds of `body`, each after
      the registers so far and the state (numbered from the loop's first result on, as an `if`'s branch); its `out` the
      next state, its bit `done` set ending the loop with it. `k` (a `size`) rounds with `done` clear fail the run
      with `msg`: `Tab.fixOn`'s and `Tab.foldRounds`' cap. -/
  | loop (k : Nat) (init : Array Nat) (body : List Instr) (out : Array Nat) (done : Nat) (msg : String)
  deriving Inhabited, BEq

/-- A function: its parameters' types (registers `0 … k-1`, borrowed), its body, its result registers (owned). A
    global is a function of no parameter. -/
structure Fun where
  params : Array Ty
  body : List Instr
  res : Array Nat
  deriving Inhabited, BEq

/-- A plan (§6): functions, each applying only earlier ones, so the call graph has no cycle; globals, computed in
    order before `main`; `main`; and its input edge, `lit`s and calls of `IO` reads only, whose registers are
    `main`'s first (IO step I10: an `input` is read before anything is computed, as `n.io` reads it). -/
structure Plan where
  funs : Array Fun := #[]
  globals : Array Fun := #[]
  main : List Instr
  input : List Instr := []
  deriving Inhabited

/-- A `fail` message's pieces: the text between its placeholders, and each placeholder (`\x01`: the register as
    `Val.show` prints it; `\x02`: a `u64` word read as signed, the column convention). Control characters, not `{}`:
    no message of the plan's other failures can hold one. -/
def failSegs (msg : String) : List (String ⊕ Bool) :=
  let (d, cur) := msg.foldl (fun (d, cur) c =>
    if c == '\x01' || c == '\x02' then (d ++ [.inl cur, .inr (c == '\x02')], "") else (d, cur.push c)) ([], "")
  d ++ [.inl cur]

/-- What `fail msg args` prints: where `msg` has placeholders (`failSegs`) the registers in them, one each; else `msg`,
    then the registers after `: `, separated by `, `. -/
def failText (msg : String) (vs : List Val) : Except String String :=
  let segs := failSegs msg
  if segs.all (·.isLeft) then pure (if vs.isEmpty then msg else msg ++ ": " ++ ", ".intercalate (vs.map Val.show))
  else if (segs.filter (·.isRight)).length != vs.length then
    throw s!"plan: fail `{msg}` has {(segs.filter (·.isRight)).length} placeholders for {vs.length} registers"
  else do
    let mut out := ""
    let mut vs := vs
    for s in segs do
      match s with
      | .inl t => out := out ++ t
      | .inr signed =>
        let v :: r := vs | throw "plan: fail: no register left for a placeholder"
        vs := r
        out := out ++ (match signed, v with
          | true, .u64 x => toString (Int64.ofNat x.toNat)
          | _, v => v.show)
    pure out

/-- Register `a`, read by `who`. -/
def reg (rs : Array Val) (who : String) (a : Nat) : Except String Val := match rs[a]? with
  | some v => pure v
  | none => throw s!"plan: {who} reads register {a}, which no earlier instruction defines"

/-- The calls of `IO` kernels a run made, in order: each kernel's symbol and its argument registers. A run is pure;
    these are performed after it, at the output edge (`Plan.exec`). -/
abbrev Writes := Array (String × Array Val)

/-- What a function means, given the globals: its parameters' values to its results', after the writes so far. -/
abbrev Sem := Array (Array Val) → Array Val → Writes → Except String (Array Val × Writes)

/-- `Instr.loop`'s rounds, at most `k`: `step` from the state `s`, its registers holding the next state `out` and the
    bit `done`. -/
def rounds (step : Array Val → Writes → Except String (Array Val × Writes)) (out : Array Nat) (done : Nat)
    (msg : String) : Nat → Array Val → Writes → Except String (Array Val × Writes)
  | 0, _, _ => throw msg
  | k + 1, s, ws => do
    let (xs, ws) ← step s ws
    let s ← out.mapM (reg xs "loop")
    match ← reg xs "loop" done with
    | .bit true => pure (s, ws)
    | .bit false => rounds step out done msg k s ws
    | _ => throw s!"plan: loop's done reads register {done}, which is not a bit"

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
    | .inr _ =>
      unless k.res.isEmpty do throw s!"plan: `{sym}` reads, which a plan does only at its input edge (`Plan.input`)"
      pure (rs, ws.push (sym, vs))
  | .readOpt sym .., _, _ => throw s!"plan: `{sym}` reads, which a plan does only at its input edge (`Plan.input`)"
  | .fail msg as, rs, _ => do throw (← failText msg (← as.mapM (reg rs "fail")).toList)
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
  | .sproj x tag nobj ss i, rs, ws => do
    match ← reg rs "sproj" x with
    | .ctor tag' os vs =>
      unless tag' == tag && os.size == nobj && (vs.map Val.ty) == ss do
        throw s!"plan: sproj r{x}.{i} reads constructor {tag'} of {os.size} objects and scalars {repr (vs.map Val.ty)}, not {tag} of {nobj} and {repr ss}"
      match vs[i]? with
      | some v => pure (rs.push v, ws)
      | none => throw s!"plan: sproj r{x}.{i}: constructor {tag} has {vs.size} scalar fields"
    | _ => throw s!"plan: sproj reads register {x}, which is not a constructor"
  | .part x i, rs, ws => do
    match ← reg rs "part" x with
    | .parts bs => match bs[i]? with
      | some b => pure (rs.push (.bytes b), ws)
      | none => throw s!"plan: part r{x}.{i} of an array of {bs.size} parts"
    | _ => throw s!"plan: part reads register {x}, which is not a parts array"
  | .loop k init body out done msg, rs, ws => do
    let .size c ← reg rs "loop" k | throw s!"plan: loop reads register {k} as its cap, which is not a size"
    let (s, ws) ← rounds (fun s ws => runB abi fs gs body (rs ++ s) ws) out done msg c.toNat
      (← init.mapM (reg rs "loop")) ws
    pure (rs ++ s, ws)
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
  unless p.input.isEmpty do throw "plan: an input edge, which only `Plan.exec` performs (it reads files)"
  let fs := sems abi p.funs
  let (gs, ws) ← p.globals.foldlM (fun (gs, ws) g => do
    let (v, ws) ← g.sem abi fs gs #[] ws; pure (gs.push v, ws)) (#[], #[])
  runB abi fs gs p.main #[] ws

/-- `p` run, then its writes performed in order by their `IO` kernels: the output edge. A run that fails writes
    nothing, where the C has written what came before its `fail`; the gates compare runs that succeed. -/
def Plan.exec (abi : String → Option Kernel) (p : Plan) : IO (Array Val) := do
  -- the input edge first: each read's registers become `lit`s of `main`, so the run stays pure
  let read (ins : Array Val) (sym : String) (as : Array Nat) (dflt : Option (Array Val)) : IO (Array Val) := do
    let some k := abi sym | throw (IO.userError s!"plan: no kernel `{sym}` in the ABI table")
    let .inr act := k.run | throw (IO.userError s!"plan: the input edge calls `{sym}`, which is no `IO` kernel")
    let vs : Array Val ← IO.ofExcept (as.mapM (reg ins sym))
    let path? : Option Val := vs[0]?
    let out ← match dflt, path? with
      | none, _ => act vs
      | some d, some (.str path) => if ← System.FilePath.pathExists path then act vs else pure d
      | some _, _ => throw (IO.userError s!"plan: readOpt `{sym}`: its first register is not a path")
    unless out.size == k.res.size do
      throw (IO.userError s!"plan: `{sym}` answered {out.size} registers, its declaration {k.res.size}")
    pure out
  let mut ins : Array Val := #[]
  for i in p.input do
    match i with
    | .lit v => ins := ins.push v
    | .call sym as => ins := ins ++ (← read ins sym as none)
    | .readOpt sym as d => ins := ins ++ (← read ins sym as (some d))
    | _ => throw (IO.userError "plan: the input edge holds `lit`s and `IO` reads only")
  let (rs, ws) ← IO.ofExcept ({ p with input := [], main := ins.toList.map Instr.lit ++ p.main }.run abi)
  for (sym, vs) in ws do
    let some k := abi sym | throw (IO.userError s!"plan: no kernel `{sym}` in the ABI table")
    match k.run with
    | .inr act => discard <| act vs
    | .inl _ => throw (IO.userError s!"plan: `{sym}` is no `IO` kernel")
  pure rs

/-! ### Building a plan -/

/-- A build error: `lazy` where the part needs its use site's bounds (`known`), so it has no closed table, which `shareB`
    expects (a lazy slot); any other error is a bug, and a `String` thrown or caught is one. -/
structure BErr where
  msg : String
  lazy : Bool := false

instance : Coe String BErr := ⟨fun msg => { msg }⟩

instance : ToString BErr := ⟨BErr.msg⟩

instance : MonadLift (Except String) (Except BErr) := ⟨Except.mapError fun msg => { msg }⟩

/-- A plan being built: the current block's instructions, the number of registers defined so far, and the plan's
    functions and globals. -/
abbrev Bld := StateT (Array Instr × Nat × Array Fun × Array Fun) (Except BErr)

/-- A `String` thrown in `Bld` is a bug (`BErr`); one caught is the message of any error, its `lazy` mark dropped. -/
instance : MonadExceptOf String Bld where
  throw msg := throwThe BErr { msg }
  tryCatch x h := tryCatchThe BErr x fun e => h e.msg

/-- A one-register instruction's register. -/
def emit1 (i : Instr) : Bld Nat := modifyGet fun (is, n, fg) => (n, (is.push i, n + 1, fg))

/-- `r = lit v`: the new register. -/
def lit (v : Val) : Bld Nat := emit1 (.lit v)

/-- An instruction defining `nres` registers: the new registers. -/
def emit (i : Instr) (nres : Nat) : Bld (Array Nat) :=
  modifyGet fun (is, n, fg) => ((List.range' n nres).toArray, (is.push i, n + nres, fg))

/-- `call sym(args)` of a kernel answering `nres` registers: the new registers. -/
def call (sym : String) (args : Array Nat) (nres : Nat) : Bld (Array Nat) := emit (.call sym args) nres

/-- `readOpt sym(args)` of an `IO` read answering `nres` registers, `dflt` where the file at `args[0]` is absent. -/
def readOpt (sym : String) (args : Array Nat) (dflt : Array Val) : Bld (Array Nat) :=
  emit (.readOpt sym args dflt) dflt.size

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

/-- `loop k(init)` of the round `b`, given the state's registers (as many as `init`) and answering the next state's
    and the bit `done`: the last state's registers. -/
def loop (k : Nat) (init : Array Nat) (msg : String) (b : Array Nat → Bld (Array Nat × Nat)) : Bld (Array Nat) := do
  let (is, n, fg) ← get
  let ((out, d), is', _, fg') ← (b (List.range' n init.size).toArray).run (#[], n + init.size, fg)
  unless out.size == init.size do throw s!"loop: a round answers {out.size} state registers, not {init.size}"
  set (is, n, fg'); emit (.loop k init is'.toList out d msg) init.size

/-- The function of parameters `ps` and body `b` (run on the parameter registers), added to the plan: its number. -/
def defFun (ps : Array Ty) (b : Array Nat → Bld (Array Nat)) : Bld Nat := do
  let (is, n, fs, gs) ← get
  let (r, body, _, fs', gs') ← (b (List.range ps.size).toArray).run (#[], ps.size, fs, gs)
  set (is, n, fs'.push ⟨ps, body.toList, r⟩, gs'); pure fs'.size

/-- `apply f(args)`, `f` answering `nres` registers. -/
def apply (f : Nat) (args : Array Nat) (nres : Nat) : Bld (Array Nat) := emit (.apply f args) nres


/-- The plan of `main`. -/
def Bld.plan (b : Bld Unit) : Except String Plan := Except.mapError BErr.msg do
  let ((), is, _, fs, gs) ← b.run (#[], 0, #[], #[])
  pure { funs := fs, globals := gs, main := is.toList }

/-- The plan of `rd`, its input edge (`lit`s and `IO` reads only, as `Plan.exec` checks), then `main`'s `b` on what
    `rd` answers. -/
def Bld.planIO {α : Type} (rd : Bld α) (b : α → Bld Unit) : Except String Plan := Except.mapError BErr.msg do
  let (a, is, n, fs, gs) ← rd.run (#[], 0, #[], #[])
  let ((), ms, _, fs, gs) ← (b a).run (#[], n, fs, gs)
  pure { funs := fs, globals := gs, main := ms.toList, input := is.toList }

/-- One column of a side (`cols`): a side of `1`'s count, or an atom column with its type and length. -/
abbrev SideCol := USize ⊕ (t : QAtomicType) × (k : USize) × Opt t k

/-- An atom column at ownership `o` as a nullable one: `Opt.ofArr` where every row is owned, itself where it is `Opt`. -/
def ColB.toOpt : {o : Bool} → {t : QAtomicType} → {n : USize} → ColB o t n → Opt t n
  | false, _, _, x => Opt.ofArr x
  | true, _, _, x => x

/-- A side's atom columns, each with its path in the side: `""` an atom; `.1`/`.2` a product's; `.lo`/`.hi`/`.e`
    an array's bounds and payload; `.tag`/`.l`/`.r` a sum's tags and two summand columns, a band sum
    (`Obj.band`) its one nullable column at the side's own path. A side of `1`
    is `.inl` its count: it has a file like any side (`Db.ownNParts` kind 5), holding the count and no part. -/
def cols : {o : Bool} → (A : Obj) → {n : USize} → ValsB o A n → String → List (String × SideCol)
  | _, .atom _, _, x, p => [(p, .inr ⟨_, _, ColB.toOpt x⟩)]
  | _, .prod a b, _, x, p => cols a x.1 (p ++ ".1") ++ cols b x.2 (p ++ ".2")
  | _, .arr b, _, ⟨_, lo, hi, f⟩, p =>
    [(p ++ ".lo", .inr ⟨_, _, ColB.toOpt lo⟩), (p ++ ".hi", .inr ⟨_, _, ColB.toOpt hi⟩)] ++ cols b f (p ++ ".e")
  | _, .sum a b, _, s, p => match s.view with
    | .opt _ x => [(p, .inr ⟨_, _, x⟩)]
    | .gen _ tag x y => [(p ++ ".tag", .inr ⟨_, _, Opt.ofArr tag⟩)] ++ cols a x (p ++ ".l") ++ cols b y (p ++ ".r")
  | _, .one, n, _, p => [(p, .inl n)]

/-- `Db.ownNParts`'s kind of a side of `1`: the header's count, no part. -/
def oneKind : UInt8 := 5

/-- A `cols` entry as qlean's column writer takes it (`Db.ownFile`): `code`, `kind`, `count`,
    `parts`; a side of `1` is kind `oneKind`, its count and no part; `none` for positions, which have no file. -/
def ownFile (p : String) : SideCol → Except String (Option Db.OwnFile)
  | .inl n => pure (some { code := 0, kind := oneKind, count := n, parts := #[] })
  | .inr ⟨t, k, x⟩ => (Db.ownFile t k x.enc).mapError fun e => s!"column `{p}`: {e}"

/-- A side's registers: each column's path and its four `ownFile` registers, then its `Enc` register where the plan
    holds one (a literal or computed vector, a CSV read; not a column mapped from its file, which is its parts). -/
abbrev Side := List (String × Array Nat)

/-- A column's `ownFile` registers in `Db.ownWrite`'s argument order, the one place that order is written: every
    reader indexes them by `Side.count` and `Side.enc`. -/
def Side.regs (code kind count parts : Nat) : Array Nat := #[code, kind, count, parts]

/-- The position of a column's row count among its registers (`Side.regs`). -/
def Side.count : Nat := 2

/-- The position of a column's `Enc` register, after its `Side.regs`. -/
def Side.enc : Nat := 4

/-- The side's columns as `lit`s; a positions column has none. -/
def litSide {A : Obj} {n : USize} (x : Vals A n) : Bld Side :=
  (cols A x "").filterMapM fun (p, c) => do
    let .inr ⟨_, _, x⟩ := c | return none
    let some f ← ownFile p c | return none
    let rs := Side.regs (← lit (.u8 f.code)) (← lit (.u8 f.kind)) (← lit (.size f.count)) (← lit (.parts f.parts))
    return some (p, rs.push (← lit (Reg.put x.enc)))

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

/-- `r = part x.i`, a `bytes`. -/
def partB (x i : Nat) : Bld Nat := emit1 (.part x i)

/-- The list of the registers `rs`, laid out as `Reg (List α)` lays it. -/
def listB (rs : List Nat) : Bld Nat := do rs.foldrM (fun x l => ctorB 1 #[x, l] #[]) (← ctorB 0 #[] #[])

/-- A source of `kscan`: the row count `n` and the column `x`, as the pair `(USize × Enc)` lays out. -/
def srcB (n x : Nat) : Bld Nat := ctorB 0 #[n, x] #[]

/-- `kscatter` of no row into `n` cells: the column of `n` rows, each the word in register `fill`. -/
def constB (n fill : Nat) : Bld Nat := do
  let e ← lit (Reg.put (wordsFoR #[]))
  call1 (kernel% kscatter) #[← lit (Reg.put Kernel.Op.last), ← lit (.size 0), e, e, n, fill]

/-- `kscan op` at `t` over the `n` rows of the columns `es`, a segment starting at each row `seg` sets (`none`: every
    row, a map), no chain: the column and the fold result. -/
def scanB (op : Kernel.Op) (t : QAtomicType) (n : Nat) (seg : Option Nat) (es : List Nat) : Bld (Array Nat) := do
  let g ← match seg with | some s => ctorB 1 #[s] #[] | none => ctorB 0 #[] #[]
  callK (kernel% kscan) #[← lit (Reg.put op), ← lit (.bit false), ← lit (Reg.put t), ← lit (Reg.put t), n, g,
    ← listB (← es.mapM (srcB n)), ← listB [], ← listB []]

/-- `where` (design §4: scan → scatter, no sort): the count `r` (a `size`) and the positions, in order, of the rows the
    `n`-row mask `keep` sets. The inclusive prefix sum `P` (`kscan add`, one segment) numbers the kept rows `1 … r`
    and its fold is `r` (`0` at `n = 0`, where no row is folded); row `i` goes to cell `keep[i] · P[i]` of `r + 1`
    (`kscatter`), a dropped row to the spare cell `0`, which the `kgather` of cells `1 … r` cuts off. -/
def whereB (n keep : Nat) : Bld (Nat × Nat) := do
  let z ← constB n (← lit (.u64 0))
  let ps ← scanB .add .i64 n (some z) [z, keep]
  let p ← nth ps 0 "kscan"
  let fold ← nth ps 1 "kscan"
  let empty ← call1 (kernel% USize.decEq) #[n, ← lit (.size 0)]
  let r ← call1 (kernel% UInt64.toUSize) #[← nth (← ite empty (do pure #[← lit (.u64 0)])
    (do pure #[← projB fold 1 0 .u64])) 0 "if"]
  let ix ← nth (← scanB .mul .i64 n none [keep, p]) 0 "kscan"
  let r1 ← call1 (kernel% USize.add) #[r, ← lit (.size 1)]
  let ix1 ← call1 (kernel% kscatter) #[← lit (Reg.put Kernel.Op.last), n, ix, ← lit (Reg.put (Ext.Enc.pos : Enc)), r1,
    ← lit (.u64 0)]
  let zr ← constB r (← lit (.u64 0))
  let cut ← nth (← scanB .add .i64 r (some zr) [zr, ← constB r (← lit (.u64 1))]) 0 "kscan"
  pure (r, ← call1 (kernel% kgather) #[r, cut, r1, ix1])

/-- What `arithB` builds once its `exact` column (register `ex`) is known: the rows kept where no operand and not `s` is
    null and `s` did not wrap, `whereB` of them, and the columns gathered there. A `def` of its own so that its build
    theorem is a lemma of its own (a declaration's proof is limited in heartbeats). -/
def arithTail (n u v s nul ex : Nat) : Bld (Array Nat) := do
  let m (o : Kernel.Op) (a b : Nat) : Bld Nat := do nth (← scanB o .i64 n none [a, b]) 0 "kscan"
  let keep ← m .and (← m .and (← m .ne u nul) (← m .ne v nul)) (← m .and (← m .ne s nul) ex)
  let (r, w) ← whereB n keep
  let g (x : Nat) := call1 (kernel% kgather) #[r, w, n, x]
  return #[r, ← g u, ← g v, ← g s]

/-- `Alg.arith op` (`add`, `sub`, `mul`) on the `i64` columns `u`, `v` of `n` rows: `s = u op v` wrapped (a `kscan`
    map: every row a segment), the rows kept where no operand and not `s` is null and `s` did not wrap (`kscan` maps
    of compares), `whereB` of them, and the columns gathered there (`kgather`): the count, then `u`, `v`, `s`. -/
def arithB (op : Kernel.Op) (n u v : Nat) : Bld (Array Nat) := do
  let z ← constB n (← lit (.u64 0))
  let nul ← constB n (← lit (.u64 Alg.nul.toUInt64))
  let m (o : Kernel.Op) (a b : Nat) : Bld Nat := do nth (← scanB o .i64 n none [a, b]) 0 "kscan"
  let s ← m op u v
  -- `s` wrapped iff the sign of `v` disagrees with the side of `u` that `s` lies on; a product iff `s / u ≠ v`
  let exact ← match op with
    | .add => do m .eq (← m .ge v z) (← m .ge s u)
    | .sub => do m .eq (← m .ge v z) (← m .le s u)
    | .mul => do let u0 ← m .eq u z; m .or u0 (← m .eq (← m .div s (← m .add u u0)) v)
    | _ => throw s!"arithB: {repr op} is not `add`, `sub` or `mul`, the arithmetic whose wrap it checks"
  arithTail n u v s nul exact

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

