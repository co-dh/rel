import Rel.Run.Lang.Plan
import Rel.Run.Lang.Expand
import Rel.Kernel.Db.ObjectFile
import Rel.Lang.Table

/-! # `relc`: a plan printed as C (`doc/rel-native-design.md` §6, stage 1a)

The C has no plan interpreter: one line per instruction. A literal is a static Lean object with `m_rc = 0` (a
persistent object, never counted or freed), a kernel a direct call to its C symbol, `fail` a message and exit 1.
It is linked against qlean's `libqleankernel.a` and `qrt.o` (`rust/build.sh rt`), not against the Lean runtime. -/

namespace Rel.Lang.Plan

open Tab

/-- The kernels a plan may call, each read off its `@[extern]` declaration: the five of design §4, the column writer
    and the toolchain's own arithmetic on sizes and buffers. -/
def abi : List Kernel :=
  [kernel% Rel.Kernel.kscan, kernel% Rel.Kernel.kscatter, kernel% Rel.Kernel.kgather, kernel% Rel.Kernel.kasc,
   kernel% Rel.Kernel.kseen, kernel% Rel.Db.ownWrite, kernel% Rel.Db.pushPart, kernel% USize.decEq,
   kernel% USize.add, kernel% USize.div, kernel% UInt64.toUSize, kernel% USize.toUInt64, kernel% ByteArray.usize]

def abiOf (sym : String) : Option Kernel := abi.find? (·.sym == sym)

/-! ### Writing a relation as a column directory -/

/-- `output R to dir`: each column of `R`'s registers written by `qlean_own_write` to `dir/key<path>` and
    `dir/val<path>`. The directory must exist; the kernel's error names the path when it does not. -/
def output (dir : String) (rs : Side × Side) : Bld Unit := do
  for (side, cs) in [("key", rs.1), ("val", rs.2)] do
    for (p, r) in cs do
      let path ← lit (.str (System.FilePath.mk dir / (side ++ p)).toString)
      discard <| call "qlean_own_write" (#[path] ++ r) 0

/-- A computed atom column's six `output` registers: type `t`, `count` rows (a register), constructor `kind`
    (`Db.ownParts`'s numbering) whose parts are the registers `bs`, gathered by `pushPart` from the empty literal. -/
def colRegs (t : QAtomicType) (kind : UInt8) (count : Nat) (bs : Array Nat) : Bld (Array Nat) := do
  let ps ← bs.foldlM (fun ps b => call1 (kernel% Rel.Db.pushPart) #[ps, b]) (← lit (.parts #[]))
  return #[← lit (.u8 t.code.toUInt8), ← lit (.u8 0), ← lit (.u8 kind), count, ← lit (.str ""), ps]

/-- The `Enc` register `e` of `count` rows of type `t` as `output`'s six registers: a `foR` (what every kernel answers,
    design §4) handed over as kind `2` (`Db.ownParts`), its parts its two fields, so it is written as it is encoded. -/
def encRegs (t : QAtomicType) (count e : Nat) : Bld (Array Nat) := do
  colRegs t 2 count #[← projB e 2 0 .bytes, ← projB e 2 1 .bytes]

/-- The plan's steps of `output x to dir` in the program `prog`, read after the programs `chain` (`Expand.read`). -/
def outputOf (chain : List (Lean.Name × Program)) (prog : Program) (x : String) (dir : String) :
    Lean.Meta.MetaM (Except String (Bld Unit)) := do
  let r ← (Expand.read (fun _ => none) chain prog).run
  return do
    let (ds, _) ← r.mapError (s!"{repr ·}")
    let some ⟨_, _, t⟩ := ds.lookup x | throw s!"`{x}` is no closed definition of the program"
    pure (do output dir (← ofTm t))

/-- The Lean side of the same output: `R`'s two sides written by the table writer under the names `output` gives
    them, from the value Lean computed, not from a plan. -/
def writeRel {A B : Obj} (dir : String) (R : Tab A B) : IO Unit := do
  Table.writeVals dir "key" R.key; Table.writeVals dir "val" R.val

/-! ### The C -/

def isObj : Ty → Bool
  | .bytes | .str | .parts | .obj => true
  | _ => false

def cTy (t : Ty) : String := match t with
  | .size | .nat => "size_t"
  | .bit | .u8 => "uint8_t"
  | .u64 => "uint64_t"
  | .i64 => "int64_t"
  | _ => "lean_object *"

/-- A C string literal of `s`'s bytes, each an octal escape: three digits, so no following byte is absorbed. -/
def cStr (s : String) : String :=
  "\"" ++ String.join (s.toUTF8.toList.map fun b =>
    let o := Nat.toDigits 8 b.toNat; "\\" ++ String.mk (List.replicate (3 - o.length) '0' ++ o)) ++ "\""

/-- A static scalar array `L` holding `b`, `m_rc = 0`. -/
def cBytes (L : String) (b : ByteArray) : String :=
  let n := b.size
  s!"static struct \{ lean_object h; size_t n, c; uint8_t d[{max n 1}]; } __attribute__((aligned(8))) {L} = " ++
    s!"\{\{0, 0, 1, LeanScalarArray}, {n}, {max n 1}, \{" ++
    ", ".intercalate (b.toList.map toString) ++ "}};\n"

/-- Whether `k` answers its one register or none itself, not inside an object: no `Except`, no product. -/
def Kernel.direct (k : Kernel) : Bool := !k.exc && k.paths.all (·.isEmpty)

/-- The C prototype of `k`, from its declaration: an owned or borrowed object, a scalar; an `IO` world; an object
    holding the registers where `k` is not `direct`. A `Nat` crosses the ABI as an object, which `relc` does not pass. -/
def proto (k : Kernel) : Except String String := do
  if k.args.any (·.1 == .nat) || (k.direct && k.res.contains .nat) then
    throw s!"`{k.sym}`: a `Nat` argument or answer, which `relc` passes only inside an object"
  let as := k.args.toList.map fun (t, b) => if isObj t then (if b then "b_lean_obj_arg" else "lean_obj_arg") else cTy t
  let as := if k.io then as ++ ["lean_obj_arg"] else as
  let r ← if k.io || !k.direct then pure "lean_obj_res" else match k.res.toList with
    | [] => pure "void"
    | [t] => pure (cTy t)
    | _ => throw s!"`{k.sym}`: a result of {k.res.size} registers, which `relc` does not print"
  pure s!"{r} {k.sym}({", ".intercalate as});\n"

/-- `fail`'s print of register `r` of type `t`, as `Val.show` prints it. -/
def cShow (r : String) : Ty → String
  | .bytes => s!"fprintf(stderr, \"<%zu bytes>\", lean_sarray_size({r}));"
  | .size => s!"fprintf(stderr, \"%zu\", {r});"
  | .bit => s!"fputs({r} ? \"true\" : \"false\", stderr);"
  | .u8 => s!"fprintf(stderr, \"%u\", (unsigned){r});"
  | .str => s!"fputs(lean_string_cstr({r}), stderr);"
  | .parts => s!"fprintf(stderr, \"<%zu parts>\", lean_array_size({r}));"
  | .u64 => s!"fprintf(stderr, \"%llu\", (unsigned long long){r});"
  | .i64 => s!"fprintf(stderr, \"%lld\", (long long){r});"
  | .nat => s!"fprintf(stderr, \"%zu\", {r});"
  | .obj => s!"fprintf(stderr, \"<constructor %u>\", lean_obj_tag({r}));"

/-- A register of type `t` read out of the boxed object `v`: an `IO` value, a field of polymorphic type. -/
def cUnbox (t : Ty) (v : String) : String := match t with
  | .size => s!"lean_unbox_usize({v})"
  | .bit | .u8 => s!"(uint8_t)lean_unbox({v})"
  | .u64 => s!"lean_unbox_uint64({v})"
  | .i64 => s!"(int64_t)lean_unbox_uint64({v})"
  | .nat => s!"relc_unbox_nat({v})"
  | _ => v

/-- The register `x` of type `t` as an object field: boxed when a scalar, `cUnbox`'s converse. -/
def cBox (t : Ty) (x : String) : String := match t with
  | .size => s!"lean_box_usize({x})"
  | .bit | .u8 => s!"lean_box({x})"
  | .u64 => s!"lean_box_uint64({x})"
  | .i64 => s!"lean_box_uint64((uint64_t){x})"
  | .nat => s!"relc_box_nat({x})"
  | _ => x

/-- The constructor object `x` of tag `tag`, from the C names `os` of its object fields (owned, each moved in) and
    `ss` of its scalar fields, laid out as the Lean compiler lays them: the objects, then the `size_t` fields, then
    the other scalars by size, largest first; with no field it is `lean_box(tag)`. -/
def ctorC (x : String) (tag : Nat) (os ss : List (String × Ty)) : Except String String := do
  if os.isEmpty && ss.isEmpty then return s!"lean_object *{x} = lean_box({tag});\n"
  let sz (t : Ty) : Except String Nat := match t with
    | .u64 | .i64 => pure 8 | .u8 | .bit => pure 1
    | t => throw s!"ctor {tag}: a scalar field of type {repr t}, which no constructor holds unboxed"
  let us := ss.filter (·.2 == .size)
  let rest ← ((ss.filter (·.2 != .size)).mapM fun (y, t) => return (y, t, ← sz t))
  -- by size and stably, so equal sizes keep declaration order
  let rest := rest.filter (·.2.2 == 8) ++ rest.filter (·.2.2 == 1)
  let base := 8 * (os.length + us.length)
  let (sets, end_) := rest.foldl (fun (s, off) (y, t, n) =>
    (s ++ s!" lean_ctor_set_uint{8 * n}({x}, {off}, (uint{8 * n}_t){y});", off + n)) ("", base)
  pure (s!"lean_object *{x} = lean_alloc_ctor({tag}, {os.length}, {end_ - 8 * os.length});" ++
    String.join (os.zipIdx.map fun ((y, t), i) => s!" lean_ctor_set({x}, {i}, {cBox t y});") ++
    String.join (us.zipIdx.map fun ((y, _), k) => s!" lean_ctor_set_usize({x}, {os.length + k}, {y});") ++ sets ++ "\n")

/-- The registers an instruction reads that were defined before register `base` (an `if`'s first result): a nested
    block's own registers are numbered from `base` on, so its reads below `base` are the outer ones. -/
partial def reads (base : Nat) : Instr → List Nat
  | .call _ as | .fail _ as | .apply _ as => as.toList
  | .ite c t rt e re => c :: ((t.flatMap (reads base) ++ rt.toList ++ e.flatMap (reads base) ++ re.toList).filter (· < base))
  | .ctor _ os ss => os.toList ++ ss.toList
  | .proj x .. => [x]
  | .lit _ | .global _ => []

/-- How many registers an instruction defines. -/
def defs (abi : String → Option Kernel) (fres : Array (Array Ty)) (gtys : Array (Array Ty)) : Instr → Except String Nat
  | .lit _ => pure 1
  | .call sym _ => match abi sym with | some k => pure k.res.size | none => throw s!"no kernel `{sym}` in the ABI table"
  | .fail .. => pure 0
  | .apply f _ => match fres[f]? with | some t => pure t.size | none => throw s!"apply f{f}: no earlier function"
  | .global g => match gtys[g]? with | some t => pure t.size | none => throw s!"global g{g}: no earlier global"
  | .ite _ _ rt _ _ => pure rt.size
  | .ctor .. | .proj .. => pure 1

/-- The emitter's state: the next fresh C name, the prototypes, the statics. -/
abbrev EM := StateT (Nat × List String × String) (Except String)

def fresh : EM String := modifyGet fun (k, ps, st) => (s!"v{k}", (k + 1, ps, st))
def static (s : String) : EM Unit := modify fun (k, ps, st) => (k, ps, st ++ s)

/-- A scope's register: its C name, its type, and whether the scope holds a reference it must release. -/
abbrev CReg := String × Ty × Bool

def creg (rs : Array CReg) (a : Nat) : EM CReg := match rs[a]? with
  | some r => pure r
  | none => throw s!"an instruction reads register {a}, which no earlier instruction defines"

/-- The C of the literal `v`, as register `x`; a constructor is built at run time (`ctorC`), its fields first, each
    moved into it. -/
partial def litC (x : String) (v : Val) : EM String := do
  let L := "L" ++ x
  match v with
  | .bytes b => static (cBytes L b); pure s!"lean_object *{x} = (lean_object *)&{L};\n"
  | .str s =>
    let n := s.utf8ByteSize + 1
    static (s!"static struct \{ lean_object h; size_t n, c, l; char d[{n}]; } __attribute__((aligned(8))) " ++
      s!"{L} = \{\{0, 0, 0, LeanString}, {n}, {n}, {s.length}, {cStr s}};\n")
    pure s!"lean_object *{x} = (lean_object *)&{L};\n"
  | .parts bs =>
    for (b, j) in bs.toList.zipIdx do static (cBytes s!"{L}_{j}" b)
    static (s!"static struct \{ lean_object h; size_t n, c; lean_object *d[{max bs.size 1}]; } " ++
      s!"__attribute__((aligned(8))) {L} = \{\{0, 0, 0, LeanArray}, {bs.size}, {max bs.size 1}, \{" ++
      ", ".intercalate ((List.range bs.size).map (s!"(lean_object *)&{L}_{·}")) ++ "}};\n")
    pure s!"lean_object *{x} = (lean_object *)&{L};\n"
  | .size n => pure s!"size_t {x} = {n}u;\n"
  | .u8 b => pure s!"uint8_t {x} = {b};\n"
  | .bit b => pure s!"uint8_t {x} = {if b then 1 else 0};\n"
  -- through the unsigned bits, so `INT64_MIN` (q's null) is no out-of-range literal
  | .u64 w => pure s!"uint64_t {x} = UINT64_C({w.toNat});\n"
  | .i64 w => pure s!"int64_t {x} = (int64_t)UINT64_C({w.toUInt64.toNat});\n"
  | .nat n => if n < 2 ^ 63 then pure s!"size_t {x} = {n}u;\n" else throw s!"the Nat {n} is past `lean_box`"
  | .ctor tag os ss =>
    let fs (vs : Array Val) : EM (String × List (String × Ty)) := do
      let cs ← vs.toList.mapM fun v => do let y ← fresh; pure (← litC y v, y, v.ty)
      pure (String.join (cs.map (·.1)), cs.map (·.2))
    let (co, os) ← fs os; let (cs, ss) ← fs ss
    pure (co ++ cs ++ (← ctorC x tag os ss))

/-- A block as C at indent `ind`, after the scope's registers `rs`, releasing the references it holds: those `owe`
    hands it from the enclosing scope and those its instructions make, each right after its last read (§8); an owned
    argument at its last read is moved, not counted. Its results `res` leave owned: moved where the block holds the
    reference, counted otherwise. The C, and the scope's registers at its end. -/
partial def blockC (abi : String → Option Kernel) (fres gtys : Array (Array Ty)) (ind : String) (rs₀ : Array CReg)
    (owe : List Nat) (is : List Instr) (res : Array Nat) : EM (String × Array CReg × Array String) := do
  let held (rs : Array CReg) (a : Nat) : Bool := match rs[a]? with | some (_, t, o) => o && isObj t | none => false
  -- the references held, minus those released; `later j` the reads at and after instruction `j`, results included
  let ia := is.toArray
  let mut bases : Array Nat := #[]
  let mut n := rs₀.size
  for i in ia do bases := bases.push n; n := n + (← defs abi fres gtys i)
  let later (j : Nat) : List Nat := res.toList ++ ((ia.extract j ia.size).zip (bases.extract j ia.size)).toList.flatMap
    fun (i, b) => reads b i
  let mut rs := rs₀
  let mut live : List Nat := owe
  let mut c := ""
  let release (rs : Array CReg) (live : List Nat) (keep : List Nat) : List Nat × String :=
    live.foldl (fun (l, s) a => if keep.contains a then (l ++ [a], s) else
      (l, s ++ match rs[a]? with | some (x, t, _) => if isObj t then s!"{ind}lean_dec({x});\n" else "" | none => "")) ([], "")
  let (l0, s0) := release rs live (later 0); live := l0; c := c ++ s0
  for (i, j) in ia.toList.zipIdx do
    let after := later (j + 1)
    match i with
    | .lit v =>
      let x ← fresh; c := c ++ ind ++ (← litC x v)
      -- a constructor literal is built, so owned; every other literal is static
      match v with
      | .ctor .. => rs := rs.push (x, .obj, true); live := live ++ [rs.size - 1]
      | _ => rs := rs.push (x, v.ty, false)
    | .ctor tag os ss =>
      let fs (as : Array Nat) : EM (List (String × Ty)) := as.toList.mapM fun a => return ((← creg rs a).1, (← creg rs a).2.1)
      let (os, ss) := (← fs os, ← fs ss)
      for (y, t) in os do if isObj t then c := c ++ s!"{ind}lean_inc({y});\n"
      let x ← fresh; c := c ++ ind ++ (← ctorC x tag os ss)
      rs := rs.push (x, .obj, true); live := live ++ [rs.size - 1]
    | .proj r tag i t =>
      let (y, ty, _) ← creg rs r
      unless ty == .obj do throw s!"proj reads register {r}, a {repr ty}, not a constructor"
      let x ← fresh
      c := c ++ s!"{ind}if (lean_obj_tag({y}) != {tag}) \{ fprintf(stderr, \"plan: proj r{r}.{i} reads constructor %u, " ++
        s!"not {tag}\\n\", lean_obj_tag({y})); exit(1); }\n"
      c := c ++ (if isObj t then s!"{ind}lean_object *{x} = lean_ctor_get({y}, {i}); lean_inc({x});\n"
        else s!"{ind}{cTy t} {x} = {cUnbox t s!"lean_ctor_get({y}, {i})"};\n")
      rs := rs.push (x, t, true); live := live ++ [rs.size - 1]
    | .call sym as =>
      let some k := abi sym | throw s!"no kernel `{sym}` in the ABI table"
      unless k.args.size == as.size do throw s!"`{sym}` takes {k.args.size} registers, given {as.size}"
      let mut args : List String := []
      for ((t, b), a) in k.args.toList.zip as.toList do
        let (x, t', _) ← creg rs a
        unless t' == t do throw s!"`{sym}`: register {a} is a {repr t'}, the kernel's argument a {repr t}"
        if isObj t && !b then
          -- moved where this is its last read and the only one in the call; counted otherwise
          if live.contains a && !after.contains a && (as.toList.filter (· == a)).length == 1 then live := live.erase a
          else c := c ++ s!"{ind}lean_inc({x});\n"
        args := args ++ [x]
      let pr ← proto k
      unless k.std do modify fun (q, ps, st) => (q, if ps.contains pr then ps else ps ++ [pr], st)
      let call := s!"{sym}({", ".intercalate (args ++ if k.io then ["lean_box(0)"] else [])})"
      let call := if k.io then s!"qlean_rt_io({call}, {cStr sym})" else call
      match k.direct, k.res.toList with
      | true, [] => c := c ++ s!"{ind}{if k.io then s!"lean_dec({call})" else call};\n"
      | true, [t] =>
        let x ← fresh
        c := c ++ s!"{ind}{cTy t} {x} = {if k.io then cUnbox t call else call};\n"
        rs := rs.push (x, t, true)
      | true, _ => throw s!"`{sym}`: a result of {k.res.size} registers, which `relc` does not print"
      | false, _ =>
        if k.io then throw s!"`{sym}`: an `IO` kernel answering an object, which `relc` does not print"
        -- the answer is an object: an `Except`'s `error` fails the run as `Plan.run` does, its registers are fields
        let p ← fresh
        c := c ++ s!"{ind}lean_object *{p} = {call};\n"
        if k.exc then
          c := c ++ s!"{ind}if (lean_obj_tag({p}) == 0) \{ fputs(lean_string_cstr(lean_ctor_get({p}, 0)), stderr); " ++
            "fputc('\\n', stderr); exit(1); }\n"
        let v := if k.exc then s!"lean_ctor_get({p}, 0)" else p
        for (t, path) in k.res.toList.zip k.paths.toList do
          let e := path.foldl (fun e i => s!"lean_ctor_get({e}, {i})") v
          let x ← fresh
          c := c ++ (if isObj t then s!"{ind}lean_object *{x} = {e}; lean_inc({x});\n"
            else s!"{ind}{cTy t} {x} = {cUnbox t e};\n")
          rs := rs.push (x, t, true)
        c := c ++ s!"{ind}lean_dec({p});\n"
      live := live ++ ((List.range k.res.size).map (rs.size - k.res.size + ·))
    | .fail msg as =>
      let shows ← as.toList.zipIdx.mapM fun (a, j) => do
        let (x, t, _) ← creg rs a
        pure ((if j == 0 then "fputs(\": \", stderr); " else "fputs(\", \", stderr); ") ++ cShow x t)
      c := c ++ s!"{ind}fputs({cStr msg}, stderr); " ++ " ".intercalate shows ++ " fputc('\\n', stderr); exit(1);\n"
    | .apply f as =>
      let some ts := fres[f]? | throw s!"apply f{f}: no earlier function"
      let xs ← as.toList.mapM fun a => return (← creg rs a).1
      let os ← ts.toList.mapM fun t => return (← fresh, t)
      for (o, t) in os do c := c ++ s!"{ind}{cTy t} {o};\n"
      c := c ++ s!"{ind}f{f}({", ".intercalate (xs ++ os.map (s!"&{·.1}"))});\n"
      for (o, t) in os do rs := rs.push (o, t, true); live := live ++ [rs.size - 1]
    | .global g =>
      let some ts := gtys[g]? | throw s!"global g{g}: no earlier global"
      for (t, k) in ts.toList.zipIdx do rs := rs.push (s!"g{g}_{k}", t, false)
    | .ite cnd t rt e re =>
      let (x, ty, _) ← creg rs cnd
      unless ty == .bit do throw s!"if reads register {cnd}, a {repr ty}, not a bit"
      -- the references read last here are handed to the branches, each releasing them itself
      let down := live.filter (!after.contains ·)
      live := live.filter (after.contains ·)
      let (tc, trs, txs) ← blockC abi fres gtys (ind ++ "  ") rs down t rt
      let (ec, _, exs) ← blockC abi fres gtys (ind ++ "  ") rs down e re
      let tys ← rt.toList.mapM fun a => return (← creg trs a).2.1
      let os ← tys.mapM fun t => return (← fresh, t)
      for (o, t) in os do c := c ++ s!"{ind}{cTy t} {o};\n"
      let set (xs : Array String) := String.join ((os.zip xs.toList).map fun ((o, _), v) => s!"{ind}  {o} = {v};\n")
      c := c ++ s!"{ind}if ({x}) \{\n" ++ tc ++ set txs ++ s!"{ind}} else \{\n" ++ ec ++ set exs ++ s!"{ind}}\n"
      for (o, t) in os do rs := rs.push (o, t, true); live := live ++ [rs.size - 1]
    let (l, s) := release rs live after; live := l; c := c ++ s
  -- the results: moved where held, counted otherwise
  let mut outs : Array String := #[]
  let mut moved : List Nat := []
  for a in res do
    let (x, t, _) ← creg rs a
    if held rs a && live.contains a && !moved.contains a then moved := a :: moved
    else if isObj t then c := c ++ s!"{ind}lean_inc({x});\n"
    outs := outs.push x
  pure (c, rs, outs)

/-- `p` as one C file: the statics, the kernels' prototypes, one `static` function per plan function, and `main`,
    which computes the globals, runs `main`'s block in the directory its one argument names, and frees the globals. -/
def relc (abi : String → Option Kernel) (p : Plan) : Except String String := do
  let go : EM String := do
    let mut fres : Array (Array Ty) := #[]
    let mut fns := ""
    for (f, i) in p.funs.toList.zipIdx do
      let ps ← f.params.toList.mapM fun t => return (← fresh, t)
      let (c, rs, outs) ← blockC abi fres #[] "  " (ps.toArray.map fun (x, t) => (x, t, false)) [] f.body f.res
      let tys ← f.res.toList.mapM fun a => return (← creg rs a).2.1
      let sig := ps.map (fun (x, t) => s!"{cTy t} {x}") ++ (tys.zipIdx.map fun (t, k) => s!"{cTy t} *o{k}")
      fns := fns ++ s!"static void f{i}({", ".intercalate sig}) \{\n" ++ c ++
        String.join ((outs.toList.zipIdx).map fun (x, k) => s!"  *o{k} = {x};\n") ++ "}\n"
      fres := fres.push tys.toArray
    let mut gtys : Array (Array Ty) := #[]
    let mut gs := ""
    let mut gdec := ""
    for (g, i) in p.globals.toList.zipIdx do
      let (c, rs, outs) ← blockC abi fres gtys "    " #[] [] g.body g.res
      let tys ← g.res.toList.mapM fun a => return (← creg rs a).2.1
      for (t, k) in tys.zipIdx do
        static s!"static {cTy t} g{i}_{k};\n"
        if isObj t then gdec := gdec ++ s!"  lean_dec(g{i}_{k});\n"
      gs := gs ++ "  {\n" ++ c ++ String.join ((outs.toList.zipIdx).map fun (x, k) => s!"    g{i}_{k} = {x};\n") ++ "  }\n"
      gtys := gtys.push tys.toArray
    let (c, _, _) ← blockC abi fres gtys "  " #[] [] p.main #[]
    let (_, protos, stat) ← get
    pure <| "/* generated by relc (Rel.Lang.EmitC): do not edit */\n" ++
      "#include <lean/lean.h>\n#include <errno.h>\n#include <stdio.h>\n#include <stdlib.h>\n#include <string.h>\n" ++
      "#include <unistd.h>\n\nlean_object *qlean_rt_io(lean_object *r, const char *sym);\n" ++
      "static inline lean_object *relc_box_nat(size_t n) { if (n > LEAN_MAX_SMALL_NAT) { " ++
      "fprintf(stderr, \"relc: the Nat %zu is past lean_box\\n\", n); exit(1); } return lean_box(n); }\n" ++
      "static inline size_t relc_unbox_nat(lean_object *o) { if (!lean_is_scalar(o)) { " ++
      "fputs(\"relc: a Nat past lean_box\\n\", stderr); exit(1); } return lean_unbox(o); }\n" ++ String.join protos ++
      "\n" ++ stat ++ "\n" ++ fns ++ "\nint main(int argc, char **argv) {\n" ++
      "  if (argc > 2) { fprintf(stderr, \"usage: %s [DIR]\\n\", argv[0]); return 2; }\n" ++
      "  if (argc == 2 && chdir(argv[1]) != 0) { fprintf(stderr, \"chdir %s: %s\\n\", argv[1], strerror(errno)); return 1; }\n" ++
      gs ++ c ++ gdec ++ "  return 0;\n}\n"
  go.run' (0, [], "")

end Rel.Lang.Plan
