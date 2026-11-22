import Rel.Run.Lang.Plan
import Rel.Run.Lang.Expand
import Rel.Kernel.Db.ObjectFile
import Rel.Kernel.Db.Csv
import Rel.Run.Lang.TmGen
import Rel.Lang.Table

/-! # `relc`: a plan printed as C (`doc/rel-native-design.md` §6, stage 1a)

The C has no plan interpreter: one line per instruction. A literal is a static Lean object with `m_rc = 0` (a
persistent object, never counted or freed), a kernel a direct call to its C symbol, `fail` a message and exit 1.
It is linked against qlean's `libqleankernel.a` and `qrt.o` (`rust/build.sh rt`), not against the Lean runtime. -/

namespace Rel.Lang.Plan

open Tab

/-- An `ownMap` answer: constructor `0`, its objects `domain`, `parts`, its scalars `code`, `attr`, `kind`, `count` in
    declaration order, which `Instr.sproj` reads. -/
instance : Reg Db.OwnFile := ⟨.obj, fun
  | .ctor 0 #[d, ps] #[c, a, k, n] => do
    pure ⟨← Reg.get? c, ← Reg.get? a, ← Reg.get? k, ← Reg.get? n, ← Reg.get? d, ← Reg.get? ps⟩
  | _ => none, fun f => .ctor 0 #[.str f.domain, .parts f.parts] #[.u8 f.code, .u8 f.attr, .u8 f.kind, .size f.count]⟩

/-- A CSV column's shape is an enum: its constructor index in a byte. -/
instance : Reg Db.CsvShape := ⟨.u8, fun | .u8 0 => some .atom | .u8 1 => some .null | .u8 2 => some .text | _ => none,
  fun s => .u8 s.ctorIdx.toUInt8⟩

/-- The kernels a plan may call, each read off its `@[extern]` declaration: the five of design §4, the IO exports of
    `crate/RELIO.txt` (the column files, the CSV reader and writer) and the toolchain's own arithmetic on sizes,
    bytes and buffers. -/
def abi : List Kernel :=
  [kernel% Rel.Kernel.kscan, kernel% Rel.Kernel.kscatter, kernel% Rel.Kernel.kgather, kernel% Rel.Kernel.kasc,
   kernel% Rel.Kernel.kseen, kernel% Rel.Db.ownWrite, kernel% Rel.Db.ownMap, kernel% Rel.Db.csvRead,
   kernel% Rel.Db.csvWrite, kernel% Rel.Db.pushPart, kernel% USize.decEq, kernel% UInt8.decEq,
   kernel% USize.add, kernel% USize.div, kernel% UInt64.toUSize, kernel% USize.toUInt64, kernel% ByteArray.usize]

def abiOf (sym : String) : Option Kernel := abi.find? (·.sym == sym)

/-! ### Writing a relation as a column directory -/

/-- `output R to dir`: each column of `R`'s registers written by `qlean_own_write` to `dir/key<path>` and
    `dir/val<path>`. The directory must exist; the kernel's error names the path when it does not. -/
def output (dir : String) (rs : Side × Side) : Bld Unit := do
  for (side, cs) in [("key", rs.1), ("val", rs.2)] do
    for (p, r) in cs do
      let path ← lit (.str (System.FilePath.mk dir / (side ++ p)).toString)
      discard <| call "qlean_own_write" (#[path] ++ r.extract 0 6) 0

/-- A computed atom column's six `output` registers: type `t`, `count` rows (a register), constructor `kind`
    (`Db.ownParts`'s numbering) whose parts are the registers `bs`, gathered by `pushPart` from the empty literal. -/
def colRegs (t : QAtomicType) (kind : UInt8) (count : Nat) (bs : Array Nat) : Bld (Array Nat) := do
  let ps ← bs.foldlM (fun ps b => call1 (kernel% Rel.Db.pushPart) #[ps, b]) (← lit (.parts #[]))
  return #[← lit (.u8 t.code.toUInt8), ← lit (.u8 0), ← lit (.u8 kind), count, ← lit (.str ""), ps]

/-- The `Enc` register `e` of `count` rows of type `t` as `output`'s six registers: a `foR` (what every kernel answers,
    design §4) handed over as the kind `Db.ownParts` gives it, its parts its two fields, so it is written as it is
    encoded. The tag and the kind are read off the constructor, so a renumbering of either reaches the plan. -/
def encRegs (t : QAtomicType) (count e : Nat) : Bld (Array Nat) := do
  let f : Enc := .foR .empty .empty
  let .ok (some (k, _)) := Db.ownParts f | throw "encRegs: `Db.ownParts` holds no `foR`"
  colRegs t k count #[← projB e f.ctorIdx 0 .bytes, ← projB e f.ctorIdx 1 .bytes]

/-- The atom columns of the object `A`, each with its path as `cols` names it under `p`, from the object alone. -/
def objCols : Obj → String → List (String × QAtomicType)
  | .atom t, p => [(p, t)]
  | .prod a b, p => objCols a (p ++ ".1") ++ objCols b (p ++ ".2")
  | .arr b, p => [(p ++ ".lo", .i64), (p ++ ".hi", .i64)] ++ objCols b (p ++ ".e")
  | .sum a b, p => [(p ++ ".tag", .u1), (p ++ ".idx", .i64)] ++ objCols a (p ++ ".l") ++ objCols b (p ++ ".r")

/-- Whether `A` is atoms and products only, the sides whose `Vals.cols` are their atom columns as they are. -/
def flatObj : Obj → Bool
  | .atom _ => true
  | .prod a b => flatObj a && flatObj b
  | _ => false

/-- **`Tab.canon`** (design §4: `asc → seen → gather`, as `Vals.nub` of the pair side) of the relation whose sides
    `s` are of the objects `A`, `B`: `kasc` over the key's atom columns then the value's, `kseen` on the sorted columns,
    the count `k` of runs (the last row's group `+ 1`: a `kscan max` fold of the groups, `0` at no row), `kgather` of
    the permutation at each run's first row, and every column gathered there. An array or a sum side (`cells` keys,
    summand gathers) and a column with no `Enc` register (mapped from its file) are refused, naming them. -/
def canonB (A B : Obj) (s : Side × Side) : Bld (Side × Side) := do
  unless flatObj A && flatObj B do throw "canon of an array or a sum side, whose `cells` keys no plan recipe builds yet"
  let col (sd : Side) (p : String) (t : QAtomicType) : Bld (String × QAtomicType × Nat × Nat) := do
    let some rs := sd.lookup p | throw s!"canon: column `{p}` has no registers (a positions column)"
    let (some n, some e) := (rs[3]?, rs[6]?) | throw s!"canon: column `{p}` has no `Enc` register (mapped from its file)"
    pure (p, t, n, e)
  let ks ← (objCols A "").mapM fun (p, t) => col s.1 p t
  let vs ← (objCols B "").mapM fun (p, t) => col s.2 p t
  let some (_, _, n, _) := (ks ++ vs).head? | throw "canon of a relation with no atom column"
  let key (t : QAtomicType) (e : Nat) : Bld Nat := do ctorB 0 #[← ctorB 0 #[] #[← lit (Reg.put t)], e] #[]
  let sp ← callK (kernel% Rel.Kernel.kasc) #[n, ← listB (← (ks ++ vs).mapM fun (_, t, _, e) => key t e)]
  let mut l ← nth sp 0 "kasc"
  let mut sorted := #[]
  for (_, t, _, _) in ks ++ vs do
    sorted := sorted.push (← key t (← projB l 1 0 .obj)); l ← projB l 1 1 .obj
  let kg ← callK (kernel% Rel.Kernel.kseen) #[n, ← listB sorted.toList]
  let z ← constB n (← lit (.u64 0))
  let mx ← nth (← scanB .max .i64 n (some z) [z, ← nth kg 1 "kseen"]) 1 "kscan"
  let k ← nth (← ite (← call1 (kernel% USize.decEq) #[n, ← lit (.size 0)]) (do pure #[← lit (.size 0)]) (do
    pure #[← call1 (kernel% USize.add) #[← call1 (kernel% UInt64.toUSize) #[← projB mx 1 0 .u64], ← lit (.size 1)]]))
    0 "if"
  let ix ← call1 (kernel% Rel.Kernel.kgather) #[k, ← nth kg 2 "kseen", n, ← nth sp 1 "kasc"]
  let side (cs : List (String × QAtomicType × Nat × Nat)) : Bld Side := cs.mapM fun (p, t, _, e) => do
    let g ← call1 (kernel% Rel.Kernel.kgather) #[k, ix, n, e]
    pure (p, (← encRegs t k g).push g)
  pure (← side ks, ← side vs)

/-- The registers of a term's value, key side then value side, its variables `σ` the registers of the tables bound
    to them (a run-time definition's inputs, `Once.binds`). Stage 1a builds a literal, a converse (`Tab.conv`: the
    sides swapped, then `canonB`), a shared term and a bound variable (I10); any other node is refused. -/
def ofTm (σ : List (Nat × Side × Side)) : {A B : Obj} → Tm A B → Bld (Side × Side)
  | _, _, .val R => return (← litSide R.key, ← litSide R.val)
  | A, B, .conv R => do canonB A B (← ofTm σ R).swap
  | _, _, .share _ R => ofTm σ R
  | _, _, .var _ k => match σ.lookup k with
    | some s => pure s
    | none => throw s!"variable {k}, which no input table is bound to"
  | _, _, _ => throw "a node other than a literal, a converse, a shared term or a variable: stage 1a builds only those"

/-- The plan's steps of `output x to dir` in the program `prog`, read after the programs `chain` (`Expand.read`). -/
def outputOf (chain : List (Lean.Name × Program)) (prog : Program) (x : String) (dir : String) :
    Lean.Meta.MetaM (Except String (Bld Unit)) := do
  let r ← (Expand.read (fun _ => none) chain prog).run
  return do
    let (ds, _) ← r.mapError (s!"{repr ·}")
    let some ⟨_, _, t⟩ := ds.lookup x | throw s!"`{x}` is no closed definition of the program"
    pure (do output dir (← ofTm [] t))

/-- The Lean side of the same output: `R`'s two sides written by the table writer under the names `output` gives
    them, from the value Lean computed, not from a plan. -/
def writeRel {A B : Obj} (dir : String) (R : Tab A B) : IO Unit := do
  Table.writeVals dir "key" R.key; Table.writeVals dir "val" R.val

/-! ### A program's IO statements (IO step I10): what `n.io` reads, computes and writes, as a plan -/

/-- Whether `A` holds a sum, whose CSV columns (`S+1`) `Table.ofCsv` regroups and checks, which no plan recipe does. -/
def hasSum : Obj → Bool
  | .atom _ => false
  | .prod a b => hasSum a || hasSum b
  | .arr b => hasSum b
  | .sum .. => true

/-- `Table.writeCols`' order of the columns of a schema reversed: the rest's, then the first. -/
def fieldsR : Schema → List (String × Obj)
  | [] => []
  | [f] => [f]
  | f :: g :: R => fieldsR (g :: R) ++ [f]

/-- Each atom column of a side of schema `S`, as `Table.write` names its file: its path in `S.obj` (`cols`), its file
    name (the column's name, then its path in the column's object), its atom. -/
def schemaCols (S : Schema) : List (String × String × QAtomicType) :=
  ((objCols S.obj "").zip ((fieldsR S.reverse).flatMap fun (n, A) => objCols A n)).map fun ((p, t), (q, _)) => (p, q, t)

/-- An input as its read at the input edge answers it: each atom column's path, atom and `ownMap` register (a table
    directory), or the atom columns of the side and `csvRead`'s list register (a CSV file). -/
inductive InRead
  | own (cs : List (String × QAtomicType × Nat))
  | csv (cs : List (String × QAtomicType)) (l : Nat)

/-- The input edge's reads of `input x : N ⟶ v from [csv] path` (`n.io`'s `Table.read`, `Table.readCsv`). A keyed
    input (`Table.readKeyed`) sorts its rows, a float column read from its file is checked canonical, a nullable CSV
    column is regrouped: no plan recipe does those, so each is refused, naming the input. -/
def readIn (x : String) (k v : Schema) (csv : Option Db.CsvCols) (path : String) : Bld InRead := do
  let no (why : String) : Bld InRead := throw s!"input `{x}` from \"{path}\": {why}, which no plan recipe does yet"
  unless k.isEmpty do return ← no "a keyed input, whose rows the read sorts (`Table.canon`)"
  match csv with
  | some cs =>
    if hasSum v.obj then return ← no "a nullable CSV column, whose parts the read regroups and checks (`Table.ofCsv`)"
    let rs ← callK (kernel% Rel.Db.csvRead) #[← lit (.str path), ← lit (Reg.put cs)]
    return .csv (objCols v.obj "") (← nth rs 1 "csvRead")
  | none => .own <$> (schemaCols v).mapM fun (p, q, t) => do
    if [QAtomicType.sym, .general, .f32, .f64].contains t then
      discard <| no s!"column `{q}` of type {repr t}, refused or checked by `Table.readArr`"
    return (p, t, ← call1 (kernel% Rel.Db.ownMap) #[← lit (.str (Table.file path q))])

/-- The side an input's read answered, in `main`: a CSV column's count and `Enc` taken off `csvRead`'s list, a
    mapped file's fields off `ownMap`'s answer, its type code and count checked as `Table.readArr`/`Table.same` check
    them (the attribute not taken over, the domain the empty one a vector has). -/
def sideOf (x : String) : InRead → Bld Side
  | .csv cs l => do
    let mut l := l
    let mut s : Side := []
    for (p, t) in cs do
      let cell ← projB l 1 0 .obj
      let (n, e) := (← projB cell 0 0 .size, ← projB cell 0 1 .obj)
      s := s ++ [(p, (← encRegs t n e).push e)]
      l ← projB l 1 1 .obj
    pure s
  | .own cs => do
    let mut s : Side := []
    let mut n₀ : Option Nat := none
    for (p, t, f) in cs do
      let sc (i : Nat) := emit1 (.sproj f 0 2 #[.u8, .u8, .u8, .size] i)
      let code ← lit (.u8 t.code.toUInt8)
      guard (← call1 (kernel% UInt8.decEq) #[← sc 0, code]) s!"input `{x}`: column `{p}` has another atom type code than {repr t}" #[]
      let n ← sc 3
      if let some m := n₀ then
        guard (← call1 (kernel% USize.decEq) #[n, m]) s!"input `{x}`: column `{p}` of another row count than the first" #[n, m]
      n₀ := some n
      s := s ++ [(p, #[code, ← lit (.u8 0), ← sc 2, n, ← lit (.str ""), ← projB f 0 1 .parts])]
    pure s

/-- `output x to [csv] path` of the table `s` (`n.io`'s `Table.write`, `writeKeyed`, `writeCsv`): key `k = []`, the
    value side only, its rows renumbered by their order; else `key/` and `val/` (a CSV file: the key's columns, then
    the value's). A positions column has no file and no CSV part, and a column mapped from its file has no `Enc` for
    the CSV writer: each is refused, naming the column. -/
def writeOut (x : String) (k v : Schema) (csv : Option Db.CsvCols) (path : String) (s : Side × Side) : Bld Unit := do
  let sides := if k.isEmpty then [(v, s.2, path)] else [(k, s.1, Table.file path "key"), (v, s.2, Table.file path "val")]
  let col (S : Schema) (side : Side) (p : String) : Bld (Array Nat) := match side.lookup p with
    | some r => pure r
    | none => throw s!"output `{x}` to \"{path}\": column `{p}` of {Schema.names S} is positions, which have no file"
  match csv with
  | none => for (S, side, dir) in sides do
      for (p, q, _) in schemaCols S do
        discard <| call "qlean_own_write" (#[← lit (.str (Table.file dir q))] ++ (← col S side p).extract 0 6) 0
  | some cs =>
    let mut es : List Nat := []
    let mut rows : Option Nat := none
    for (S, side, _) in sides do
      if hasSum S.obj then throw s!"output `{x}` to csv \"{path}\": a nullable CSV column, which no plan recipe writes yet"
      for (p, _, _) in schemaCols S do
        let r ← col S side p
        let (some m, some e) := (r[3]?, r[6]?)
          | throw s!"output `{x}` to csv \"{path}\": column `{p}` is mapped from its file, whose parts the plan holds as an array, not as the `Enc` `csvWrite` takes"
        rows := some m
        es := es ++ [← ctorB 0 #[m, e] #[]]
    let some n := rows | throw s!"output `{x}` to csv \"{path}\": no column"
    discard <| call "qlean_csv_write" #[← lit (.str path), ← lit (Reg.put cs), n, ← listB es] 0

/-- The plan of the IO statements of the program `prog`, read after the programs `chain` (`Expand.read`), as `n.io`
    runs them: the input edge reads the inputs the outputs reach (`Expand.ioReach`, `readIn`); `main` builds each
    run-time definition they reach on the tables of its run-time names (`ofTm`, its variables `Once.binds`), then
    writes each output (`writeOut`), a closed definition's from its term. -/
def ioOf (chain : List (Lean.Name × Program)) (prog : Program) :
    Lean.Meta.MetaM (Except String (Bld (List (String × InRead)) × (List (String × InRead) → Bld Unit))) := do
  let r ← (Expand.read (fun _ => none) chain prog).run
  return do
    let (ds, _, _, _, os, io) ← r.mapError (s!"{repr ·}")
    let reach := Expand.ioReach io
    let rd : Bld (List (String × InRead)) := io.filterMapM fun
      | .input x _ _ k v c p => if reach.contains x then return some (x, ← readIn x k v c p) else pure none
      | _ => pure none
    let wr (ins : List (String × InRead)) : Bld Unit := do
      let mut σ : List (String × Side × Side) := []
      for (x, r) in ins do σ := σ ++ [(x, [], ← sideOf x r)]
      for s in io do
        match s with
        | .defn x c deps =>
          if reach.contains x then
            let some o := os.find? (·.const == c) | throw s!"`{x}`: its constant `{c}` has no body here"
            let env ← (o.binds.zip deps).mapM fun (k, d) => match σ.lookup d with
              | some t => pure (k, t)
              | none => throw s!"`{x}` reads `{d}`, which is not read or computed before it"
            let ⟨_, _, t⟩ := o.res
            σ := σ ++ [(x, ← ofTm env t)]
        | .output x _ _ k v c p cl =>
          let t ← match cl, σ.lookup x with
            | none, some t => pure t
            | some _, _ => match ds.lookup x with
              | some ⟨_, _, t⟩ => ofTm [] t
              | none => throw s!"output `{x}`: no closed definition `{x}`"
            | none, none => throw s!"output `{x}`: not read or computed before it"
          writeOut x k v c p t
        | _ => pure ()
    pure (rd, wr)

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

/-- Where the Lean compiler puts each scalar field of a constructor of `nobj` object fields, in declaration order, with
    its type and size: a `size_t` one (size `0`) at its slot after the objects, every other at its byte offset after
    the objects and slots, by size, largest first, equal sizes in declaration order; and the end of the last byte. -/
def scalarLayout (nobj : Nat) (ss : List Ty) : Except String (List (Ty × Nat × Nat) × Nat) := do
  let ns ← ss.mapM fun t => match t with
    | .size => pure 0 | .u64 | .i64 => pure 8 | .u8 | .bit => pure 1
    | t => throw s!"a scalar field of type {repr t}, which no constructor holds unboxed"
  let cnt (k i : Nat) := ((ns.take i).filter (· == k)).length
  let base := 8 * (nobj + cnt 0 ns.length)
  let place (i n : Nat) := if n == 0 then nobj + cnt 0 i else if n == 8 then base + 8 * cnt 8 i
    else base + 8 * cnt 8 ns.length + cnt 1 i
  pure ((ss.zip ns).zipIdx.map fun ((t, n), i) => (t, n, place i n), base + 8 * cnt 8 ns.length + cnt 1 ns.length)

/-- The constructor object `x` of tag `tag`, from the C names `os` of its object fields (owned, each moved in) and
    `ss` of its scalar fields, laid out by `scalarLayout`; with no field it is `lean_box(tag)`. -/
def ctorC (x : String) (tag : Nat) (os ss : List (String × Ty)) : Except String String := do
  if os.isEmpty && ss.isEmpty then return s!"lean_object *{x} = lean_box({tag});\n"
  let (ps, end_) ← (scalarLayout os.length (ss.map (·.2))).mapError (s!"ctor {tag}: " ++ ·)
  let sets := String.join ((ss.zip ps).map fun ((y, _), (_, n, o)) =>
    if n == 0 then s!" lean_ctor_set_usize({x}, {o}, {y});" else s!" lean_ctor_set_uint{8 * n}({x}, {o}, (uint{8 * n}_t){y});")
  pure (s!"lean_object *{x} = lean_alloc_ctor({tag}, {os.length}, {end_ - 8 * os.length});" ++
    String.join (os.zipIdx.map fun ((y, t), i) => s!" lean_ctor_set({x}, {i}, {cBox t y});") ++ sets ++ "\n")

/-- The registers an instruction reads that were defined before register `base` (an `if`'s first result): a nested
    block's own registers are numbered from `base` on, so its reads below `base` are the outer ones. -/
partial def reads (base : Nat) : Instr → List Nat
  | .call _ as | .fail _ as | .apply _ as => as.toList
  | .ite c t rt e re => c :: ((t.flatMap (reads base) ++ rt.toList ++ e.flatMap (reads base) ++ re.toList).filter (· < base))
  | .ctor _ os ss => os.toList ++ ss.toList
  | .proj x .. | .sproj x .. => [x]
  | .lit _ | .global _ => []

/-- How many registers an instruction defines. -/
def defs (abi : String → Option Kernel) (fres : Array (Array Ty)) (gtys : Array (Array Ty)) : Instr → Except String Nat
  | .lit _ => pure 1
  | .call sym _ => match abi sym with | some k => pure k.res.size | none => throw s!"no kernel `{sym}` in the ABI table"
  | .fail .. => pure 0
  | .apply f _ => match fres[f]? with | some t => pure t.size | none => throw s!"apply f{f}: no earlier function"
  | .global g => match gtys[g]? with | some t => pure t.size | none => throw s!"global g{g}: no earlier global"
  | .ite _ _ rt _ _ => pure rt.size
  | .ctor .. | .proj .. | .sproj .. => pure 1

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
    | .sproj r tag nobj ss i =>
      let (y, ty, _) ← creg rs r
      unless ty == .obj do throw s!"sproj reads register {r}, a {repr ty}, not a constructor"
      let (ps, _) ← scalarLayout nobj ss.toList
      let some (t, sz, o) := ps[i]? | throw s!"sproj r{r}.{i}: a constructor of {ss.size} scalar fields"
      let x ← fresh
      c := c ++ s!"{ind}if (lean_obj_tag({y}) != {tag}) \{ fprintf(stderr, \"plan: sproj r{r}.{i} reads constructor %u, " ++
        s!"not {tag}\\n\", lean_obj_tag({y})); exit(1); }\n"
      c := c ++ s!"{ind}{cTy t} {x} = ({cTy t})" ++
        (if sz == 0 then s!"lean_ctor_get_usize({y}, {o});\n" else s!"lean_ctor_get_uint{8 * sz}({y}, {o});\n")
      rs := rs.push (x, t, true)
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
        -- the answer (an `IO` read's value, `qlean_rt_io` having failed the run on its error) is an object: an `Except`'s `error` fails the run as `Plan.run` does, its registers are fields
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
    -- the input edge's registers are `main`'s first, so the two are one block (`Plan.exec` splices them likewise)
    let (c, _, _) ← blockC abi fres gtys "  " #[] [] (p.input ++ p.main) #[]
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
