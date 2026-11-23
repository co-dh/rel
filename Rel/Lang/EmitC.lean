module

public import Rel.Run.Lang.Plan
public import Rel.Run.Lang.Expand
public import Rel.Kernel.Db.ObjectFile
public import Rel.Kernel.Db.Csv
public import Rel.Run.Lang.TmGen
public import Rel.Lang.Table

-- exposed: every def body is a spec a downstream `rfl`/`decide`/`simp` may unfold (PLAN W.8)
@[expose] public section

/-! # `relc`: a plan printed as C (`doc/rel-native-design.md` §6, stage 1a)

The C has no plan interpreter: one line per instruction. A literal is a static Lean object with `m_rc = 0` (a
persistent object, never counted or freed), a kernel a direct call to its C symbol, `fail` a message and exit 1.
It is linked against qlean's `libqleankernel.a` and `qrt.o` (`rust/build.sh rt`), not against the Lean runtime. -/

namespace Rel.Lang.Plan

open Tab

/-- An `ownMap` answer: constructor `0`, its object `parts`, its scalars `code`, `kind`, `count` in
    declaration order, which `Instr.sproj` reads. -/
instance : Reg Db.OwnFile := ⟨.obj, fun
  | .ctor 0 #[ps] #[c, k, n] => do
    pure ⟨← Reg.get? c, ← Reg.get? k, ← Reg.get? n, ← Reg.get? ps⟩
  | _ => none, fun f => .ctor 0 #[.parts f.parts] #[.u8 f.code, .u8 f.kind, .size f.count]⟩

/-- A CSV column's shape is an enum: its constructor index in a byte. -/
instance : Reg Db.CsvShape := ⟨.u8, fun | .u8 0 => some .atom | .u8 1 => some .null | .u8 2 => some .text | .u8 3 => some .opt | _ => none,
  fun s => .u8 s.ctorIdx.toUInt8⟩

/-- The kernels a plan may call, each read off its `@[extern]` declaration: the five of design §4, the IO exports of
    `crate/RELIO.txt` (the column files, the CSV reader and writer) and the toolchain's own arithmetic on sizes,
    bytes and buffers. -/
def abi : List Kernel :=
  [kernel% Rel.Kernel.kscan, kernel% Rel.Kernel.kscatter, kernel% Rel.Kernel.kgather, kernel% Rel.Kernel.kasc,
   kernel% Rel.Kernel.kseen, kernel% Rel.Kernel.kbitrows, kernel% Rel.Db.ownWrite, kernel% Rel.Db.ownMap, kernel% Rel.Db.csvRead,
   kernel% Rel.Db.csvWrite, kernel% Rel.Db.pushPart, kernel% USize.decEq, kernel% UInt8.decEq,
   kernel% USize.add, kernel% USize.sub, kernel% USize.mul, kernel% USize.decLt, kernel% USize.div, kernel% UInt64.toUSize, kernel% USize.toUInt64, kernel% ByteArray.usize]

def abiOf (sym : String) : Option Kernel := abi.find? (·.sym == sym)

/-! ### Writing a relation as a column directory -/

/-- A computed atom column's `output` registers (`Side.regs`): type `t`, `count` rows (a register), constructor `kind`
    (`Db.ownParts`'s numbering) whose parts are the registers `bs`, gathered by `pushPart` from the empty literal. -/
def colRegs (t : QAtomicType) (kind : UInt8) (count : Nat) (bs : Array Nat) : Bld (Array Nat) := do
  let ps ← bs.foldlM (fun ps b => call1 (kernel% Rel.Db.pushPart) #[ps, b]) (← lit (.parts #[]))
  return Side.regs (← lit (.u8 t.code.toUInt8)) (← lit (.u8 kind)) count ps

/-- The `Enc` register `e` of `count` rows of type `t` as `output`'s registers: a `foR` (what every kernel answers,
    design §4) handed over as the kind `Db.ownParts` gives it, its parts its two fields, so it is written as it is
    encoded. The tag and the kind are read off the constructor, so a renumbering of either reaches the plan. -/
def encRegs (t : QAtomicType) (count e : Nat) : Bld (Array Nat) := do
  let f : Enc := .foR .empty .empty
  let .ok (some (k, _)) := Db.ownParts f | throw "encRegs: `Db.ownParts` holds no `foR`"
  colRegs t k count #[← projB e f.ctorIdx 0 .bytes, ← projB e f.ctorIdx 1 .bytes]

/-- The files of the object `A`, each with its path as `cols` names it under `p`, from the object alone: an atom column
    with its atom (`some`), a side of `1` (`none`). -/
def objLeaves : Obj → String → List (String × Option QAtomicType)
  | .atom t, p => [(p, some t)]
  | .prod a b, p => objLeaves a (p ++ ".1") ++ objLeaves b (p ++ ".2")
  | .arr b, p => [(p ++ ".lo", some .i64), (p ++ ".hi", some .i64)] ++ objLeaves b (p ++ ".e")
  -- the one representation function of a sum side, chosen by the object: in-band (`Obj.band`) it is one nullable column
  | .sum a b, p => match Obj.band a b with
    | some t => [(p, some t)]
    | none => (p ++ ".tag", some .u1) :: (objLeaves a (p ++ ".l") ++ objLeaves b (p ++ ".r"))
  -- a side of `1` has a file of its own (kind `oneKind`: its count, no part), and no atom
  | .one, p => [(p, none)]

/-- The atom columns of `objLeaves`. -/
def objCols (A : Obj) (p : String) : List (String × QAtomicType) := (objLeaves A p).filterMap fun (q, t) => t.map (q, ·)


/-! ### A term's table as a plan: the `GenK` recipe of each `Tm` node on the five kernels (design §4) -/

/-- A column of a side as the plan holds it, node for node as `Vals`: an atom column (its path as `cols` names it, its
    atom, its `Enc` register); an `arr` side (its path; its payload's row count `m`, a `size` register; `lo`, `hi`,
    `Enc` registers of `i64`; its payload's columns, `m` rows); a `sum` side `A+B` not in band (`Obj.band`): its two
    payloads' row counts `l`, `r` (size registers), the tag (`u1`) and position (`i64`) `Enc` registers, the payloads'
    columns. A sum in band (`1+t`) is the atom column `Opt t n`, its null inside the encoding: an `atom`, as `ValsB.cols`
    keys it. A product side is its two sides' columns one after the other (`Cols`), in `objCols` order. -/
inductive Col where
  | atom (p : String) (t : QAtomicType) (e : Nat)
  | arr (p : String) (m lo hi : Nat) (pay : List Col)
  | sum (p : String) (tag : Nat) (x y : List Col)
  deriving Inhabited

/-- A side's columns. -/
abbrev Cols := List Col

/-- The recipes' refusal of a `sum` side no recipe reads yet (so far: a list or sum inside an `asc` key's
    summand, a summand `1`); `what` names the recipe. -/
def sumB {α : Type} (what : String) : Bld α :=
  throw s!"{what} on a sum side (tag, idx, two payloads): no plan recipe reads it yet"

/-- The number of `Col`s of a side of `A`: a product's two sides', none for `1` (`objCols`), else one. -/
def objWidth : Obj → Nat
  | .prod a b => objWidth a + objWidth b
  | .one => 0
  | _ => 1

/-- A table in registers: its row count (a `size`), its key's and value's columns. -/
structure TabB where
  n : Nat
  key : Cols
  val : Cols
  deriving Inhabited

/-- `colMap op` (one `kscan` pass, every row a segment) of the `n` rows of `a`, `b` read at `s`, written at `t`. -/
def mapB (op : Kernel.Op) (n a b : Nat) (t : QAtomicType := .i64) (s : QAtomicType := .i64)
    (pre post : List (Kernel.Op × UInt64) := []) : Bld Nat := do
  nth (← callK (kernel% Rel.Kernel.kscan) #[← lit (Reg.put op), ← lit (.bit false), ← lit (Reg.put s), ← lit (Reg.put t),
    n, ← ctorB 0 #[] #[], ← listB [← srcB n a, ← srcB n b], ← lit (Reg.put pre), ← lit (Reg.put post)]) 0 "kscan"

/-- `colConst n w`: `n` cells of the word `w`. -/
def wordsB (n : Nat) (w : UInt64) : Bld Nat := do constB n (← lit (.u64 w))

/-- `kscatter op` of the `rows` words `x` to the cells `dst` of `cells`, the others `fill`. -/
def scatterB (op : Kernel.Op) (rows dst x cells : Nat) (fill : UInt64 := 0) : Bld Nat := do
  call1 (kernel% Rel.Kernel.kscatter) #[← lit (Reg.put op), rows, dst, x, cells, ← lit (.u64 fill)]

/-- `kgather` of the `n`-row column `x` at the `m` rows `ix`. -/
def gatherB (m ix n x : Nat) : Bld Nat := call1 (kernel% Rel.Kernel.kgather) #[m, ix, n, x]

/-- The positions `0, 1, …`, the `Enc` of every length. -/
def posB : Bld Nat := lit (Reg.put (Ext.Enc.pos : Enc))

/-- The last word of an `n`-row `kscan`'s fold `fold`, plus `d`, as a size; `0` at `n = 0`, where no row is folded
    (`lastCount`). -/
def lastB (n fold : Nat) (d : USize) : Bld Nat := do
  nth (← ite (← call1 (kernel% USize.decEq) #[n, ← lit (.size 0)]) (do pure #[← lit (.size 0)]) (do
    pure #[← call1 (kernel% USize.add) #[← call1 (kernel% UInt64.toUSize) #[← projB fold 1 0 .u64], ← lit (.size d)]]))
    0 "if"

/-- The registers of the columns `cs`, a loop's state: an atom's `Enc`; an array's `m`, `lo`, `hi`, its payload's. -/
partial def regsOf (cs : Cols) : Bld (List Nat) := return (← cs.mapM fun
  | .atom _ _ e => pure [e]
  | .arr _ m lo hi f => return [m, lo, hi] ++ (← regsOf f)
  | .sum _ tag x y => return [tag] ++ (← regsOf x) ++ (← regsOf y)).flatten

/-- The columns `cs` with their registers taken in order from `rs` (`regsOf`'s inverse), and the registers left. -/
partial def withRegs (cs : Cols) (rs : List Nat) : Bld (Cols × List Nat) :=
  cs.foldlM (init := (([] : Cols), rs)) fun (acc, rs) c => match c, rs with
    | .atom p t _, e :: rs => pure (acc ++ [.atom p t e], rs)
    | .arr p _ _ _ f, m :: lo :: hi :: rs => do let (f, rs) ← withRegs f rs; pure (acc ++ [.arr p m lo hi f], rs)
    | .sum p _ x y, tag :: rs => do
      let (x, rs) ← withRegs x rs; let (y, rs) ← withRegs y rs; pure (acc ++ [.sum p tag x y], rs)
    | _, _ => throw "a loop's state: fewer registers than its columns read"

/-- The types of `regsOf cs`: an `Enc` an object, an array's count a size. -/
partial def tysOf (cs : Cols) : Bld (List Ty) := return (← cs.mapM fun
  | .atom .. => pure [Ty.obj]
  | .arr _ _ _ _ f => return [.size, .obj, .obj] ++ (← tysOf f)
  | .sum _ _ x y => return [Ty.obj] ++ (← tysOf x) ++ (← tysOf y)).flatten

/-- The registers an instruction reads that were defined before register `base` (an `if`'s first result): a nested
    block's own registers are numbered from `base` on, so its reads below `base` are the outer ones. -/
partial def reads (base : Nat) : Instr → List Nat
  | .call _ as | .readOpt _ as _ | .fail _ as | .apply _ as => as.toList
  | .ite c t rt e re => c :: ((t.flatMap (reads base) ++ rt.toList ++ e.flatMap (reads base) ++ re.toList).filter (· < base))
  | .ctor _ os ss => os.toList ++ ss.toList
  | .proj x .. | .sproj x .. | .part x _ => [x]
  | .lit _ | .global _ => []
  | .loop k init b out d _ => k :: init.toList ++ ((b.flatMap (reads base) ++ out.toList ++ [d]).filter (· < base))

/-- `i` with each register `a` it names read as `f a`: blocks share one register space, so nested ones move alike. -/
partial def Instr.rename (f : Nat → Nat) : Instr → Instr
  | .lit v => .lit v
  | .call s as => .call s (as.map f)
  | .readOpt s as d => .readOpt s (as.map f) d
  | .fail m as => .fail m (as.map f)
  | .apply g as => .apply g (as.map f)
  | .global g => .global g
  | .ite c t rt e re => .ite (f c) (t.map (·.rename f)) (rt.map f) (e.map (·.rename f)) (re.map f)
  | .ctor tag os ss => .ctor tag (os.map f) (ss.map f)
  | .proj x tag i t => .proj (f x) tag i t
  | .sproj x tag nobj ss i => .sproj (f x) tag nobj ss i
  | .part x i => .part (f x) i
  | .loop k init b out d msg => .loop (f k) (init.map f) (b.map (·.rename f)) (out.map f) (f d) msg

/-- The type the block `is` reads the outer register `a` as: the declared type of the first reader's argument, a
    kernel's (`abiOf`) or a function's of `fs`; an `if`'s bit, a `loop`'s cap, a `proj`'s constructor. -/
partial def useTy (fs : Array Fun) (a : Nat) : List Instr → Option Ty
  | [] => none
  | i :: is => (match i with
    | .call s as | .readOpt s as _ => (as.toList.idxOf? a).bind fun j => (abiOf s).bind (·.args[j]?.map (·.1))
    | .apply g as => (as.toList.idxOf? a).bind fun j => fs[g]?.bind (·.params[j]?)
    | .ite c t _ e _ => if c == a then some .bit else useTy fs a t <|> useTy fs a e
    | .proj x .. | .sproj x .. => if x == a then some .obj else none
    | .part x _ => if x == a then some .parts else none
    | .loop k _ b .. => if k == a then some .size else useTy fs a b
    | _ => none) <|> useTy fs a is

/-- The number of registers the instruction `i` defines, `fs` and `gs` the plan's functions and globals. -/
def resN (fs gs : Array Fun) : Instr → Nat
  | .lit _ | .ctor .. | .proj .. | .sproj .. | .part .. => 1
  | .fail .. => 0
  | .call s _ => (abiOf s).elim 0 (·.res.size)
  | .readOpt _ _ d => d.size
  | .apply g _ => (fs[g]?).elim 0 (·.res.size)
  | .global g => (gs[g]?).elim 0 (·.res.size)
  | .ite _ _ rt _ _ => rt.size
  | .loop _ init .. => init.size

/-- The type of register `a` as the instruction defining it declares it, in the block `is` numbered from `base`
    (`pre` the registers before it): a literal's, a kernel's or a function's result, a field read. -/
partial def defTy (fs gs : Array Fun) (pre : Nat → Option Ty) (base : Nat) (is : List Instr) (a : Nat) : Option Ty :=
  if a < base then pre a else match is with
  | [] => none
  | i :: is =>
    let funTy (F : Fun) (j : Nat) : Option Ty := F.res[j]?.bind (defTy fs gs (F.params[·]?) F.params.size F.body)
    let j := a - base
    if j < resN fs gs i then match i with
      | .lit v => some v.ty
      | .ctor .. => some .obj
      | .proj _ _ _ t => some t
      | .sproj _ _ _ ss k => ss[k]?
      | .part .. => some .bytes
      | .fail .. => none
      | .call s _ | .readOpt s _ _ => (abiOf s).bind (·.res[j]?)
      | .apply g _ => (fs[g]?).bind (funTy · j)
      | .global g => (gs[g]?).bind (funTy · j)
      | .ite _ t rt _ _ => rt[j]?.bind (defTy fs gs pre base t)
      | .loop _ init .. => init[j]?.bind pre
    else defTy fs gs (defTy fs gs pre base [i]) (base + resN fs gs i) is a

/-- `b` on parameters of the types `tys` as a plan function, applied to `args`; `b` answers its result registers,
    their types and a value `α` (the answer's shape): a recipe built at many nodes is one C function, not a copy
    inlined at each (which outgrows `cc -O2`). A function whose body equals an earlier one's is that one, so each
    table shape builds one function. Closure conversion: the body is built after the enclosing scope's `n` registers,
    and those it reads (a variable's table, a cap) become parameters after `tys`, first read first, typed as their
    reader declares (`useTy`) or, one only answered, as its result slot, so `b` may close over anything in scope. -/
def funB {α : Type} (tys : List Ty) (args : List Nat) (b : List Nat → Bld (Array Nat × List Ty × α)) :
    Bld (Array Nat × α) := do
  let (is, n, fs, gs) ← get
  let k := tys.length
  unless args.length == k do throw s!"a function of {k} parameters applied to {args.length} registers"
  let ((r, rtys, x), body, m, fs, gs) ← (b (List.range' n k)).run (#[], n + k, fs, gs)
  -- a body of at most one instruction holding no block is spliced in place: its `apply` costs as much
  let flat : Instr → Bool := fun | .ite .. | .loop .. => false | _ => true
  if body.all flat && body.size ≤ 1 then
    let g (a : Nat) : Nat := if a < n then a else if a < n + k then args.getD (a - n) a else a - k
    set (is ++ body.map (·.rename g), m - k, fs, gs); return (r.map g, x)
  let cs := ((body.toList.flatMap (reads n) ++ r.toList).filter (· < n)).eraseDups
  -- a register no reader types is typed by its definition in the enclosing block
  let dty := defTy fs gs (fun _ => none) (n - (is.toList.map (resN fs gs)).sum) is.toList
  let ctys ← cs.mapM fun a => match useTy fs a body.toList <|> (r.toList.idxOf? a).bind (rtys[·]?) <|> dty a with
    | some t => pure t
    | none => throw s!"a function's body reads the enclosing register r{a}, but no instruction declares its type"
  let f (a : Nat) : Nat := if a < n then k + cs.idxOf a else if a < n + k then a - n else a - n + cs.length
  let F : Fun := ⟨(tys ++ ctys).toArray, body.toList.map (·.rename f), r.map f⟩
  let (g, fs) := match fs.findIdx? (· == F) with | some i => (i, fs) | none => (fs.size, fs.push F)
  set (is, n, fs, gs)
  return (← apply g (args ++ cs).toArray r.size, x)

/-- `funB` on tables: each `T` of `Ts` passed as its count, then `regsOf`, and the answer a table likewise. -/
def funT (Ts : List TabB) (b : List TabB → Bld TabB) : Bld TabB := do
  let regs (T : TabB) : Bld (List Nat) := return T.n :: (← regsOf (T.key ++ T.val))
  let tysT (T : TabB) : Bld (List Ty) := return Ty.size :: (← tysOf (T.key ++ T.val))
  let shape (Ts : List TabB) (rs : List Nat) : Bld (List TabB) := do
    let (Us, _) ← Ts.foldlM (init := (([] : List TabB), rs)) fun (Us, rs) T => match rs with
      | n :: rs => do
        let (cs, rs) ← withRegs (T.key ++ T.val) rs
        pure (Us ++ [⟨n, cs.take T.key.length, cs.drop T.key.length⟩], rs)
      | [] => throw "a function's parameters: fewer registers than its tables read"
    pure Us
  let (rs, U) ← funB (← Ts.mapM tysT).flatten (← Ts.mapM regs).flatten fun ps => do
    let U ← b (← shape Ts ps); pure ((← regs U).toArray, ← tysT U, U)
  match ← shape [U] rs.toList with
  | [V] => pure V
  | _ => throw "a function's answer: not one table"

/-- A step of `main` (an output: its sides and writes) as one plan function (`funB`), so `main` is one `apply` per
    step and holds none of the step's registers. -/
def mainStepB (b : Bld Unit) : Bld Unit := discard <| funB [] [] fun _ => do b; pure (#[], [], ())

/-- `funT` of a recipe on the `n` values `X` (a leaf on demand's), and on the tables `Ts`. -/
def funV (n : Nat) (X : Cols) (Ts : List TabB) (b : Nat → Cols → List TabB → Bld TabB) : Bld TabB :=
  funT (⟨n, X, []⟩ :: Ts) fun
    | T :: Ts => b T.n T.key Ts
    | [] => throw "a function on values: no table"

/-- `b` on the columns `xs` (each with its row count) as a plan function (`funT`), answering one column and its count:
    a table recipe calls it once per column, so the recipe's body no longer inlines each column's kernels, and each
    column kind (atom type, array of a payload shape) builds one function shared by every table holding it. -/
def funC (xs : List (Nat × Col)) (b : List (Nat × Col) → Bld (Nat × Col)) : Bld Col := do
  let one (T : TabB) : Bld (Nat × Col) := match T.key with
    | [c] => pure (T.n, c)
    | _ => throw "a column function: not one column"
  let T ← funT (xs.map fun (n, c) => ⟨n, [c], []⟩) fun Ts => do
    let (m, c) ← b (← Ts.mapM one); pure ⟨m, [c], []⟩
  pure (← one T).2

/-- `funV` of a recipe on a count `n` and the `n`-row words `ws`, answering a size (a count, or a fold's last word)
    and words. -/
def funW (n : Nat) (ws : List Nat) (b : Nat → List Nat → Bld (Nat × List Nat)) : Bld (Nat × List Nat) := do
  let words (cs : Cols) : Bld (List Nat) := cs.mapM fun | .atom _ _ e => pure e | _ => throw "words: not an atom column"
  let T ← funV n (ws.map (.atom "" .i64 ·)) [] fun n cs _ => do
    let (m, xs) ← b n (← words cs); pure ⟨m, xs.map (.atom "" .i64 ·), []⟩
  pure (T.n, ← words T.key)

/-- `colPrefix op`: the running fold of the `n` words `a` from `0` (one segment), and its last word (`lastB`); one
    plan function (`funW`). -/
def prefixB (op : Kernel.Op) (n a : Nat) : Bld (Nat × Nat) := do
  let (l, [P]) ← funW n [a] fun n ws => do
      let [a] := ws | throw "prefix: not one column"
      let z ← wordsB n 0
      let r ← scanB op .i64 n (some z) [z, a]
      pure (← lastB n (← nth r 1 "kscan") 0, [← nth r 0 "kscan"])
    | throw "prefix: not one column"
  pure (P, l)

/-- The `n`-row columns `cs` at the `m` rows `ix` (`ValsB.gather`): an array's `lo` and `hi` gathered, its payload
    kept; a sum's tags and positions gathered, its two payloads kept. -/
partial def gatherCols (m ix n : Nat) (cs : Cols) : Bld Cols := cs.mapM fun c => funC [(n, c)] fun
  | [(n, .atom p t e)] => return (m, .atom p t (← gatherB m ix n e))
  | [(n, .arr p c lo hi f)] => return (m, .arr p c (← gatherB m ix n lo) (← gatherB m ix n hi) f)
  -- dense sum: the tag and both summand columns are `n` rows (`ValsB.gather`), so all three are gathered
  | [(n, .sum p tag x y)] => return (m, .sum p (← gatherB m ix n tag) (← gatherCols m ix n x) (← gatherCols m ix n y))
  | _ => throw "gather: not one column"

mutual
/-- The `kasc` key of the `n`-row column `c` (`ValsB.cols`), an `AscKey` register and its column: an atom column its
    words at its atom; an `arr` side one `cells` key over its `lo`, `hi` and its payload's keys, its column the
    positions, row `i` naming cell `i`. A sum has several keys (`keysB`), so no one. -/
partial def keyB (n : Nat) : Col → Bld (Nat × Nat)
  | .atom _ t e => return (← ctorB 0 #[] #[← lit (Reg.put t)], e)
  | .arr _ m lo hi f => do
    let els ← (← f.mapM (keysB m)).flatten.mapM fun (k, e) => ctorB 0 #[k, e] #[]
    return (← ctorB 1 #[lo, hi, ← listB els] #[n, m], ← posB)
  | .sum .. => sumB "a list's cell key of"

/-- The keys of the column `c` (`ValsB.cols`' list): one, or for a sum its tag, then the left summand's keys gathered at
    `idx · ¬tag`, then the right's at `idx · tag` (`Vals.summandCols`). A summand of no rows has no keys there; its
    positions would read outside it, so there the keys are zeros, which ties every row as no key does. -/
partial def keysB (n : Nat) : Col → Bld (List (Nat × Nat))
  | .sum _ tag x y => do
    let ks (c : Cols) : Bld (List (Nat × Nat)) := return (← c.mapM (keysB n)).flatten
    return (← ctorB 0 #[] #[← lit (Reg.put QAtomicType.u1)], tag) :: ((← ks x) ++ (← ks y))
  | c => return [← keyB n c]
end

/-- `kseen` over the `n` rows, in `kasc` order, of the columns `es` (each an `AscKey` beside its column, one register):
    the count `k` of runs of equal rows (the last row's group `+ 1`, a `kscan max` fold), each row's group `g`, each
    run's first row `f`. -/
def seenB (n : Nat) (es : List Nat) : Bld (Nat × Nat × Nat) := do
  let kg ← callK (kernel% Rel.Kernel.kseen) #[n, ← listB es]
  let g ← nth kg 1 "kseen"
  let z ← wordsB n 0
  pure (← lastB n (← nth (← scanB .max .i64 n (some z) [z, g]) 1 "kscan") 1, g, ← nth kg 2 "kseen")

/-- `kasc ≫ kseen` over the `n` rows of the columns `cs`: the count `k` of runs of equal rows (the last row's group
    `+ 1`, a `kscan max` fold), each sorted row's group `g`, each run's first sorted row `f`, the permutation `p`. -/
def ascSeenB (n : Nat) (cs : Cols) : Bld (Nat × Nat × Nat × Nat) := do
  let T ← funV n cs [] fun n cs _ => do
    let (k, g, f, p) ← ascSeenOnB n cs; pure ⟨k, [.atom "" .i64 g, .atom "" .i64 f, .atom "" .i64 p], []⟩
  let [.atom _ _ g, .atom _ _ f, .atom _ _ p] := T.key | throw "asc: not three columns"
  pure (T.n, g, f, p)
where ascSeenOnB (n : Nat) (cs : Cols) : Bld (Nat × Nat × Nat × Nat) := do
  let ks := (← cs.mapM (keysB n)).flatten
  let sp ← callK (kernel% Rel.Kernel.kasc) #[n, ← listB (← ks.mapM fun (k, e) => ctorB 0 #[k, e] #[])]
  let mut l ← nth sp 0 "kasc"
  let mut sorted := #[]
  for (k, _) in ks do
    sorted := sorted.push (← ctorB 0 #[k, ← projB l 1 0 .obj] #[]); l ← projB l 1 1 .obj
  let (k, g, f) ← seenB n sorted.toList
  pure (k, g, f, ← nth sp 1 "kasc")

/-- **`Vals.nub`**: the `n` rows of `cs` without duplicates, ascending: each run's first input row (`kgather` of
    `p` at `f`), every column gathered there. One plan function per shape of `cs` (`funT`). -/
def nubB (n : Nat) (cs : Cols) : Bld (Nat × Cols) := do
  let T ← funV n cs [] fun n cs _ => do
    let (k, _, f, p) ← ascSeenB n cs; pure ⟨k, ← gatherCols k (← gatherB k f n p) n cs, []⟩
  pure (T.n, T.key)

/-- **`Tab.canon`**: `nubB` of the pair side, the key's columns then the value's. -/
def canonT (T : TabB) : Bld TabB := do
  let (k, cs) ← nubB T.n (T.key ++ T.val)
  pure ⟨k, cs.take T.key.length, cs.drop T.key.length⟩

/-- **`Tab.dom`** of the side `cs` of `n` rows (`Tab.ran` of the value side, `Tab.idU`): `nubB`, each row paired with
    itself. -/
def coreflB (n : Nat) (cs : Cols) : Bld TabB := do let (k, cs) ← nubB n cs; pure ⟨k, cs, cs⟩

/-- **`catPlan`**: the count `n₁ + n₂` and the cells `off` (`n₁ + pos`) of the second part's rows. -/
def catB (n₁ n₂ : Nat) : Bld (Nat × Nat) := do
  pure (← call1 (kernel% USize.add) #[n₁, n₂],
    ← mapB .add n₂ (← posB) (← constB n₂ (← call1 (kernel% USize.toUInt64) #[n₁])))

/-- A `size` register as a `u64` word. -/
def u64B (s : Nat) : Bld Nat := call1 (kernel% USize.toUInt64) #[s]

/-- **`Opt.concat`**, `Arr.concat`: ONE `kscan .first` stream of the `n₁` words `x` then the `n₂` words `y` (`n` rows),
    which re-encodes them block by block and carries each row's null flag, so a null stays in-band. -/
def catColB (t : QAtomicType) (n n₁ n₂ x y : Nat) : Bld Nat := do
  nth (← callK (kernel% Rel.Kernel.kscan) #[← lit (Reg.put Kernel.Op.first), ← lit (.bit false), ← lit (Reg.put t),
    ← lit (Reg.put t), n, ← ctorB 0 #[] #[], ← listB [← srcB n₁ x, ← srcB n₂ y],
    ← lit (Reg.put ([] : List (Kernel.Op × UInt64))), ← lit (Reg.put ([] : List (Kernel.Op × UInt64)))]) 0 "kscan"

/-- **`Arr.shift`**: the `n` words `x`, `s` added (`s` a `size` register). -/
def shiftB (n x s : Nat) : Bld Nat := do mapB .add n x (← constB n (← u64B s))

/-- `nth` of an `if`'s one register. -/
def ite1 (c : Nat) (t e : Bld Nat) : Bld Nat := do nth (← ite c (return #[← t]) (return #[← e])) 0 "if"

/-- `c ∧ d`, `d` built only in the branch where `c` holds. -/
def andB (c : Nat) (d : Bld Nat) : Bld Nat := ite1 c d (lit (.bit false))

/-- **`ValsB.concat`** into `n` rows, the two sides' columns paired by position (one object, one `objCols` order):
    atom columns by `catColB`; an array's payloads joined (`catB`, the recursive call) and its `lo`, `hi` as they are
    (`0 ≤ lo ≤ hi ≤ m`, `Vals.WF`), the second's shifted past the first (`shiftB`); a sum's tags joined, its positions
    `0 … n-1`, each summand by `catSummandB`. -/
partial def concatB (n n₁ n₂ off : Nat) (xs ys : Cols) : Bld Cols :=
  (xs.zip ys).mapM fun (x, y) => funC [(n₁, x), (n₂, y)] fun
    | [(n₁, x), (n₂, y)] => return (n, ← concatColB n n₁ n₂ off x y)
    | _ => throw "concat: not two columns"
where
  concatColB (n n₁ n₂ off : Nat) : Col → Col → Bld Col
    -- dense sum: the tags and both summand columns are `n₁`, `n₂` rows, so each is joined as any column (nulls stay in-band)
    | .sum p tag₁ x₁ y₁, .sum _ tag₂ x₂ y₂ => do
      return .sum p (← catColB .u1 n n₁ n₂ tag₁ tag₂) (← concatB n n₁ n₂ off x₁ x₂) (← concatB n n₁ n₂ off y₁ y₂)
    | .atom p t x, .atom _ _ y => return .atom p t (← catColB t n n₁ n₂ x y)
    | .arr p m₁ lo₁ hi₁ f₁, .arr _ m₂ lo₂ hi₂ f₂ => do
      let (m, o) ← catB m₁ m₂
      guard (← call1 (kernel% USize.decLt) #[m, ← lit (.size (2 ^ 63))]) "concat: payload rows m₁ + m₂ past an Int64 bound"
        #[m₁, m₂]
      let b (x₁ x₂ : Nat) : Bld Nat := do catColB .i64 n n₁ n₂ x₁ (← shiftB n₂ x₂ m₁)
      return .arr p m (← b lo₁ lo₂) (← b hi₁ hi₂) (← concatB m m₁ m₂ o f₁ f₂)
    | .sum .., _ | _, .sum .. => sumB "∪"
    | _, _ => throw "concat: two sides of one object with columns of different shapes"

/-- **`R ∪ S`** (`Tab.union`): `Tab.canon` of the concatenation. -/
def unionB (R S : TabB) : Bld TabB := funT [R, S] fun
  | [R, S] => do
    let (n, off) ← catB R.n S.n
    canonT ⟨n, ← concatB n R.n S.n off R.key S.key, ← concatB n R.n S.n off R.val S.val⟩
  | _ => throw "∪: not two tables"

/-- **`groupFold`**: per group of the `n` sorted rows (`m` groups `g`, first rows `f`), `op` folded over `x` from `z`
    within its run (a segmented `kscan`), the run's last row scattered to its group. -/
def groupFoldB (op : Kernel.Op) (n g f m : Nat) (z : UInt64) (x : Nat) : Bld Nat := do
  let (_, [o]) ← funW n [g, x] fun n ws => do
      let [g, x] := ws | throw "groupFold: not two columns"
      let seg ← scatterB .last m f (← wordsB m 1) n
      let o ← nth (← scanB op .i64 n (some seg) [← wordsB n z, x]) 0 "kscan"
      pure (m, [← scatterB .last n g o m z])
    | throw "groupFold: not one column"
  pure o

/-- **`Tab.select`** (`∩`, `−`): the concatenation tagged by source (`1` at `S`'s rows), its groups of equal rows
    (`ascSeenB`), per group the `and` and the `or` of the tags, `keep` of the two, and the kept groups' first input
    rows gathered (`whereB`). -/
def selectB (keep : Nat → Nat → Nat → Bld Nat) (R S : TabB) : Bld TabB := funT [R, S] fun
  | [R, S] => do
    let (n, off) ← catB R.n S.n
    let tag ← scatterB .last S.n off (← wordsB S.n 1) n
    let ks ← concatB n R.n S.n off R.key S.key
    let vs ← concatB n R.n S.n off R.val S.val
    let (m, g, f, p) ← ascSeenB n (ks ++ vs)
    let ts ← gatherB n p n tag
    let mn ← groupFoldB .and n g f m 1 ts
    let mx ← groupFoldB .or n g f m 0 ts
    let (k, sel) ← whereB m (← keep m mn mx)
    let ix ← gatherB k (← gatherB k sel m f) n p
    pure ⟨k, ← gatherCols k ix n ks, ← gatherCols k ix n vs⟩
  | _ => throw "select: not two tables"

/-- **`expand`** of the `K` widths `w`: the count `T` of output rows, each row's group `G` and offset `u` in it. -/
def expandB (K w : Nat) : Bld (Nat × Nat × Nat) := do
  let (T, [G, u]) ← funW K [w] fun K ws => do
      let [w] := ws | throw "expand: not one column"
      let (P, T) ← prefixB .add K w
      let T1 ← call1 (kernel% USize.add) #[T, ← lit (.size 1)]
      let o ← mapB .sub K P w
      let G ← gatherB T (← posB) T1 (← prefixB .max T1 (← scatterB .max K o (← posB) T1)).1
      pure (T, [G, ← mapB .sub T (← posB) (← gatherB T G K o)])
    | throw "expand: not two columns"
  pure (T, G, u)

/-- **`cellSpan`**: the `n` cells `lo`, `hi` clamped to a payload of `m` rows, `[s, e)`. -/
def spanB (n m lo hi : Nat) : Bld (Nat × Nat) := do
  let (_, [s, e]) ← funW n [lo, hi] fun n ws => do
      let [lo, hi] := ws | throw "cellSpan: not two columns"
      let s ← mapB .max n lo (← wordsB n 0)
      pure (n, [s, ← mapB .max n (← mapB .min n hi (← constB n (← u64B m))) s])
    | throw "cellSpan: not two columns"
  pure (s, e)

/-- **`Tab.compGroups`**: the `N` rows of `R.val` then `S.key`, their permutation `p`, groups `g`, first rows `f`, the
    count `K` of groups, per group the counts `cR`, `cS` and the width `w = cR · cS`. -/
def groupsB (R S : TabB) : Bld (Nat × Nat × Nat × Nat × Nat × Nat × Nat × Nat) := do
  let (N, off) ← catB R.n S.n
  let (K, g, f, p) ← ascSeenB N (← concatB N R.n S.n off R.val S.key)
  -- the counts on words alone, one plan function (`funW`) whatever the tables' shapes
  let (_, [cR, cS, w]) ← funW N [g, p] fun N ws => do
      let [g, p] := ws | throw "compGroups: not two columns"
      let nR ← constB N (← call1 (kernel% USize.toUInt64) #[R.n])
      let cR ← scatterB .add N g (← mapB .lt N p nR) K
      let cS ← mapB .sub K (← scatterB .add N g (← wordsB N 1) K) cR
      pure (K, [cR, cS, ← mapB .mul K cR cS])
    | throw "compGroups: not three columns"
  pure (N, p, g, f, K, cR, cS, w)

/-- **`R ≫ S`** (`Tab.compOne`): the groups of equal middle values of `R.val` then `S.key` (`kasc` is stable, so a
    group's `R` rows come first), per group the counts `cR`, `cS` and the width `w = cR · cS`, EXPAND of `w` (each
    output row's group `G` and offset `u`), its `R` row `p[f + u / cS]` and `S` row `p[f + cR + u % cS] - n`, both
    sides gathered there, then `canonT`. `Tab.comp`'s blocks past `blockRows` and its bit matrices change no answer. -/
def compFromB (R S : TabB) (x : Nat × Nat × Nat × Nat × Nat × Nat × Nat × Nat) : Bld TabB := do
  let (N, p, _, f, K, cR, cS, w) := x
  -- the rows of each side on words alone, one plan function (`funW`) whatever the tables' shapes
  let (T, [iR, iS]) ← funW K [f, cR, cS, w] fun K ws => do
      let [f, cR, cS, w] := ws | throw "compOne: not four columns"
      let (T, G, u) ← expandB K w
      let ft ← gatherB T G K f
      let ct ← gatherB T G K cS
      let iR ← gatherB T (← mapB .add T ft (← mapB .div T u ct)) N p
      let qS ← mapB .add T (← mapB .add T ft (← gatherB T G K cR)) (← mapB .mod T u ct)
      pure (T, [iR, ← mapB .sub T (← gatherB T qS N p) (← constB T (← call1 (kernel% USize.toUInt64) #[R.n]))])
    | throw "compOne: not two columns"
  canonT ⟨T, ← gatherCols T iR R.n R.key, ← gatherCols T iS S.n S.val⟩

/-- `compFromB` on `groupsB R S`. -/
def compB (R S : TabB) : Bld TabB := funT [R, S] fun
  | [R, S] => do compFromB R S (← groupsB R S)
  | _ => throw "comp: not two tables"

/-- **`Vals.cross`** of `n` rows `xs` and `m` rows `ys` (`crossIx`): `T = n · m` rows, `xs` at `pos / m`, `ys` at
    `pos % m`. Its two checks first, as `Vals.cross` and `crossIx` make them: `n · m ≤ crossMax` (tested as
    `crossMax / m < n`, so no product wraps), then `n · m + m < 2^63`; `fail` appends the counts to the message. -/
def crossB (n m : Nat) (xs ys : Cols) : Bld (Nat × Cols × Cols) := do
  let past ← nth (← ite (← call1 (kernel% USize.decEq) #[m, ← lit (.size 0)]) (do pure #[← lit (.bit false)]) (do
    pure #[← call1 (kernel% USize.decLt) #[← call1 (kernel% USize.div) #[← lit (.size crossMax.toUSize), m], n]])) 0 "if"
  discard <| ite past (do
    discard <| emit (.fail (s!"cross: values of the left object by values of the right, past the bound {crossMax} " ++
      "pairs: a relation on two whole objects (`≤`, `<`, `⊤`) read where nothing bounds it to fewer pairs; meet it " ++
      "with a table (`T ∩ ≤` tests T's pairs only) or compose a smaller table on each side (`K ≤ L`)") #[n, m]) 0
    pure #[]) (pure #[])
  let T ← call1 (kernel% USize.mul) #[n, m]
  guard (← call1 (kernel% USize.decLt) #[m, ← call1 (kernel% USize.sub) #[← lit (.size (2 ^ 63)), T]])
    "cross: rows past 2^63 or USize, n × m" #[n, m]
  let c ← constB T (← call1 (kernel% USize.toUInt64) #[m])
  pure (T, ← gatherCols T (← mapB .div T (← posB) c) n xs, ← gatherCols T (← mapB .mod T (← posB) c) m ys)

/-- The columns `cs` of a side of `A`, under the paths `A`'s side has at `pre` (`cols`). -/
partial def repath (A : Obj) (pre : String) (cs : Cols) : Bld Cols := match A, cs with
  | .atom _, [.atom _ t e] => pure [.atom pre t e]
  | .prod a b, cs => return (← repath a (pre ++ ".1") (cs.take (objWidth a))) ++
      (← repath b (pre ++ ".2") (cs.drop (objWidth a)))
  | .arr b, [.arr _ m lo hi f] => return [.arr pre m lo hi (← repath b (pre ++ ".e") f)]
  | .one, [] => pure []
  | .sum a b, cs => match Obj.band a b, cs with
    | some t, [.atom _ _ e] => pure [.atom pre t e]
    | none, [.sum _ tag x y] => do
      pure [.sum pre tag (← repath a (pre ++ ".l") x) (← repath b (pre ++ ".r") y)]
    | _, cs => throw s!"{cs.length} columns where a side of {repr A} is read"
  | _, cs => throw s!"{cs.length} columns where a side of {repr A} is read"

/-- **`⟨R, S⟩`** (`Tab.pair`): `⟨(a, b), a⟩` on `R`'s rows composed with `S`, each key `(a, b)` rebracketed to `a`
    beside `(b, c)`. -/
def pairB (A B C : Obj) (R S : TabB) : Bld TabB := do
  let T ← compB ⟨R.n, (← repath A ".1" R.key) ++ (← repath B ".2" R.val), R.key⟩ S
  let a := objWidth A
  pure ⟨T.n, ← repath A "" (T.key.take a), (← repath B ".1" (T.key.drop a)) ++ (← repath C ".2" T.val)⟩


/-- **`Vals.none`**: a side of `A` at `p` with no row: each atom column `Arr.zeros t 0`, an array's `lo`, `hi` the
    same over a payload of no row; `z` the register of the count `0`. -/
partial def noneB (z : Nat) (A : Obj) (p : String := "") : Bld Cols := match A with
  | .atom t => do let c ← wordsB z 0; return [.atom p t (← mapB .add z c c t)]
  | .prod a b => return (← noneB z a (p ++ ".1")) ++ (← noneB z b (p ++ ".2"))
  | .arr b => do
    let c ← wordsB z 0
    return [.arr p z (← mapB .add z c c) (← mapB .add z c c) (← noneB z b (p ++ ".e"))]
  -- a side of `1` stores no column (`objCols`)
  | .one => return []
  | .sum a b => match Obj.band a b with
    | some t => noneB z (.atom t) p
    | none => do
      let c ← wordsB z 0
      return [.sum p (← mapB .add z c c .u1) (← noneB z a (p ++ ".l")) (← noneB z b (p ++ ".r"))]

/-- **`Opt.nuls`**: `n` nulls of a band column, the `kgather` of one flagged zero word (the encoding `Opt.nuls` writes
    for one row) at `n` zero indices; a null is a value to `kgather`, its flag moving with its word. -/
def nulsB (n : Nat) : Bld Nat := do
  gatherB n (← wordsB n 0) (← lit (.size 1)) (← lit (Reg.put (Kernel.wordsFoR #[0] (Kernel.nulMap #[1]) : Enc)))

/-- **`Vals.zeros`**: `n` rows of `A` all in-band null, the filler of the rows a dense summand does not own: `nulsB` per atom
    column; an `arr` side `n` null cells over no payload; a band sum `n` nulls; another sum tag `0` over two such summands. -/
partial def zerosB (n : Nat) (A : Obj) (p : String) : Bld Cols := match A with
  -- Lean's `Opt.fill .general` is `.gen default`, a form native `Enc` has none of (nor the own format): refuse, never
  -- write a different filler that a Lean read of the same file would not equal
  | .atom .general => throw s!"column `{p}`: a general atom has no native filler (Lean's `Opt.fill` writes `.gen default`)"
  | .atom t => return [.atom p t (← nulsB n)]
  | .prod a b => return (← zerosB n a (p ++ ".1")) ++ (← zerosB n b (p ++ ".2"))
  | .arr b => do
    let z ← lit (.size 0)
    return [.arr p z (← nulsB n) (← nulsB n) (← noneB z b (p ++ ".e"))]
  | .one => return []
  | .sum a b => match Obj.band a b with
    | some t => return [.atom p t (← nulsB n)]
    | none => return [.sum p (← mapB .first n (← posB) (← posB) .u1 .i64 [] [(.and, 0), (.or, 0)])
        (← zerosB n a (p ++ ".l")) (← zerosB n b (p ++ ".r"))]

/-- **`inl`/`inr` on the `n` values `X`** (`Tab.inl`, `Tab.inr`, `s` the right one): row `k` is `X`'s row `k` beside the
    summand's row `k`, canonical. In band the `inr` side is `X` as it is (`Vals.optInr`), the `inl ()` side `n` nulls
    (`nulsB`). Else the tag is `s` in every row (`tagCol`: the positions through `[(.and, 0), (.or, s)]` at `u1`), `X`
    the owned summand as it is (`Vals.lift`) and the other `n` null rows (`zerosB`). -/
def injB (A B : Obj) (s : Bool) (n : Nat) (X : Cols) : Bld TabB := do
  match Obj.band A B with
  | some t =>
    canonT ⟨n, X, ← if s then repath B "" X else do pure [.atom "" t (← nulsB n)]⟩
  | none =>
    let tag ← mapB .first n (← posB) (← posB) .u1 .i64 [] [(.and, 0), (.or, if s then 1 else 0)]
    if s then canonT ⟨n, X, [.sum "" tag (← zerosB n A ".l") (← repath B ".r" X)]⟩
    else canonT ⟨n, X, [.sum "" tag (← repath A ".l" X) (← zerosB n B ".r")]⟩

/-- A side's columns of the object `A` at the path `p`: each atom column's `Enc` register; a positions column, which
    has no registers (`litSide`), the positions; an array's `lo`, `hi` and payload, its row count a payload column's
    `count`. A column mapped from its file (no `Enc`) is refused, naming it. -/
partial def colsOf (A : Obj) (s : Side) (p : String := "") : Bld Cols := match A with
  | .atom t => match s.lookup p with
    | none => return [.atom p t (← posB)]
    | some rs => match rs[Side.enc]? with
      | some e => pure [.atom p t e]
      | none => throw s!"column `{p}` has no `Enc` register (a literal that is no vector)"
  | .prod a b => return (← colsOf a s (p ++ ".1")) ++ (← colsOf b s (p ++ ".2"))
  | .arr b => do
    let reg (q : String) (i : Nat) : Option Nat := (s.lookup q).bind (·[i]?)
    let some m := (objCols b (p ++ ".e")).findSome? (reg ·.1 Side.count)
      | throw s!"array `{p}`: no payload column holds a row count register"
    let (some lo, some hi) := (reg (p ++ ".lo") Side.enc, reg (p ++ ".hi") Side.enc)
      | throw s!"array `{p}`: its bounds have no `Enc` register"
    return [.arr p m lo hi (← colsOf b s (p ++ ".e"))]
  | .one => return []
  | .sum a b => match Obj.band a b with
    | some t => colsOf (.atom t) s p
    | none => do
      let reg (q : String) (i : Nat) : Option Nat := (s.lookup q).bind (·[i]?)
      let some tag := reg (p ++ ".tag") Side.enc | throw s!"sum `{p}`: its tag column has no `Enc` register"
      return [.sum p tag (← colsOf a s (p ++ ".l")) (← colsOf b s (p ++ ".r"))]

/-- The row count of a table's sides: a column's `count` register. -/
def countOf (s : Side × Side) : Bld Nat := match (s.1 ++ s.2).findSome? (·.2[Side.count]?) with
  | some n => pure n
  | none => throw "a table whose every column is positions, so no register holds its row count"

/-- The `n`-row columns `cs` as `output` takes them, in `cols` order: an atom column's registers; an array's `lo`,
    `hi`, then its payload's columns at its count `m`. -/
partial def flatB (n : Nat) (cs : Cols) : Bld Side := return (← cs.mapM fun
  | .atom p t e => return [(p, (← encRegs t n e).push e)]
  | .arr p m lo hi f => return [(p ++ ".lo", (← encRegs .i64 n lo).push lo), (p ++ ".hi", (← encRegs .i64 n hi).push hi)]
      ++ (← flatB m f)
  | .sum p tag x y => return (p ++ ".tag", (← encRegs .u1 n tag).push tag) :: ((← flatB n x) ++ (← flatB n y))).flatten

/-- A `TabB`'s sides as `output` takes them: each column's registers (`encRegs`), then its `Enc`. -/
def sidesOf (T : TabB) : Bld (Side × Side) := do pure (← flatB T.n T.key, ← flatB T.n T.val)

/-- What a node's context knows of its sides (design §0 `Known`): the values of its domain and of its range, each a
    count and columns, and the pairs a meet hands it (`GenK.bound`). -/
structure Dom where
  dom : Option (Nat × Cols) := none
  ran : Option (Nat × Cols) := none
  pairs : Option TabB := none
  deriving Inhabited

/-- The values a leaf on demand reads, or `GenK.ofVals`' error where they are unknown. -/
def known (what : String) : Option (Nat × Cols) → Bld (Nat × Cols)
  | some d => pure d
  | none => throw s!"{what}: a leaf on demand ran with its domain unknown"

/-- `T`'s domain values (`Tab.dom`'s side), the bound `GenK.bound` hands the other operand of `∩`, `−`, `⟨,⟩`. -/
def domOf (T : TabB) : Bld (Nat × Cols) := nubB T.n T.key

/-- `GenK.bound`'s context of `T`: its two sides' values and `T` itself as the pairs (`∩`, `−`). -/
def boundOf (T : TabB) : Bld Dom := return ⟨some (← domOf T), some (← nubB T.n T.val), some T⟩

/-- Two operands `r`, `s` in the context `D`, as `GenK.meetK`/`pairK` order them: the one not on demand first, the
    context `ctx` of its table bounding the other where that one runs on demand. -/
def bothB (r s : Dom → Bld TabB) (dr ds : Bool) (D : Dom) (ctx : TabB → Bld Dom) : Bld (TabB × TabB) := do
  if dr && !ds then let t ← s D; pure (← r (← ctx t), t)
  else
    let t ← r D
    pure (t, ← s (← if ds then ctx t else pure D))

/-- **`R ∩ S`** (`Tab.inter`): `Tab.select` keeping the groups of a row of each. -/
def interB (R S : TabB) : Bld TabB := selectB (fun m mn mx => mapB .lt m mn mx) R S

/-- The check `Vals.pack`, `Tab.mem`, `Tab.map` make before reading `n` cells over `m` elements signed:
    `n · m + n + m < 2^63`, on size registers as `n, m < 2^63` and `(n + 1) · (m + 1) ≤ 2^63`, the last tested as
    `¬ 2^63 / (m + 1) < n + 1` (no sum or product wraps); else `fail` with `what` and the two counts. -/
def cellsBoundB (what : String) (n m : Nat) : Bld Unit := do
  let c ← lit (.size (2 ^ 63))
  let one ← lit (.size 1)
  let ok ← andB (← call1 (kernel% USize.decLt) #[n, c]) do andB (← call1 (kernel% USize.decLt) #[m, c]) do
    let q ← call1 (kernel% USize.div) #[c, ← call1 (kernel% USize.add) #[m, one]]
    ite1 (← call1 (kernel% USize.decLt) #[q, ← call1 (kernel% USize.add) #[n, one]]) (lit (.bit false)) (lit (.bit true))
  guard ok s!"{what}: n cells × m elements past 2^63, n · m + n + m" #[n, m]

/-- **`Vals.pack`** of the `n`-row columns `cs`: each array's payload cut to the elements its cells read where at most
    half of it is read (`0 < m`, `2 · T ≤ m`, `T` the summed widths): the widths EXPANDed, the payload gathered there,
    laid out one cell after another (`Vals.cells`); else kept. Nested payloads the same. -/
partial def packB (n : Nat) (cs : Cols) : Bld Cols := cs.mapM fun
  | c@(.atom ..) => pure c
  | .arr p m lo hi f => do
    cellsBoundB "pack" n m
    let (s, e) ← spanB n m lo hi
    let w ← mapB .sub n e s
    let (P, T) ← prefixB .add n w
    let keep : Bld (Array Nat) := do pure (← regsOf [.arr p m lo hi (← packB m f)]).toArray
    let cut : Bld (Array Nat) := do
      let (T', G, u) ← expandB n w
      let g ← gatherCols T' (← mapB .add T' (← gatherB T' G n s) u) m f
      pure (← regsOf [.arr p T' (← mapB .sub n P w) (← mapB .add n P (← wordsB n 0)) (← packB T' g)]).toArray
    let wide ← call1 (kernel% USize.decLt) #[m, ← call1 (kernel% USize.add) #[T, T]]
    let rs ← ite (← call1 (kernel% USize.decEq) #[m, ← lit (.size 0)]) keep (ite wide keep cut)
    match ← withRegs [.arr p m lo hi f] rs.toList with
    | ([c], _) => pure c
    | _ => throw "pack: an array's registers read as no one column"
  | .sum p tag x y => return .sum p tag (← packB n x) (← packB n y)

/-- **`Tab.pack`**: both sides' payloads cut (`packB`). -/
def packT (T : TabB) : Bld TabB := funT [T] fun
  | [T] => return ⟨T.n, ← packB T.n T.key, ← packB T.n T.val⟩
  | _ => throw "pack: not one table"

/-- **`Tab.fixOn`**: rounds of `step` from `X` (`Plan.loop`, the state its count and columns), at most the register
    `k` of them, until a round leaves the row count as it was; that round's table. `k` rounds with the count still
    moving fail with `msg`. Each round's table has its payloads cut (`packT`). One plan function (`funT`), `step`'s
    reads of the scope its parameters. -/
def fixB (msg : String) (step : TabB → Bld TabB) (k : Nat) (X : TabB) : Bld TabB := funT [X] fun
  | [X] => do
    let st (T : TabB) : Bld (Array Nat) := return #[T.n] ++ (← regsOf (T.key ++ T.val)).toArray
    let shape (rs : Array Nat) : Bld TabB := do
      let (cs, _) ← withRegs (X.key ++ X.val) (rs.toList.drop 1)
      pure ⟨← nth rs 0 "loop", cs.take X.key.length, cs.drop X.key.length⟩
    shape (← loop k (← st X) msg fun rs => do
      let X ← shape rs
      let Y ← packT (← step X)
      pure (← st Y, ← call1 (kernel% USize.decEq) #[Y.n, X.n]))
  | _ => throw "a fixed point: not one table"

/-- **`Tab.nu`**: rounds `X ↦ X ∩ f(X)` from `top` made canonical, its row count plus two of them. -/
def nuB (f : TabB → Bld TabB) (top : TabB) : Bld TabB := do
  let T ← canonT top
  fixB "Tab.nu: the row count still moved at the rows of top + 2 rounds" (fun X => do interB X (← f X))
    (← call1 (kernel% USize.add) #[T.n, ← lit (.size 2)]) T

/-- **`Tab.mu`**: rounds `X ↦ X ∪ f(X)` from `Z` (`𝟘`), at most the register `k` of them. -/
def muB (msg : String) (k : Nat) (f : TabB → Bld TabB) (Z : TabB) : Bld TabB :=
  fixB msg (fun X => do unionB X (← f X)) k Z

/-- A round count `c` as a `size` literal; past a `size`, refused rather than wrapped. -/
def sizeB (c : Nat) : Bld Nat := do
  unless c < USize.size do throw s!"a cap of {c} rounds, past a size"
  lit (.size c.toUSize)

/-- The `Enc` of a one-column side. -/
def col1 (cs : Cols) : Bld Nat := match cs with
  | [.atom _ _ e] => pure e
  | _ => throw s!"a side of {cs.length} columns where an atom's one column is read"

/-- **`Tab.keep`**: the rows of `T` whose `0`/`1` word in `b` is `1` (`whereB`), both sides gathered there. -/
def keepB (T : TabB) (b : Nat) : Bld TabB := do
  let (k, sel) ← whereB T.n b
  pure ⟨k, ← gatherCols k sel T.n T.key, ← gatherCols k sel T.n T.val⟩

/-- **`wideCol`**: the `n` words of `a` read at `t` through `widen t`, `a` itself where the chain is empty. -/
def wideB (t : QAtomicType) (n a : Nat) : Bld Nat :=
  if (widen t).isEmpty then pure a else mapB .first n a a .i64 t (widen t)

/-- A step's error as the plan's refusal, with its message. -/
def ofExc {α : Type} : Except String α → Bld α
  | .ok a => pure a
  | .error e => throw e

open Rel.Kernel in
/-- **`stepColsAt`**: the value verb `k` at `t` on the `n` operand rows `a`, `b`, its answer and keep flag; at `i64`
    `stepCols`' compares, at a float atom `fstepArr` (one pass by `fverbOne`, else `fverbBy` on the widened columns,
    each pass a `mapB`) and `nanFlag`. -/
def stepB (t : QAtomicType) (k : UInt8) (n a b : Nat) : Bld (Nat × Nat) := do
  let m (o : Kernel.Op) (x y : Nat) : Bld Nat := mapB o n x y
  match t with
  | .i64 =>
    let nul ← wordsB n nulWord
    let z ← wordsB n 0
    let ne (x : Nat) : Bld Nat := m .ne x nul
    let both ← m .and (← ne a) (← ne b)
    if k == Ew.add || k == Ew.sub then
      let w ← m (if k == Ew.add then .add else .sub) a b
      let ord ← if k == Ew.add then m .le a w else m .le w a
      let ex ← m .eq (← m .ge b z) ord
      pure (w, ← m .and (← m .and both (← ne w)) ex)
    else if k == Ew.mul then
      let w ← m .mul a b
      let a0 ← m .eq a z
      let ex ← m .or (← m .eq (← m .div w (← m .or a a0)) b) a0
      pure (w, ← m .and (← m .and both (← ne w)) ex)
    else if k == Ew.idiv || k == Ew.imod then
      let b0 ← m .eq b z
      let w ← m (if k == Ew.idiv then .div else .mod) a (← m .or b b0)
      pure (w, ← m .and (← m .and both (← m .not b0 b0)) (← ne w))
    else if k == Ew.greater || k == Ew.lesser then
      let w ← m (if k == Ew.greater then .max else .min) a b
      pure (w, ← ne w)
    else throw s!"arith: verb code {k} is none of + - * div mod max min"
  | .f32 | .f64 =>
    let w ← match fverbOne k with
      | some (o, c) => mapB o n a b t t (widen t) (c ++ [(.fto t, 0)])
      | none => do
        -- `fverbBy`'s composition run on builders: a part it reads twice is built twice, the same words
        let r ← ofExc (fverbBy (fun o (x y : Bld Nat) => pure do mapB o n (← x) (← y)) k (wideB t n a) (wideB t n b))
        let r ← r
        mapB (.fto t) n r r t
    pure (w, ← mapB .first n w w .u1 .i64 [] [(.ne, nulWord)])
  | t => throw s!"arith on objects of {repr t}: no value verb"

/-- **`K ≫ o ≫ L`** (`GenK.cmp`) on `U`'s universe, `u` its table in a context: each side `dom U` cut to the values
    the context knows of it (`cmpSide`, its message where nothing bounds it), then the pairs a meet hands it cut to
    the two sides, else CROSS of them (`Tab.cmpOn`), the rows whose widened words pass `o` kept (`Tab.cmpPairs`). -/
def cmpB (u : Dom → Bld TabB) (op : String) (o : Except String Kernel.Op) (t : QAtomicType) (D : Dom) : Bld TabB := do
  let o ← ofExc o
  let side (w : String) (s : Option (Nat × Cols)) : Bld (Nat × Cols) := do
    let U ← try u { dom := s } catch e => throw (if s.isSome then e else
      s!"{op} on an unbounded object: nothing bounds its {w} side; compose it with a table on that side ({e})")
    let d ← coreflB U.n U.key
    match s with
    | none => pure (d.n, d.key)
    | some (n, X) => do let c ← compB (← coreflB n X) d; pure (c.n, c.key)
  let k ← side "left" D.dom
  let l ← side "right" D.ran
  let T ← match D.pairs with
    | some p => do compB (← compB (← coreflB k.1 k.2) p) (← coreflB l.1 l.2)
    | none => do let (T, x, y) ← crossB k.1 l.1 k.2 l.2; canonT ⟨T, x, y⟩
  keepB T (← mapB o T.n (← wideB t T.n (← col1 T.key)) (← wideB t T.n (← col1 T.val)))

/-- **`Tab.floatOp s`** on the values `X` of `A` (`floatDen`): `fmapCols` of the row's `Op` from `A`'s float atom (each
    component's, for a row reading two) to `B`'s number atom, each value to its answer, kept where it is a word of
    `B`'s atom; `Tab.floatOp`'s errors at the objects it refuses. -/
def floatOpB (s : String) (A B : Obj) (n : Nat) (X : Cols) : Bld TabB := do
  let fmap (t u : QAtomicType) (o : Kernel.Op) (a b : Nat) : Bld TabB := do
    let w ← mapB o n a b u t (widen t) [(.ofF64 u, 0)]
    keepB ⟨n, X, [.atom "" u w]⟩ (← mapB .first n w w .u1 .i64 [] [(.ne, nulWord)])
  match floatOps.lookup s, A, B with
  | some (o, _), .atom t, .atom u =>
    if o.readsAcc = false ∧ (t = .f32 ∨ t = .f64) ∧ u.storeFmt?.isSome then do let x ← col1 X; fmap t u o x x
    else throw s!"{s} runs from a float object to a number object, found {repr t} to {repr u}"
  | some (o, _), .prod (.atom t) (.atom t'), .atom u =>
    if o.readsAcc = true ∧ t = t' ∧ (t = .f32 ∨ t = .f64) ∧ u.storeFmt?.isSome then do
      let (some (Col.atom _ _ x), some (Col.atom _ _ y)) := (X[0]?, X[1]?)
        | throw s!"{s}: a pair side of {X.length} columns, not of two atoms"
      fmap t u o x y
    else throw s!"{s} runs from a pair of one float object to a number object, found {repr t}×{repr t'} to {repr u}"
  | some _, _, _ => throw s!"{s} runs from a float object, or a pair of one, to a number object"
  | none, _, _ => throw s!"{s}: no float verb"

/-- **`Tab.cast`** (`$`) on the values `X` of `A`: each value to the word of `B`'s atom holding its number, kept where
    that is not `nulWord`. -/
def castB (A B : Obj) (n : Nat) (X : Cols) : Bld TabB := match A, B with
  | .atom s, .atom t => do
    unless QAtomicType.castOK s t do throw s!"$: no cast from {repr s} to {repr t}"
    let x ← col1 X
    let w ← mapB (.cast s t) n x x t
    keepB ⟨n, X, [.atom "" t w]⟩ (← mapB .ne n w (← wordsB n nulWord))
  | _, _ => throw "$: casts a number object to a number object"

/-- **`Tab.asc`** of `P : B ⟶ B`: `canon` of the rows `(0, b)`, `b` a key of `P`, keyed by their positions. -/
def ascB (B : Obj) (P : TabB) : Bld TabB := do
  if let some t := B.ascBad then
    throw s!"asc: elements of type {repr t} have no order code (a symbol or a general atom): number a set of numbers"
  let U ← canonT ⟨P.n, [.atom "" .i64 (← wordsB P.n 0)], P.key⟩
  pure ⟨U.n, [.atom "" .i64 (← posB)], U.val⟩

/-- The one array column of a side of `[B]`, or the error naming `what` reads it. -/
def arrCol (what : String) : Cols → Bld (Nat × Nat × Nat × Cols)
  | [.arr _ m lo hi f] => pure (m, lo, hi, f)
  | cs => throw s!"{what}: a side of {cs.length} columns where one array side is read"

/-- **`Tab.mem`** (`∋`) on the arrays `X` (`n` rows): EXPAND of the clamped widths `e - s`, the key the cell `X[G]`,
    the value the payload at `s[G] + u`; then `canonT`. -/
def memB (B : Obj) (n : Nat) (X : Cols) : Bld TabB := funV n X [] fun n X _ => do
  let (m, lo, hi, f) ← arrCol "∋" X
  cellsBoundB "mem" n m
  let (s, e) ← spanB n m lo hi
  let (T, G, u) ← expandB n (← mapB .sub n e s)
  canonT ⟨T, ← gatherCols T G n X, ← repath B "" (← gatherCols T (← mapB .add T (← gatherB T G n s) u) m f)⟩

/-! #### `R \ S` and `R / S` (`GenK.ldiv`, `GenK.rdiv`: `Tab.ldivSel`) -/

/-- The size register `x` as a word. -/
def wordOf (x : Nat) : Bld Nat := call1 (kernel% USize.toUInt64) #[x]

/-- **`Vals.code`**: the `n` rows of `cs` numbered by value (`ascSeenB`): the count `k`, each input row's number
    (`kscatter .last` of the groups through `p`), each number's first input row. -/
def codeB (n : Nat) (cs : Cols) : Bld (Nat × Nat × Nat) := do
  let (k, g, f, p) ← ascSeenB n cs
  pure (k, ← scatterB .last n p g n, ← gatherB k f n p)

/-- **`Vals.code2`**: `xs` (`n₁` rows) and `ys` (`n₂`) numbered in one order, `codeB` of their concatenation `z`: the
    count, `xs`' numbers, `ys`', and `z`'s count, columns and each number's first row in it. -/
def code2B (n₁ n₂ : Nat) (xs ys : Cols) : Bld (Nat × Nat × Nat × Nat × Cols × Nat) := do
  let (N, off) ← catB n₁ n₂
  let z ← concatB N n₁ n₂ off xs ys
  let (k, c, rep) ← codeB N z
  pure (k, ← gatherB n₁ (← posB) N c, ← gatherB n₂ off N c, N, z, rep)

/-- **`colCat`**: the words `a` (`n₁`) then `b` (`n₂`), `concatB` of one column each. -/
def colCatB (n₁ n₂ a b : Nat) : Bld (Nat × Nat) := do
  let (N, off) ← catB n₁ n₂
  pure (N, ← col1 (← concatB N n₁ n₂ off [.atom "" .i64 a] [.atom "" .i64 b]))

/-- **`csr`**: the `n` rows `(gid, x)` grouped by `gid` (each below `g`): each group's end (`prefixB` of the group
    sizes) and `x` in group order (`kasc` of `gid`, stable). -/
def csrB (n g gid x : Nat) : Bld (Nat × Nat) := do
  let ends := (← prefixB .add g (← scatterB .add n gid (← wordsB n 1) g)).1
  let (k, e) ← keyB n (.atom "" .i64 gid)
  let p ← nth (← callK (kernel% Rel.Kernel.kasc) #[n, ← listB [← ctorB 0 #[k, e] #[]]]) 1 "kasc"
  pure (ends, ← gatherB n p n x)

/-- **`bitMatrix`**: `na` rows of `w` bits, bit `r[k]·w + c[k]` set for each of the `n` rows. -/
def bitMatrixB (n na w r c : Nat) : Bld Nat := do
  scatterB .last n (← mapB .add n (← mapB .mul n r (← constB n (← wordOf w))) c) (← wordsB n 1)
    (← call1 (kernel% USize.mul) #[na, w])

/-- **`Tab.ofBits`**: the set bits of the `g · w` bits `o` (`whereB`), bit `a·w + c` the row of `x` (`nx` rows) at
    `ra[a]` and of `y` (`ny`) at `rc[c]`. -/
def ofBitsB (g w o nx : Nat) (x : Cols) (ra ny : Nat) (y : Cols) (rc : Nat) : Bld TabB := do
  let (M, sel) ← whereB (← call1 (kernel% USize.mul) #[g, w]) o
  let wc ← constB M (← wordOf w)
  let ix ← gatherB M (← mapB .div M sel wc) g ra
  let iy ← gatherB M (← mapB .mod M sel wc) w rc
  pure ⟨M, ← gatherCols M ix nx x, ← gatherCols M iy ny y⟩

/-- **`Tab.ldivOf`** (`r`, `s` canonical): `Q = r° ≫ ⟨𝟙, s⟩`; per group of equal `(b, c)` its row count `cnt`; the
    count `d` of `r`'s rows of `b` (CODE over `r.val ++ Q.key`); the groups with `cnt = d`; `∪` the vacuous part
    `(ran UB − ran r) × ran UC`. -/
def ldivOfB (r s UB UC : TabB) : Bld TabB := do
  let Q ← compB ⟨r.n, r.val, r.key⟩ ⟨s.n, s.key, s.key ++ s.val⟩
  let C := Q.val.drop s.key.length
  let (K, g, f, p) ← ascSeenB Q.n (Q.key ++ C)
  let cnt ← groupFoldB .add Q.n g f K 0 (← wordsB Q.n 1)
  let (N, sh) ← catB r.n Q.n
  guard (← call1 (kernel% USize.decLt) #[N, ← lit (.size (2 ^ 63))]) "ldiv: rows past 2^63" #[N]
  let (bk, bg, bf, bp) ← ascSeenB N (← concatB N r.n Q.n sh r.val Q.key)
  let cR ← groupFoldB .add N bg bf bk 0 (← mapB .lt N bp (← constB N (← wordOf r.n)))
  let code ← scatterB .last N bp bg N
  let q ← gatherB K f Q.n p
  let d ← gatherB K (← gatherB K (← mapB .add K q (← constB K (← wordOf r.n))) N code) bk cR
  let (M, sel) ← whereB K (← mapB .eq K cnt d)
  let ix ← gatherB M sel K q
  let P : TabB := ⟨M, ← gatherCols M ix Q.n Q.key, ← gatherCols M ix Q.n C⟩
  let V ← selectB (fun m _ mx => mapB .not m mx mx) (← coreflB UB.n UB.val) (← coreflB r.n r.val)
  let W ← coreflB UC.n UC.val
  let (T, x, y) ← crossB V.n W.n V.key W.key
  unionB P ⟨T, x, y⟩

/-- **`Tab.ldiv`**: `ldivOfB` of `canonT R`, `canonT S`. -/
def ldivB (R S UB UC : TabB) : Bld TabB := do ldivOfB (← canonT R) (← canonT S) UB UC

/-- **`Tab.ldivBits`**: `S` as `ka + 1` rows (keys numbered with `R.key`'s, row `ka` holding `ran UC`) of `kc` bits,
    `R`'s rows grouped by value over `ran R ∪ ran UB` (`kb` groups, a value of no `R` row given row `ka`), each the
    `∧` of its rows (`kbitrows true`). Its `2^63` check is left out: its one caller `ldivSelB` runs it where
    `bitsWinB` holds, so every count is below `2^27`. -/
def ldivBitsB (R S UB UC : TabB) : Bld TabB := do
  let (ka, aR, aS, _) ← code2B R.n S.n R.key S.key
  let (kb, bR, _, NB, zb, rb) ← code2B R.n UB.n R.val UB.val
  let (kc, cS, cU, NC, zc, rc) ← code2B S.n UC.n S.val UC.val
  let ka1 ← call1 (kernel% USize.add) #[ka, ← lit (.size 1)]
  let cnt ← scatterB .add R.n bR (← wordsB R.n 1) kb
  let (E, eb) ← whereB kb (← mapB .eq kb cnt (← wordsB kb 0))
  let (N, gid) ← colCatB R.n E bR eb
  let (_, ix) ← colCatB R.n E aR (← constB E (← wordOf ka))
  let (ends, idx) ← csrB N kb gid ix
  let (NS, r) ← colCatB S.n UC.n aS (← constB UC.n (← wordOf ka))
  let (_, c) ← colCatB S.n UC.n cS cU
  let m ← bitMatrixB NS ka1 kc r c
  let o ← nth (← callK (kernel% Rel.Kernel.kbitrows) #[← lit (.bit true), kc, ka1, N, kb, ends, idx, m]) 0 "kbitrows"
  ofBitsB kb kc o NB zb rb NC zc rc

/-- **`Tab.bitsWin bits T na g w`** on size registers, every product kept from wrapping: `x · w ≤ bits` as
    `w = 0 ∨ ¬ bits / w < x`, and `s < rowBits · T` as `s / rowBits < T` (`s` the two products, each `≤ bits`). The
    `2^32` bounds follow from `bits < 2^32`, checked as the plan is built. -/
def bitsWinB (bits : Nat) (T na g w : Nat) : Bld Nat := do
  unless bits < 2 ^ 32 do throw s!"bitsWin: the bound {bits} is not below 2^32, which `kbitrows` reads"
  let leW (x : Nat) : Bld Nat := do ite1 (← call1 (kernel% USize.decEq) #[w, ← lit (.size 0)]) (lit (.bit true)) do
    let q ← call1 (kernel% USize.div) #[← lit (.size bits.toUSize), w]
    ite1 (← call1 (kernel% USize.decLt) #[q, x]) (lit (.bit false)) (lit (.bit true))
  andB (← leW na) do andB (← leW g) do
    let s ← call1 (kernel% USize.add) #[← call1 (kernel% USize.mul) #[na, w], ← call1 (kernel% USize.mul) #[g, w]]
    call1 (kernel% USize.decLt) #[← call1 (kernel% USize.div) #[s, ← lit (.size Tab.rowBits.toUSize)], T]

/-- `if c then t else e` of two tables whose sides have the shape of `ks`, `vs` (`regsOf`): the new registers, read
    back into that shape (`withRegs`). -/
def iteT (c : Nat) (ks vs : Cols) (t e : Bld TabB) : Bld TabB := do
  let w := (← regsOf (ks ++ vs)).length
  let flat (b : Bld TabB) : Bld (Array Nat) := do
    let T ← b
    let rs ← regsOf (T.key ++ T.val)
    unless T.key.length == ks.length && T.val.length == vs.length && rs.length == w do
      throw s!"if r{c}: a branch's table of {T.key.length} and {T.val.length} columns, {rs.length} registers, not {ks.length} and {vs.length}, {w}"
    pure (#[T.n] ++ rs.toArray)
  -- each branch one plan function (`funT`), as a node is: a choice between two recipes inlines neither
  let rs ← ite c (flat (funT [] fun _ => t)) (flat (funT [] fun _ => e))
  let (cs, _) ← withRegs (ks ++ vs) (rs.toList.drop 1)
  pure ⟨← nth rs 0 "if", cs.take ks.length, cs.drop ks.length⟩

/-- **`Tab.ldivSel d bits`**: `T` the expansion of `R° ≫ S` (`groupsB`), `ka` its groups; the division `d` where
    `rowBits · T ≤ ka + 2` (tested as `(ka + 2) / rowBits < T`, no product), else `ldivBitsB` where `bitsWinB T
    (ka + 1) kb kc` holds, else `d`. -/
def ldivSelB (d : TabB → TabB → TabB → TabB → Bld TabB) (bits : Nat) (R S UB UC : TabB) : Bld TabB :=
  funT [R, S, UB, UC] fun
  | [R, S, UB, UC] => do
    let (_, _, _, _, ka, _, _, w) ← groupsB ⟨R.n, R.val, R.key⟩ S
    let T := (← prefixB .add ka w).2
    let big ← call1 (kernel% USize.decLt)
      #[← call1 (kernel% USize.div) #[← call1 (kernel% USize.add) #[ka, ← lit (.size 2)], ← lit (.size Tab.rowBits.toUSize)], T]
    -- one choice bit, so each form is built once in the plan (as `compSelB`)
    let win ← andB big do
      bitsWinB bits T (← call1 (kernel% USize.add) #[ka, ← lit (.size 1)]) (← code2B R.n UB.n R.val UB.val).1
        (← code2B S.n UC.n S.val UC.val).1
    iteT win R.val S.val (ldivBitsB R S UB UC) (d R S UB UC)
  | _ => throw "ldivSel: not four tables"

/-- `T°` (`Tab.conv`): the sides swapped, then `canonT`. -/
def convB (T : TabB) : Bld TabB := canonT ⟨T.n, T.val, T.key⟩

/-- **`R / S`** within `UA`, `UB` (`GenK.rdiv`): `(S° \ R°)°`; the two converses are `canonT` answers, so the division
    is `ldivOfB` (`Tab.ldivOf`), with no second `canon`. -/
def rdivB (R S UA UB : TabB) : Bld TabB := do
  convB (← ldivSelB ldivOfB Tab.bitsMax (← convB S) (← convB R) UB UA)

/-- **`Tab.compBits`**: `S` as `kb` rows (middle values, numbered with `R.val`'s) of `kc` bits, `R`'s rows grouped by
    key (`ka` groups), each the `∨` of its rows (`kbitrows false`), read back by `ofBitsB`: each side's value is the
    first row of its number, so equal values written apart (two empty cells) read back as one. Its `2^63` check is
    left out: its one caller `compSelB` runs it where `bitsWinB` holds, so every count is below `2^27`. -/
def compBitsB (R S : TabB) : Bld TabB := funT [R, S] fun
  | [R, S] => do
    let (kb, bR, bS, _) ← code2B R.n S.n R.val S.key
    let (ka, aR, ra) ← codeB R.n R.key
    let (kc, cS, rc) ← codeB S.n S.val
    let (ends, idx) ← csrB R.n ka aR bR
    let m ← bitMatrixB S.n kb kc bS cS
    let o ← nth (← callK (kernel% Rel.Kernel.kbitrows) #[← lit (.bit false), kc, kb, R.n, ka, ends, idx, m]) 0 "kbitrows"
    ofBitsB ka kc o R.n R.key ra S.n S.val rc
  | _ => throw "compBits: not two tables"

/-- **`Tab.compSel bits`** (`GenK.compR`'s `compSelM`, read back): `T` the expansion of `groupsB`, `K` its groups; the
    expansion (`compFromB`) where `rowBits · T ≤ K + 1` (tested as `(K + 1) / rowBits < T`, no product), else
    `compBitsB` where `bitsWinB T K ka kc` holds, else the expansion. -/
def compSelB (bits : Nat) (R S : TabB) : Bld TabB := funT [R, S] fun
  | [R, S] => do
    let x ← groupsB R S
    let (_, _, _, _, K, _, _, w) := x
    let T := (← prefixB .add K w).2
    let big ← call1 (kernel% USize.decLt)
      #[← call1 (kernel% USize.div) #[← call1 (kernel% USize.add) #[K, ← lit (.size 1)], ← lit (.size Tab.rowBits.toUSize)], T]
    -- one choice bit, so each form is built once in the plan (two copies of the expansion per `≫` outgrow `cc`)
    let win ← andB big do bitsWinB bits T K (← codeB R.n R.key).1 (← codeB S.n S.val).1
    iteT win R.key S.val (compBitsB R S) (compFromB R S x)
  | _ => throw "compSel: not two tables"

/-- **`compT`**: `R ≫ S` (`compSelB`, as `GenK.compV`), `S` (the table `s` in a context, on demand where `ds`) read at
    `ran R`, its range the values `ran` the composition's context knows. -/
def compTB (R : TabB) (s : Dom → Bld TabB) (ds : Bool) (ran : Option (Nat × Cols) := none) : Bld TabB := do
  let bound : Bld TabB := do s { dom := some (← nubB R.n R.val), ran }
  -- a closed `S` that cannot run closed (`<` on an infinite universe; `GenK.memo` keeps it lazy) is read at `ran R`
  compSelB Tab.bitsMax R (← if ds then bound else tryCatch (s {}) fun e => tryCatch bound fun _ => throw e)

/-! #### The rounds of a fold (`Tab.foldRounds`) and the list rows its steps read -/

/-- **`R − S`** (`Tab.diff`): `Tab.select` keeping the groups of no `S` row. -/
def diffB (R S : TabB) : Bld TabB := selectB (fun m _ mx => mapB .not m mx mx) R S

/-- **`𝟘`** at `A ⟶ B`: no row. -/
def zeroB (A B : Obj) : Bld TabB := do let z ← lit (.size 0); pure ⟨z, ← noneB z A, ← noneB z B⟩

/-- **`Tab.nil`** on the keys `X` (`n` rows): each to the empty cell, `lo = hi = 0` over a payload of no row of `B`;
    then `canonT`. -/
def nilB (B : Obj) (n : Nat) (X : Cols) : Bld TabB := funV n X [] fun n X _ => do
  let c ← wordsB n 0
  let z ← mapB .add n c c
  let z0 ← lit (.size 0)
  canonT ⟨n, X, [.arr "" z0 z z (← noneB z0 B ".e")]⟩

/-- **`Tab.outl`** (`left`) or **`Tab.outr`** on the `n` pairs `X` of `A` and `B`: each pair beside its component, then
    `canonT`. -/
def piB (A B : Obj) (left : Bool) (n : Nat) (X : Cols) : Bld TabB := do
  let w := objWidth A
  canonT ⟨n, X, ← if left then repath A "" (X.take w) else repath B "" (X.drop w)⟩

/-- **`T ≫ π₁`** (`left`) or **`T ≫ π₂`**, `T`'s value a pair of `A` and `B`: `T.comp (outl T.val)` (`piB`). -/
def projT (A B : Obj) (left : Bool) (T : TabB) : Bld TabB := do compB T (← piB A B left T.n T.val)

/-- The check `uncons`, `unsnoc` make on `n` cells over `m` elements, `n + m + 1 < 2^63`, on size registers with
    `n, m < 2^63` tested first, so the sum does not wrap; else `fail` with `what` and the two counts. -/
def sumBoundB (what : String) (n m : Nat) : Bld Unit := do
  let c ← lit (.size (2 ^ 63))
  let ok ← andB (← call1 (kernel% USize.decLt) #[n, c]) do andB (← call1 (kernel% USize.decLt) #[m, c]) do
    call1 (kernel% USize.decLt) #[← call1 (kernel% USize.add) #[← call1 (kernel% USize.add) #[n, m], ← lit (.size 1)], c]
  guard ok s!"{what}: n cells over m elements past 2^63, n + m + 1" #[n, m]

/-- **`Tab.uncons`** (`cons°`, `left`) or **`Tab.unsnoc`** (`snoc°`) on the cells `X` (`n` rows) of `B`: each non-empty
    cell `[s, e)` (`whereB` of `s < e`) to its first element (the payload at `s`) and the slice `[s + 1, e)`, or to the
    slice `[s, e - 1)` and its last element (at `e - 1`); then `canonT`. No payload is built: each answer cell is a
    slice of `X`'s own. -/
def unconsB (B : Obj) (left : Bool) (n : Nat) (X : Cols) : Bld TabB := funV n X [] fun n X _ => do
  let (m, lo, hi, f) ← arrCol (if left then "uncons" else "unsnoc") X
  sumBoundB (if left then "uncons" else "unsnoc") n m
  let (s, e) ← spanB n m lo hi
  let (M, sel) ← whereB n (← mapB .lt n s e)
  let key ← gatherCols M sel n X
  if left then
    let sM ← gatherB M sel n s
    canonT ⟨M, key, (← repath B ".1" (← gatherCols M sM m f)) ++
      [.arr ".2" m (← mapB .add M sM (← wordsB M 1)) (← gatherB M sel n e) (← repath B ".2.e" f)]⟩
  else
    let l ← mapB .sub M (← gatherB M sel n e) (← wordsB M 1)
    canonT ⟨M, key, [.arr ".1" m (← gatherB M sel n s) l (← repath B ".1.e" f)] ++ (← repath B ".2" (← gatherCols M l m f))⟩

/-- **`Vals.cat`** of the `n` cells `x`, `y` of `B` (`arrCol`s): row `i` the cell `x[i] ++ y[i]`, the payloads joined
    (`concatB`), EXPAND of the summed widths, element `u` of cell `G` read at `s₁[G] + u` where `u < w₁`, else at
    `m₁ + s₂[G] + u - w₁` (`b + c · (a - b)`), laid out one cell after another (`Vals.cells`). -/
def cellCatB (B : Obj) (n : Nat) (x y : Nat × Nat × Nat × Cols) : Bld Col := do
  let (m₁, lo₁, hi₁, f₁) := x
  let (m₂, lo₂, hi₂, f₂) := y
  let (N, off) ← catB m₁ m₂
  cellsBoundB "cat" n N
  let F ← concatB N m₁ m₂ off f₁ f₂
  let (s₁, e₁) ← spanB n m₁ lo₁ hi₁
  let (s₂, e₂) ← spanB n m₂ lo₂ hi₂
  let w₁ ← mapB .sub n e₁ s₁
  let w ← mapB .add n w₁ (← mapB .sub n e₂ s₂)
  let (T, G, u) ← expandB n w
  let a ← mapB .add T (← gatherB T G n s₁) u
  let b ← mapB .add T (← gatherB T G n (← mapB .sub n (← mapB .add n s₂ (← constB n (← u64B m₁))) w₁)) u
  let c ← mapB .lt T u (← gatherB T G n w₁)
  let pay ← gatherCols T (← mapB .add T b (← mapB .mul T c (← mapB .sub T a b))) N F
  let (P, _) ← prefixB .add n w
  pure (.arr "" T (← mapB .sub n P w) (← mapB .add n P (← wordsB n 0)) (← repath B ".e" pay))

/-- **`Tab.snoc`**: `(xs, a)` to `xs ++ [a]`, `Vals.cat` after `𝟙 × τ` (`Vals.tau`: row `i` the one-element cell
    `[i, i + 1)` over the rows of `a`); then `canonT`. -/
def snocB (B : Obj) (P : TabB) : Bld TabB := funT [P] fun Ps => do
  let [P] := Ps | throw "snoc: not one table"
  let x ← arrCol "snoc" (P.val.take 1)
  let tau := (P.n, ← posB, ← mapB .add P.n (← posB) (← wordsB P.n 1), ← repath B ".e" (P.val.drop 1))
  canonT ⟨P.n, P.key, [← cellCatB B P.n x tau]⟩

/-- **`Tab.peelL`** (`left`) or **`Tab.peelR`** on `rest`, cells of `E`: `rest ≫ cons°` (`snoc°`), its first (last)
    element read now and the rest (`projT`). -/
def peelB (E : Obj) (left : Bool) (rest : TabB) : Bld (TabB × TabB) := do
  let c ← compB rest (← unconsB E left rest.n rest.val)
  if left then pure (← projT E (.arr E) true c, ← projT E (.arr E) false c)
  else pure (← projT (.arr E) E false c, ← projT (.arr E) E true c)

/-- **`Tab.foldRounds`** on `Instr.loop`, as `fixB` runs `Tab.fixOn`: the state `rest`, `P`, `out` (each its count,
    then `regsOf`), at most the register `k` rounds. A round where `P` has no row answers the state as it is and ends
    the loop; else `peel rest` gives the elements `el` read now and the rest, `P` becomes `step P el`, and `out` gains
    `P − dom(el) P` (the rows whose key has no element left), both cut (`packT`). The answer is the last `out`. -/
def foldRoundsB (peel : TabB → Bld (TabB × TabB)) (step : TabB → TabB → Bld TabB) (k : Nat) (rest P out : TabB) :
    Bld TabB := do
  let st (T : TabB) : Bld (List Nat) := return T.n :: (← regsOf (T.key ++ T.val))
  let shape (X : TabB) : List Nat → Bld (TabB × List Nat)
    | n :: rs => do
      let (cs, rs) ← withRegs (X.key ++ X.val) rs
      pure (⟨n, cs.take X.key.length, cs.drop X.key.length⟩, rs)
    | [] => throw "a fold's state: fewer registers than its tables read"
  let three (rs : List Nat) : Bld (TabB × TabB × TabB) := do
    let (R, rs) ← shape rest rs
    let (Q, rs) ← shape P rs
    pure (R, Q, (← shape out rs).1)
  let init := ((← st rest) ++ (← st P) ++ (← st out)).toArray
  let s ← loop k init "Tab.foldRounds: rows still folding when the rounds ran out" fun rs => do
    let (R, Q, O) ← three rs.toList
    let e ← call1 (kernel% USize.decEq) #[Q.n, ← lit (.size 0)]
    let nx ← ite e (pure rs) do
      let (el, R') ← peel R
      let Q' ← packT (← step Q el)
      let O' ← packT (← unionB O (← diffB Q (← compB (← coreflB el.n el.key) Q)))
      return ((← st R') ++ (← st Q') ++ (← st O')).toArray
    pure (nx, e)
  return (← three s.toList).2.2

/-- **`Tab.map`'s left fold** `⦇nil, ⟨π₁, π₂ ≫ R⟩ ≫ snoc⦈` on the arrays `I = idU X` of `A` (`foldRoundsB`, `peelB`),
    their payload's row count plus two rounds; one plan function per table shape (`funT`). -/
def mapFoldB (A B : Obj) (I R : TabB) : Bld TabB := funT [I, R] fun
  | [I, R] => do
    let (m, _, _, _) ← arrCol "F" I.key
    foldRoundsB (peelB A true) (fun acc el => do snocB B (← pairB (.arr A) (.arr B) B acc (← compB el R)))
      (← call1 (kernel% USize.add) #[m, ← lit (.size 2)]) I (← nilB B I.n I.key) (← zeroB (.arr A) (.arr B))
  | _ => throw "F(R)'s fold: not two tables"

/-- `G = ∋` on the `n` arrays `X` of `B`, `P = ⟨G, G⟩` and `D = ran P`: the pairs of elements of one array that
    `Tab.est` and `Tab.front` ask their test about. -/
def pairsB (B : Obj) (n : Nat) (X : Cols) : Bld (TabB × TabB × TabB) := do
  let G ← memB B n X
  let P ← pairB (.arr B) B B G G
  pure (G, P, ← coreflB P.n P.val)

/-- **`GenK.fold`** (`left`) or **`GenK.foldr`** on the `n` arrays `X` of `E`: `foldRoundsB` from `idU X` and
    `Tab.top X (ran e)` (`ev` the table of `e`), `step` a round's, their payload's row count plus two rounds. One
    plan function (`funT`), `step`'s reads of the scope its parameters. -/
def foldB (E V : Obj) (left : Bool) (n : Nat) (X : Cols) (ev : TabB) (step : TabB → TabB → Bld TabB) : Bld TabB :=
  funT [⟨n, X, []⟩, ev] fun
  | [I, ev] => do
    let (m, _, _, _) ← arrCol "fold" I.key
    let (T, x, y) ← crossB I.n ev.n I.key ev.val
    foldRoundsB (peelB E left) step (← call1 (kernel% USize.add) #[m, ← lit (.size 2)]) (← coreflB I.n I.key)
      (← canonT ⟨T, x, y⟩) (← zeroB (.arr E) V)
  | _ => throw "fold: not two tables"

/-- **`Tab.map`** (`F(R)`) on the arrays `X` (`n` rows) of `A`, `R` the table of the relation on elements: the elements
    EXPANDed (`v`, `T` rows), `⟨pos, v⟩ ≫ R`; where each position has exactly one image, those images in position
    order under the same widths (`Vals.cells`), then `canonT`; else the left fold (`mapFoldB`), as `Tab.map` chooses. -/
def cellsMapB (A B : Obj) (n : Nat) (X : Cols) (R : TabB) : Bld TabB := funV n X [R] fun n X Rs => do
  let [R] := Rs | throw "F: not one table"
  let (m, lo, hi, f) ← arrCol "F" X
  cellsBoundB "map" n m
  let (s, e) ← spanB n m lo hi
  let w ← mapB .sub n e s
  let (T, G, u) ← expandB n w
  let v ← gatherCols T (← mapB .add T (← gatherB T G n s) u) m f
  let C ← compB ⟨T, [.atom "" .i64 (← posB)], v⟩ R
  let fn ← andB (← call1 (kernel% USize.decEq) #[C.n, T]) do
    call1 (kernel% USize.decEq) #[(← nubB C.n C.key).1, T]
  -- the value side's shape for `iteT`: its registers are not read
  iteT fn X [.arr "" T lo hi (← repath B ".e" C.val)] (do
      let (P, _) ← prefixB .add n w
      canonT ⟨n, X, [.arr "" T (← mapB .sub n P w) (← mapB .add n P (← wordsB n 0)) (← repath B ".e" C.val)]⟩)
    (do mapFoldB A B (← coreflB n X) R)

/-- **`Tab.lam`** on the keys `X` (`n` rows) of `R` (`lamOf` of `canonT R`): one GROUP over `X` then `r`'s keys, a
    group's `X` rows (`cD`, input row below `n`) first; its cell the sorted rows `[f + cD, f + c)` of `r.val` gathered
    in sorted order (`r.val` itself where `r` has no row, an `ite`); the groups with `0 < cD` kept, keyed by their
    first row; then `canonT`. -/
def lamB (B : Obj) (n : Nat) (X : Cols) (R : TabB) : Bld TabB := funV n X [R] fun n X Rs => do
  let [R] := Rs | throw "Λ: not one table"
  let r ← canonT R
  let (N, sh) ← catB n r.n
  guard (← call1 (kernel% USize.decLt) #[N, ← lit (.size (2 ^ 63))]) "lam: rows past 2^63" #[N]
  let (k, g, f, p) ← ascSeenB N (← concatB N n r.n sh X r.key)
  let nc ← constB N (← u64B n)
  let cD ← scatterB .add N g (← mapB .lt N p nc) k
  let lo ← mapB .add k f cD
  let hi ← mapB .add k f (← scatterB .add N g (← wordsB N 1) k)
  let (M, sel) ← whereB k (← mapB .lt k (← wordsB k 0) cD)
  let iD ← gatherB M (← gatherB M sel k f) N p
  let pay ← ite (← call1 (kernel% USize.decEq) #[r.n, ← lit (.size 0)]) (do pure (#[r.n] ++ (← regsOf r.val).toArray))
    (do
      let ix ← mapB .max N (← mapB .sub N p nc) (← wordsB N 0)
      pure (#[N] ++ (← regsOf (← gatherCols N ix r.n r.val)).toArray))
  let (pv, _) ← withRegs r.val (pay.toList.drop 1)
  canonT ⟨M, ← gatherCols M iD n X,
    [.arr "" (← nth pay 0 "if") (← gatherB M sel k lo) (← gatherB M sel k hi) (← repath B ".e" pv)]⟩

/-- The two atom columns of a pair side `X`, the error naming the verb `s` otherwise. -/
def pairCols (s : String) (X : Cols) : Bld (Nat × Nat) := do
  let (some (Col.atom _ _ x), some (Col.atom _ _ y)) := (X[0]?, X[1]?)
    | throw s!"{s}: a pair side of {X.length} columns, not of two atoms"
  pure (x, y)

/-- **`Tab.failAt`**: where a row of the `n` rows is flagged `1` in `flag`, fail the run with `msg`, its placeholders
    (`failSegs`, `\x02`) the words of the columns `ws` at the FIRST flagged row (`Tab.keep` keeps row order). That row is
    `flag ∧ (prefix count = 1)`; a column's word there is the fold of the `kscan add` of the column times that mask. -/
def failAtB (n flag : Nat) (msg : String) (ws : List Nat) : Bld Unit := do
  let (r, _) ← whereB n flag
  discard <| ite (← call1 (kernel% USize.decEq) #[r, ← lit (.size 0)]) (pure #[]) (do
    let z ← wordsB n 0
    let P ← nth (← scanB .add .i64 n (some z) [z, flag]) 0 "kscan"
    let first ← mapB .and n flag (← mapB .eq n P (← wordsB n 1))
    let xs ← ws.mapM fun w => do
      let fold ← nth (← scanB .add .i64 n (some z) [z, ← mapB .mul n w first]) 1 "kscan"
      projB fold 1 0 .u64
    discard <| emit (.fail msg xs.toArray) 0
    pure #[])

/-- The flag of `Tab.arithOvf`: the row has both operands non-null and a divisor `≠ 0`, and `keep` (`stepB`'s) is `0`. -/
def arithOvfB (n a b keep : Nat) : Bld Nat := do
  let nn (x : Nat) : Bld Nat := mapB .first n x x .i64 .i64 [] [(.ne, nulWord)]
  let z ← mapB .first n b b .i64 .i64 [] [(.eq, 0)]
  mapB .and n (← mapB .and n (← nn a) (← nn b)) (← mapB .and n (← mapB .not n keep keep) (← mapB .not n z z))

/-- **`Tab.arithOp s`** on the pairs `X` of `A` (`stepOn`): `stepB` of the row's verb at `B`'s atom on the two
    components, the rows it keeps with their answers, the run failing where an `i64` answer overflowed
    (`Tab.arithOvf`, the same message); `Tab.arithOp`'s errors at the objects it refuses. -/
def arithOpB (s : String) (A B : Obj) (n : Nat) (X : Cols) : Bld TabB := match arithOps.lookup s, A, B with
  | some k, .prod (.atom t) (.atom t'), .atom u =>
    if t = u ∧ t' = u then do
      let (a, b) ← pairCols s X
      let (w, f) ← stepB u k n a b
      if u == .i64 then failAtB n (← arithOvfB n a b f) s!"{s}: i64 overflow at {s}(\x02, \x02)" [a, b]
      keepB ⟨n, X, [.atom "" u w]⟩ f
    else throw s!"{s} runs from a pair of one number object to it, found {repr t}×{repr t'} to {repr u}"
  -- `1+i64`: `Tab.arithOp`'s composition, null read in band: one `kscan` of an op that orders null, else `nulStepCol`
  | some k, .prod (.opt (.atom .i64)) (.opt (.atom .i64)), .opt (.atom .i64) =>
    match nulVerb k with
    | some (o, nb, nf) => do
      let (a, b) ← pairCols s X
      if o.nulFold = some (nb, nf) then return ⟨n, X, [.atom "" .i64 (← mapB o n a b)]⟩
      let p ← mapB .min n a b .i64 .i64 [] [(.first, 0x7fffffffffffffff)]
      -- `fillNulCol`: `max` against `nulWord`, the row count from `kscan .null`
      let fill (e : Nat) : Bld Nat := do
        let z ← nth (← callK (kernel% Rel.Kernel.kscan) #[← lit (Reg.put Kernel.Op.null), ← lit (.bit false),
          ← lit (Reg.put QAtomicType.i64), ← lit (Reg.put QAtomicType.i64), n, ← ctorB 0 #[] #[], ← listB [← srcB n e],
          ← lit (Reg.put ([] : List (Kernel.Op × UInt64))), ← lit (Reg.put [(Kernel.Op.first, nulWord)])]) 0 "kscan"
        mapB .max n e z
      let a' ← fill a; let b' ← fill b
      let (w, keep) ← stepB .i64 k n a' b'
      failAtB n (← arithOvfB n a' b' keep) s!"{s}: i64 overflow at {s}(\x02, \x02)" [a', b']
      let d ← mapB .mul n (← mapB .first n w w .i64 .i64 [] [(.sub, nulWord)]) keep .i64 .i64 [] [(.sub, nulWord)]
      return ⟨n, X, [.atom "" .i64 (← mapB .min n d p)]⟩
    | none => throw s!"{s} on 1+i64: a zero divisor drops a non-null row, which a `1+i64` answer cannot"
  | some _, _, _ => throw s!"{s} runs from a pair of one number object to it"
  | none, _, _ => throw s!"{s}: no value verb"

/-- **`Tab.succOp`** on the values `X` of `i64` (`succOn`): each word `u` to `u + [u ≠ null]` (`Tab.succCol`), the
    null to itself. -/
def succOpB (A B : Obj) (n : Nat) (X : Cols) : Bld TabB := match A, B with
  | .atom .i64, .atom .i64 => do
    let e ← col1 X
    failAtB n (← mapB .first n e e .i64 .i64 [] [(.eq, 0x7FFFFFFFFFFFFFFF)]) "succ: i64 overflow at succ(\x02)" [e]
    pure ⟨n, X, [.atom "" .i64 (← mapB .add n e (← mapB .first n e e .i64 .i64 [] [(.ne, nulWord)]))]⟩
  | _, _ => throw "succ runs from an object of i64 to it"

/-- **`Tab.mixOp`** on the values `X` of `i64` (`mixOn`): one `kscan` map of `Op.mix`, each word `u` to `Op.mixWord u`. -/
def mixOpB (A B : Obj) (n : Nat) (X : Cols) : Bld TabB := match A, B with
  | .atom .i64, .atom .i64 => do let e ← col1 X; pure ⟨n, X, [.atom "" .i64 (← mapB .mix n e e)]⟩
  | _, _ => throw "mix runs from an object of i64 to it"

/-- **`Tab.atIx`** on the pairs `X = (xs, k)` (`n` rows): the rows whose index `k` is nonneg (`first` with the post step
    `0 ≤ k`) and below the cell's width (`lt`), `and`ed to one `0`/`1` word, each to the payload at `s + k`; then `canonT`. -/
def atIxB (B : Obj) (n : Nat) (X : Cols) : Bld TabB := funV n X [] fun n X _ => do
  let (m, lo, hi, f) ← arrCol "at" (X.take 1)
  let k ← col1 (X.drop 1)
  guard (← call1 (kernel% USize.decLt) #[m, ← lit (.size (2 ^ 63))]) s!"at: a payload of m rows, past 2^63" #[m]
  let (s, e) ← spanB n m lo hi
  let c ← mapB .and n (← mapB .lt n k (← mapB .sub n e s)) (← mapB .first n k k .i64 .i64 [] [(.le, 0)])
  let (M, sel) ← whereB n c
  let ix ← gatherB M sel n (← mapB .add n s k)
  canonT ⟨M, ← gatherCols M sel n X, ← repath B "" (← gatherCols M ix m f)⟩

/-- **`Tab.cmpOp s`** on the pairs `X` of `A` (`cmpAt`): the rows whose two words, through `wideB`, pass the row's
    order `Tab.ordOp`, kept as the coreflexive on the pairs. -/
def cmpOpB (s : String) (A B : Obj) (n : Nat) (X : Cols) : Bld TabB := match cmpOps.lookup s, A, B with
  | some lt, .prod (.atom t) (.atom t'), .prod (.atom u) (.atom u') =>
    if t' = t ∧ u = t ∧ u' = t then do
      let (a, c) ← pairCols s X
      keepB ⟨n, X, X⟩ (← mapB (← ofExc (Tab.ordOp lt t)) n (← wideB t n a) (← wideB t n c))
    else throw s!"{s} runs on pairs of one number object, found {repr t}×{repr t'} to {repr u}×{repr u'}"
  | some _, _, _ => throw s!"{s} runs on pairs of one number object"
  | none, _, _ => throw s!"{s}: no order"

/-- **`Tab.sumTail`**: the prefix sum `W` of the `n` words `v` within the segments `seg` (one `kscan` from `0`) at the
    atom `u`, and each row's bad word: at `i64` a wrap (`v`, `W − v` of one sign, `W` of the other) or the null read
    or made; at `f64` the `fto` `W'` of the IEEE sum not `W`, or a NaN; a `W'` that is neither fails the run. -/
def sumTailB (what : String) (u : QAtomicType) (n seg v : Nat) : Bld (Nat × Nat) := do
  let z ← wordsB n 0
  let test (x : Nat) (o : Kernel.Op) (w : UInt64) : Bld Nat := mapB .first n x x .i64 .i64 [] [(o, w)]
  match u with
  | .i64 =>
    let W ← nth (← scanB .add .i64 n (some seg) [z, v]) 0 "kscan"
    let sv ← test v .gt 0
    let d ← mapB .sub n W v
    let ovf ← mapB .and n (← mapB .eq n sv (← test d .gt 0)) (← mapB .ne n sv (← test W .gt 0))
    let bad ← mapB .or n ovf (← mapB .or n (← test W .eq nulWord) (← test v .eq nulWord))
    pure (← mapB .add n W z, bad)
  | .f64 =>
    let W ← nth (← scanB .fadd .i64 n (some seg) [z, v]) 0 "kscan"
    let W' ← mapB (.fto .f64) n W W .f64
    let ne ← mapB .ne n W' W
    let nan ← test W' .eq nulWord
    let (k, _) ← whereB n (← mapB .and n ne (← mapB .not n nan nan))
    guard (← call1 (kernel% USize.decEq) #[k, ← lit (.size 0)])
      s!"{what}: an f64 prefix sum is -0, which no sum of canonical words from +0 makes" #[]
    pure (W', ← mapB .or n ne nan)
  | u => throw s!"{what}: values of {repr u} have no sum here; cast them to f64 or i64 first (x $ F)"

/-- **`Tab.sumOn`** on the `n` cells `X` of the atom `u`: the elements EXPANDed into `(G, i)`, a segment opened at
    each cell's first element, `sumTailB`; a cell with a bad element (`scatter or`) dropped (`keepB`), the others
    reading the sum at their last element (`scatter last`, `0` at an empty cell); then `canonT`. -/
def sumOnB (u : QAtomicType) (n : Nat) (X : Cols) : Bld TabB := funV n X [] fun n X _ => do
  let (m, lo, hi, f) ← arrCol "sum" X
  cellsBoundB "sum" n m
  let (T, G, i) ← expandB n (← mapB .sub n hi lo)
  let v ← gatherB T (← mapB .add T (← gatherB T G n lo) i) m (← col1 f)
  let (W, bad) ← sumTailB "sum" u T (← mapB .first T i i .i64 .i64 [] [(.eq, 0)]) v
  let badC ← scatterB .or T G bad n
  let L ← scatterB .last T G W n
  canonT (← keepB ⟨n, X, [.atom "" u (← mapB .or n L L u)]⟩ (← mapB .not n badC badC))

/-- **`Tab.sumsOn`** on `x : K × P ⟶ u`: `canonT`, `x` checked simple (`seenB` on the whole key has a run per row),
    the segments the runs of `K` (`seenB` on `K`'s columns, ones scattered to the first rows), `sumTailB`, and a bad
    word carried to the rest of its key (a segmented `kscan or`), those rows dropped (`keepB`). -/
def sumsOnB (K : Obj) (u : QAtomicType) (x : TabB) : Bld TabB := funT [x] fun
  | [x] => do
    let C ← canonT x
    let n := C.n
    let seen (cs : Cols) : Bld (Nat × Nat × Nat) := do
      seenB n (← (← cs.mapM (keysB n)).flatten.mapM fun (k, e) => ctorB 0 #[k, e] #[])
    let (m, _, _) ← seen C.key
    guard (← call1 (kernel% USize.decEq) #[m, n])
      "sums: x is not simple, two values at one (key, position); sums folds one value per (key, position): rows, distinct" #[n, m]
    let (gk, _, fk) ← seen (C.key.take (objWidth K))
    let seg ← scatterB .last gk fk (← wordsB gk 1) n
    let (W, bad) ← sumTailB "sums" u n seg (← col1 C.val)
    let badR ← nth (← scanB .or .i64 n (some seg) [← wordsB n 0, bad]) 0 "kscan"
    keepB ⟨n, C.key, [.atom "" u W]⟩ (← mapB .not n badR badR)
  | _ => throw "sums: not one table"

/-- **`Tab.length`** on the `n` cells `X`: a payload of `2^63` rows or more fails the run, past an `Int64` count; each
    cell to its width `hi - lo` (one `kscan .sub`); then `canonT`. -/
def lengthB (n : Nat) (X : Cols) : Bld TabB := funV n X [] fun n X _ => do
  let (m, lo, hi, _) ← arrCol "length" X
  guard (← call1 (kernel% USize.decLt) #[m, ← lit (.size (2 ^ 63))]) "length: a payload of m rows, past an Int64 count" #[m]
  canonT ⟨n, X, [.atom "" .i64 (← mapB .sub n hi lo)]⟩

/-- A row of `kernRows` at `A ⟶ B` given its relations' tables `xs` in a context, by the wrapper its `Tab` operator
    runs under (`Expand.primE`): `floatOp`, `cast`, `arithOp`, `succOp` and `cmpOp` on the values in demand (`GenK.ofVals`), `asc` on its
    relation's whole table (`GenK.ofRel`), `uncons`/`unsnoc` on the values, `snoc` after them (`GenK.after`), `flat`
    on its keys (`GenK.onKeys`), `foldI` one fold per (key, array) in demand, `sum` on the arrays in demand, `sums` on
    its relation's whole table. Any other row is refused, naming it. -/
def rowB (r : Prim) (A B : Obj) (D : Dom) (xs : List (Dom → Bld TabB)) : Bld TabB := do
  let some (c, _) := kernRows.lookup r.sym | throw s!"row `{r.sym}`: no `Tab` operator in `kernRows`"
  if c == ``Tab.floatOp then let (n, X) ← known r.sym D.dom; floatOpB r.sym A B n X
  else if c == ``Tab.cast then let (n, X) ← known r.sym D.dom; castB A B n X
  else if c == ``Tab.arithOp then let (n, X) ← known r.sym D.dom; arithOpB r.sym A B n X
  else if c == ``Tab.succOp then let (n, X) ← known r.sym D.dom; succOpB A B n X
  else if c == ``Tab.mixOp then let (n, X) ← known r.sym D.dom; mixOpB A B n X
  else if c == ``Tab.atRow then match A with
    | .prod (.arr b) (.atom .i64) => do let (n, X) ← known r.sym D.dom; atIxB b n X
    | _ => throw s!"row `{r.sym}` (`{c}`) at a source that is no array with an i64 index"
  else if c == ``Tab.cmpOp then let (n, X) ← known r.sym D.dom; cmpOpB r.sym A B n X
  -- `GenK.cmpRel strict`: `U` run in the context, `strict` read from the row's `cmpOps` entry
  else if c == ``GenK.cmpRel then match cmpOps.find? (ordSym ·.2 == r.sym), A, xs with
    | some (_, b), .atom t, [x] => cmpB x (ordSym b) (Tab.ordOp b t) t D
    | _, _, _ => throw s!"row `{r.sym}` (`{c}`) at a source that is no atom, or given {xs.length} relations, not one"
  else if c == ``Tab.map then match A, B, xs with
    -- `GenK.elems`: `R` run knowing its domain is `ran(∋)` at the arrays in demand
    | .arr a, .arr b, [x] => do
      let (n, X) ← known r.sym D.dom
      let M ← memB a n X
      cellsMapB a b n X (← x { dom := some (← nubB M.n M.val) })
    | _, _, _ => throw s!"row `{r.sym}` (`{c}`) at objects that are no arrays, or given {xs.length} relations, not one"
  else if c == ``Tab.asc then match xs with
    | [x] => ascB B (← x {})
    | _ => throw s!"asc given {xs.length} relations, not one"
  else if c == ``Tab.uncons || c == ``Tab.unsnoc then match A with
    | .arr b => do let (n, X) ← known r.sym D.dom; unconsB b (c == ``Tab.uncons) n X
    | _ => throw s!"row `{r.sym}` (`{c}`) at a source that is no array"
  -- `GenK.after`: `idU X ≫ snoc`
  else if c == ``Tab.snoc then match B with
    | .arr b => do let (n, X) ← known r.sym D.dom; snocB b (← coreflB n X)
    | _ => throw s!"row `{r.sym}` (`{c}`) at a target that is no array"
  -- `GenK.onKeys`: `R` run knowing its domain is the keys `i` of the pairs `X` in demand; then `Tab.flat`'s
  -- composition `((outl X ≫ R) ∩ (outr X ≫ (outl R.val)°)) ≫ outr R.val`
  else if c == ``Tab.flat then match A, xs with
    | .prod I a, [x] => do
      let (n, X) ← known r.sym D.dom
      let R ← x { dom := some (← nubB n (X.take (objWidth I))) }
      let L ← compB (← piB I a true n X) R
      let M ← compB (← piB I a false n X) (← convB (← piB a B true R.n R.val))
      compB (← interB L M) (← piB a B false R.n R.val)
    | _, _ => throw s!"row `{r.sym}` (`{c}`) at a source that is no pair, or given {xs.length} relations, not one"
  -- `GenK.foldI`: one left fold on `I × V` from `(i, b)`, each round's step met with `⟨π₁, S ≫ π₂⟩`
  else if c == ``GenK.foldI then match A, xs with
    | .prod I (.arr E), [e, S] => do
      let (n, X) ← known r.sym D.dom
      -- one plan function (`funT`), as `foldB`
      funT [⟨n, X, []⟩] fun
      | [Xt] => do
        let K := Obj.prod I (.arr E)
        let i ← piB I (.arr E) true Xt.n Xt.key
        let rest ← piB I (.arr E) false Xt.n Xt.key
        let es ← compTB i e true
        let step (P el : TabB) : Bld TabB := do
          let s ← compTB (← pairB K (.prod I B) E P el) S true
          interB s (← pairB K I B i (← projT I B false s))
        let (m, _, _, _) ← arrCol "foldI" rest.val
        let out ← foldRoundsB (peelB E true) step (← call1 (kernel% USize.add) #[m, ← lit (.size 2)]) rest
          (← pairB K I B i (← projT B B false es)) (← zeroB K (.prod I B))
        projT I B false out
      | _ => throw "foldI: not one table"
    | _, _ => throw s!"row `{r.sym}` (`{c}`) at a source that is no pair of a key and an array, or given {xs.length} relations, not two"
  -- `GenK.dom`/`GenK.ran`: `R` run on the keys in demand, its key (value) side as a coreflexive
  else if c == ``GenK.dom || c == ``GenK.ran then match xs with
    | [x] => do
      let r ← x (if c == ``GenK.dom then { dom := D.dom <|> D.ran } else { ran := D.dom <|> D.ran })
      coreflB r.n (if c == ``GenK.dom then r.key else r.val)
    | _ => throw s!"row `{r.sym}` given {xs.length} relations, not one"
  -- `GenK.testVals`: `Tab.est`, `Tab.front` on the arrays in demand, the pair test `Q` run knowing its domain `Dt`
  else if c == ``Tab.est || c == ``Tab.front then match A, xs with
    | .arr b, [q] => do
      let (n, X) ← known r.sym D.dom
      let (G, P, Dt) ← pairsB b n X
      if c == ``Tab.est then
        let V ← coreflB G.n G.val
        let VV ← pairB b b b V V
        let Y ← diffB (← diffB Dt (← q { dom := some (Dt.n, Dt.val) })) (← coreflB VV.n VV.val)
        diffB G (← compB P (← piB b b true Y.n Y.key))
      else
        let Δ ← interB (← q { dom := some (Dt.n, Dt.val) }) Dt
        let w ← pairB (.prod b b) b b (← piB b b false Dt.n Dt.key) (← piB b b true Dt.n Dt.key)
        let wΔ ← compB w Δ
        let Y ← diffB Δ (← coreflB wΔ.n wΔ.key)
        lamB b n X (← diffB G (← compB P (← piB b b false Y.n Y.key)))
    | _, _ => throw s!"row `{r.sym}` (`{c}`) at a source that is no array, or given {xs.length} relations, not one"
  else if c == ``Tab.sum then match A with
    | .arr (.atom u) => do let (n, X) ← known r.sym D.dom; sumOnB u n X
    | _ => throw "sum: the elements are no atom"
  else if c == ``Tab.length then match A with
    | .arr _ => do let (n, X) ← known r.sym D.dom; lengthB n X
    | _ => throw s!"row `{r.sym}` (`{c}`) at a source that is no array"
  -- `Tab.sums`' cases at the position object `P`, the value object `V`
  else if c == ``Tab.sums then match A, B, xs with
    | .prod K (.atom t), .atom u, [x] => match u with
      | .i64 | .f64 => if t.intOrd then do sumsOnB K u (← x {}) else throw s!"sums: positions of {repr t} are not ordered by value"
      | u => throw s!"sums: values of {repr u} have no sum here; cast them to f64 or i64 first (x $ F)"
    | .prod _ (.atom _), _, [_] => throw "sums: the values are no atom"
    | _, _, [_] => throw "sums: the positions are no atom"
    | _, _, _ => throw s!"sums given {xs.length} relations, not one"
  else if c == ``GenK.nil then match B with
    | .arr b => do let (n, X) ← known r.sym D.dom; nilB b n X
    | _ => throw s!"row `{r.sym}` (`{c}`) at a target that is no array"
  else throw s!"row `{r.sym}` (`{c}`): no plan recipe builds its `Tab` operator yet"

/-- What each variable reads (`Code`'s twin): its table at the objects and in the context its use gives it. -/
abbrev Vars := List (Nat × Bool × ((A B : Obj) → Dom → Bld TabB))

/-- The demand bit of each variable of `σ` (`Tm.dem`'s `δ`): the bit its binder wrote, `false` for a variable no binder bound. -/
def Vars.dem (σ : Vars) : Dem := fun k => ((σ.lookup k).map (·.1)).getD false

/-- A variable bound to the registers `s` of a table (an input, a run-time definition): `s` in every context. -/
def sideArg (s : Side × Side) : (A B : Obj) → Dom → Bld TabB :=
  fun A B _ => return ⟨← countOf s, ← colsOf A s.1, ← colsOf B s.2⟩

mutual
/-- **A term's table**: its node's recipe (`nodeB`) as one plan function (`funT`), closing over the tables of its
    context and its variables, so every node kind is built by one path and the block applying it (`main`, a
    function, a loop's round) holds one `apply` per node, never the node's kernels inlined. -/
partial def tabB (σ : Vars) (D : Dom) : {A B : Obj} → Tm A B → Bld TabB :=
  fun t => funT [] fun _ => nodeB σ D t

/-- A node's table, by the `Tab` operators its `GenK` code runs (design §4), its variables `σ` what
    each reads (`Vars`), `D` the values its context knows its source to hold (`compT`: a composition's left
    operand's range). A node on demand is read at `D`; a closed node ignores it, and its full table is a superset
    that every consumer of a `D`-bounded answer cuts alike. The nodes no plan recipe builds are refused, naming
    them and what they need. -/
partial def nodeB (σ : Vars) (D : Dom) : {A B : Obj} → Tm A B → Bld TabB
  | A, B, .val R => do
    let (k, v) := (← litSide R.key, ← litSide R.val)
    canonT ⟨← lit (.size R.n), ← colsOf A k, ← colsOf B v⟩
  | A, _, .uni (m := m) U => do coreflB (← lit (.size m)) (← colsOf A (← litSide U))
  | A, B, .zero => zeroB A B
  | _, _, .mem (B := b) => do let (n, X) ← known "∋" D.dom; memB b n X
  | _, _, .inl (A := A) (B := B) => do let (n, X) ← known "inl" D.dom; injB A B false n X
  | _, _, .inr (A := A) (B := B) => do let (n, X) ← known "inr" D.dom; injB A B true n X
  | _, _, .id => do let (n, X) ← known "𝟙" (D.dom <|> D.ran); coreflB n X
  | _, _, .top V => do
    let (n, X) ← known "⊤" D.dom
    let v ← tabB σ {} V
    let (T, x, y) ← crossB n v.n X v.val
    canonT ⟨T, x, y⟩
  | _, _, .outl (A := A) => do
    let (n, X) ← known "π₁" D.dom; canonT ⟨n, X, ← repath A "" (X.take (objWidth A))⟩
  | _, _, .outr (A := A) (B := B) => do
    let (n, X) ← known "π₂" D.dom; canonT ⟨n, X, ← repath B "" (X.drop (objWidth A))⟩
  -- `GenK.comp`: `R` first, handing `S` its range; where `R` cannot run so (`<` bounded only by `S`) or the context
  -- bounds only the range, `S` first, `R` run knowing its range is `S`'s domain (`compS`); where neither runs, `R`'s error
  | _, _, .comp R S => do
    let rFirst := do compTB (← tabB σ { dom := D.dom } R) (tabB σ · S) (S.dem σ.dem []) D.ran
    let sFirst := do
      let s ← tabB σ { ran := D.ran } S
      compSelB Tab.bitsMax (← tabB σ { dom := D.dom, ran := some (← domOf s) } R) s
    if (R.dem σ.dem []) && D.dom.isNone && D.ran.isSome then tryCatch sFirst fun e => tryCatch rFirst fun _ => throw e
    else tryCatch rFirst fun e => tryCatch sFirst fun _ => throw e
  | _, _, .conv R => do
    let r ← tabB σ ⟨D.ran, D.dom, D.pairs.map fun p => ⟨p.n, p.val, p.key⟩⟩ R; canonT ⟨r.n, r.val, r.key⟩
  | _, _, .meet R S => do
    let (r, s) ← bothB (tabB σ · R) (tabB σ · S) (R.dem σ.dem []) (S.dem σ.dem []) D boundOf
    interB r s
  | _, _, .join R S => do unionB (← tabB σ D R) (← tabB σ D S)
  | _, _, .diff R S => do
    let r ← tabB σ D R
    diffB r (← tabB σ (← if (S.dem σ.dem []) then boundOf r else pure D) S)
  | _, _, .pair (A := A) (B := B) (C := C) R S => do
    let (r, s) ← bothB (tabB σ · R) (tabB σ · S) (R.dem σ.dem []) (S.dem σ.dem []) { dom := D.dom }
      fun t => return { dom := some (← domOf t) }
    pairB A B C r s
  | A, B, .var k => match σ.lookup k with
    | some (_, b) => b A B D
    | none => throw s!"variable {k}, which no input table or call argument is bound to"
  | _, _, .nu k S b => do nuB (fun X => tabB ((k, false, fun _ _ _ => pure X) :: σ) {} b) (← tabB σ {} S)
  | A, B, .mu k w cap b => do
    muB (Tab.capMsg w cap) (← sizeB (cap - 1)) (fun X => tabB ((k, false, fun _ _ _ => pure X) :: σ) {} b)
      (← tabB σ {} (.zero : Tm A B))
  | A, B, .hylo k w b => do
    -- `GenK.hylo` on the keys `X` in demand: the nodes `N`, no cycle among them (`ν`), then `D ≫ μY : N ≫ φ(Y)`
    let (n, X) ← known "hylo" D.dom
    let some ch := b.kids k A | throw s!"Tm.gen: {w} gives the hylo no children (Tm.kids)"
    let Dt ← coreflB n X
    let N ← muB (Tab.capMsg w USize.size) (← sizeB (USize.size - 1)) (fun N => do
        let C ← compTB N (tabB σ · ch) (ch.dem σ.dem []); unionB Dt (← coreflB C.n C.val))
      (← tabB σ {} (.zero : Tm A A))
    let C ← compTB N (tabB σ · ch) (ch.dem σ.dem [])
    let cyc ← nuB (fun P => do let CP ← compB C P; coreflB CP.n CP.key) N
    guard (← call1 (kernel% USize.decEq) #[cyc.n, ← lit (.size 0)]) (GenK.cycleMsg w) #[cyc.n, N.n]
    compB Dt (← muB s!"{w} ran its cap of its nodes' count + 3 rounds without reaching a fixed point"
      (← call1 (kernel% USize.add) #[N.n, ← lit (.size 2)])
      (fun Y => compTB N (tabB ((k, false, fun _ _ _ => pure Y) :: σ) · b) (b.dem (Vars.dem ((k, false, fun _ _ _ => pure Y) :: σ)) [])) (← tabB σ {} (.zero : Tm A B)))
  | A, B, t@(.prim _) | A, B, t@(.arg ..) | A, B, t@(.call ..) => argB σ D A B t []
  -- `GenK.ldiv`'s bit-matrix `S` (`ldivM`) answers the table `ldivSel` does (`Tab.ldivTabMat_law`); a plan's `S` is rows
  | _, _, .ldiv R S UB UC => do
    ldivSelB ldivB Tab.bitsMax (← tabB σ {} R) (← tabB σ {} S) (← tabB σ {} UB) (← tabB σ {} UC)
  | _, _, .rdiv R S UA UB => do rdivB (← tabB σ {} R) (← tabB σ {} S) (← tabB σ {} UA) (← tabB σ {} UB)
  | _, _, .lam (B := B) R => do
    let (n, X) ← known "Λ" D.dom
    lamB B n X (← tabB σ { dom := some (n, X) } R)
  -- `GenK.fold`, `GenK.foldr`: `Tab.foldRounds` from `idU X` and `X × ran e`, `S` on `⟨P, el⟩` (`⟨el, P⟩`)
  | _, _, .fold (E := E) (V := V) e S => do
    let (n, X) ← known "fold" D.dom
    foldB E V true n X (← tabB σ {} e) fun P el => do compTB (← pairB (.arr E) V E P el) (tabB σ · S) (S.dem σ.dem [])
  | _, _, .foldr (E := E) (V := V) e S => do
    let (n, X) ← known "foldr" D.dom
    foldB E V false n X (← tabB σ {} e) fun P el => do compTB (← pairB (.arr E) E V el P) (tabB σ · S) (S.dem σ.dem [])


/-- A spine `f x₁ … xₖ` (`Tm.argGen`) given its later relations `xs`, in the context `D`: a row by `rowB`, each
    relation's table built in the context the row's wrapper gives it; a call by its body under its arguments bound at
    `ks` and no other variable (`Code.args`). An argument is built at each use in the context the use gives it where
    it runs on demand, or where it cannot run closed (`GenK.memo` keeps it lazy); else once, closed (`GenK.memo`).
    A use at other objects than the argument's reads `𝟘` (`Code.bind`). -/
partial def argB (σ : Vars) (D : Dom) (A B : Obj) :
    Tm A B → List ((C : Obj) × (E : Obj) × Tm C E) → Bld TabB
  | .arg f x, xs => argB σ D A B f (⟨_, _, x⟩ :: xs)
  | .call ks _ _ _ b, xs => do
    let bs ← (ks.zip xs).mapM fun (k, ⟨C, E, x⟩) => do
      let at_ (b : Dom → Bld TabB) : (A' B' : Obj) → Dom → Bld TabB :=
        fun A' B' D' => if C = A' ∧ E = B' then b D' else zeroB A' B'
      let lazy := at_ (tabB σ · x)
      if x.dem σ.dem [] then pure (k, true, lazy) else
        try let t ← tabB σ {} x; pure (k, false, at_ fun _ => pure t) catch _ => pure (k, false, lazy)
    tabB bs D b
  | .prim r, xs => rowB r A B D (xs.map fun ⟨_, _, x⟩ => (tabB σ · x))
  | t, [] => tabB σ D t
  | _, xs => throw s!"{xs.length} relations given to a term that is no row and no call"
end

/-- The registers of a term's value, key side then value side, its variables `σ` the registers of the tables bound
    to them (a run-time definition's inputs, `Once.binds`): a variable's own registers, else `tabB`'s table. -/
def ofTm (σ : List (Nat × Side × Side)) : {A B : Obj} → Tm A B → Bld (Side × Side)
  | _, _, .var k => match σ.lookup k with
    | some s => pure s
    | none => throw s!"variable {k}, which no input table is bound to"
  | _, _, t => do sidesOf (← tabB (σ.map fun (k, s) => (k, false, sideArg s)) {} t)


unsafe def progOfUnsafe (n : Lean.Name) : Lean.Meta.MetaM (List (Lean.Name × Program) × Program) := do
  let env ← Lean.getEnv
  let opts ← Lean.getOptions
  let val (m : Lean.Name) : Lean.Meta.MetaM Program := match env.evalConstCheck Program opts ``Program m with
    | .ok p => pure p
    | .error e => throwError "cannot read the program `{m}`: {e}"
  let hs := ((Expand.relRegistry.getState env).chains.lookup n).getD []
  return (← hs.mapM fun h => return (h, ← val h), ← val n)

/-- The program `n` (a `rel_program`) and the programs its names reach, its homes as `rel_program` recorded them
    (`RegEntry.chain`), each with its value: what `Expand.read` reads it after, so a name of the prelude resolves. -/
@[implemented_by progOfUnsafe] opaque progOf (n : Lean.Name) : Lean.Meta.MetaM (List (Lean.Name × Program) × Program)

/-- The Lean side of the same output: `R`'s two sides written by the table writer under the names `output` gives
    them, from the value Lean computed, not from a plan. -/
def writeRel {A B : Obj} (dir : String) (R : Tab A B) : IO Unit := do
  Table.writeVals dir "key" R.key; Table.writeVals dir "val" R.val

/-! ### A program's IO statements (IO step I10): what `n.io` reads, computes and writes, as a plan -/

/-- The CSV columns of a side of `A` in file order, as `Table.ofCsv`/`Table.toCsv` lay them out: `part`, one atom column of
    `objCols` (one file part: an atom, an in-band `1+t`, a text's `lo`, `hi`, `e` each); `one`, a side of `1`, whose
    file part holds no column; `null`, a `1+S` not in band, `S` atoms `vs`: the tag column's path and one file column per
    atom of `S`, each of three parts (tag `1` at a null, position, the non-null rows' values) that the side holds as the
    dense sum's tag and `n`-row summand columns (`vs` the paths of those, `csvSideB`). -/
inductive CsvCol
  | part (p : String) (t : QAtomicType)
  | one
  | null (tag : String) (vs : List (String × QAtomicType))

/-- `CsvCol`s of the side of `A` at `p`, by the object alone (`Table.ofCsv`'s cases); refused where `Table.ofCsv` is: a
    `1+S` whose `S` is no product of atoms, a list of no atom, a sum of no `1+S`. -/
def csvCols : Obj → String → Except String (List CsvCol)
  | .atom t, p => pure [.part p t]
  | .prod a b, p => return (← csvCols a (p ++ ".1")) ++ (← csvCols b (p ++ ".2"))
  | .arr (.atom t), p => pure ((objCols (.arr (.atom t)) p).map fun (q, u) => .part q u)
  | .one, _ => pure [.one]
  | .sum a b, p => match Obj.band a b, a with
    | some t, _ => pure [.part p t]
    | none, .one => if (Table.atomTypes b).isSome then pure [.null (p ++ ".tag") (objCols b (p ++ ".r"))]
      else throw s!"column `{p}` is a `1+S` whose `S` ({repr b}) is no product of atoms, which has no CSV columns"
    | none, _ => throw s!"column `{p}` is a sum of no `1+S` ({repr (Obj.sum a b)}), which has no CSV columns"
  | A, p => throw s!"column `{p}` is {repr A}, which is no CSV column set"

/-- `Table.writeCols`' order of the columns of a schema reversed: the rest's, then the first. -/
def fieldsR : Schema → List (String × Obj)
  | [] => []
  | [f] => [f]
  | f :: g :: R => fieldsR (g :: R) ++ [f]

/-- Each atom column of a side of schema `S`, as `Table.write` names its file: its path in `S.obj` (`cols`), its file
    name (the column's name, then its path in the column's object), its atom. -/
def schemaLeaves (S : Schema) : List (String × String × Option QAtomicType) :=
  ((objLeaves S.obj "").zip ((fieldsR S.reverse).flatMap fun (n, A) => objLeaves A n)).map fun ((p, t), (q, _)) => (p, q, t)

/-- The atom columns of `schemaLeaves`. -/
def schemaCols (S : Schema) : List (String × String × QAtomicType) :=
  (schemaLeaves S).filterMap fun (p, q, t) => t.map (p, q, ·)

/-- The row count of each side of `1` of the side `cs` of `A` (`objLeaves`' `none`), by its path under `p`: the count `n` of
    the rows of the side it lies in, a list's payload's `m`, a sum's summand's `l` or `r`. -/
partial def onesOf (n : Bld Nat) : (A : Obj) → Cols → String → Bld (List (String × Nat))
  | .one, _, p => return [(p, ← n)]
  | .prod a b, cs, p => return (← onesOf n a (cs.take (objWidth a)) (p ++ ".1")) ++
      (← onesOf n b (cs.drop (objWidth a)) (p ++ ".2"))
  | .arr b, [.arr _ m _ _ f], p => onesOf (pure m) b f (p ++ ".e")
  | .sum a b, [.sum _ _ x y], p => return (← onesOf n a x (p ++ ".l")) ++ (← onesOf n b y (p ++ ".r"))
  | _, _, _ => pure []

/-- Each side of `1` of the side `side` of `A`, written to the file `files` names by its path: kind `oneKind`, its count
    (`onesOf`), no part (`ownFile`). -/
def writeOnes (A : Obj) (side : Side) (files : List (String × String)) : Bld Unit := do
  if files.isEmpty then return
  let ones ← onesOf (countOf (side, [])) A (← colsOf A side) ""
  for (p, f) in files do
    let some m := ones.lookup p | throw s!"the side of `1` at `{p}` (file {f}) has no row count"
    discard <| call "qlean_own_write" #[← lit (.str f), ← lit (.u8 0), ← lit (.u8 oneKind), m, ← lit (.parts #[])] 0

/-- `output R to dir`, `R : A ⟶ B`: each column of `R`'s registers written by `qlean_own_write` to `dir/key<path>` and
    `dir/val<path>`, each side of `1` as `writeOnes`. The directory must exist; the kernel's error names the path when it
    does not. -/
def output (dir : String) (A B : Obj) (rs : Side × Side) : Bld Unit := do
  for (side, O, cs) in [("key", A, rs.1), ("val", B, rs.2)] do
    let file (p : String) := (System.FilePath.mk dir / (side ++ p)).toString
    for (p, r) in cs do
      discard <| call "qlean_own_write" (#[← lit (.str (file p))] ++ r.extract 0 Side.enc) 0
    writeOnes O cs ((objLeaves O "").filterMap fun (p, t) => if t.isNone then some (p, file p) else none)

/-- The plan's steps of `output x to dir` in the program `n`, read after its homes (`progOf`, `Expand.read`). -/
def outputOf (n : Lean.Name) (x : String) (dir : String) : Lean.Meta.MetaM (Except String (Bld Unit)) := do
  let (chain, prog) ← progOf n
  let r ← (Expand.read (fun _ => none) chain prog).run
  return do
    let (ds, _) ← r.mapError (s!"{repr ·}")
    let some ⟨A, B, t⟩ := ds.lookup x | throw s!"`{x}` is no closed definition of the program"
    pure (mainStepB do output dir A B (← ofTm [] t))

/-- An input as its read at the input edge answers it, with its key schema `k` (`[]`: positions) and value schema
    `v`: each atom column's path, atom and `ownMap` register, the key's and the value's (a table directory), or the
    CSV columns of the key and of the value (`csvCols`) and `csvRead`'s list register (a CSV file). -/
inductive InRead
  | own (k v : Schema) (kc vc : List (String × Option QAtomicType × Nat))
  | csv (k v : Schema) (kc vc : List CsvCol) (l : Nat)

/-- The input edge's reads of `input x : k ⟶ v from [csv] path` (`n.io`'s `Table.read`, `Table.readKeyed`,
    `Table.readCsvDict`): a keyed table directory's `key/` and `val/`, a keyed CSV file's key columns then value
    columns; a nullable `1+S` not in band is regrouped by `csvSideB`, a symbol column interned by `sideOf`. A column
    mapped from its file that holds a symbol, a general column or a sum is refused, naming the input. -/
def readIn (x : String) (k v : Schema) (csv : Option (UInt8 × Db.CsvCols)) (path : String) : Bld InRead := do
  let no (why : String) : Bld InRead := throw s!"input `{x}` from \"{path}\": {why}, which no plan recipe does yet"
  match csv with
  | some (sep, cs) =>
    -- a symbol column is read as its texts (`Db.Csv.symText`), interned by `sideOf` (`internB`)
    let ts ← ofExc ((Db.Csv.symText cs).mapError (s!"{path}: " ++ ·))
    let rs ← callK (kernel% Rel.Db.csvRead) #[← lit (.str path), ← lit (Reg.put ts), ← lit (.u8 sep)]
    let cols (S : Schema) := ofExc ((csvCols S.obj "").mapError (s!"input `{x}` from \"{path}\": " ++ ·))
    let kc ← if k.isEmpty then pure [] else cols k
    return .csv k v kc (← cols v) (← nth rs 1 "csvRead")
  | none =>
    let own (S : Schema) (dir : String) := (schemaLeaves S).mapM fun (p, q, t) => do
      if let some t := t then
        if [QAtomicType.sym, .general].contains t then
          discard <| no s!"column `{q}` of type {repr t}, refused by `Table.readArr`"
      return (p, t, ← call1 (kernel% Rel.Db.ownMap) #[← lit (.str (Table.file dir q))])
    if k.isEmpty then return .own k v [] (← own v path)
    return .own k v (← own k (Table.file path "key")) (← own v (Table.file path "val"))

/-- `Table.readArr`'s check of the float column `e` of `n` rows at `t`: each word canonical (`QAtomicType.nonCanonical`:
    no NaN, no `-0`), i.e. equal to the canonical word nearest it (`fto t` of the widened word, as a float verb's answer
    is made, `stepB`); else the run fails with the count of the rows that are not. -/
def canonFloatB (what : String) (t : QAtomicType) (n e : Nat) : Bld Unit := do
  let c ← mapB .first n e e t t (widen t) [(.fto t, 0)]
  let (_, k) ← prefixB .add n (← mapB .ne n e c .i64 t)
  guard (← call1 (kernel% USize.decEq) #[k, ← lit (.size 0)])
    s!"{what}: a {repr t} column of rows whose bit pattern is not canonical (a NaN or -0)" #[k]

/-- `Table.readVals`' check of a list's cells (`cellBad`): none of the `n` cells `[lo, hi)` of the column `p` is past
    its payload of `m` rows (`0 ≤ lo ≤ hi ≤ m` fails), counted by one pass over `lo < 0 ∨ hi < lo ∨ m < hi`. -/
def cellsB (x p : String) (n m lo hi : Nat) : Bld Unit := do
  let bad ← mapB .or n (← mapB .or n (← mapB .lt n lo (← wordsB n 0)) (← mapB .lt n hi lo))
    (← mapB .lt n (← constB n (← u64B m)) hi)
  let (_, k) ← prefixB .add n bad
  guard (← call1 (kernel% USize.decEq) #[k, ← lit (.size 0)])
    s!"input `{x}`: column `{p}.lo`: cells that are no slice of the payload rows, `0 ≤ lo ≤ hi ≤ m` fails" #[k, m]

/-- `Table.same`: the column file `p`, read with row count register `c` among `cnt` (path, count), has `n` rows. -/
def sameCount (x : String) (cnt : List (String × Nat)) (p : String) (n : Nat) : Bld Unit := do
  let some c := cnt.lookup p | throw s!"input `{x}`: column `{p}` has no file read"
  if c != n then
    guard (← call1 (kernel% USize.decEq) #[c, n]) s!"input `{x}`: column `{p}` of another row count than the rows it lies in" #[c, n]

/-- The row count a side of `A` at `p` has of its own (`Table.readVals`: a list's payload, a sum's summand): the count of
    its first atom column, as `colsOf` takes it, else of its first file (a side of `1`). -/
def ownCount (x : String) (cnt : List (String × Nat)) (A : Obj) (p : String) : Bld Nat :=
  match (objCols A p).findSome? (cnt.lookup ·.1) <|> (objLeaves A p).findSome? (cnt.lookup ·.1) with
  | some m => pure m
  | none => throw s!"input `{x}`: side at `{p}` has no file read"

/-- `Table.readVals`' row counts of a side of `A` read at `p`: each depth's files have the count of the rows they lie in
    (`n`; a list's payload and a sum's summand have their own, `ownCount`), a list's cells are slices of its payload
    (`cellsB`). A summand with no atom column (a side of `1`) has no count of its own that `colsOf` could take: it is the
    rows the tag gives it, the tag's sum `k` right, `n - k` left (`tagCount`), so its files must have it. -/
partial def ownCountsB (x : String) (s : Side) (cnt : List (String × Nat)) : (A : Obj) → String → Nat → Bld Unit
  | .atom _, p, n | .one, p, n => sameCount x cnt p n
  | .prod a b, p, n => do ownCountsB x s cnt a (p ++ ".1") n; ownCountsB x s cnt b (p ++ ".2") n
  | .arr b, p, n => do
    sameCount x cnt (p ++ ".lo") n; sameCount x cnt (p ++ ".hi") n
    let m ← ownCount x cnt b (p ++ ".e")
    let enc (q : String) := (s.lookup (p ++ q)).bind (·[Side.enc]?)
    let (some lo, some hi) := (enc ".lo", enc ".hi") | throw s!"input `{x}`: array `{p}`: its bounds have no `Enc` register"
    cellsB x p n m lo hi
    ownCountsB x s cnt b (p ++ ".e") m
  | .sum a b, p, n => match Obj.band a b with
    | some _ => sameCount x cnt p n
    | none => do
      -- dense: both summand columns have the sum's `n` rows (null where the tag names the other side)
      sameCount x cnt (p ++ ".tag") n
      ownCountsB x s cnt a (p ++ ".l") n; ownCountsB x s cnt b (p ++ ".r") n

/-- The side an input's mapped files answer (`Table.readVals`): each atom column's type code, constructor kind
    checked as `Table.readArr` checks them, its `Enc` rebuilt from its parts as `Db.ownEnc` rebuilds it, a float column
    checked canonical (`canonFloatB`); each side of `1` a file of kind `oneKind` (`Plan.oneKind`); the row counts of every
    depth as `ownCountsB`. `n₀` the count of the side read before, else the first file's: the one the side `A` has. -/
def ownSideB (x : String) (A : Obj) (cs : List (String × Option QAtomicType × Nat)) (n₀ : Option Nat) :
    Bld (Side × Option Nat) := do
  let fe : Enc := .foR .empty .empty
  let .ok (some (kind, _)) := Db.ownParts fe | throw "ownSideB: `Db.ownParts` holds no `foR`"
  let mut s : Side := []
  let mut cnt : List (String × Nat) := []
  let mut n₀ := n₀
  for (p, t, f) in cs do
    let sc (i : Nat) := emit1 (.sproj f 0 1 #[.u8, .u8, .size] i)
    let k ← sc 1
    let n ← sc 2
    cnt := cnt ++ [(p, n)]
    if n₀.isNone then n₀ := some n
    match t with
    | none =>
      guard (← call1 (kernel% UInt8.decEq) #[k, ← lit (.u8 oneKind)])
        s!"input `{x}`: column `{p}` has another constructor kind than {oneKind}, a side of `1`" #[k]
    | some t =>
      let code ← lit (.u8 t.code.toUInt8)
      guard (← call1 (kernel% UInt8.decEq) #[← sc 0, code]) s!"input `{x}`: column `{p}` has another atom type code than {repr t}" #[]
      guard (← call1 (kernel% UInt8.decEq) #[k, ← lit (.u8 kind)])
        s!"input `{x}`: column `{p}` has another constructor kind than {kind}, the one `Db.ownEnc` rebuilds" #[k]
      let ps ← projB f 0 0 .parts
      let e ← ctorB fe.ctorIdx #[← partB ps 0, ← partB ps 1] #[]
      if t matches .f32 | .f64 then canonFloatB s!"input `{x}`: column `{p}`" t n e
      s := s ++ [(p, (Side.regs code k n ps).push e)]
  if let some n := n₀ then if !cs.isEmpty then ownCountsB x s cnt A "" n
  pure (s, n₀)

/-- The parts `csvRead` answers for the columns `cs`: a symbol column's are its texts' (`Db.Csv.symText`: a list of `char`,
    `objCols`' `lo`, `hi`, payload), any other's its own. -/
def csvParts (cs : List (String × QAtomicType)) : List (String × QAtomicType) :=
  cs.flatMap fun (p, t) => if t == .sym then objCols (.arr (.atom .char)) p else [(p, t)]

/-- `Table.intern` of the `n` texts `x` (cells of `char`) into the dictionary `D : ℕ ⟶ [C]` as plan nodes, the recipe
    as the Lean states it: `R` the texts by row, the new texts `N = ran R − ran D`, each to its first row
    `F = Λ((R ≫ N)°) ≫ uncons ≫ π₁`, `D'` is `D` then the texts of `F°` (`concatB`), each row's id `R ≫ D'°`. `D`'s rows
    are kept, so no stored id changes. Answers `D'` and the register of the `n` ids. -/
def internB (D : TabB) (n : Nat) (x : Col) : Bld (TabB × Nat) := do
  let R : TabB := ⟨n, [.atom "" .i64 (← posB)], [x]⟩
  let N ← diffB (← coreflB R.n R.val) (← coreflB D.n D.val)
  let L ← lamB .long N.n N.key (← convB (← compB R N))
  let F ← compB L (← unconsB .long true L.n L.val)
  let Fc ← convB ⟨F.n, F.key, F.val.take 1⟩
  let (m, off) ← catB D.n Fc.n
  let D' : TabB := ⟨m, [.atom "" .i64 (← posB)], ← concatB m D.n Fc.n off D.val Fc.val⟩
  let I ← compB R (← convB D')
  let [.atom _ _ ids] := I.val | throw "intern: the ids are not one column"
  pure (D', ids)

/-- The symbol columns `cs` (paths, atoms) of a side `s` read by `csvSideB`, each one's three text parts replaced by
    its ids (`internB`, `Table.internCsv`) into `D`, left to right; the side and the grown dictionary. -/
def internSide (cs : List CsvCol) (D : TabB) (s : Side) : Bld (Side × TabB) := do
  let mut s := s
  let mut D := D
  for p in cs.filterMap fun | .part p .sym => some p | _ => none do
    let reg (q : String) (i : Nat) : Option Nat := (s.lookup q).bind (·[i]?)
    let (some lo, some hi, some e, some m, some n) :=
        (reg (p ++ ".lo") Side.enc, reg (p ++ ".hi") Side.enc, reg (p ++ ".e") Side.enc, reg (p ++ ".e") Side.count,
          reg (p ++ ".lo") Side.count)
      | throw s!"symbol column `{p}`: its text parts have no registers"
    let (D', ids) ← internB D n (.arr "" m lo hi [.atom ".e" .char e])
    s := s.filter (fun (q, _) => ![p ++ ".lo", p ++ ".hi", p ++ ".e"].contains q) ++ [(p, (← encRegs .sym n ids).push ids)]
    D := D'
  pure (s, D)

/-- The first cell of `csvRead`'s list `l`: its count and `Enc`; the rest of the list. -/
def csvCell (l : Nat) : Bld (Nat × Nat × Nat) := do
  let cell ← projB l 1 0 .obj
  pure (← projB cell 0 0 .size, ← projB cell 0 1 .obj, ← projB l 1 1 .obj)

/-- The CSV columns `cs` of a side, each count and `Enc` taken off `csvRead`'s list `l`; the rest of the list. A `1+S`
    not in band (`Table.ofCsv`): the first file column's tag, swapped to the language's (`1` at the `inr`, `swapTag`),
    its position and values, then each other file column's values, its tag required equal to the first's (the `1` is
    every field of `S` empty), else the run fails with the count of the rows that differ. -/
def csvSideB (cs : List CsvCol) (l : Nat) : Bld (Side × Nat) := do
  let mut l := l
  let mut s : Side := []
  for c in cs do
    match c with
    | .part p t =>
      for (q, u) in csvParts [(p, t)] do
        let (n, e, l') ← csvCell l
        s := s ++ [(q, (← encRegs u n e).push e)]
        l := l'
    | .one => l := (← csvCell l).2.2
    | .null tag vs =>
      let mut first : Option (Nat × Nat × Nat × String) := none
      let mut vals : List (QAtomicType × String × Nat × Nat) := []
      for (q, u) in vs do
        let (n, t, l₁) ← csvCell l
        let (_, i, l₂) ← csvCell l₁
        let (m, v, l₃) ← csvCell l₂
        l := l₃
        match first with
        | none =>
          let nt ← mapB .first n t t .u1 .i64 [] [(.not, 0)]
          s := s ++ [(tag, (← encRegs .u1 n nt).push nt)]
          first := some (n, t, i, q)
        | some (n₁, t₁, _, q₁) =>
          let (_, k) ← prefixB .add n₁ (← mapB .ne n₁ t₁ t .i64 .u1)
          guard (← call1 (kernel% USize.decEq) #[k, ← lit (.size 0)])
            s!"nullable columns `{q₁}` and `{q}` of one `1+S` are empty in different rows; they are empty together, \
              and all of them empty is the `1`" #[k]
        vals := vals ++ [(u, q, m, v)]
      -- the dense summands (`Table.denseVals`): each atom's non-null values then as many nulls as the tag has, gathered at
      -- the positions `i + m·tag`, so a null row reads one of the trailing nulls
      let some (n, t, i, _) := first | throw s!"column `{tag}`: a `1+S` with no atom column"
      let (_, nn) ← prefixB .add n t
      for (u, q, m, v) in vals do
        let tot ← call1 (kernel% USize.add) #[m, nn]
        let ix ← mapB .add n i (← mapB .mul n t (← constB n (← u64B m)))
        let d ← gatherB n ix tot (← catColB u tot m nn v (← nulsB nn))
        s := s ++ [(q, (← encRegs u n d).push d)]
  pure (s, l)

/-- The table an input's read answered, in `main`: its key side and value side (`csvSideB`, `ownSideB`); a keyed
    one's rows sorted with equal rows merged (`canonT`, `Table.canon`), as `Table.readKeyed`/`readCsvDict` read it. A CSV
    file's symbol columns are interned into the program's dictionary `D` (`internSide`, key columns first), which the
    answer carries grown. -/
def sideOf (x : String) (D : TabB) (r : InRead) : Bld ((Side × Side) × TabB) := do
  let (k, v, s, D) ← match r with
    | .csv k v kc vc l => do
      let (ks, l) ← csvSideB kc l
      let (ks, D) ← internSide kc D ks
      let (vs, D) ← internSide vc D (← csvSideB vc l).1
      pure (k, v, (ks, vs), D)
    | .own k v kc vc => do
      let (ks, n₀) ← ownSideB x k.obj kc none
      pure (k, v, (ks, (← ownSideB x v.obj vc n₀).1), D)
  if k.isEmpty then return (s, D)
  return (← sidesOf (← canonT ⟨← countOf s, ← colsOf k.obj s.1, ← colsOf v.obj s.2⟩), D)

/-- `output x to [csv] path` of the table `s` (`n.io`'s `Table.write`, `writeKeyed`, `writeCsv`): key `k = []`, the
    value side only, its rows renumbered by their order; else `key/` and `val/` (a CSV file: the key's columns, then
    the value's), each column from its `Enc` register (a column mapped from its file too, `ownSideB`), a directory's
    side with its `.d` (`Table.dName`) as `Table.write` writes it. A positions
    column has no file and no CSV part: it is refused, naming the column. A CSV file's symbol column is its texts, its
    ids decoded through the program's dictionary `D` (`Table.decodeCsv`: `unenum`, `I ≫ D`, then the text's three parts). -/
def writeOut (x : String) (k v : Schema) (csv : Option (UInt8 × Db.CsvCols)) (path : String) (s : Side × Side)
    (D : TabB) : Bld Unit := do
  let sides := if k.isEmpty then [(v, s.2, path)] else [(k, s.1, Table.file path "key"), (v, s.2, Table.file path "val")]
  let col (S : Schema) (side : Side) (p : String) : Bld (Array Nat) := match side.lookup p with
    | some r => pure r
    | none => throw s!"output `{x}` to \"{path}\": column `{p}` of {Schema.names S} is positions, which have no file"
  match csv with
  | none => for (S, side, dir) in sides do
      -- the side's `.d` as `Table.write` writes it: the same column (`textCol S.names`) through `writeVals`' own
      -- steps (`cols`, `ownFile`), known when the plan is built, so its parts are literals
      for (q, c) in cols _ (Table.textCol S.names).2 Table.dName do
        if let some f ← ofExc (ownFile q c) then
          discard <| call "qlean_own_write" #[← lit (.str (Table.file dir q)), ← lit (Reg.put f.code),
            ← lit (Reg.put f.kind), ← lit (Reg.put f.count), ← lit (.parts f.parts)] 0
      for (p, q, _) in schemaCols S do
        discard <| call "qlean_own_write" (#[← lit (.str (Table.file dir q))] ++ (← col S side p).extract 0 Side.enc) 0
      -- a side of `1` is a file of kind `oneKind`: its count (`ownFile`) and no part
      writeOnes S.obj side ((schemaLeaves S).filterMap fun (p, q, t) => if t.isNone then some (p, Table.file dir q) else none)
  | some (sep, cs) =>
    let ts ← ofExc ((Db.Csv.symText cs).mapError (s!"{path}: " ++ ·))
    let mut es : List Nat := []
    let mut rows : Option Nat := none
    for (S, side, _) in sides do
      let reg (p : String) : Bld (Nat × Nat) := do
        let r ← col S side p
        let (some m, some e) := (r[Side.count]?, r[Side.enc]?)
          | throw s!"output `{x}` to csv \"{path}\": column `{p}` has no `Enc` register, which `csvWrite` takes"
        pure (m, e)
      for c in ← ofExc ((csvCols S.obj "").mapError (s!"output `{x}` to csv \"{path}\": " ++ ·)) do
        -- the parts of one CSV column, each its count and `Enc`, as `Table.toCsv` lays them out
        let ps : List (Nat × Nat) ← match c with
          | .part p .sym => do
            let (m, e) ← reg p
            -- `unenum`: the ids `I ≫ D` as texts, refused unless every id has one (`Table.decode`)
            let T ← compB ⟨m, [.atom "" .i64 (← posB)], [.atom "" .i64 e]⟩ D
            guard (← call1 (kernel% USize.decEq) #[T.n, m])
              s!"output `{x}` to csv \"{path}\": column `{p}` has ids past the dictionary of texts, ids and texts matched" #[m, T.n]
            let [.arr _ m' lo hi [.atom _ _ pe]] := T.val | throw s!"output `{x}`: the texts of column `{p}` are not one text column"
            pure [(m, lo), (m, hi), (m', pe)]
          | .part p _ => do pure [← reg p]
          -- a side of `1` stores no column; its CSV part is its one element's code `0` in each row (`Table.csvEncs`)
          | .one => do let m ← countOf (side, []); pure [(m, ← wordsB m 0)]
          -- a `1+S` not in band: each atom as the extern's tag (swapped), position (the count of own-side rows before
          -- the row) and non-null values, as `Table.toCsv`'s `.null` case: a prefix count per side, a `where` of the tag
          | .null tag vs => do
            let (n, t) ← reg tag
            let e ← mapB .first n t t .u1 .i64 [] [(.not, 0)]
            let ex (a : Nat) : Bld Nat := do mapB .sub n (← prefixB .add n a).1 a
            let i ← mapB .add n (← mapB .mul n e (← ex e)) (← mapB .mul n t (← ex t))
            let (m, w) ← whereB n t
            let mut ps := []
            for (q, _) in vs do
              ps := ps ++ [(n, e), (n, i), (m, ← gatherB m w n (← reg q).2)]
            pure ps
        -- the first column holds the rows: a later column may be an array's payload (`.e`), of its own count
        if rows.isNone then rows := ps.head?.map (·.1)
        for (m, e) in ps do es := es ++ [← ctorB 0 #[m, e] #[]]
    let some n := rows | throw s!"output `{x}` to csv \"{path}\": no column"
    discard <| call "qlean_csv_write" #[← lit (.str path), ← lit (Reg.put ts), ← lit (.u8 sep), n, ← listB es] 0

/-- The library `L`'s dictionary as `Table.writeDict` lays it out: the text column `sym`'s files (`objCols` of `[C]`). -/
def libCols : List (String × QAtomicType) := objCols (.arr (.atom .char)) ""

/-- The library's dictionary files `L/sym.lo`, `sym.hi`, `sym.e` at the input edge, each column's `ownMap` register
    (`libDict`): a file absent is the empty column (`readOpt`), so a library with no dictionary yet reads as the
    empty one. -/
def readLib (L : String) : Bld (List (String × QAtomicType × Nat)) := libCols.mapM fun (p, t) => do
  let some f ← ofExc (Db.ownFile t 0 (Rel.Kernel.wordsFoR #[] : Enc)) | throw "readLib: an empty column has no file"
  let d : Val := .ctor 0 #[.parts f.parts] #[.u8 f.code, .u8 f.kind, .size f.count]
  let k := kernel% Rel.Db.ownMap
  pure (p, t, ← nth (← readOpt k.sym #[← lit (.str (Table.file L ("sym" ++ p)))] #[d]) 0 "ownMap")

/-- The dictionary `D : ℕ ⟶ [C]` of the files `readLib` read, as `Table.libDict` reads them: its key the ids `0 …`. -/
def libDictB (L : String) (cs : List (String × QAtomicType × Nat)) : Bld TabB := do
  let (s, _) ← ownSideB s!"the dictionary of the library {L}" (.arr (.atom .char)) (cs.map fun (p, t, n) => (p, some t, n)) none
  let some n := (s.lookup ".lo").bind (·[Side.count]?) | throw s!"library {L}: its dictionary has no row count"
  pure ⟨n, [.atom "" .i64 (← posB)], ← colsOf (.arr (.atom .char)) s ""⟩

/-- `Table.writeLib`: `D` as the dictionary of the library `L` whose files held `old`, append-only. `old ⊑ D` (`old − D`
    empty) else the run fails; where `D` has more rows, its three text files `sym.lo`, `sym.hi`, `sym.e` and
    `sym.rank = D ≫ asc(ran D)°` (`Table.rank`) are written, as `Table.writeDict` writes them. -/
def writeLibB (L : String) (old D : TabB) : Bld Unit := do
  let X ← diffB old D
  guard (← call1 (kernel% USize.decEq) #[X.n, ← lit (.size 0)])
    s!"{L}: the library's dictionary of \x01 texts and the program's of \x01 differ; a dictionary is append-only, so \
      these ids are not of this library" #[old.n, D.n]
  let w (q : String) (rs : Array Nat) : Bld Unit := do
    discard <| call "qlean_own_write" (#[← lit (.str (Table.file L q))] ++ rs.extract 0 Side.enc) 0
  discard <| ite (← call1 (kernel% USize.decEq) #[old.n, D.n]) (pure #[]) (do
    let s ← flatB D.n D.val
    for (p, _) in libCols do
      let some rs := s.lookup p | throw s!"library {L}: the dictionary's column `{p}` has no registers"
      w ("sym" ++ p) rs
    let R ← compB D (← convB (← ascB (.arr (.atom .char)) (← coreflB D.n D.val)))
    let some rs := (← flatB R.n R.val).lookup "" | throw s!"library {L}: the rank is not one column"
    w "sym.rank" rs
    pure #[])

/-- What the input edge answered: each input's read (`readIn`), and the library's dictionary files (`readLib`) of the own
    tables with a symbol column (`Table.progLib`), if any. -/
abbrev IoIn := List (String × InRead) × Option (String × List (String × QAtomicType × Nat))

/-- The plan of the IO statements of the program `n`, read after its homes (`progOf`, `Expand.read`), as `n.io`
    runs them: the input edge reads the inputs the outputs reach (`Expand.ioReach`, `readIn`); `main` builds each
    run-time definition they reach on the tables of its run-time names (`ofTm`, its variables `Once.binds`), then
    writes each output (`writeOut`), a closed definition's from its term. -/
def ioOf (n : Lean.Name) :
    Lean.Meta.MetaM (Except String (Bld IoIn × (IoIn → Bld Unit))) := do
  let (chain, prog) ← progOf n
  let r ← (Expand.read (fun _ => none) chain prog).run
  return do
    let (ds, _, _, _, os, io) ← r.mapError (s!"{repr ·}")
    let reach := Expand.ioReach io
    -- the library of the own tables with symbol columns, as `ioE` finds it (`Table.progLib`)
    let lib ← Table.progLib (io.filterMap fun
      | .input x _ _ k v none p => if reach.contains x then some (x, p, k, v) else none
      | .output x _ _ k v none p _ => some (x, p, k, v)
      | _ => none)
    let symOut := io.any fun | .output _ _ _ k v none _ _ => Table.symIn k.obj || Table.symIn v.obj | _ => false
    -- every input's refusal, not the first's, as `wr` below
    let rd : Bld IoIn := do
      let (rs, errs) ← io.foldlM (init := ([], #[])) fun (rs, errs) s => match s with
        | .input x _ _ k v c p =>
          if reach.contains x then
            tryCatch (do pure (rs ++ [(x, ← readIn x k v c p)], errs)) fun e => pure (rs, errs.push e)
          else pure (rs, errs)
        | _ => pure (rs, errs)
      unless errs.isEmpty do throw ("\n".intercalate errs.toList)
      pure (rs, ← lib.mapM fun L => return (L, ← readLib L))
    let wr (ins : IoIn) : Bld Unit := do
      let mut σ : List (String × Side × Side) := []
      -- the program's dictionary (§0.2): grown by each CSV input's symbols in statement order (`Expand.ioE`), from the
      -- library's (`libDictB`) where an own table has a symbol column, else from the empty one
      let old ← match ins.2 with
        | some (L, cs) => libDictB L cs
        | none => zeroB .long (.arr (.atom .char))
      let mut D := old
      -- every statement's refusal, not the first's: the list is the work a program needs of the plan
      let mut errs : Array String := #[]
      for s in io do
       try
        match s with
        -- an input's table in statement order, so a `dictionary` after it holds its symbols and none of a later input's
        | .input x .. =>
          if let some r := ins.1.lookup x then
            let (t, D') ← sideOf x D r
            σ := σ ++ [(x, t)]; D := D'
        | .defn x c deps =>
          if reach.contains x then
            let some o := os.find? (·.const == c) | throw s!"`{x}`: its constant `{c}` has no body here"
            let env ← (o.binds.zip deps).mapM fun (k, d) => match σ.lookup d with
              | some t => pure (k, t)
              | none => throw s!"`{x}` reads `{d}`, which is not read or computed before it"
            let ⟨_, _, t⟩ := o.res
            σ := σ ++ [(x, ← ofTm env t)]
        -- `dictionary x : S ⟶ [C]` (`Table.dictRel`): `D` as it is here, its key the ids `0 …` (`internB`'s `D'`)
        | .dict x _ _ =>
          if reach.contains x then
            -- the ids are `pos`, which no write reads the parts of (`encRegs`): one `kscan` makes them a `foR`
            let [.atom q t p] := D.key | throw s!"`dictionary {x}`: the dictionary's key is not one column"
            σ := σ ++ [(x, ← sidesOf { D with key := [.atom q t (← mapB .add D.n p (← wordsB D.n 0))] })]
        | .output x _ _ k v c p cl =>
          mainStepB do
            let t ← match cl, σ.lookup x with
              | none, some t => pure t
              | some _, _ => match ds.lookup x with
                | some ⟨_, _, t⟩ => ofTm [] t
                | none => throw s!"output `{x}`: no closed definition `{x}`"
              | none, none => throw s!"output `{x}`: not read or computed before it"
            writeOut x k v c p t D
       catch e => errs := errs.push e
      unless errs.isEmpty do throw ("\n".intercalate errs.toList)
      if symOut then
        let some (L, _) := ins.2 | throw "an own output with a symbol column has no library"
        mainStepB (writeLibB L old D)
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

/-- How many registers an instruction defines. -/
def defs (abi : String → Option Kernel) (fres : Array (Array Ty)) (gtys : Array (Array Ty)) : Instr → Except String Nat
  | .lit _ => pure 1
  | .call sym _ => match abi sym with | some k => pure k.res.size | none => throw s!"no kernel `{sym}` in the ABI table"
  | .readOpt _ _ d => pure d.size
  | .fail .. => pure 0
  | .apply f _ => match fres[f]? with | some t => pure t.size | none => throw s!"apply f{f}: no earlier function"
  | .global g => match gtys[g]? with | some t => pure t.size | none => throw s!"global g{g}: no earlier global"
  | .ite _ _ rt _ _ => pure rt.size
  | .loop _ init .. => pure init.size
  | .ctor .. | .proj .. | .sproj .. | .part .. => pure 1

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
  -- `if (cnd) { t } else { e }` in the scope `rs`: each branch hands its results `rt`, `re` to fresh C variables, which
  -- the enclosing scope owns; `down` the references the branches release themselves
  let ifC (cnd : String) (rs : Array CReg) (down : List Nat) (t : List Instr) (rt : Array Nat) (e : List Instr)
      (re : Array Nat) : EM (String × List (String × Ty)) := do
    let (tc, trs, txs) ← blockC abi fres gtys (ind ++ "  ") rs down t rt
    let (ec, _, exs) ← blockC abi fres gtys (ind ++ "  ") rs down e re
    let tys ← rt.toList.mapM fun a => return (← creg trs a).2.1
    let os ← tys.mapM fun t => return (← fresh, t)
    let set (xs : Array String) := String.join ((os.zip xs.toList).map fun ((o, _), v) => s!"{ind}  {o} = {v};\n")
    pure (String.join (os.map fun (o, t) => s!"{ind}{cTy t} {o};\n") ++ s!"{ind}if ({cnd}) \{\n" ++ tc ++ set txs ++
      s!"{ind}} else \{\n" ++ ec ++ set exs ++ s!"{ind}}\n", os)
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
    | .part r i =>
      let (y, ty, _) ← creg rs r
      unless ty == .parts do throw s!"part reads register {r}, a {repr ty}, not a parts array"
      let x ← fresh
      c := c ++ s!"{ind}if (lean_array_size({y}) <= {i}) \{ fprintf(stderr, \"plan: part r{r}.{i} of an array of %zu parts\\n\", " ++
        s!"lean_array_size({y})); exit(1); }\n{ind}lean_object *{x} = lean_array_get_core({y}, {i}); lean_inc({x});\n"
      rs := rs.push (x, .bytes, true); live := live ++ [rs.size - 1]
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
      -- as `failText`: placeholders take the registers in order, else `: ` and the registers after the message
      let segs := failSegs msg
      let regs ← as.toList.mapM (creg rs ·)
      let body ← if segs.all (·.isLeft) then
          pure (s!"fputs({cStr msg}, stderr); " ++ " ".intercalate (regs.zipIdx.map fun ((x, t, _), j) =>
            (if j == 0 then "fputs(\": \", stderr); " else "fputs(\", \", stderr); ") ++ cShow x t))
        else do
          unless (segs.filter (·.isRight)).length == regs.length do
            throw s!"fail `{msg}` has {(segs.filter (·.isRight)).length} placeholders for {regs.length} registers"
          let mut out := ""
          let mut rest := regs
          for s in segs do
            match s with
            | .inl t => out := out ++ s!"fputs({cStr t}, stderr); "
            | .inr signed =>
              let (x, t, _) :: r := rest | throw "fail: no register left for a placeholder"
              rest := r
              if signed then
                unless t == .u64 do throw s!"fail `{msg}`: a signed placeholder reads a {repr t}, not a u64 word"
                out := out ++ s!"fprintf(stderr, \"%lld\", (long long)(int64_t){x}); "
              else out := out ++ cShow x t ++ " "
          pure out
      c := c ++ s!"{ind}" ++ body ++ " fputc('\\n', stderr); exit(1);\n"
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
      let (s, os) ← ifC x rs down t rt e re
      c := c ++ s
      for (o, t) in os do rs := rs.push (o, t, true); live := live ++ [rs.size - 1]
    | .readOpt sym as dflt =>
      -- `if (the file exists) { the read } else { dflt }`, as an `if` whose condition is the path's
      let some k := abi sym | throw s!"no kernel `{sym}` in the ABI table"
      unless k.res.size == dflt.size do throw s!"readOpt `{sym}`: {dflt.size} defaults for {k.res.size} registers"
      let some p := as[0]? | throw s!"readOpt `{sym}`: no path register"
      let (x, ty, _) ← creg rs p
      unless ty == .str do throw s!"readOpt `{sym}`: register {p} is a {repr ty}, not a path"
      let down := live.filter (!after.contains ·)
      live := live.filter (after.contains ·)
      let (s, os) ← ifC s!"access(lean_string_cstr({x}), F_OK) == 0" rs down [.call sym as]
        (List.range' rs.size dflt.size).toArray (dflt.toList.map .lit) (List.range' rs.size dflt.size).toArray
      c := c ++ s
      for (o, t) in os do rs := rs.push (o, t, true); live := live ++ [rs.size - 1]
    | .loop k init body out done msg =>
      let (kx, kt, _) ← creg rs k
      unless kt == .size do throw s!"loop reads register {k}, a {repr kt}, not a size"
      -- the state owns a reference to each `init`; a round releases the state it reads and leaves the next one owned
      let st ← init.toList.mapM fun a => do let (y, t, _) ← creg rs a; pure (← fresh, y, t)
      let cnt ← fresh
      c := c ++ s!"{ind}size_t {cnt} = {kx};\n"
      for (x, y, t) in st do c := c ++ s!"{ind}{cTy t} {x} = {y};" ++ (if isObj t then s!" lean_inc({x});\n" else "\n")
      let srs := rs ++ (st.map fun (x, _, t) => (x, t, true)).toArray
      let (bc, brs, bxs) ← blockC abi fres gtys (ind ++ "    ") srs ((List.range st.length).map (rs.size + ·)) body
        (out.push done)
      for ((_, _, t), a) in st.zip out.toList do
        let t' := (← creg brs a).2.1
        unless t' == t do throw s!"loop: next state register {a} is a {repr t'}, the state's a {repr t}"
      -- through temporaries, since a next state may be another slot of this one
      let tmp ← st.mapM fun (_, _, t) => return (← fresh, t)
      let dn ← fresh
      let some dv := bxs.back? | throw "loop: a round answers no done register"
      c := c ++ s!"{ind}for (;;) \{\n{ind}  if ({cnt}-- == 0) \{ fputs({cStr msg}, stderr); fputc('\\n', stderr); exit(1); }\n" ++
        s!"{ind}  uint8_t {dn};\n{ind}  \{\n" ++ bc ++
        String.join ((tmp.zip bxs.toList).map fun ((x, t), v) => s!"{ind}    {cTy t} {x} = {v};\n") ++
        String.join ((st.zip tmp).map fun ((x, _, _), (y, _)) => s!"{ind}    {x} = {y};\n") ++
        s!"{ind}    {dn} = {dv};\n{ind}  }\n{ind}  if ({dn}) break;\n{ind}}\n"
      for (x, _, t) in st do rs := rs.push (x, t, true); live := live ++ [rs.size - 1]
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
