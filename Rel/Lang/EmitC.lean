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
   kernel% USize.add, kernel% USize.mul, kernel% USize.div, kernel% UInt64.toUSize, kernel% USize.toUInt64, kernel% ByteArray.usize]

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
    design §4) handed over as kind `2` (`Db.ownParts`), its parts its two fields, so it is written as it is encoded. -/
def encRegs (t : QAtomicType) (count e : Nat) : Bld (Array Nat) := do
  colRegs t 2 count #[← projB e 2 0 .bytes, ← projB e 2 1 .bytes]

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

/-! ### A term's table as a plan: the `GenK` recipe of each `Tm` node on the five kernels (design §4) -/

/-- A side's atom columns as the plan holds them: path (`objCols`), atom, `Enc` register. -/
abbrev Cols := List (String × QAtomicType × Nat)

/-- A table in registers: its row count (a `size`), its key's and value's columns. -/
structure TabB where
  n : Nat
  key : Cols
  val : Cols
  deriving Inhabited

/-- `colMap op` (one `kscan` pass, every row a segment) of the `n` rows of `a`, `b` read at `s`, written at `t`. -/
def mapB (op : Kernel.Op) (n a b : Nat) (t : QAtomicType := .i64) (s : QAtomicType := .i64) : Bld Nat := do
  nth (← callK (kernel% Rel.Kernel.kscan) #[← lit (Reg.put op), ← lit (.bit false), ← lit (Reg.put s), ← lit (Reg.put t),
    n, ← ctorB 0 #[] #[], ← listB [a, b], ← listB [], ← listB []]) 0 "kscan"

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

/-- `colPrefix op`: the running fold of the `n` words `a` from `0` (one segment), and its last word (`lastB`). -/
def prefixB (op : Kernel.Op) (n a : Nat) : Bld (Nat × Nat) := do
  let z ← wordsB n 0
  let r ← scanB op .i64 n (some z) [z, a]
  pure (← nth r 0 "kscan", ← lastB n (← nth r 1 "kscan") 0)

/-- `kasc ≫ kseen` over the `n` rows of the columns `cs`: the count `k` of runs of equal rows (the last row's group
    `+ 1`, a `kscan max` fold), each sorted row's group `g`, each run's first sorted row `f`, the permutation `p`. -/
def ascSeenB (n : Nat) (cs : Cols) : Bld (Nat × Nat × Nat × Nat) := do
  let key (t : QAtomicType) (e : Nat) : Bld Nat := do ctorB 0 #[← ctorB 0 #[] #[← lit (Reg.put t)], e] #[]
  let sp ← callK (kernel% Rel.Kernel.kasc) #[n, ← listB (← cs.mapM fun (_, t, e) => key t e)]
  let mut l ← nth sp 0 "kasc"
  let mut sorted := #[]
  for (_, t, _) in cs do
    sorted := sorted.push (← key t (← projB l 1 0 .obj)); l ← projB l 1 1 .obj
  let kg ← callK (kernel% Rel.Kernel.kseen) #[n, ← listB sorted.toList]
  let g ← nth kg 1 "kseen"
  let z ← wordsB n 0
  let k ← lastB n (← nth (← scanB .max .i64 n (some z) [z, g]) 1 "kscan") 1
  pure (k, g, ← nth kg 2 "kseen", ← nth sp 1 "kasc")

/-- The `n`-row columns `cs` at the `m` rows `ix` (`Vals.gather`). -/
def gatherCols (m ix n : Nat) (cs : Cols) : Bld Cols := cs.mapM fun (p, t, e) => return (p, t, ← gatherB m ix n e)

/-- **`Vals.nub`**: the `n` rows of `cs` without duplicates, ascending: each run's first input row (`kgather` of
    `p` at `f`), every column gathered there. -/
def nubB (n : Nat) (cs : Cols) : Bld (Nat × Cols) := do
  let (k, _, f, p) ← ascSeenB n cs
  pure (k, ← gatherCols k (← gatherB k f n p) n cs)

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

/-- **`Vals.concat`** of flat sides into `n` rows: each pair of columns `kscatter`ed to `pos` and to `off` and added
    (`Arr.concat`), the two sides' columns paired by position (one object, one `objCols` order). -/
def concatB (n n₁ n₂ off : Nat) (xs ys : Cols) : Bld Cols :=
  (xs.zip ys).mapM fun ((p, t, x), (_, _, y)) => do
    let a ← scatterB .last n₁ (← posB) x n
    return (p, t, ← mapB .add n a (← scatterB .last n₂ off y n) t)

/-- **`R ∪ S`** (`Tab.union`): `Tab.canon` of the concatenation. -/
def unionB (R S : TabB) : Bld TabB := do
  let (n, off) ← catB R.n S.n
  canonT ⟨n, ← concatB n R.n S.n off R.key S.key, ← concatB n R.n S.n off R.val S.val⟩

/-- **`groupFold`**: per group of the `n` sorted rows (`m` groups `g`, first rows `f`), `op` folded over `x` from `z`
    within its run (a segmented `kscan`), the run's last row scattered to its group. -/
def groupFoldB (op : Kernel.Op) (n g f m : Nat) (z : UInt64) (x : Nat) : Bld Nat := do
  let seg ← scatterB .last m f (← wordsB m 1) n
  let o ← nth (← scanB op .i64 n (some seg) [← wordsB n z, x]) 0 "kscan"
  scatterB .last n g o m z

/-- **`Tab.select`** (`∩`, `−`): the concatenation tagged by source (`1` at `S`'s rows), its groups of equal rows
    (`ascSeenB`), per group the `and` and the `or` of the tags, `keep` of the two, and the kept groups' first input
    rows gathered (`whereB`). -/
def selectB (keep : Nat → Nat → Nat → Bld Nat) (R S : TabB) : Bld TabB := do
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

/-- **`R ≫ S`** (`Tab.compOne`): the groups of equal middle values of `R.val` then `S.key` (`kasc` is stable, so a
    group's `R` rows come first), per group the counts `cR`, `cS` and the width `w = cR · cS`, EXPAND of `w` (each
    output row's group `G` and offset `u`), its `R` row `p[f + u / cS]` and `S` row `p[f + cR + u % cS] - n`, both
    sides gathered there, then `canonT`. `Tab.comp`'s blocks past `blockRows` and its bit matrices change no answer. -/
def compB (R S : TabB) : Bld TabB := do
  let (N, off) ← catB R.n S.n
  let (K, g, f, p) ← ascSeenB N (← concatB N R.n S.n off R.val S.key)
  let nR ← constB N (← call1 (kernel% USize.toUInt64) #[R.n])
  let cR ← scatterB .add N g (← mapB .lt N p nR) K
  let cS ← mapB .sub K (← scatterB .add N g (← wordsB N 1) K) cR
  let w ← mapB .mul K cR cS
  let (P, T) ← prefixB .add K w
  let T1 ← call1 (kernel% USize.add) #[T, ← lit (.size 1)]
  let o ← mapB .sub K P w
  let G ← gatherB T (← posB) T1 (← prefixB .max T1 (← scatterB .max K o (← posB) T1)).1
  let u ← mapB .sub T (← posB) (← gatherB T G K o)
  let ft ← gatherB T G K f
  let ct ← gatherB T G K cS
  let iR ← gatherB T (← mapB .add T ft (← mapB .div T u ct)) N p
  let qS ← mapB .add T (← mapB .add T ft (← gatherB T G K cR)) (← mapB .mod T u ct)
  let iS ← mapB .sub T (← gatherB T qS N p) (← constB T (← call1 (kernel% USize.toUInt64) #[R.n]))
  canonT ⟨T, ← gatherCols T iR R.n R.key, ← gatherCols T iS S.n S.val⟩

/-- **`Vals.cross`** of `n` rows `xs` and `m` rows `ys` (`crossIx`): `T = n · m` rows, `xs` at `pos / m`, `ys` at
    `pos % m`. -/
def crossB (n m : Nat) (xs ys : Cols) : Bld (Nat × Cols × Cols) := do
  let T ← call1 (kernel% USize.mul) #[n, m]
  let c ← constB T (← call1 (kernel% USize.toUInt64) #[m])
  pure (T, ← gatherCols T (← mapB .div T (← posB) c) n xs, ← gatherCols T (← mapB .mod T (← posB) c) m ys)

/-- The columns `cs`, in `objCols A` order, under the paths `objCols A pre` gives them. -/
def repath (A : Obj) (pre : String) (cs : Cols) : Cols :=
  ((objCols A pre).zip cs).map fun ((p, _), (_, t, e)) => (p, t, e)

/-- **`⟨R, S⟩`** (`Tab.pair`): `⟨(a, b), a⟩` on `R`'s rows composed with `S`, each key `(a, b)` rebracketed to `a`
    beside `(b, c)`. -/
def pairB (A B C : Obj) (R S : TabB) : Bld TabB := do
  let T ← compB ⟨R.n, repath A ".1" R.key ++ repath B ".2" R.val, R.key⟩ S
  let a := (objCols A "").length
  pure ⟨T.n, repath A "" (T.key.take a), repath B ".1" (T.key.drop a) ++ repath C ".2" T.val⟩

/-- **`R × S`** (`Tab.prod`): CROSS of the two tables' rows, each row `((a, c), (b, d))`, then `canonT`. -/
def prodB (A B C D : Obj) (R S : TabB) : Bld TabB := do
  let (T, x, y) ← crossB R.n S.n (R.key ++ R.val) (S.key ++ S.val)
  let (a, c) := (R.key.length, S.key.length)
  canonT ⟨T, repath A ".1" (x.take a) ++ repath C ".2" (y.take c), repath B ".1" (x.drop a) ++ repath D ".2" (y.drop c)⟩

/-- **`Vals.none`**: each atom column of `A`, no row (`Arr.zeros t 0`); `z` the register of the count `0`. -/
def noneB (z : Nat) (A : Obj) : Bld Cols := do
  unless flatObj A do throw "𝟘 at an array or a sum, whose `cells` keys no plan recipe builds yet"
  (objCols A "").mapM fun (p, t) => do let c ← wordsB z 0; return (p, t, ← mapB .add z c c t)

/-- A side's columns of the object `A`: each atom column's `Enc` register; a positions column, which has no
    registers (`litSide`), the positions. An array or a sum side, and a column mapped from its file (no `Enc`), are
    refused, naming them. -/
def colsOf (A : Obj) (s : Side) : Bld Cols := do
  unless flatObj A do throw "an array or a sum side, whose `cells` keys no plan recipe builds yet"
  (objCols A "").mapM fun (p, t) => match s.lookup p with
    | none => return (p, t, ← posB)
    | some rs => match rs[6]? with
      | some e => pure (p, t, e)
      | none => throw s!"column `{p}` is mapped from its file, whose parts no plan recipe reads as an `Enc` yet"

/-- The row count of a table's sides: a column's `count` register. -/
def countOf (s : Side × Side) : Bld Nat := match (s.1 ++ s.2).findSome? (·.2[3]?) with
  | some n => pure n
  | none => throw "a table whose every column is positions, so no register holds its row count"

/-- A `TabB`'s sides as `output` takes them: each column's six registers (`encRegs`), then its `Enc`. -/
def sidesOf (T : TabB) : Bld (Side × Side) := do
  let side (cs : Cols) : Bld Side := cs.mapM fun (p, t, e) => return (p, (← encRegs t T.n e).push e)
  pure (← side T.key, ← side T.val)

/-- The values a node on demand is read at (design §0 `Known`): its source's values, a count and columns. -/
abbrev Dom := Option (Nat × Cols)

/-- The values `D` a leaf on demand reads, or `GenK.ofVals`' error where they are unknown. -/
def known (what : String) : Dom → Bld (Nat × Cols)
  | some d => pure d
  | none => throw s!"{what}: a leaf on demand ran with its domain unknown"

/-- `T`'s domain values (`Tab.dom`'s side), the bound `GenK.bound` hands the other operand of `∩`, `−`, `⟨,⟩`. -/
def domOf (T : TabB) : Bld (Nat × Cols) := nubB T.n T.key

/-- Two operands `r`, `s` in the context `D`, as `GenK.meetK`/`pairK` order them: the one not on demand first, its
    domain bounding the other where that one runs on demand. -/
def bothB (r s : Dom → Bld TabB) (dr ds : Bool) (D : Dom) : Bld (TabB × TabB) := do
  if dr && !ds then let t ← s D; pure (← r (some (← domOf t)), t)
  else
    let t ← r D
    pure (t, ← s (← if ds then some <$> domOf t else pure D))

/-- **`compT`**: `R ≫ S`, `S` (the table `s` in a context, on demand where `ds`) read at `ran R`. -/
def compTB (R : TabB) (s : Dom → Bld TabB) (ds : Bool) : Bld TabB := do
  compB R (← s (← if ds then some <$> nubB R.n R.val else pure none))

/-- **`R ∩ S`** (`Tab.inter`): `Tab.select` keeping the groups of a row of each. -/
def interB (R S : TabB) : Bld TabB := selectB (fun m mn mx => mapB .lt m mn mx) R S

/-- **`Tab.fixOn`**: rounds of `step` from `X` (`Plan.loop`, the state its count and columns), at most the register
    `k` of them, until a round leaves the row count as it was; that round's table. `k` rounds with the count still
    moving fail with `msg`. `Tab.pack` is the identity on the flat sides a `TabB` holds. -/
def fixB (msg : String) (step : TabB → Bld TabB) (k : Nat) (X : TabB) : Bld TabB := do
  let st (T : TabB) : Array Nat := #[T.n] ++ ((T.key ++ T.val).map (·.2.2)).toArray
  let shape (rs : Array Nat) : Bld TabB := do
    let cs := ((X.key ++ X.val).zip (rs.extract 1 rs.size).toList).map fun ((p, t, _), e) => (p, t, e)
    pure ⟨← nth rs 0 "loop", cs.take X.key.length, cs.drop X.key.length⟩
  shape (← loop k (st X) msg fun rs => do
    let X ← shape rs
    let Y ← step X
    pure (st Y, ← call1 (kernel% USize.decEq) #[Y.n, X.n]))

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

/-- What a variable reads in `tabB`, given its objects: an input's registers (`Side`s) or a fixed point's round. -/
abbrev Env := List (Nat × (Obj → Obj → Bld TabB))

/-- **A term's table**, each node by the `Tab` operators its `GenK` code runs (design §4), its variables `σ` the
    tables bound to them, `D` the values its context knows its source to hold (`compT`: a composition's left
    operand's range). A node on demand is read at `D`; a closed node ignores it, and its full table is a superset
    that every consumer of a `D`-bounded answer cuts alike. The nodes no plan recipe builds are refused, naming
    them and what they need. -/
partial def tabB (σ : Env) (D : Dom) : {A B : Obj} → Tm A B → Bld TabB
  | A, B, .val R => do
    let (k, v) := (← litSide R.key, ← litSide R.val)
    canonT ⟨← lit (.size R.n), ← colsOf A k, ← colsOf B v⟩
  | A, _, .uni (m := m) U => do coreflB (← lit (.size m)) (← colsOf A (← litSide U))
  | A, B, .zero => do let z ← lit (.size 0); pure ⟨z, ← noneB z A, ← noneB z B⟩
  | _, _, .id => do let (n, X) ← known "𝟙" D; coreflB n X
  | _, _, .top V => do
    let (n, X) ← known "⊤" D
    let v ← tabB σ none V
    let (T, x, y) ← crossB n v.n X v.val
    canonT ⟨T, x, y⟩
  | _, _, .outl (A := A) => do
    let (n, X) ← known "π₁" D; canonT ⟨n, X, repath A "" (X.take (objCols A "").length)⟩
  | _, _, .outr (A := A) (B := B) => do
    let (n, X) ← known "π₂" D; canonT ⟨n, X, repath B "" (X.drop (objCols A "").length)⟩
  | _, _, .comp R S => do compTB (← tabB σ D R) (tabB σ · S) S.dem
  | _, _, .conv R => do let r ← tabB σ none R; canonT ⟨r.n, r.val, r.key⟩
  | _, _, .meet R S => do
    let (r, s) ← bothB (tabB σ · R) (tabB σ · S) R.dem S.dem D
    interB r s
  | _, _, .join R S => do unionB (← tabB σ D R) (← tabB σ D S)
  | _, _, .diff R S => do
    let r ← tabB σ D R
    selectB (fun m _ mx => mapB .not m mx mx) r (← tabB σ (← if S.dem then some <$> domOf r else pure D) S)
  | _, _, .dom R => do let r ← tabB σ D R; coreflB r.n r.key
  | _, _, .ran R => do let r ← tabB σ none R; coreflB r.n r.val
  | _, _, .pair (A := A) (B := B) (C := C) R S => do
    let (r, s) ← bothB (tabB σ · R) (tabB σ · S) R.dem S.dem D
    pairB A B C r s
  | _, _, .prod (A := A) (B := B) (C := C) (D := D') R S => do prodB A B C D' (← tabB σ none R) (← tabB σ none S)
  | _, _, .own R | _, _, .share _ R => tabB σ D R
  | A, B, .var _ k => match σ.lookup k with
    | some t => t A B
    | none => throw s!"variable {k}, which no input table is bound to"
  | _, _, .nu k S b => do nuB (fun X => tabB ((k, fun _ _ => pure X) :: σ) none b) (← tabB σ none S)
  | A, B, .mu k w cap b => do
    muB (Tab.capMsg w cap) (← sizeB (cap - 1)) (fun X => tabB ((k, fun _ _ => pure X) :: σ) none b)
      (← tabB σ none (.zero : Tm A B))
  | A, B, .hylo k w b => do
    -- `GenK.hylo` on the keys `X` in demand: the nodes `N`, no cycle among them (`ν`), then `D ≫ μY : N ≫ φ(Y)`
    let (n, X) ← known "hylo" D
    let some ch := b.kids k A | throw s!"Tm.gen: {w} gives the hylo no children (Tm.kids)"
    let Dt ← coreflB n X
    let N ← muB (Tab.capMsg w USize.size) (← sizeB (USize.size - 1)) (fun N => do
        let C ← compTB N (tabB σ · ch) ch.dem; unionB Dt (← coreflB C.n C.val))
      (← tabB σ none (.zero : Tm A A))
    let C ← compTB N (tabB σ · ch) ch.dem
    let cyc ← nuB (fun P => do let CP ← compB C P; coreflB CP.n CP.key) N
    guard (← call1 (kernel% USize.decEq) #[cyc.n, ← lit (.size 0)]) (GenK.cycleMsg w) #[cyc.n, N.n]
    compB Dt (← muB s!"{w} ran its cap of its nodes' count + 3 rounds without reaching a fixed point"
      (← call1 (kernel% USize.add) #[N.n, ← lit (.size 2)])
      (fun Y => compTB N (tabB ((k, fun _ _ => pure Y) :: σ) · b) b.dem) (← tabB σ none (.zero : Tm A B)))
  | _, _, .leq .. | _, _, .lt .. => throw
    "`≤`/`<` (`GenK.cmp`): its order `Op` per atom (`Tab.ordOp`, floats widened) and the pairs a meet hands it are not built by a plan recipe yet"
  | _, _, .succ _ | _, _, .arith .. => throw
    "a value verb (`Tab.succ`, `Tab.arith`): `dom U` composed on each operand around the `kscan` chain (`stepCols`) is not built by a plan recipe yet"
  | _, _, .ldiv .. | _, _, .rdiv .. => throw
    "a division (`Tab.ldivSel`): its grouped counts and bit matrices are not built by a plan recipe yet"
  | _, _, .lam _ | _, _, .E _ | _, _, .est _ | _, _, .thin _ | _, _, .nil | _, _, .atPos _ | _, _, .fold ..
  | _, _, .foldr .. | _, _, .foldI .. => throw
    "a node on an array side (`Λ`, `E`, `est`, `thin`, `nil`, `at`, a fold): arrays need `cells` keys, which no plan recipe builds yet"
  | _, _, .prim _ | _, _, .arg .. | _, _, .call .. | _, _, .callCv .. => throw
    "a library row or a constant's call: its row's `Tab` operator (`kernRows`) is not built by a plan recipe yet"

/-- The registers of a term's value, key side then value side, its variables `σ` the registers of the tables bound
    to them (a run-time definition's inputs, `Once.binds`): a variable's own registers, else `tabB`'s table. -/
def ofTm (σ : List (Nat × Side × Side)) : {A B : Obj} → Tm A B → Bld (Side × Side)
  | _, _, .var _ k => match σ.lookup k with
    | some s => pure s
    | none => throw s!"variable {k}, which no input table is bound to"
  | _, _, .share _ R => ofTm σ R
  | _, _, t => do
    sidesOf (← tabB (σ.map fun (k, s) => (k, fun A B => do pure ⟨← countOf s, ← colsOf A s.1, ← colsOf B s.2⟩)) none t)


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
  | .loop k init b out d _ => k :: init.toList ++ ((b.flatMap (reads base) ++ out.toList ++ [d]).filter (· < base))

/-- How many registers an instruction defines. -/
def defs (abi : String → Option Kernel) (fres : Array (Array Ty)) (gtys : Array (Array Ty)) : Instr → Except String Nat
  | .lit _ => pure 1
  | .call sym _ => match abi sym with | some k => pure k.res.size | none => throw s!"no kernel `{sym}` in the ABI table"
  | .fail .. => pure 0
  | .apply f _ => match fres[f]? with | some t => pure t.size | none => throw s!"apply f{f}: no earlier function"
  | .global g => match gtys[g]? with | some t => pure t.size | none => throw s!"global g{g}: no earlier global"
  | .ite _ _ rt _ _ => pure rt.size
  | .loop _ init .. => pure init.size
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
