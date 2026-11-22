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
   kernel% Rel.Kernel.kseen, kernel% Rel.Kernel.kbitrows, kernel% Rel.Db.ownWrite, kernel% Rel.Db.ownMap, kernel% Rel.Db.csvRead,
   kernel% Rel.Db.csvWrite, kernel% Rel.Db.pushPart, kernel% USize.decEq, kernel% UInt8.decEq,
   kernel% USize.add, kernel% USize.sub, kernel% USize.mul, kernel% USize.decLt, kernel% USize.div, kernel% UInt64.toUSize, kernel% USize.toUInt64, kernel% ByteArray.usize]

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

/-! ### A term's table as a plan: the `GenK` recipe of each `Tm` node on the five kernels (design §4) -/

/-- A column of a side as the plan holds it, node for node as `Vals`: an atom column (its path as `cols` names it, its
    atom, its `Enc` register); an `arr` side (its path; its payload's row count `m`, a `size` register; `lo`, `hi`,
    `Enc` registers of `i64`; its payload's columns, `m` rows); a `sum` side, which `sumB` alone reads. A product side
    is its two sides' columns one after the other (`Cols`), in `objCols` order. -/
inductive Col where
  | atom (p : String) (t : QAtomicType) (e : Nat)
  | arr (p : String) (m lo hi : Nat) (pay : List Col)
  | sum (p : String) (l r tag idx : Nat) (x y : List Col)
  deriving Inhabited

/-- A side's columns. -/
abbrev Cols := List Col

/-- Every recipe's case of a `sum` side, the one place a sum's layout would be read (so a change of it, `nullband4`'s
    in-band `foR` for `sum (atom t) one`, lands here alone); `what` names the recipe. No recipe reads one yet. -/
def sumB {α : Type} (what : String) : Bld α :=
  throw s!"{what} on a sum side (tag, idx, two payloads): no plan recipe reads a sum yet"

/-- The number of `Col`s of a side of `A`: a product's two sides', else one. -/
def objWidth : Obj → Nat
  | .prod a b => objWidth a + objWidth b
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
    n, ← ctorB 0 #[] #[], ← listB [a, b], ← lit (Reg.put pre), ← lit (Reg.put post)]) 0 "kscan"

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

/-- The `kasc` key of the `n`-row column `c` (`Vals.cols`), an `AscKey` register and its column: an atom column its
    words at its atom; an `arr` side one `cells` key over its `lo`, `hi` and its payload's keys, its column the
    positions, row `i` naming cell `i`. -/
partial def keyB (n : Nat) : Col → Bld (Nat × Nat)
  | .atom _ t e => return (← ctorB 0 #[] #[← lit (Reg.put t)], e)
  | .arr _ m lo hi f => do
    let els ← f.mapM fun c => do let (k, e) ← keyB m c; ctorB 0 #[k, e] #[]
    return (← ctorB 1 #[lo, hi, ← listB els] #[n, m], ← posB)
  | .sum .. => sumB "asc"

/-- `kasc ≫ kseen` over the `n` rows of the columns `cs`: the count `k` of runs of equal rows (the last row's group
    `+ 1`, a `kscan max` fold), each sorted row's group `g`, each run's first sorted row `f`, the permutation `p`. -/
def ascSeenB (n : Nat) (cs : Cols) : Bld (Nat × Nat × Nat × Nat) := do
  let ks ← cs.mapM (keyB n)
  let sp ← callK (kernel% Rel.Kernel.kasc) #[n, ← listB (← ks.mapM fun (k, e) => ctorB 0 #[k, e] #[])]
  let mut l ← nth sp 0 "kasc"
  let mut sorted := #[]
  for (k, _) in ks do
    sorted := sorted.push (← ctorB 0 #[k, ← projB l 1 0 .obj] #[]); l ← projB l 1 1 .obj
  let kg ← callK (kernel% Rel.Kernel.kseen) #[n, ← listB sorted.toList]
  let g ← nth kg 1 "kseen"
  let z ← wordsB n 0
  let k ← lastB n (← nth (← scanB .max .i64 n (some z) [z, g]) 1 "kscan") 1
  pure (k, g, ← nth kg 2 "kseen", ← nth sp 1 "kasc")

/-- The `n`-row columns `cs` at the `m` rows `ix` (`Vals.gather`): an array's `lo` and `hi` gathered, its payload
    kept. -/
def gatherCols (m ix n : Nat) (cs : Cols) : Bld Cols := cs.mapM fun
  | .atom p t e => return .atom p t (← gatherB m ix n e)
  | .arr p c lo hi f => return .arr p c (← gatherB m ix n lo) (← gatherB m ix n hi) f
  | .sum .. => sumB "gather"

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

/-- A `size` register as a `u64` word. -/
def u64B (s : Nat) : Bld Nat := call1 (kernel% USize.toUInt64) #[s]

/-- **`Arr.concat`**: the `n₁` words `x` `kscatter`ed to `pos` and the `n₂` words `y` to `off`, added. -/
def catColB (t : QAtomicType) (n n₁ n₂ off x y : Nat) : Bld Nat := do
  mapB .add n (← scatterB .last n₁ (← posB) x n) (← scatterB .last n₂ off y n) t

/-- **`Arr.clampShift`**: the `n` words `x` clamped into `[0, c]`, then `s` added (`c`, `s` `size` registers). -/
def clampShiftB (n x c s : Nat) : Bld Nat := do
  let a ← mapB .max n x (← wordsB n 0)
  mapB .add n (← mapB .min n a (← constB n (← u64B c))) (← constB n (← u64B s))

/-- **`Vals.concat`** into `n` rows, the two sides' columns paired by position (one object, one `objCols` order):
    atom columns by `catColB`; an array's payloads joined (`catB`, the recursive call) and its `lo`, `hi` each clamped
    into its own payload, the second's shifted past the first (`clampShiftB`). -/
partial def concatB (n n₁ n₂ off : Nat) (xs ys : Cols) : Bld Cols :=
  (xs.zip ys).mapM fun
    | (.atom p t x, .atom _ _ y) => return .atom p t (← catColB t n n₁ n₂ off x y)
    | (.arr p m₁ lo₁ hi₁ f₁, .arr _ m₂ lo₂ hi₂ f₂) => do
      let (m, o) ← catB m₁ m₂
      guard (← call1 (kernel% USize.decLt) #[m, ← lit (.size (2 ^ 63))]) "concat: payload rows m₁ + m₂ past an Int64 bound"
        #[m₁, m₂]
      let z ← lit (.size 0)
      let b (x₁ x₂ : Nat) : Bld Nat := do
        catColB .i64 n n₁ n₂ off (← clampShiftB n₁ x₁ m₁ z) (← clampShiftB n₂ x₂ m₂ m₁)
      return .arr p m (← b lo₁ lo₂) (← b hi₁ hi₂) (← concatB m m₁ m₂ o f₁ f₂)
    | (.sum .., _) | (_, .sum ..) => sumB "∪"
    | _ => throw "concat: two sides of one object with columns of different shapes"

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

/-- **`expand`** of the `K` widths `w`: the count `T` of output rows, each row's group `G` and offset `u` in it. -/
def expandB (K w : Nat) : Bld (Nat × Nat × Nat) := do
  let (P, T) ← prefixB .add K w
  let T1 ← call1 (kernel% USize.add) #[T, ← lit (.size 1)]
  let o ← mapB .sub K P w
  let G ← gatherB T (← posB) T1 (← prefixB .max T1 (← scatterB .max K o (← posB) T1)).1
  pure (T, G, ← mapB .sub T (← posB) (← gatherB T G K o))

/-- **`cellSpan`**: the `n` cells `lo`, `hi` clamped to a payload of `m` rows, `[s, e)`. -/
def spanB (n m lo hi : Nat) : Bld (Nat × Nat) := do
  let s ← mapB .max n lo (← wordsB n 0)
  pure (s, ← mapB .max n (← mapB .min n hi (← constB n (← u64B m))) s)

/-- The registers of the columns `cs`, a loop's state: an atom's `Enc`; an array's `m`, `lo`, `hi`, its payload's. -/
partial def regsOf (cs : Cols) : Bld (List Nat) := return (← cs.mapM fun
  | .atom _ _ e => pure [e]
  | .arr _ m lo hi f => return [m, lo, hi] ++ (← regsOf f)
  | .sum .. => sumB "a loop's state").flatten

/-- The columns `cs` with their registers taken in order from `rs` (`regsOf`'s inverse), and the registers left. -/
partial def withRegs (cs : Cols) (rs : List Nat) : Bld (Cols × List Nat) :=
  cs.foldlM (init := (([] : Cols), rs)) fun (acc, rs) c => match c, rs with
    | .atom p t _, e :: rs => pure (acc ++ [.atom p t e], rs)
    | .arr p _ _ _ f, m :: lo :: hi :: rs => do let (f, rs) ← withRegs f rs; pure (acc ++ [.arr p m lo hi f], rs)
    | .sum .., _ => sumB "a loop's state"
    | _, _ => throw "a loop's state: fewer registers than its columns read"

/-- The types of `regsOf cs`: an `Enc` an object, an array's count a size. -/
partial def tysOf (cs : Cols) : Bld (List Ty) := return (← cs.mapM fun
  | .atom .. => pure [Ty.obj]
  | .arr _ _ _ _ f => return [.size, .obj, .obj] ++ (← tysOf f)
  | .sum .. => sumB "a function's parameters").flatten

/-- `b` on the tables `Ts` as a plan function (`defFun`), applied to their registers (each its count, then `regsOf`):
    a recipe built at many nodes is one C function, not a copy inlined at each (which outgrows `cc -O2`). A function
    whose body equals an earlier one's is that one, so each table shape builds one function. -/
def funT (Ts : List TabB) (b : List TabB → Bld TabB) : Bld TabB := do
  let regs (T : TabB) : Bld (List Nat) := return T.n :: (← regsOf (T.key ++ T.val))
  let tys ← Ts.mapM fun T => return Ty.size :: (← tysOf (T.key ++ T.val))
  let ps := List.range tys.flatten.length
  let shape (Ts : List TabB) (rs : List Nat) : Bld (List TabB) := do
    let (Us, _) ← Ts.foldlM (init := (([] : List TabB), rs)) fun (Us, rs) T => match rs with
      | n :: rs => do
        let (cs, rs) ← withRegs (T.key ++ T.val) rs
        pure (Us ++ [⟨n, cs.take T.key.length, cs.drop T.key.length⟩], rs)
      | [] => throw "a function's parameters: fewer registers than its tables read"
    pure Us
  let (is, n, fs, gs) ← get
  let ((U, r), body, _, fs, gs) ← (do let U ← b (← shape Ts ps); pure (U, (← regs U).toArray)).run (#[], ps.length, fs, gs)
  let F : Fun := ⟨tys.flatten.toArray, body.toList, r⟩
  let (f, fs) := match fs.findIdx? (· == F) with | some i => (i, fs) | none => (fs.size, fs.push F)
  set (is, n, fs, gs)
  let rs ← apply f (← Ts.mapM regs).flatten.toArray r.size
  match ← shape [U] rs.toList with
  | [V] => pure V
  | _ => throw "a function's answer: not one table"

/-- **`Tab.compGroups`**: the `N` rows of `R.val` then `S.key`, their permutation `p`, groups `g`, first rows `f`, the
    count `K` of groups, per group the counts `cR`, `cS` and the width `w = cR · cS`. -/
def groupsB (R S : TabB) : Bld (Nat × Nat × Nat × Nat × Nat × Nat × Nat × Nat) := do
  let (N, off) ← catB R.n S.n
  let (K, g, f, p) ← ascSeenB N (← concatB N R.n S.n off R.val S.key)
  let nR ← constB N (← call1 (kernel% USize.toUInt64) #[R.n])
  let cR ← scatterB .add N g (← mapB .lt N p nR) K
  let cS ← mapB .sub K (← scatterB .add N g (← wordsB N 1) K) cR
  pure (N, p, g, f, K, cR, cS, ← mapB .mul K cR cS)

/-- **`R ≫ S`** (`Tab.compOne`): the groups of equal middle values of `R.val` then `S.key` (`kasc` is stable, so a
    group's `R` rows come first), per group the counts `cR`, `cS` and the width `w = cR · cS`, EXPAND of `w` (each
    output row's group `G` and offset `u`), its `R` row `p[f + u / cS]` and `S` row `p[f + cR + u % cS] - n`, both
    sides gathered there, then `canonT`. `Tab.comp`'s blocks past `blockRows` and its bit matrices change no answer. -/
def compFromB (R S : TabB) (x : Nat × Nat × Nat × Nat × Nat × Nat × Nat × Nat) : Bld TabB := do
  let (N, p, _, f, K, cR, cS, w) := x
  let (T, G, u) ← expandB K w
  let ft ← gatherB T G K f
  let ct ← gatherB T G K cS
  let iR ← gatherB T (← mapB .add T ft (← mapB .div T u ct)) N p
  let qS ← mapB .add T (← mapB .add T ft (← gatherB T G K cR)) (← mapB .mod T u ct)
  let iS ← mapB .sub T (← gatherB T qS N p) (← constB T (← call1 (kernel% USize.toUInt64) #[R.n]))
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
  | .sum .., _ => sumB "a path"
  | _, cs => throw s!"{cs.length} columns where a side of {repr A} is read"

/-- **`⟨R, S⟩`** (`Tab.pair`): `⟨(a, b), a⟩` on `R`'s rows composed with `S`, each key `(a, b)` rebracketed to `a`
    beside `(b, c)`. -/
def pairB (A B C : Obj) (R S : TabB) : Bld TabB := do
  let T ← compB ⟨R.n, (← repath A ".1" R.key) ++ (← repath B ".2" R.val), R.key⟩ S
  let a := objWidth A
  pure ⟨T.n, ← repath A "" (T.key.take a), (← repath B ".1" (T.key.drop a)) ++ (← repath C ".2" T.val)⟩

/-- **`R × S`** (`Tab.prod`): CROSS of the two tables' rows, each row `((a, c), (b, d))`, then `canonT`. -/
def prodB (A B C D : Obj) (R S : TabB) : Bld TabB := do
  let (T, x, y) ← crossB R.n S.n (R.key ++ R.val) (S.key ++ S.val)
  let (a, c) := (R.key.length, S.key.length)
  canonT ⟨T, (← repath A ".1" (x.take a)) ++ (← repath C ".2" (y.take c)),
    (← repath B ".1" (x.drop a)) ++ (← repath D ".2" (y.drop c))⟩

/-- **`Vals.none`**: a side of `A` at `p` with no row: each atom column `Arr.zeros t 0`, an array's `lo`, `hi` the
    same over a payload of no row; `z` the register of the count `0`. -/
partial def noneB (z : Nat) (A : Obj) (p : String := "") : Bld Cols := match A with
  | .atom t => do let c ← wordsB z 0; return [.atom p t (← mapB .add z c c t)]
  | .prod a b => return (← noneB z a (p ++ ".1")) ++ (← noneB z b (p ++ ".2"))
  | .arr b => do
    let c ← wordsB z 0
    return [.arr p z (← mapB .add z c c) (← mapB .add z c c) (← noneB z b (p ++ ".e"))]
  | .sum .. => sumB "𝟘"

/-- A side's columns of the object `A` at the path `p`: each atom column's `Enc` register; a positions column, which
    has no registers (`litSide`), the positions; an array's `lo`, `hi` and payload, its row count a payload column's
    `count`. A column mapped from its file (no `Enc`) is refused, naming it. -/
partial def colsOf (A : Obj) (s : Side) (p : String := "") : Bld Cols := match A with
  | .atom t => match s.lookup p with
    | none => return [.atom p t (← posB)]
    | some rs => match rs[6]? with
      | some e => pure [.atom p t e]
      | none => throw s!"column `{p}` is mapped from its file, whose parts no plan recipe reads as an `Enc` yet"
  | .prod a b => return (← colsOf a s (p ++ ".1")) ++ (← colsOf b s (p ++ ".2"))
  | .arr b => do
    let reg (q : String) (i : Nat) : Option Nat := (s.lookup q).bind (·[i]?)
    let some m := (objCols b (p ++ ".e")).findSome? (reg ·.1 3)
      | throw s!"array `{p}`: no payload column holds a row count register"
    let (some lo, some hi) := (reg (p ++ ".lo") 6, reg (p ++ ".hi") 6)
      | throw s!"array `{p}`: its bounds have no `Enc` register"
    return [.arr p m lo hi (← colsOf b s (p ++ ".e"))]
  | .sum .. => sumB "a side's registers"

/-- The row count of a table's sides: a column's `count` register. -/
def countOf (s : Side × Side) : Bld Nat := match (s.1 ++ s.2).findSome? (·.2[3]?) with
  | some n => pure n
  | none => throw "a table whose every column is positions, so no register holds its row count"

/-- The `n`-row columns `cs` as `output` takes them, in `cols` order: an atom column's registers; an array's `lo`,
    `hi`, then its payload's columns at its count `m`. -/
partial def flatB (n : Nat) (cs : Cols) : Bld Side := return (← cs.mapM fun
  | .atom p t e => return [(p, (← encRegs t n e).push e)]
  | .arr p m lo hi f => return [(p ++ ".lo", (← encRegs .i64 n lo).push lo), (p ++ ".hi", (← encRegs .i64 n hi).push hi)]
      ++ (← flatB m f)
  | .sum .. => sumB "output").flatten

/-- A `TabB`'s sides as `output` takes them: each column's six registers (`encRegs`), then its `Enc`. -/
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

/-- `nth` of an `if`'s one register. -/
def ite1 (c : Nat) (t e : Bld Nat) : Bld Nat := do nth (← ite c (return #[← t]) (return #[← e])) 0 "if"

/-- `c ∧ d`, `d` built only in the branch where `c` holds. -/
def andB (c : Nat) (d : Bld Nat) : Bld Nat := ite1 c d (lit (.bit false))

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
  | .sum .. => sumB "pack"

/-- **`Tab.pack`**: both sides' payloads cut (`packB`). -/
def packT (T : TabB) : Bld TabB := return ⟨T.n, ← packB T.n T.key, ← packB T.n T.val⟩

/-- **`Tab.fixOn`**: rounds of `step` from `X` (`Plan.loop`, the state its count and columns), at most the register
    `k` of them, until a round leaves the row count as it was; that round's table. `k` rounds with the count still
    moving fail with `msg`. Each round's table has its payloads cut (`packT`). -/
def fixB (msg : String) (step : TabB → Bld TabB) (k : Nat) (X : TabB) : Bld TabB := do
  let st (T : TabB) : Bld (Array Nat) := return #[T.n] ++ (← regsOf (T.key ++ T.val)).toArray
  let shape (rs : Array Nat) : Bld TabB := do
    let (cs, _) ← withRegs (X.key ++ X.val) (rs.toList.drop 1)
    pure ⟨← nth rs 0 "loop", cs.take X.key.length, cs.drop X.key.length⟩
  shape (← loop k (← st X) msg fun rs => do
    let X ← shape rs
    let Y ← packT (← step X)
    pure (← st Y, ← call1 (kernel% USize.decEq) #[Y.n, X.n]))

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

/-- `dom U` at the values `c`, `u` the table of `U` in a context. -/
def domAt (u : Dom → Bld TabB) (c : Nat × Cols) : Bld TabB := do let t ← u { dom := some c }; coreflB t.n t.key

/-- **`D ≫ succDen U`** (`Tab.succ`) on the values `X`: `D = idU X`, `≫ dom U`, each value `v` to `v + [v ≠ null]`,
    `≫ dom U`. -/
def succB (u : Dom → Bld TabB) (n : Nat) (X : Cols) : Bld TabB := do
  let D ← coreflB n X
  let E ← compB D (← domAt u (D.n, D.val))
  let v ← col1 E.val
  let s := [.atom "" .i64 (← mapB .add E.n v (← mapB .ne E.n v (← wordsB E.n nulWord)))]
  compB ⟨E.n, E.key, s⟩ (← domAt u (E.n, s))

/-- **`D ≫ arithDen k U`** (`Tab.arith`) on the pairs `X`: `D = idU X`; the rows whose first operand is in `dom U`,
    of those the ones whose second is (two `compB`s, each row keyed by `D`'s key and its operands); `stepB` on the
    operands; the kept rows with their answers (`keepB`); `≫ U`. -/
def arithT (u : Dom → Bld TabB) (t : QAtomicType) (k : UInt8) (n : Nat) (X : Cols) : Bld TabB := do
  let D ← coreflB n X
  let opnd (cs : Cols) (i : Nat) : Bld Cols := match cs[i]? with
    | some (.atom _ t e) => pure [.atom "" t e]
    | _ => throw s!"arith: a pair side of {cs.length} columns, not of two atoms"
  let a ← opnd D.val 0
  let E₁ ← compB ⟨D.n, D.key ++ D.val, a⟩ (← domAt u (D.n, a))
  let b ← opnd E₁.key (D.key.length + 1)
  let E ← compB ⟨E₁.n, E₁.key, b⟩ (← domAt u (E₁.n, b))
  let (w, f) ← stepB t k E.n (← col1 (← opnd E.key D.key.length)) (← col1 (← opnd E.key (D.key.length + 1)))
  let P ← keepB ⟨E.n, E.key.take D.key.length, [.atom "" t w]⟩ f
  compB P (← u { dom := some (P.n, P.val) })

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
def memB (B : Obj) (n : Nat) (X : Cols) : Bld TabB := do
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
  let rs ← ite c (flat t) (flat e)
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
def compBitsB (R S : TabB) : Bld TabB := do
  let (kb, bR, bS, _) ← code2B R.n S.n R.val S.key
  let (ka, aR, ra) ← codeB R.n R.key
  let (kc, cS, rc) ← codeB S.n S.val
  let (ends, idx) ← csrB R.n ka aR bR
  let m ← bitMatrixB S.n kb kc bS cS
  let o ← nth (← callK (kernel% Rel.Kernel.kbitrows) #[← lit (.bit false), kc, kb, R.n, ka, ends, idx, m]) 0 "kbitrows"
  ofBitsB ka kc o R.n R.key ra S.n S.val rc

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
  compSelB Tab.bitsMax R (← s (← if ds then (return { dom := some (← nubB R.n R.val), ran }) else pure {}))

/-- **`Tab.map`** (`F(R)`) on the arrays `X` (`n` rows), `R` the table of the relation on elements: the elements
    EXPANDed (`v`, `T` rows), `⟨pos, v⟩ ≫ R`; where each position has exactly one image, those images in position
    order under the same widths (`Vals.cells`), then `canonT`. Where some element has none or two, `Tab.map` runs its
    left fold (`foldRounds`), which no plan recipe builds yet: the run fails there, naming it. -/
def cellsMapB (B : Obj) (n : Nat) (X : Cols) (R : TabB) : Bld TabB := do
  let (m, lo, hi, f) ← arrCol "F" X
  cellsBoundB "map" n m
  let (s, e) ← spanB n m lo hi
  let w ← mapB .sub n e s
  let (T, G, u) ← expandB n w
  let v ← gatherCols T (← mapB .add T (← gatherB T G n s) u) m f
  let C ← compB ⟨T, [.atom "" .i64 (← posB)], v⟩ R
  let fn ← andB (← call1 (kernel% USize.decEq) #[C.n, T]) do
    call1 (kernel% USize.decEq) #[(← nubB C.n C.key).1, T]
  guard fn ("F(R): an element with no image or with two under R, where `Tab.map` runs its fold (`foldRounds`), " ++
    "which no plan recipe builds yet; images, elements") #[C.n, T]
  let (P, _) ← prefixB .add n w
  canonT ⟨n, X, [.arr "" T (← mapB .sub n P w) (← mapB .add n P (← wordsB n 0)) (← repath B ".e" C.val)]⟩

/-- A row of `kernRows` at `A ⟶ B` given its relations' tables `xs` in a context, by the wrapper its `Tab` operator
    runs under (`Expand.primE`): `floatOp` and `cast` on the values in demand (`GenK.ofVals`), `asc` on its
    relation's whole table (`GenK.ofRel`). Any other row is refused, naming it: each reads or answers an array or a
    sum side. -/
def rowB (r : Prim) (A B : Obj) (D : Dom) (xs : List (Dom → Bld TabB)) : Bld TabB := do
  let some (c, _) := kernRows.lookup r.sym | throw s!"row `{r.sym}`: no `Tab` operator in `kernRows`"
  if c == ``Tab.floatOp then let (n, X) ← known r.sym D.dom; floatOpB r.sym A B n X
  else if c == ``Tab.cast then let (n, X) ← known r.sym D.dom; castB A B n X
  else if c == ``Tab.mem then match A with
    | .arr b => do let (n, X) ← known r.sym D.dom; memB b n X
    | _ => throw s!"row `{r.sym}` (`{c}`) at a source that is no array"
  else if c == ``Tab.map then match A, B, xs with
    -- `GenK.elems`: `R` run knowing its domain is `ran(∋)` at the arrays in demand
    | .arr a, .arr b, [x] => do
      let (n, X) ← known r.sym D.dom
      let M ← memB a n X
      cellsMapB b n X (← x { dom := some (← nubB M.n M.val) })
    | _, _, _ => throw s!"row `{r.sym}` (`{c}`) at objects that are no arrays, or given {xs.length} relations, not one"
  else if c == ``Tab.asc then match xs with
    | [x] => ascB B (← x {})
    | _ => throw s!"asc given {xs.length} relations, not one"
  else throw s!"row `{r.sym}` (`{c}`): it reads or answers an array or a sum side, whose `cells` keys no plan recipe builds yet"

/-- **`Tab.nil`** on the keys `X` (`n` rows): each to the empty cell, `lo = hi = 0` over a payload of no row of `B`;
    then `canonT`. -/
def nilB (B : Obj) (n : Nat) (X : Cols) : Bld TabB := do
  let c ← wordsB n 0
  let z ← mapB .add n c c
  let z0 ← lit (.size 0)
  canonT ⟨n, X, [.arr "" z0 z z (← noneB z0 B ".e")]⟩

/-- **`Tab.atPos k`** on the arrays `X` (`n` rows): the cells wider than `k` (`whereB` of `k < e - s`), each to the
    payload at `s + k`; then `canonT`. `s + k` is read signed, so `m + k` stays below `2^63`. -/
def atB (B : Obj) (k n : Nat) (X : Cols) : Bld TabB := do
  let (m, lo, hi, f) ← arrCol "at" X
  guard (← call1 (kernel% USize.decLt) #[← call1 (kernel% USize.add) #[m, ← lit (.size k.toUSize)],
    ← lit (.size (2 ^ 63))]) s!"at: position {k} in a payload of m rows, past 2^63" #[m]
  let (s, e) ← spanB n m lo hi
  let kc ← constB n (← lit (.u64 k.toUInt64))
  let (M, sel) ← whereB n (← mapB .lt n kc (← mapB .sub n e s))
  let ix ← gatherB M sel n (← mapB .add n s kc)
  canonT ⟨M, ← gatherCols M sel n X, ← repath B "" (← gatherCols M ix m f)⟩

/-- **`Tab.lam`** on the keys `X` (`n` rows) of `R` (`lamOf` of `canonT R`): one GROUP over `X` then `r`'s keys, a
    group's `X` rows (`cD`, input row below `n`) first; its cell the sorted rows `[f + cD, f + c)` of `r.val` gathered
    in sorted order (`r.val` itself where `r` has no row, an `ite`); the groups with `0 < cD` kept, keyed by their
    first row; then `canonT`. -/
def lamB (B : Obj) (n : Nat) (X : Cols) (R : TabB) : Bld TabB := do
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
/-- **`𝟘`** at `A ⟶ B`: no row. -/
def zeroB (A B : Obj) : Bld TabB := do let z ← lit (.size 0); pure ⟨z, ← noneB z A, ← noneB z B⟩

/-- What each variable reads (`Code`'s twin): its table at the objects and in the context its use gives it. -/
abbrev Vars := List (Nat × ((A B : Obj) → Dom → Bld TabB))

/-- A variable bound to the registers `s` of a table (an input, a run-time definition): `s` in every context. -/
def sideArg (s : Side × Side) : (A B : Obj) → Dom → Bld TabB :=
  fun A B _ => return ⟨← countOf s, ← colsOf A s.1, ← colsOf B s.2⟩

mutual
/-- **A term's table**, each node by the `Tab` operators its `GenK` code runs (design §4), its variables `σ` what
    each reads (`Vars`), `D` the values its context knows its source to hold (`compT`: a composition's left
    operand's range). A node on demand is read at `D`; a closed node ignores it, and its full table is a superset
    that every consumer of a `D`-bounded answer cuts alike. The nodes no plan recipe builds are refused, naming
    them and what they need. -/
partial def tabB (σ : Vars) (D : Dom) : {A B : Obj} → Tm A B → Bld TabB
  | A, B, .val R => do
    let (k, v) := (← litSide R.key, ← litSide R.val)
    canonT ⟨← lit (.size R.n), ← colsOf A k, ← colsOf B v⟩
  | A, _, .uni (m := m) U => do coreflB (← lit (.size m)) (← colsOf A (← litSide U))
  | A, B, .zero => zeroB A B
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
  | _, _, .comp R S => do compTB (← tabB σ { dom := D.dom } R) (tabB σ · S) S.dem D.ran
  | _, _, .conv R => do
    let r ← tabB σ ⟨D.ran, D.dom, D.pairs.map fun p => ⟨p.n, p.val, p.key⟩⟩ R; canonT ⟨r.n, r.val, r.key⟩
  | _, _, .meet R S => do
    let (r, s) ← bothB (tabB σ · R) (tabB σ · S) R.dem S.dem D boundOf
    interB r s
  | _, _, .join R S => do unionB (← tabB σ D R) (← tabB σ D S)
  | _, _, .diff R S => do
    let r ← tabB σ D R
    selectB (fun m _ mx => mapB .not m mx mx) r (← tabB σ (← if S.dem then boundOf r else pure D) S)
  | _, _, .dom R => do let r ← tabB σ { dom := D.dom <|> D.ran } R; coreflB r.n r.key
  | _, _, .ran R => do let r ← tabB σ { ran := D.dom <|> D.ran } R; coreflB r.n r.val
  | _, _, .pair (A := A) (B := B) (C := C) R S => do
    let (r, s) ← bothB (tabB σ · R) (tabB σ · S) R.dem S.dem { dom := D.dom }
      fun t => return { dom := some (← domOf t) }
    pairB A B C r s
  | _, _, .prod (A := A) (B := B) (C := C) (D := D') R S => do prodB A B C D' (← tabB σ {} R) (← tabB σ {} S)
  | _, _, .own R | _, _, .share _ R => tabB σ D R
  | A, B, .var _ k => match σ.lookup k with
    | some b => b A B D
    | none => throw s!"variable {k}, which no input table or call argument is bound to"
  | _, _, .nu k S b => do nuB (fun X => tabB ((k, fun _ _ _ => pure X) :: σ) {} b) (← tabB σ {} S)
  | A, B, .mu k w cap b => do
    muB (Tab.capMsg w cap) (← sizeB (cap - 1)) (fun X => tabB ((k, fun _ _ _ => pure X) :: σ) {} b)
      (← tabB σ {} (.zero : Tm A B))
  | A, B, .hylo k w b => do
    -- `GenK.hylo` on the keys `X` in demand: the nodes `N`, no cycle among them (`ν`), then `D ≫ μY : N ≫ φ(Y)`
    let (n, X) ← known "hylo" D.dom
    let some ch := b.kids k A | throw s!"Tm.gen: {w} gives the hylo no children (Tm.kids)"
    let Dt ← coreflB n X
    let N ← muB (Tab.capMsg w USize.size) (← sizeB (USize.size - 1)) (fun N => do
        let C ← compTB N (tabB σ · ch) ch.dem; unionB Dt (← coreflB C.n C.val))
      (← tabB σ {} (.zero : Tm A A))
    let C ← compTB N (tabB σ · ch) ch.dem
    let cyc ← nuB (fun P => do let CP ← compB C P; coreflB CP.n CP.key) N
    guard (← call1 (kernel% USize.decEq) #[cyc.n, ← lit (.size 0)]) (GenK.cycleMsg w) #[cyc.n, N.n]
    compB Dt (← muB s!"{w} ran its cap of its nodes' count + 3 rounds without reaching a fixed point"
      (← call1 (kernel% USize.add) #[N.n, ← lit (.size 2)])
      (fun Y => compTB N (tabB ((k, fun _ _ _ => pure Y) :: σ) · b) b.dem) (← tabB σ {} (.zero : Tm A B)))
  | _, _, .leq t U => cmpB (tabB σ · U) "≤" (Tab.ordOp false t) t D
  | _, _, .lt t U => cmpB (tabB σ · U) "<" (Tab.ordOp true t) t D
  | _, _, .succ U => do let (n, X) ← known "succ" D.dom; succB (tabB σ · U) n X
  | _, _, .arith t k U => do let (n, X) ← known "arith" D.dom; arithT (tabB σ · U) t k n X
  | A, B, t@(.prim _) | A, B, t@(.arg ..) | A, B, t@(.call ..) | A, B, t@(.callCv ..) => argB σ D A B t []
  -- `GenK.ldiv`'s bit-matrix `S` (`ldivM`) answers the table `ldivSel` does (`Tab.ldivTabMat_law`); a plan's `S` is rows
  | _, _, .ldiv R S UB UC => do
    ldivSelB ldivB Tab.bitsMax (← tabB σ {} R) (← tabB σ {} S) (← tabB σ {} UB) (← tabB σ {} UC)
  | _, _, .rdiv R S UA UB => do rdivB (← tabB σ {} R) (← tabB σ {} S) (← tabB σ {} UA) (← tabB σ {} UB)
  | _, _, .lam (B := B) R => do
    let (n, X) ← known "Λ" D.dom
    lamB B n X (← tabB σ { dom := some (n, X) } R)
  | _, _, .E (A := A) (B := B) R => do
    let (n, X) ← known "E" D.dom
    lamB B n X (← compTB (← memB A n X) (tabB σ · R) R.dem)
  | _, _, .nil (B := B) => do let (n, X) ← known "nil" D.dom; nilB B n X
  | _, _, .atPos (B := B) k => do let (n, X) ← known "at" D.dom; atB B k n X
  | _, _, .est _ | _, _, .thin _ | _, _, .fold .. | _, _, .foldr .. | _, _, .foldI .. => throw
    "`est`, `thin`, a fold: their recipes (`Tab.est`, `Tab.thin`, `Tab.foldRounds` on `Instr.loop`) are not built by a plan yet"


/-- A spine `f x₁ … xₖ` (`Tm.argGen`) given its later relations `xs`, in the context `D`: a row by `rowB`, each
    relation's table built in the context the row's wrapper gives it; a call by its body under its arguments bound at
    `ks` and no other variable (`Code.args`). An argument is built at each use in the context the use gives it where
    it runs on demand, or where it cannot run closed (`GenK.memo` keeps it lazy); else once, closed (`GenK.memo`).
    A use at other objects than the argument's reads `𝟘` (`Code.bind`). -/
partial def argB (σ : Vars) (D : Dom) (A B : Obj) :
    Tm A B → List ((C : Obj) × (E : Obj) × Tm C E) → Bld TabB
  | .arg f x, xs => argB σ D A B f (⟨_, _, x⟩ :: xs)
  | .share _ R, xs => argB σ D A B R xs
  | .call ks _ _ b, xs | .callCv ks _ _ _ b _, xs => do
    let bs ← (ks.zip xs).mapM fun (k, ⟨C, E, x⟩) => do
      let at_ (b : Dom → Bld TabB) : (A' B' : Obj) → Dom → Bld TabB :=
        fun A' B' D' => if C = A' ∧ E = B' then b D' else zeroB A' B'
      let lazy := at_ (tabB σ · x)
      if x.dem then pure (k, lazy) else
        try let t ← tabB σ {} x; pure (k, at_ fun _ => pure t) catch _ => pure (k, lazy)
    tabB bs D b
  | .prim r, xs => rowB r A B D (xs.map fun ⟨_, _, x⟩ => (tabB σ · x))
  | t, [] => tabB σ D t
  | _, xs => throw s!"{xs.length} relations given to a term that is no row and no call"
end

/-- The registers of a term's value, key side then value side, its variables `σ` the registers of the tables bound
    to them (a run-time definition's inputs, `Once.binds`): a variable's own registers, else `tabB`'s table. -/
def ofTm (σ : List (Nat × Side × Side)) : {A B : Obj} → Tm A B → Bld (Side × Side)
  | _, _, .var _ k => match σ.lookup k with
    | some s => pure s
    | none => throw s!"variable {k}, which no input table is bound to"
  | _, _, .share _ R => ofTm σ R
  | _, _, t => do sidesOf (← tabB (σ.map fun (k, s) => (k, sideArg s)) {} t)


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
