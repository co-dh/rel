import Rel.Run.Lang.Plan
import Rel.Run.Lang.Schema
import Rel.Kernel.Db.ObjectFile
import Rel.Kernel.Db.Csv
import Rel.Kernel.Cast
import Rel.Run.Cols
import Rel.Run.Canon
import Rel.Run.Lang.Lazy

/-! # A table directory (PLAN D.9, `doc/dataframe-design.zh.typ` F6)

A directory is a table and a file one column: an own-format file written by `Db.ownWrite` and mapped back by
`Db.ownMap`, its parts taken as they lie, so nothing is decoded, converted or copied. A side's files are the paths
`cols` gives its atom columns under a prefix, the column's name; a positions column has no file (`Db.ownParts`), so a
frame's key `0 … n-1` is not on disk.

A side is read and written by a `Schema`: each column's files under its name. A side that is not a record is the
one-column schema named by the side, `[("key", A)]` or `[("val", B)]`. The two forms of a table on disk:

- positional, `N ⟶ S`: the value side's columns in `dir`, rows in key order, renumbered `0 … n-1`; no key file
  (`write`, `read`, the renumbering `frame_holds`);
- keyed, `K ⟶ S` with `K` not the positions (q's keyed table, a dictionary from a key table to a value table): two
  positional tables of one length, `dir/key` and `dir/val` (`writeKeyed`, `readKeyed`).

Which form a result takes is decided by its key OBJECT where the program is elaborated (`Expand.emit`), never by
reading the key column. A CSV file is the same two forms in one file, key columns then value columns (IO design D),
read straight into encoded columns (`Db.csvRead`) and written straight from them (`Db.csvWrite`). This is the code `n.io` calls (lib `RelRun`); the laws about it
are in `Rel.Lang.Table`. -/

namespace Rel.Lang.Table

open Rel Rel.Lang.Plan

/-- The file of the column `q` in the table directory `dir`. -/
def file (dir q : String) : String := (System.FilePath.mk dir / q).toString

/-- The one column writer of a side: each atom column of `x` (`cols` under the prefix `p`) to `file dir <path>`; a
    positions column has no file. -/
def writeVals {A : Obj} {n : USize} (dir p : String) (x : Vals A n) : IO Unit := do
  for (q, v) in cols A x p do
    if let some f ← IO.ofExcept (ownFile q v) then
      Db.ownWrite (file dir q) f.code f.attr f.kind f.count f.domain f.parts

/-- The bit pattern of a word of type `t` that is not in the canonical form `Obj.key` and the kernels assume (typed
    base design, R7 and decision D: a NaN has no row, `-0` is `+0`), `none` for a canonical word: the stored word
    (`QAtomicType.word`) where `QAtomicType.nonCanonical`, the one predicate, holds of it. -/
def nonCanonical (t : QAtomicType) (b : El t) : Option Nat :=
  if t.nonCanonical (t.word b) then some (t.word b).toNat else none

/-- The atom column of type `t` mapped from `path`: the header's type code and domain checked, the parts taken as
    they lie (`Db.ownEnc`) and entered through `Arr.of`, which decides `Enc.WF`; a float column's words checked to be
    canonical (`nonCanonical`), the first row that is not refused. The header's attribute is a promise nothing here
    re-checks, so it is not taken over. -/
def readArr (t : QAtomicType) (path : String) : IO ((n : USize) × Arr t n) := do
  if t matches .sym then
    throw (IO.userError s!"{path}: a symbol column, which waits for the own-format sym writer (D.9 step 6)")
  if t matches .general then throw (IO.userError s!"{path}: a general column, which the own format does not hold")
  let f ← Db.ownMap path
  unless f.code == t.code.toUInt8 do
    throw (IO.userError s!"{path}: atom type code {f.code}, the column is {repr t} (code {t.code})")
  unless f.domain.isEmpty do
    throw (IO.userError s!"{path}: an enumeration over `{f.domain}`, which waits for the own-format sym writer \
      (D.9 step 6)")
  let some e := Db.ownEnc f.kind f.parts
    | throw (IO.userError s!"{path}: constructor kind {f.kind}, which `Db.ownEnc` does not rebuild")
  let x ← IO.ofExcept (Arr.of t f.count (.vector t f.count e none) path)
  if t matches .f32 | .f64 then
    if let some (b, i) := x.toList.zipIdx.findSome? fun (v, i) => (nonCanonical t v).map (·, i) then
      throw (IO.userError s!"{path}: row {i} holds the {repr t} bit pattern 0x{String.mk (Nat.toDigits 16 b)}, \
        which is not canonical (a NaN or -0)")
  return ⟨f.count, x⟩

/-- `y`, read from `fy`, as a column of the side whose count `n` was read from `fx`: the two counts are equal. -/
def same {F : USize → Type} (fx : String) (n : USize) (fy : String) (y : (m : USize) × F m) : IO (F n) :=
  if h : y.1 = n then pure (h ▸ y.2)
  else throw (IO.userError s!"{fy} has {y.1} rows and {fx} has {n}: the columns of one side have one count")

/-- The inverse of `cols`: the side of object `A` mapped from the files `cols` names under the prefix `p` in `dir`,
    with its count and the file the count was read from. The columns of one side have its count; a list's payload
    and a sum's two payloads have their own. The paths are `cols`'s (`TestTable` round-trips each form). -/
def readVals : (A : Obj) → (dir p : String) → IO (String × (n : USize) × Vals A n)
  | .atom t, dir, p => do let ⟨n, x⟩ ← readArr t (file dir p); return (file dir p, ⟨n, x⟩)
  | .prod a b, dir, p => do
    let (fx, ⟨n, x⟩) ← readVals a dir (p ++ ".1")
    let (fy, y) ← readVals b dir (p ++ ".2")
    return (fx, ⟨n, x, ← same fx n fy y⟩)
  | .arr b, dir, p => do
    let ⟨n, lo⟩ ← readArr .i64 (file dir (p ++ ".lo"))
    let hi ← same (file dir (p ++ ".lo")) n (file dir (p ++ ".hi")) (← readArr .i64 (file dir (p ++ ".hi")))
    let (_, ⟨m, e⟩) ← readVals b dir (p ++ ".e")
    return (file dir (p ++ ".lo"), ⟨n, m, lo, hi, e⟩)
  | .sum a b, dir, p => do
    let ⟨n, tag⟩ ← readArr .u1 (file dir (p ++ ".tag"))
    let idx ← same (file dir (p ++ ".tag")) n (file dir (p ++ ".idx")) (← readArr .i64 (file dir (p ++ ".idx")))
    let (_, ⟨l, x⟩) ← readVals a dir (p ++ ".l")
    let (_, ⟨r, y⟩) ← readVals b dir (p ++ ".r")
    return (file dir (p ++ ".tag"), ⟨n, l, r, tag, idx, x, y⟩)

/-- The columns of `R`, a schema reversed (`Schema.objR`'s order), from `x`: each column's files under its name. -/
def writeCols {n : USize} (dir : String) : (R : Schema) → Vals (Schema.objR .long .prod R) n → IO Unit
  | [], _ => pure ()
  | [f], x => writeVals (A := f.2) dir f.1 x
  | f :: g :: R, x => do writeCols dir (g :: R) x.1; writeVals (A := f.2) dir f.1 x.2

/-- The columns of `R`, a schema reversed, read from their files under their names, with their one count and the file
    it was read from. -/
def readCols (dir : String) : (R : Schema) → IO (String × (n : USize) × Vals (Schema.objR .long .prod R) n)
  | [] => throw (IO.userError s!"{dir}: {Schema.noColumn}")
  | [f] => readVals f.2 dir f.1
  | f :: g :: R => do
    let (fx, ⟨n, x⟩) ← readCols dir (g :: R)
    let (fy, y) ← readVals f.2 dir f.1
    return (fx, ⟨n, x, ← same (F := Vals f.2) fx n fy y⟩)

/-- The side of schema `S` in the directory `dir`, one file per column (an atom column) or per atom of it (`cols`),
    named by the column. -/
def write {n : USize} (S : Schema) (dir : String) (x : Vals S.obj n) : IO Unit := do
  IO.ofExcept S.check; IO.FS.createDirAll dir; writeCols dir S.reverse x

/-- The side of schema `S` read from `dir`: the columns `S` names, each at its declared object, all of one count; a
    missing file, another atom type or another count is the error naming the file. -/
def readSide (S : Schema) (dir : String) : IO (String × (n : USize) × Vals S.obj n) := do
  IO.ofExcept S.check; readCols dir S.reverse

/-- The frame of the value side `x`: its key the positions `0 … n-1`, which are on no file. -/
def frame {B : Obj} {n : USize} (x : Vals B n) : Except String (Tab .long B) := (Arr.pos n).map fun P => ⟨n, P, x⟩

/-- The positional table of schema `S` in `dir`: its rows' key the positions. -/
def read (S : Schema) (dir : String) : IO (Tab .long S.obj) := do
  let (_, ⟨_, x⟩) ← readSide S dir; IO.ofExcept (frame x)

/-- A keyed table, q's dictionary from a key table to a value table: the key side's columns in `dir/key`, the value
    side's in `dir/val`, row `i` of each the pair `i` of `t`. -/
def writeKeyed (K S : Schema) (dir : String) (t : Tab K.obj S.obj) : IO Unit := do
  write K (file dir "key") t.key; write S (file dir "val") t.val

/-- A keyed table's rows sorted by key with equal rows merged (`Tab.canon`), as every kernel takes a table: a file's
    row order and duplicates are not kept, a relation being a set; its error after `what`. -/
def canon {K B : Obj} (what : String) (t : Tab K B) : Except String (Tab K B) := t.canon.mapError (s!"{what}: " ++ ·)

/-- The keyed table of key schema `K` and value schema `S` in `dir`: `dir/key` and `dir/val`, of one count. -/
def readKeyed (K S : Schema) (dir : String) : IO (Tab K.obj S.obj) := do
  let (fk, ⟨n, k⟩) ← readSide K (file dir "key")
  let (fv, v) ← readSide S (file dir "val")
  IO.ofExcept (canon dir ⟨n, k, ← same fk n fv v⟩)

/-- The first part of `es` as an atom column of type `t`, entered through `Arr.of` as `readArr` enters a mapped one;
    its count, and the parts left over. -/
def encArr (path : String) (t : QAtomicType) : List (USize × Enc) →
    Except String ((n : USize) × Arr t n × List (USize × Enc))
  | (k, e) :: es => do pure ⟨k, ← Arr.of t k (.vector t k e none) s!"{path}: a {repr t} column part of {k} rows", es⟩
  | [] => .error s!"{path}: no column part left for a {repr t} column"

/-- A side of object `A` from its atom columns' encodings `es`, each with its count, in `cols`' order (a sum's tags,
    positions and two payloads; a list's bounds and payload), the converse of `csvEncs`: each entered through `Arr.of`
    as `readArr` enters a mapped one; the side's count, and the parts left over. -/
def encVals (path : String) : (A : Obj) → List (USize × Enc) →
    Except String ((n : USize) × Vals A n × List (USize × Enc))
  | .atom t, es => encArr path t es
  | .prod a b, es => do
    let ⟨n, x, es⟩ ← encVals path a es
    let ⟨m, y, es⟩ ← encVals path b es
    if h : m = n then pure ⟨n, (x, h ▸ y), es⟩ else .error s!"{path}: columns of {n} and {m} rows on one side"
  | .arr b, es => do
    let ⟨n, lo, es⟩ ← encArr path .i64 es
    let ⟨m, hi, es⟩ ← encArr path .i64 es
    let ⟨k, f, es⟩ ← encVals path b es
    if h : m = n then pure ⟨n, ⟨k, lo, h ▸ hi, f⟩, es⟩ else .error s!"{path}: list bounds of {n} and {m} rows"
  | .sum a b, es => do
    let ⟨n, tag, es⟩ ← encArr path .u1 es
    let ⟨m, idx, es⟩ ← encArr path .i64 es
    let ⟨l, x, es⟩ ← encVals path a es
    let ⟨r, y, es⟩ ← encVals path b es
    if h : m = n then pure ⟨n, ⟨l, r, tag, h ▸ idx, x, y⟩, es⟩ else .error s!"{path}: sum tags of {n} and positions of {m} rows"

/-- How many atom columns `A` has when it is a product of atoms (the `S` of a CSV `S+1`); none for any other object. -/
def atomCount : Obj → Option Nat
  | .atom _ => some 1
  | .prod a b => return (← atomCount a) + (← atomCount b)
  | _ => none

/-- The parts of a side of object `A`, `ps` in `cols`' order, as its CSV columns' parts (`Db.CsvShape.atoms`), with
    the parts left over. A sum is the CSV `S+1` (`Expand.csvLeaves`): one nullable column per atom of `S`, each with
    its own copy of the sum's tags, positions and null values; every other part as it lies. -/
def toCsv {α : Type} (path : String) : Obj → List α → Except String (List α × List α)
  | .atom _, x :: ps => pure ([x], ps)
  | .prod a b, ps => do let (x, ps) ← toCsv path a ps; let (y, ps) ← toCsv path b ps; pure (x ++ y, ps)
  | .arr (.atom _), lo :: hi :: e :: ps => pure ([lo, hi, e], ps)
  | .sum a (.atom _), t :: i :: ps => match atomCount a, ps.drop (atomCount a |>.getD 0) with
    | some k, r :: ps' => pure ((ps.take k).flatMap fun v => [t, i, v, r], ps')
    | _, _ => .error s!"{path}: a sum whose left is no product of atoms, or too few parts for it, has no CSV columns"
  | _, _ => .error s!"{path}: a side whose object is no CSV column set (a list of no atom, a sum of no `S+1`), or too few parts"

/-- `k` groups of four parts from the front of `cs` (one CSV nullable column's tags, positions, values, nulls), and
    the parts left. -/
def quads {α : Type} : Nat → List α → Option (List (α × α × α × α) × List α)
  | 0, cs => some ([], cs)
  | k + 1, t :: i :: v :: r :: cs => (quads k cs).map fun (g, cs) => ((t, i, v, r) :: g, cs)
  | _ + 1, _ => none

/-- The converse of `toCsv`: the side `A`'s parts in `cols`' order from its CSV columns' parts `cs`, the header names
    of those columns `ns` in step, with what is left of both. The nullable columns of one `S+1` are null in the same
    rows (the `1` is every field of `S` empty): their tags must agree, else the first row where two differ is named. -/
def ofCsv (path : String) : Obj → List (USize × Enc) → List String →
    Except String (List (USize × Enc) × List (USize × Enc) × List String)
  | .atom _, x :: cs, _ :: ns => pure ([x], cs, ns)
  | .prod a b, cs, ns => do
    let (x, cs, ns) ← ofCsv path a cs ns; let (y, cs, ns) ← ofCsv path b cs ns; pure (x ++ y, cs, ns)
  | .arr (.atom _), lo :: hi :: e :: cs, _ :: ns => pure ([lo, hi, e], cs, ns)
  | .sum a (.atom _), cs, ns => do
    let some k := atomCount a | .error s!"{path}: a sum whose left is no product of atoms has no CSV columns"
    let some ((t, i, v, r) :: g, cs) := quads k cs | .error s!"{path}: too few column parts for {k} nullable columns"
    let some c := ns.head? | .error s!"{path}: no header name left for a nullable column"
    let ⟨n, x, _⟩ ← encArr path .u1 [t]
    for ((t', _), c') in g.zip ns.tail do
      let ⟨m, y, _⟩ ← encArr path .u1 [t']
      unless m = n do .error s!"{path}: nullable columns '{c}' of {n} rows and '{c'}' of {m}"
      for j in [0:n.toNat] do
        if hj : j < n.toNat ∧ j < m.toNat then
          let (a, b) := (x.get ⟨j, hj.1⟩, y.get ⟨j, hj.2⟩)
          let s (z : Bool) := if z then "empty (null)" else "not empty"
          unless a == b do
            .error s!"{path}: data row {j + 1}: column '{c}' is {s a} and column '{c'}' is {s b}; the columns of one \
              `S+1` are empty together, and all of them empty is the `1`"
    pure ([t, i, v] ++ g.map (·.2.2.1) ++ [r], cs, ns.drop k)
  | _, _, _ => .error s!"{path}: a side whose object is no CSV column set (a list of no atom, a sum of no `S+1`), or too few parts"

/-- The CSV file `path` as the table `K ⟶ S`, its header `cols` (the key's columns then the value's, `Db.CsvCols`),
    each column read straight into its encoding (`Db.csvRead`, `ofCsv`, `encVals`); `K = []`: positions, the frame of
    its rows (`frame`), else keyed, its rows canonical (`canon`). -/
def readCsv (K S : Schema) (cols : Db.CsvCols) (path : String) : IO (Tab K.obj S.obj) := do
  let (n, es) ← Db.csvRead path cols
  let side (R : Schema) (es : List (USize × Enc)) (ns : List String) :
      Except String (Vals R.obj n × List (USize × Enc) × List String) := do
    let (ps, es, ns) ← ofCsv path R.obj es ns
    let ⟨m, x, rest⟩ ← encVals path R.obj ps
    unless rest.isEmpty do .error s!"{path}: {rest.length} column parts past a side"
    if h : m = n then pure (h ▸ x, es, ns) else .error s!"{path}: a side of {m} rows in a file of {n}"
  let done (es : List (USize × Enc)) : Except String Unit :=
    unless es.isEmpty do .error s!"{path}: {es.length} column parts past the schema"
  let ns := cols.map (·.1)
  match K with
  | [] => IO.ofExcept (do let (v, es, _) ← side S es ns; done es; frame v)
  | K => IO.ofExcept (do
    let (k, es, ns) ← side K es ns
    let (v, es, _) ← side S es ns
    done es; canon path ⟨n, k, v⟩)

/-- The encodings of the side `x`'s CSV columns' parts with their counts (`toCsv` of `cols`' order), as
    `Db.CsvShape.atoms` lists them; which objects a CSV column may be is `Db.Csv.schema`'s to say. -/
def csvEncs {A : Obj} {n : USize} (path : String) (x : Vals A n) : Except String (List (USize × Enc)) := do
  let ps ← (cols A x "").mapM fun
    | (_, .vector _ k e _) => .ok (k, e)
    | (p, _) => .error s!"{path}: column part `{p}` is not a vector"
  let (cs, rest) ← toCsv path A ps
  unless rest.isEmpty do .error s!"{path}: {rest.length} column parts past a side"
  pure cs

/-- The table `t : K ⟶ S` as the CSV file `path`, the converse of `readCsv`: its header `cols`, then each row's key
    columns and value columns, written from their encodings (`Db.csvWrite`); `K = []`: positions, the value columns
    only, rows renumbered by their order, as `write` drops the key. -/
def writeCsv (K S : Schema) (cols : Db.CsvCols) (path : String) (t : Tab K.obj S.obj) : IO Unit := do
  let ks ← match K with | [] => pure [] | _ => IO.ofExcept (csvEncs path t.key)
  Db.csvWrite path cols t.n (ks ++ (← IO.ofExcept (csvEncs path t.val)))

/-- The table of the run-time definition `x` (IO design B): its code run closed, as a closed definition's is
    (`Expand.emit`), its error the op's message after `x`. -/
def ofRun {A B : Obj} (x : String) (r : Rel.Rel A B) : IO (Tab A B) :=
  IO.ofExcept ((r.runE {}).mapError (s!"{x}: " ++ ·))

end Rel.Lang.Table
