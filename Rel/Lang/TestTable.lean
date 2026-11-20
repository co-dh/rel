import Rel.Lang.Table
import Rel.Run.Cols

/-! The table directory read back as written (`Table.writeVals`, `Table.readVals`): a frame of three long columns
under one prefix, a named column, a list side, and the refusals. The directories are under `/data/tmp`. -/

namespace Rel.Lang.TestTable

open Rel Rel.Lang.Table Rel.Kernel

/-- The test's table directory `d`, emptied. -/
def fresh (d : String) : IO String := do
  let p := file "/data/tmp/rel-test-table" d
  if ← System.FilePath.pathExists p then IO.FS.removeDirAll p
  IO.FS.createDirAll p
  return p

/-- The `i64` column of `xs`, encoded as the kernels encode their answers (`wordsFoR`). -/
def longs (n : USize) (xs : List Int64) : IO (Vals .long n) :=
  IO.ofExcept (Arr.of .i64 n (.vector .i64 n (wordsFoR (xs.map Int64.toUInt64).toArray) none) "literal")

/-- The names in the directory `dir`, sorted. -/
def names (dir : String) : IO (List String) :=
  return (((← System.FilePath.readDir dir).map (·.fileName)).qsort (· < ·)).toList

/-- `x` written under `p` in `d` and read back: the frames' rows are equal, and the files are `cols`'s paths. -/
def roundTrip {B : Obj} [BEq B.El] {n : USize} (d p : String) (x : Vals B n) : IO (Bool × List String) := do
  let dir ← fresh d
  writeVals dir p x
  let (_, ⟨_, y⟩) ← readVals B dir p
  return ((← IO.ofExcept (frame x)).toList == (← IO.ofExcept (frame y)).toList, ← names dir)

/-- An `IO` answer as text. -/
def say {α : Type} (r : Except IO.Error α) : String := match r with | .ok _ => "ok" | .error e => toString e

-- three long columns of four rows under the prefix `t`: `t.1`, `t.2.1`, `t.2.2`
/-- info: (true, ["t.1", "t.2.1", "t.2.2"]) -/
#guard_msgs in
#eval show IO _ from do
  let x : Vals (.prod .long (.prod .long .long)) 4 :=
    (← longs 4 [3, 1, 4, 1], ← longs 4 [5, 9, 2, 6], ← longs 4 [-5, 0, 7, 1099511627776])
  roundTrip "prod" "t" x

-- a column named `qty`: its file is its name
/-- info: (true, ["qty"]) -/
#guard_msgs in
#eval show IO _ from do roundTrip (B := .long) "named" "qty" (← longs 3 [10, 20, 30])

-- a list side: `.lo`, `.hi` of the rows' count, `.e` the payload's own
/-- info: (true, ["l.e", "l.hi", "l.lo"]) -/
#guard_msgs in
#eval show IO _ from do
  let x : Vals (.arr .long) 2 := ⟨3, ← longs 2 [0, 2], ← longs 2 [2, 3], ← longs 3 [7, 8, 9]⟩
  roundTrip "list" "l" x

-- the refusals, each naming its file: a missing file, two columns of one side whose counts differ, a type code
-- other than the declared one (a long read as a float among them), and the symbol column no reader takes yet
/--
info: no such file or directory (error code: 2)
  file: /data/tmp/rel-test-table/bad/nope
/data/tmp/rel-test-table/bad/u.2 has 3 rows and /data/tmp/rel-test-table/bad/u.1 has 4: the columns of one side have one count
/data/tmp/rel-test-table/bad/u.1: atom type code 7, the column is Rel.QAtomicType.u8 (code 4)
/data/tmp/rel-test-table/bad/u.1: atom type code 7, the column is Rel.QAtomicType.f64 (code 9)
/data/tmp/rel-test-table/bad/u.1: a symbol column, which waits for the own-format sym writer (D.9 step 6)
-/
#guard_msgs in
#eval show IO Unit from do
  let dir ← fresh "bad"
  writeVals (A := .long) dir "u.1" (← longs 4 [1, 2, 3, 4]); writeVals (A := .long) dir "u.2" (← longs 3 [1, 2, 3])
  IO.println (say (← (readVals .long dir "nope").toBaseIO))
  IO.println (say (← (readVals (.prod .long .long) dir "u").toBaseIO))
  IO.println (say (← (readVals (.atom .u8) dir "u.1").toBaseIO))
  IO.println (say (← (readVals (.atom .f64) dir "u.1").toBaseIO))
  IO.println (say (← (readVals (.atom .sym) dir "u.1").toBaseIO))

/-! ## Schema-named tables: the two output forms -/

/-- The value side of a trade: three long columns. -/
def Trade : Schema := [("id", .long), ("px", .long), ("qty", .long)]

/-- A value side of two columns, a key side of two, a float column. -/
def V : Schema := [("px", .long), ("qty", .long)]
def K : Schema := [("a", .long), ("b", .long)]
def S : Schema := [("x", .atom .f64)]

/-- A trade's value side of `n` rows. -/
def trades (n : USize) (id px qty : List Int64) : IO (Vals Trade.obj n) :=
  return ((← longs n id, ← longs n px), ← longs n qty)

-- a positional table: the files are the schema's columns, no key file; read back by the schema, its key the positions
/--
info: ([((0 : Int64), ((10 : Int64), (500 : Int64)), (5 : Int64)), (1, (20, 50), 7), (2, (30, 900), 9)], ["id", "px", "qty"])
-/
#guard_msgs in
#eval show IO _ from do
  let dir ← fresh "positional"
  write Trade dir (← trades 3 [10, 20, 30] [500, 50, 900] [5, 7, 9])
  let t ← read Trade dir
  return ((t.toList : List (Int64 × (Int64 × Int64) × Int64)), ← names dir)

-- a filtered result keeps its keys (rows 0 and 2 of the trades): written, its rows are renumbered `0, 1` in key
-- order (`frame_holds`)
/--
info: [((0 : Int64), ((10 : Int64), (500 : Int64)), (5 : Int64)), (1, (30, 900), 9)]
-/
#guard_msgs in
#eval show IO _ from do
  let dir ← fresh "filtered"
  let r : Tab .long Trade.obj := ⟨2, ← longs 2 [0, 2], ← trades 2 [10, 30] [500, 900] [5, 9]⟩
  write Trade dir r.val
  return ((← read Trade dir).toList : List (Int64 × (Int64 × Int64) × Int64))

-- a keyed result, its key not a row number: `key/` and `val/`, each a positional table; a side that is not a record
-- is the one column named by the side
/--
info: (true, ["key", "val"], ["key"], ["px", "qty"])
-/
#guard_msgs in
#eval show IO _ from do
  let dir ← fresh "keyed"

  let t : Tab .long V.obj := ⟨2, ← longs 2 [7, 9], (← longs 2 [500, 50], ← longs 2 [5, 6])⟩
  writeKeyed [("key", .long)] V dir t
  let u ← readKeyed [("key", .long)] V dir
  return ((u.toList : List (Int64 × Int64 × Int64)) == (t.toList : List (Int64 × Int64 × Int64)), ← names dir, ← names (file dir "key"),
    ← names (file dir "val"))

-- a record key: the key table has a file per key column
/--
info: (true, ["a", "b"], ["val"])
-/
#guard_msgs in
#eval show IO _ from do
  let dir ← fresh "recordkey"

  let t : Tab K.obj .long := ⟨3, (← longs 3 [1, 1, 2], ← longs 3 [5, 6, 5]), ← longs 3 [100, 200, 300]⟩
  writeKeyed K [("val", .long)] dir t
  let u ← readKeyed K [("val", .long)] dir
  return ((u.toList : List ((Int64 × Int64) × Int64)) == (t.toList : List ((Int64 × Int64) × Int64)), ← names (file dir "key"), ← names (file dir "val"))

-- an empty table: its files hold no row, and it reads back empty
/--
info: ([], ["id", "px", "qty"])
-/
#guard_msgs in
#eval show IO _ from do
  let dir ← fresh "empty"
  write Trade dir (← trades 0 [] [] [])
  return (((← read Trade dir).toList : List (Int64 × (Int64 × Int64) × Int64)), ← names dir)

/-- The `f64` column of the words `ws`. -/
def floats (n : USize) (ws : List UInt64) : Arr .f64 n := Arr.ofFn .f64 n fun i => (ws[i.1]?).getD 0

-- a float column: canonical words read back; `-0` and a NaN refused, naming the file, the row and the bit pattern
/--
info: [(0, 4609434218613702656), (1, 0)]
/data/tmp/rel-test-table/floats/x: row 1 holds the Rel.QAtomicType.f64 bit pattern 0x8000000000000000, which is not canonical (a NaN or -0)
/data/tmp/rel-test-table/floats/x: row 0 holds the Rel.QAtomicType.f64 bit pattern 0x7ff8000000000000, which is not canonical (a NaN or -0)
-/
#guard_msgs in
#eval show IO Unit from do
  let dir ← fresh "floats"

  write S dir (floats 2 [0x3ff8000000000000, 0])
  IO.println ((← read S dir).toList : List (Int64 × UInt64))
  write S dir (floats 2 [0x3ff8000000000000, 0x8000000000000000])
  IO.println (say (← (read S dir).toBaseIO))
  write S dir (floats 1 [0x7ff8000000000000])
  IO.println (say (← (read S dir).toBaseIO))

-- read by a schema, each refusal names the file and what was expected or found: a column missing, a column at
-- another atom type, two columns of another count, a symbol column, a schema with a name twice
/--
info: no such file or directory (error code: 2)
  file: /data/tmp/rel-test-table/schemabad/qty
/data/tmp/rel-test-table/schemabad/px: atom type code 7, the column is Rel.QAtomicType.i32 (code 6)
/data/tmp/rel-test-table/schemabad/px has 2 rows and /data/tmp/rel-test-table/schemabad/id has 3: the columns of one side have one count
/data/tmp/rel-test-table/schemabad/id: a symbol column, which waits for the own-format sym writer (D.9 step 6)
column 'id' appears twice in schema [id, id]
-/
#guard_msgs in
#eval show IO Unit from do
  let dir ← fresh "schemabad"
  write [("id", .long), ("px", .long)] dir ((← longs 3 [1, 2, 3], ← longs 3 [4, 5, 6]) : Vals (Obj.prod .long .long) 3)
  IO.println (say (← (read Trade dir).toBaseIO))
  IO.println (say (← (read [("id", .long), ("px", .atom .i32)] dir).toBaseIO))
  write [("px", .long)] dir (← longs 2 [4, 5])
  IO.println (say (← (read [("id", .long), ("px", .long)] dir).toBaseIO))
  IO.println (say (← (read [("id", .atom .sym)] dir).toBaseIO))
  IO.println (say (← (read [("id", .long), ("id", .long)] dir).toBaseIO))

end Rel.Lang.TestTable
