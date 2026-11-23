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
  IO.ofExcept (Arr.of .i64 n (wordsFoR (xs.map Int64.toUInt64).toArray) "literal")

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
-- other than the declared one (a long read as a float among them), a long read as a symbol column among them
/--
info: no such file or directory (error code: 2)
  file: /data/tmp/rel-test-table/bad/nope
/data/tmp/rel-test-table/bad/u.2 has 3 rows and /data/tmp/rel-test-table/bad/u.1 has 4: the columns of one side have one count
/data/tmp/rel-test-table/bad/u.1: atom type code 7, the column is Rel.QAtomicType.u8 (code 4)
/data/tmp/rel-test-table/bad/u.1: atom type code 7, the column is Rel.QAtomicType.f64 (code 9)
/data/tmp/rel-test-table/bad/u.1: atom type code 7, the column is Rel.QAtomicType.sym (code 11)
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

-- a list cell that is not a slice of its payload, refused naming the `.lo` file, the row and the bounds: past the
-- payload (`hi = 7` over `m = 5`), reversed (`lo > hi`), and before it (`lo < 0`)
/--
info: /data/tmp/rel-test-table/badcell/a.lo: row 1 is the cell [2, 7), not a slice of the 5 rows of /data/tmp/rel-test-table/badcell/a.e: a cell [lo, hi) needs 0 ≤ lo ≤ hi ≤ 5
/data/tmp/rel-test-table/badcell/b.lo: row 0 is the cell [3, 1), not a slice of the 5 rows of /data/tmp/rel-test-table/badcell/b.e: a cell [lo, hi) needs 0 ≤ lo ≤ hi ≤ 5
/data/tmp/rel-test-table/badcell/c.lo: row 0 is the cell [-1, 2), not a slice of the 5 rows of /data/tmp/rel-test-table/badcell/c.e: a cell [lo, hi) needs 0 ≤ lo ≤ hi ≤ 5
-/
#guard_msgs in
#eval show IO Unit from do
  let dir ← fresh "badcell"
  let e ← longs 5 [1, 2, 3, 4, 5]
  writeVals (A := .arr .long) dir "a" (⟨5, ← longs 2 [0, 2], ← longs 2 [1, 7], e⟩ : Vals (.arr .long) 2)
  writeVals (A := .arr .long) dir "b" (⟨5, ← longs 1 [3], ← longs 1 [1], e⟩ : Vals (.arr .long) 1)
  writeVals (A := .arr .long) dir "c" (⟨5, ← longs 1 [-1], ← longs 1 [2], e⟩ : Vals (.arr .long) 1)
  ["a", "b", "c"].forM fun p => do IO.println (say (← (readVals (.arr .long) dir p).toBaseIO))

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
info: ([(0, (10, 500), 5), (1, (20, 50), 7), (2, (30, 900), 9)], [".d.e", ".d.hi", ".d.lo", "id", "px", "qty"])
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
info: [(0, (10, 500), 5), (1, (30, 900), 9)]
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
info: (true, ["key", "val"], [".d.e", ".d.hi", ".d.lo", "key"], [".d.e", ".d.hi", ".d.lo", "px", "qty"])
-/
#guard_msgs in
#eval show IO _ from do
  let dir ← fresh "keyed"

  let t : Tab .long V.obj := ⟨2, ← longs 2 [7, 9], (← longs 2 [500, 50], ← longs 2 [5, 6])⟩
  writeKeyed [("key", .long)] V dir t
  let u ← readKeyed [("key", .long)] V dir
  let l : List (Int64 × Int64 × Int64) := u.toList; let l0 : List (Int64 × Int64 × Int64) := t.toList
  return (l == l0, ← names dir, ← names (file dir "key"),
    ← names (file dir "val"))

-- a record key: the key table has a file per key column
/--
info: (true, [".d.e", ".d.hi", ".d.lo", "a", "b"], [".d.e", ".d.hi", ".d.lo", "val"])
-/
#guard_msgs in
#eval show IO _ from do
  let dir ← fresh "recordkey"

  let t : Tab K.obj .long := ⟨3, (← longs 3 [1, 1, 2], ← longs 3 [5, 6, 5]), ← longs 3 [100, 200, 300]⟩
  writeKeyed K [("val", .long)] dir t
  let u ← readKeyed K [("val", .long)] dir
  let l : List ((Int64 × Int64) × Int64) := u.toList; let l0 : List ((Int64 × Int64) × Int64) := t.toList
  return (l == l0, ← names (file dir "key"), ← names (file dir "val"))

-- an empty table: its files hold no row, and it reads back empty
/--
info: ([], [".d.e", ".d.hi", ".d.lo", "id", "px", "qty"])
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
  let l : List (Int64 × UInt64) := (← read S dir).toList; IO.println l
  write S dir (floats 2 [0x3ff8000000000000, 0x8000000000000000])
  IO.println (say (← (read S dir).toBaseIO))
  write S dir (floats 1 [0x7ff8000000000000])
  IO.println (say (← (read S dir).toBaseIO))

-- read by a declared schema, a `.d` that differs names the column (`checkDisk`): a column missing, a column at another
-- atom type, a column on disk and not declared, a symbol column, a schema with a name twice
/--
info: /data/tmp/rel-test-table/schemabad/.d: column qty is not on disk, declared i64
/data/tmp/rel-test-table/schemabad/.d: column px is i64, declared i32
/data/tmp/rel-test-table/schemabad/.d: column id is not on disk, declared i64
/data/tmp/rel-test-table/schemabad/.d: column id is not on disk, declared sym
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

-- the same reads of a directory with no `.d` (data written before `write` wrote one): `readCols`' own refusals, each
-- naming the file and what was expected or found
/--
info: no such file or directory (error code: 2)
  file: /data/tmp/rel-test-table/schemabad/qty
/data/tmp/rel-test-table/schemabad/px: atom type code 7, the column is Rel.QAtomicType.i32 (code 6)
/data/tmp/rel-test-table/schemabad/px has 2 rows and /data/tmp/rel-test-table/schemabad/id has 3: the columns of one side have one count
/data/tmp/rel-test-table/schemabad/id: atom type code 7, the column is Rel.QAtomicType.sym (code 11)
-/
#guard_msgs in
#eval show IO Unit from do
  let dir ← fresh "schemabad"
  let noD : IO Unit := IO.FS.removeFile (file dir (dName ++ ".lo"))
  write [("id", .long), ("px", .long)] dir ((← longs 3 [1, 2, 3], ← longs 3 [4, 5, 6]) : Vals (Obj.prod .long .long) 3); noD
  IO.println (say (← (read Trade dir).toBaseIO))
  IO.println (say (← (read [("id", .long), ("px", .atom .i32)] dir).toBaseIO))
  write [("px", .long)] dir (← longs 2 [4, 5]); noD
  IO.println (say (← (read [("id", .long), ("px", .long)] dir).toBaseIO))
  IO.println (say (← (read [("id", .atom .sym)] dir).toBaseIO))

/-! ## Symbol columns: ids into the database's one append-only dictionary (PLAN 8.3) -/

/-- The texts of `D`, in id order. -/
def texts (D : Table.Dict) : List String := D.toList.map fun (_, b) => String.mk (b.map fun c => Char.ofNat c.toNat)

-- by hand: the texts `ibm aapl ibm msft`, then a second load `zz aapl`, interned into one dictionary: ids `0 1 0 2`
-- then `3 1` (append order), the dictionary `ibm aapl msft zz`; its `rank` orders the texts `aapl ibm msft zz`; the
-- CSV written back through it equals each input; comparing ranks agrees with comparing texts at every pair of rows;
-- the own files (ids `s`, dictionary `sym` with `sym.rank`) map back to the same dictionary and ids
/--
info: ([0, 1, 0, 2], [3, 1], ["ibm", "aapl", "msft", "zz"], ["aapl", "ibm", "msft", "zz"], true, true, true, true, true)
-/
#guard_msgs in
#eval show IO _ from do
  let dir ← fresh "sym"
  let S : Schema := [("s", .atom .sym)]
  let cols : Db.CsvCols := [("s", .atom, .sym, [])]
  let (a, b) := ("s\nibm\naapl\nibm\nmsft\n", "s\nzz\naapl\n")
  IO.FS.writeFile (dir ++ "/a.csv") a; IO.FS.writeFile (dir ++ "/b.csv") b
  let (t, D) ← readCsvDict (← IO.ofExcept Dict.empty) [] S cols (dir ++ "/a.csv")
  let (u, D) ← readCsvDict D [] S cols (dir ++ "/b.csv")
  writeCsv D [] S cols (dir ++ "/a.out") t; writeCsv D [] S cols (dir ++ "/b.out") u
  let K ← IO.ofExcept (rank D)
  let rk (i : UInt64) : Int64 := (K.toList.lookup i.toInt64).getD (-1)
  let byRank := texts (← IO.ofExcept ((← IO.ofExcept K.conv).comp D))
  let rows := ["ibm", "aapl", "ibm", "msft", "zz", "aapl"]
  let ids := t.val.toList ++ u.val.toList
  let order := (ids.zip rows).all fun (i, x) => (ids.zip rows).all fun (j, y) => decide (rk i < rk j) == decide (x < y)
  writeDict dir D; writeSym dir "s" t.val
  let (D', K') ← readDict dir
  let ⟨_, y⟩ ← readSym D' dir "s"
  return (t.val.toList, u.val.toList, texts D, byRank, (← IO.FS.readFile (dir ++ "/a.out")) == a,
    (← IO.FS.readFile (dir ++ "/b.out")) == b, order, D'.toList == D.toList && K'.toList == K.toList,
    y.toList == t.val.toList)

-- the refusals: an id with no text in the dictionary, a dictionary with a text twice
/--
info: /data/tmp/rel-test-table/symbad/s: 1 of 1 ids are past the dictionary of 1 texts
/data/tmp/rel-test-table/symbad/sym.lo: 2 of 3 texts repeat one before them
-/
#guard_msgs in
#eval show IO Unit from do
  let dir ← fresh "symbad"
  let x : Vals (.arr (.atom .char)) 3 :=
    ⟨3, ← longs 3 [0, 1, 2], ← longs 3 [1, 2, 3], Arr.ofFn .char 3 fun _ => 97⟩
  let (D, _) ← IO.ofExcept (intern "one" (← IO.ofExcept Dict.empty) (⟨1, ← longs 1 [0], ← longs 1 [1],
    Arr.ofFn .char 1 fun _ => 97⟩ : Vals (.arr (.atom .char)) 1))
  writeSym dir "s" (Arr.ofFn .sym 1 fun _ => 5)
  IO.println (say (← (readSym D dir "s").toBaseIO))
  writeVals (A := .arr (.atom .char)) dir "sym" x
  IO.println (say (← (readDict dir).toBaseIO))

/-! ## One dictionary per library (owner decisions N, Q, O) -/

/-- The texts `xs` as a side of `[C]`, each its bytes. -/
def strs (xs : List String) : IO (Vals (.arr (.atom .char)) xs.length.toUSize) := do
  let bs := xs.flatMap (·.toUTF8.toList)
  let ls := xs.map (·.utf8ByteSize)
  let lo := (ls.foldl (fun (acc, s) l => (acc ++ [s], s + l)) (([] : List Nat), 0)).1
  return ⟨bs.length.toUSize, ← longs _ (lo.map Int64.ofNat), ← longs _ ((lo.zipWith (· + ·) ls).map Int64.ofNat),
    Arr.ofFn .char bs.length.toUSize fun i => (bs.getD i.val 0).toUInt64⟩

-- by hand: the library `lib`, the directory holding `t1` and `t2`, has no dictionary at first; `t1` with the texts
-- `ibm aapl` gets ids `0 1` and the dictionary `ibm aapl` in `lib`; `t2` with `msft ibm`, interned into that
-- dictionary, gets `2 0` (`ibm` keeps id 0), read back as written, and the dictionary grows to `ibm aapl msft`; the
-- table directory holds its ids alone; a dictionary that does not start with the library's (`zz` at id 0) is refused
/--
info: (["ibm", "aapl", "msft"], [0, 1], [2, 0], [2, 0], [".d.e", ".d.hi", ".d.lo", "s"],
  "/data/tmp/rel-test-table/lib: the library's dictionary of 3 texts and the program's of 1 differ at id 0; a dictionary is append-only, so these ids are not of this library")
-/
#guard_msgs in
#eval show IO _ from do
  let L ← fresh "lib"
  let S : Schema := [("s", .atom .sym)]
  let own (D : Dict) (t : String) (xs : List String) : IO (List UInt64) := do
    let (D, y) ← IO.ofExcept (intern t D (← strs xs))
    writeOwn D [] S (file L t) (write S (file L t) y)
    return y.toList
  let a ← own (← libDict L) "t1" ["ibm", "aapl"]
  let b ← own (← libDict L) "t2" ["msft", "ibm"]
  let D ← libDict L
  let t ← readOwn D (file L "t2") (read S (file L "t2"))
  let (E, z) ← IO.ofExcept (intern "t3" (← IO.ofExcept Dict.empty) (← strs ["zz"]))
  let r ← (writeOwn E [] S (file L "t3") (write S (file L "t3") z)).toBaseIO
  return (texts D, a, b, t.val.toList, ← names (file L "t1"), say r)

-- a program's own tables with symbol columns: `a` and `c` in the library `/db/one`, `b` in `/db/two` (its key the
-- symbol column) is refused naming both; `x` has none, so its library does not count
/--
info: the symbol columns of `a` are ids in the library /db/one and those of `b` in the library /db/two, two dictionaries, so they cannot meet; convert one to its texts with `unenum` (`I ≫ D`)
-/
#guard_msgs in
#eval IO.println (match progLib [("a", "/db/one/t", [], [("s", .atom .sym)]), ("x", "/db/two/u", [], [("n", .long)]),
    ("b", "/db/two/v", [("k", .atom .sym)], [("n", .long)]), ("c", "/db/one/w", [], [("s", .atom .sym)])] with
  | .ok l => s!"{l}" | .error e => e)
#guard progLib [("a", "/db/one/t", [], [("s", .atom .sym)]), ("x", "/db/two/u", [], [("n", .long)]),
  ("c", "/db/one/w/", [], [("s", .arr (.atom .sym))])] matches .ok (some "/db/one")

-- `unenum` by hand: `ibm aapl ibm` interned into `D` (ids `0 1 0`), its texts back through `D`; those texts interned
-- into another library's dictionary `zz` take the ids `1 2 1` there, and `unenum` through it gives the same texts
/-- info: (true, [1, 2, 1], true) -/
#guard_msgs in
#eval show IO _ from do
  let x ← strs ["ibm", "aapl", "ibm"]
  let (D, I) ← IO.ofExcept (intern "a" (← IO.ofExcept Dict.empty) x)
  let T ← IO.ofExcept (unenum "a" D (← IO.ofExcept (frame I)))
  let (E, _) ← IO.ofExcept (intern "b" (← IO.ofExcept Dict.empty) (← strs ["zz"]))
  let (E, J) ← IO.ofExcept (intern "b" E T.val)
  let U ← IO.ofExcept (unenum "b" E (← IO.ofExcept (frame J)))
  return (T.toList == (← IO.ofExcept (frame x)).toList, J.toList, U.toList == T.toList)

/-- A `u1` column as a file holds it: `bs`, one byte each, encoded by the one writer `Coc.encode`. -/
def u1Of (bs : List UInt8) : Except String (Arr .u1 bs.length.toUSize) :=
  Arr.of .u1 _ (.foR (Coc.encode 1 ⟨bs.toArray⟩).1 (Coc.encode 1 ⟨bs.toArray⟩).2) "u1 file"
-- `Column.u1Ok` on the blocks: `0`/`1` values are accepted, a value 2 widens its block and is rejected
#guard ((u1Of [0, 1, 1, 0, 1]).toOption.map Arr.toList) == some [false, true, true, false, true]
#guard ((u1Of [1, 1, 1]).toOption.map Arr.toList) == some [true, true, true]
#guard (u1Of [0, 1, 2, 1]).toOption.isNone
#guard (u1Of [2, 2]).toOption.isNone

-- TSV is the CSV reader and writer at the separator `\t` (df-F6b): a `,` is data and stays unquoted, a field holding
-- `\t` is quoted; the file written is the file read, byte for byte, and the same file read at `,` is refused
/--
info: (2, true, "a\tb\n1,2\t\"x\ty\"\n3\tz\n", true)
-/
#guard_msgs in
#eval show IO _ from do
  let dir ← fresh "tsv"
  let S : Schema := [("a", .arr (.atom .char)), ("b", .arr (.atom .char))]
  let cols : Db.CsvCols := [("a", .text, .char, []), ("b", .text, .char, [])]
  let f := "a\tb\n1,2\t\"x\ty\"\n3\tz\n"
  IO.FS.writeFile (dir ++ "/in.tsv") f
  let (t, D) ← readCsvDict (← IO.ofExcept Dict.empty) [] S cols (dir ++ "/in.tsv") 9
  writeCsv D [] S cols (dir ++ "/out.tsv") t 9
  let g ← IO.FS.readFile (dir ++ "/out.tsv")
  let refused ← try discard <| readCsvDict D [] S cols (dir ++ "/in.tsv"); pure false catch _ => pure true
  pure (t.n, g == f, g, refused)

end Rel.Lang.TestTable
