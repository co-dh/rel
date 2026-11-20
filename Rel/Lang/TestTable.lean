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

/-- The frame of value side `x`: its key the positions, which are not written. -/
def frame {B : Obj} {n : USize} (x : Vals B n) : IO (Tab .long B) := return ⟨n, ← IO.ofExcept (Arr.pos n), x⟩

/-- `x` written under `p` in `d` and read back: the frames' rows are equal, and the files are `cols`'s paths. -/
def roundTrip {B : Obj} [BEq B.El] {n : USize} (d p : String) (x : Vals B n) : IO (Bool × List String) := do
  let dir ← fresh d
  writeVals dir p x
  let (_, ⟨_, y⟩) ← readVals B dir p
  let fs := ((← System.FilePath.readDir dir).map (·.fileName)).qsort (· < ·)
  return ((← frame x).toList == (← frame y).toList, fs.toList)

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
-- other than the declared one, and the float and symbol columns no reader takes yet
/--
info: no such file or directory (error code: 2)
  file: /data/tmp/rel-test-table/bad/nope
/data/tmp/rel-test-table/bad/u.2 has 3 rows and /data/tmp/rel-test-table/bad/u.1 has 4: the columns of one side have one count
/data/tmp/rel-test-table/bad/u.1: atom type code 7, the column is Rel.QAtomicType.u8 (code 4)
/data/tmp/rel-test-table/bad/u.1: a Rel.QAtomicType.f64 column, which a table is not read with: whether a mapped float is checked to be canonical is not decided (PLAN.md, D.9 question 3)
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

end Rel.Lang.TestTable
