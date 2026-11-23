import Rel.Run.Table
import Rel.Run.Lang.Embed

/-! `schema S from "dir"` (`doc/dataframe-design.zh.typ` F1): a table directory written with its `.d` (`Table.write`),
    its schema read back (`Table.readSchema`), and a program whose schema is read from it at elaboration. The
    directories are under `/data/tmp`. -/

namespace Rel.Lang.TestSchemaDisk

open Rel Rel.Lang.Table

def trade : Schema := [("id", .long), ("qty", .atom .i32), ("name", .arr (.atom .char))]

/-- `trade`'s three rows `(1, 0, a)`, `(2, 10, bc)`, `(3, 20, d)` written afresh to `d`. -/
def fixture (d : String) : IO Unit := do
  if ← System.FilePath.pathExists d then IO.FS.removeDirAll d
  let ⟨n, t⟩ := textCol ["a", "bc", "d"]
  write trade d ((Arr.ofFn .i64 n fun i => (i.val + 1).toUInt64, Arr.ofFn .i32 n fun i => (10 * i.val).toUInt64), t)

-- the schema read back is the one written: the names from `.d`, each object from its files
/-- info: true -/
#guard_msgs in
#eval show IO Bool from do
  fixture "/data/tmp/rel-test-schema-disk/trade"; return (← readSchema "/data/tmp/rel-test-schema-disk/trade") == trade

/-! The program reads `T` from the directory: its columns at `i64`, `i32` and `[char]`, the objects named by their
    atoms, declared by the statement; `q` type-checks only at the object the file gives `qty`. -/

rel_program trades where
    schema T from "/data/tmp/rel-test-schema-disk/trade"
    obj P
    input x : P ⟶ T from "/data/tmp/rel-test-schema-disk/trade"
    q : P ⟶ i32 ≜ x col T "qty"
    check q = {(0,0),(1,10),(2,20)} where x ≜ {(0,((1,0),"a")),(1,((2,10),"bc")),(2,((3,20),"d"))}

#guard trades.ok

-- a directory with no `.d` is refused where the program names it
/--
error: no such file or directory (error code: 2)
  file: /data/tmp/rel-test-schema-disk/none/.d.lo
-/
#guard_msgs in
rel_program noSchema where
    schema U from "/data/tmp/rel-test-schema-disk/none"
    obj P
    input x : P ⟶ U from "/data/tmp/rel-test-schema-disk/none"

end Rel.Lang.TestSchemaDisk
