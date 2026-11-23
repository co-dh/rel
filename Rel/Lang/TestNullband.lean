import Rel.Lang.TestIO

/-! The in-band nullable `1+V` (`Obj.band`, one `Opt` column) through CSV: a field of `1+N` (`i64`) and of `1+B`
    (`u1`) is read as `CsvShape.opt`, one encoding whose null rows are its bitmap, and written back unchanged; the file
    is long enough that each column crosses a block boundary, with nulls on both sides of it. -/

namespace Rel.Lang.TestNullband

open Rel.Programs.prelude in
rel_program csvOptIO where
    obj N
    obj B : u1
    schema Row = {v : 1+N, f : 1+B}
    input t : N ⟶ Row from csv "/data/tmp/rel-test-nullband/in.csv"
    output t to csv "/data/tmp/rel-test-nullband/out.csv"

/-- Row `i`: `v` null at every third row, else `7 i`; `f` null at every fifth, else `i % 2`. -/
def row (i : Nat) : String :=
  let v := if i % 3 = 1 then "" else toString (7 * i)
  let f := if i % 5 = 2 then "" else toString (i % 2)
  s!"{v},{f}\n"

-- 5000 rows: past a block of `2 ^ lgEnc` rows, so both columns' nulls lie in more than one block
#eval show IO Unit from do
  let d := "/data/tmp/rel-test-nullband"
  if ← System.FilePath.pathExists d then IO.FS.removeDirAll d
  IO.FS.createDirAll d
  let s := "v,f\n" ++ String.join ((List.range 5000).map row)
  IO.FS.writeFile (d ++ "/in.csv") s
  csvOptIO.io
  let out ← IO.FS.readFile (d ++ "/out.csv")
  IO.FS.removeDirAll d
  unless out == s do throw (IO.userError s!"1+N, 1+B: written back as {out.take 200}…")

end Rel.Lang.TestNullband
