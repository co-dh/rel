import Rel.Lang.TestIO

/-! The in-band nullable `1+V` (`Obj.band`, one `Opt` column) through CSV: a field of `1+N` (`i64`) and of `1+u1`
    (`u1`) is read as `CsvShape.opt`, one encoding whose null rows are its bitmap, and written back unchanged; the file
    is long enough that each column crosses a block boundary, with nulls on both sides of it. -/

namespace Rel.Lang.TestNullband

open Rel.Programs.prelude in
rel_program csvOptIO where
    obj N
    obj M
    schema Row = {v : 1+N, f : 1+M}
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
  unless out == s do throw (IO.userError s!"1+N: written back as {out.take 200}…")

-- `1+u1`: no declared object stores `u1` (it has no literal), so the table reader and writer are called at it
-- directly; its blocks holding a null are widened to width 2, which `Table.encVals` accepts by deciding `Enc.WF`
#eval show IO Unit from do
  let d := "/data/tmp/rel-test-nullband-u1"
  if ← System.FilePath.pathExists d then IO.FS.removeDirAll d
  IO.FS.createDirAll d
  let s := "f\n" ++ String.join ((List.range 5000).map fun i => if i % 5 = 2 then "\n" else s!"{i % 2}\n")
  IO.FS.writeFile (d ++ "/in.csv") s
  let S : Schema := [("f", .opt (.atom .u1))]
  let cols : Db.CsvCols := [("f", Table.nullShape (.atom .u1), .u1, [])]
  let (t, _) ← Table.readCsvDict (← IO.ofExcept Table.Dict.empty) [] S cols (d ++ "/in.csv")
  Table.writeCsv none [] S cols (d ++ "/out.csv") t
  let out ← IO.FS.readFile (d ++ "/out.csv")
  IO.FS.removeDirAll d
  unless out == s do throw (IO.userError s!"1+u1: written back as {out.take 200}…")

-- a key of `1+N`: the rows are put in key order on reading (`canon`, its permutation applied by gather to the `1+N`
-- values), and the null key, `inl ()`, sorts before every value
open Rel.Programs.prelude in
rel_program csvOptKeyIO where
    obj N
    input t : 1+N ⟶ 1+N from csv "/data/tmp/rel-test-nullband-key/in.csv"
    output t to csv "/data/tmp/rel-test-nullband-key/out.csv"

/-- Row `i` of the keyed file: key `5000 - i`, but null at `i = 2500`; value as `row`'s `v`. -/
def keyRow (i : Nat) : String :=
  s!"{if i = 2500 then "" else toString (5000 - i)},{if i % 3 = 1 then "" else toString (7 * i)}\n"

-- 5000 rows in descending key order: written back with the null key first, then the rest in ascending key order,
-- each value gathered with its key across the block boundaries
#eval show IO Unit from do
  let d := "/data/tmp/rel-test-nullband-key"
  if ← System.FilePath.pathExists d then IO.FS.removeDirAll d
  IO.FS.createDirAll d
  IO.FS.writeFile (d ++ "/in.csv") ("key,val\n" ++ String.join ((List.range 5000).map keyRow))
  csvOptKeyIO.io
  let out ← IO.FS.readFile (d ++ "/out.csv")
  IO.FS.removeDirAll d
  let want := "key,val\n" ++ keyRow 2500 ++ String.join (((List.range 5000).reverse.filter (· ≠ 2500)).map keyRow)
  unless out == want do throw (IO.userError s!"1+N key: written back as {out.take 200}…")

/-- The one `1+N` column `v` of a CSV file whose row `i` is `f i`. -/
def vS : Schema := [("v", .opt .long)]
def vCols : Db.CsvCols := [("v", Table.nullShape .long, .i64, [])]
def vText (f : Nat → String) (k : Nat) : String := "v\n" ++ String.join ((List.range k).map fun i => f i ++ "\n")

-- concat of two 5000-row `1+N` columns (each past a block) as one of 10000: the rows of the first then the second
-- where neither holds a null; where both do, the error naming the first side (`Opt.concat`)
#eval show IO Unit from do
  let d := "/data/tmp/rel-test-nullband-cat"
  if ← System.FilePath.pathExists d then IO.FS.removeDirAll d
  IO.FS.createDirAll d
  let rd (f : Nat → String) (p : String) := do
    IO.FS.writeFile (d ++ p) (vText f 5000)
    let (t, _) ← Table.readCsvDict (← IO.ofExcept Table.Dict.empty) [] vS vCols (d ++ p)
    pure t
  let cat (x y : Nat → String) : IO (Except String ((n : USize) × Vals vS.obj n)) := do
    let (a, b) := (← rd x "/a.csv", ← rd y "/b.csv")
    pure ((⟨_, ·⟩) <$> ValsB.concat (a.n + b.n) a.val b.val)
  let full (i : Nat) := toString (7 * i)
  match ← cat full (fun i => full (5000 + i)) with
  | .ok ⟨_, v⟩ =>
    Table.writeCsv none [] vS vCols (d ++ "/c.csv") (← IO.ofExcept (Table.frame v))
    let out ← IO.FS.readFile (d ++ "/c.csv")
    unless out == vText full 10000 do throw (IO.userError s!"concat 1+N: written as {out.take 200}…")
  | .error m => throw (IO.userError s!"concat 1+N with no null: {m}")
  let holed (i : Nat) := if i % 3 = 1 then "" else full i
  match ← cat holed (fun i => holed (5000 + i)) with
  | .ok ⟨_, v⟩ =>
    Table.writeCsv none [] vS vCols (d ++ "/c.csv") (← IO.ofExcept (Table.frame v))
    let out ← IO.FS.readFile (d ++ "/c.csv")
    unless out == vText holed 10000 do throw (IO.userError s!"concat 1+N with nulls: written as {out.take 200}…")
  | .error m => throw (IO.userError s!"concat 1+N with nulls on both sides: {m}")
  IO.FS.removeDirAll d

end Rel.Lang.TestNullband
