import Rel.Kernel.Db.Csv

/-! `csvRead` and `csvWrite` beside their bodies, as `decide` beside `#guard` for a pure kernel: every file is read by
the extern (`qlean_csv_read`, which maps it) and by the body (`csvEncs` of its bytes), and both answers must be the
same encodings, byte for byte, or the same refusal; every answer read is written back by the extern
(`qlean_csv_write`) and by the body (`csvText` of `Csv.raws`), and both files must be the file read. The cases cover
each `CsvShape`, the in-band nullable `opt` at `i64` and `u1` across a block boundary among them. -/

namespace Rel.Db.CsvTest
open Rel

/-- What an encoding is compared by: its count and its bytes. -/
def key : USize × Enc → Nat × Option (List UInt8 × List UInt8)
  | (n, .foR md pk) => (n.toNat, some (md.data.toList, pk.data.toList))
  | (n, _) => (n.toNat, none)

/-- The test directory, made fresh. -/
def dir : String := "/data/tmp/rel-test-csvk"

/-- The text `s` as the file `name`, read under `cols` by the extern and by the body: the same answer, or the same
refusal `err` expects (`none`: an answer); an answer then written back by both, each file equal to `s`. -/
def check (name : String) (cols : CsvCols) (s : String) (err : Option String := none) : IO Unit := do
  IO.FS.createDirAll dir
  let p := s!"{dir}/{name}.csv"
  IO.FS.writeFile p s
  let x ← (csvRead p cols (UInt8.ofNat 44)).toBaseIO
  let y := (csvEncs (UInt8.ofNat 44) cols s.toUTF8.data.toList).mapError (s!"{p}: {·}")
  match x, y, err with
  | .error e, .error f, some w =>
    unless toString e == f ∧ f == s!"{p}: {w}" do throw (IO.userError s!"{name}: refused as '{e}' and '{f}', not '{w}'")
  | .ok (n, es), .ok (m, fs), none =>
    unless n.toNat == m ∧ es.map key == fs.map key do throw (IO.userError s!"{name}: the extern and the body read apart")
    let q := s!"{dir}/{name}.out.csv"
    csvWrite q cols (UInt8.ofNat 44) n es
    let b ← IO.ofExcept (do csvText (UInt8.ofNat 44) cols m (← Csv.raws cols es) : Except String (List UInt8))
    let a ← IO.FS.readBinFile q
    unless a.data.toList == s.toUTF8.data.toList ∧ b == s.toUTF8.data.toList do
      throw (IO.userError s!"{name}: written back as bytes {a.data.toList} by the extern, {b} by the body")
  | _, _, _ => throw (IO.userError s!"{name}: the extern and the body disagree on refusing, or {err} was expected")

/-- One record a row: `i`, then every third row's `i * 7 - 50` empty (the null) in an `opt` and a `null` column, then
    `i % 2` as a `u1` whose every fifth row is null: `k` rows, past a block of `2 ^ lgEnc` when `k` is. -/
def rows (k : Nat) : String :=
  "a,b,c,f\n" ++ String.join ((List.range k).map row)
where row (i : Nat) : String :=
  let v := if i % 3 = 1 then "" else toString ((i : Int) * 7 - 50)
  let f := if i % 5 = 2 then "" else toString (i % 2)
  s!"{i},{v},{v},{f}\n"

def mixed : CsvCols := [("a", .atom, .i64, []), ("b", .opt, .i64, []), ("c", .null, .i64, []), ("f", .opt, .u1, [])]

#eval check "few" mixed (rows 7)
#eval check "blocks" mixed (rows 5000)
#eval check "text" [("t", .text, .char, []), ("b", .opt, .i64, [])] "t,b\n\"x,y\",3\n,\nz,-1\n"
#eval check "nonull" [("b", .opt, .i64, [])] "b\n1\n2\n"
#eval check "allnull" [("b", .opt, .i64, [])] "b\n\n\n"
#eval check "bad" [("b", .opt, .i64, [])] "b\n1\nx\n"
  (some "row 1 (line 3), column 'b': expected i64: an integer from -9223372036854775808 to 9223372036854775807, or the empty field (the null), found 'x'")

end Rel.Db.CsvTest
