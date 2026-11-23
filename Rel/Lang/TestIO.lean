import Rel.Programs.FrameJoin

/-! The IO statements (IO design A, step I2): `input t : A ⟶ B from …` declares a relation with no body, a parameter
    of each definition after it that mentions it; a `check` or `print` gives its table in a `where`. Nothing is read
    or written here (I3). Expected rows worked by hand from the `where` tables. -/

namespace Rel.Lang.TestIO

-- IO design §A's example: `big` mentions the input `t`, so it is `big(t : N ⟶ Trade)`; `bigPx` mentions `big`, so
-- it is `bigPx(big : N ⟶ Big)`; each check gives `t` its table, every run-time name reached applied to it
open Rel.Programs.prelude Rel.Programs.frame in
rel_program trades where
    obj N
    obj K = {A,B,C}
    schema Trade = {sym : K, px : N, qty : N}
    schema Big   = {sym : K, px : N}
    input t : N ⟶ Trade from csv "trades.csv"
    -- qty above 100: `<°{(100,∗)}`, a closed term on the unbounded `N`, so bounded inside `big` by `t`
    big : N ⟶ Big ≜ filterBy(dom(col Trade "qty" dom(<°{(100,∗)})), t) ⟨col Trade "sym", col Trade "px"⟩
    bigPx : N ⟶ N ≜ big col Big "px"
    check big = {(0,(A,10))} where t ≜ {(0,((A,10),500)),(1,((B,20),50))}
    check bigPx = {(0,10),(1,30)} where t ≜ {(0,((A,10),500)),(1,((B,20),50)),(2,((C,30),101))}
    check t col Trade "sym" = {(0,B)} where t ≜ {(0,((B,20),50))}
    print bigPx where t ≜ {(0,((C,7),200))}
    output big to "big"
    output bigPx to csv "bigpx.csv"
    output t to "copy"

-- by hand: qty 500 > 100 keeps row 0 only; with a third row of qty 101 rows 0 and 2 are kept, renumbered 0, 1
#guard trades.failures.map toString == []
#guard trades.prints == ["bigPx(big({(0, ((C, 7), 200))})) = {(0, 7)}"]

/-- error: line 37, col 5: input `t` from "t": its type N ⟶ α has the object variable 'α'; write a declared object there -/
#guard_msgs in
rel_program varT where
    obj N
    input t : N ⟶ α from "t"

/-- error: line 43, col 19: expected an object, found 'Q' -/
#guard_msgs in
rel_program undeclaredT where
    obj N
    input t : N ⟶ Q from "t"

/-- error: line 52, col 5: input `t` from "t": column 'sym' appears twice in schema [sym, sym, px] -/
#guard_msgs in
rel_program twiceT where
    obj K = {A,B}
    obj N
    schema Key = {sym : K}
    schema Row = {sym : K, px : N}
    input t : Key ⟶ Row from "t"

/-- error: line 59, col 5: input `t` from csv "t.csv": column 'N' appears twice in schema [K, N, N] -/
#guard_msgs in
rel_program csvProdT where
    obj K = {A,B}
    obj N
    input t : N ⟶ K×(N×N) from csv "t.csv"

/-- error: line 66, col 5: input `t` from csv "t.csv": column 'val' is a list of one of A, B; a CSV field holds a list of char only (text) -/
#guard_msgs in
rel_program csvListT where
    obj K = {A,B}
    obj N
    input t : N ⟶ [K] from csv "t.csv"

/-- error: line 74, col 5: output `t` to "out": the output at line 73 writes "out" already; give each output a path of its own -/
#guard_msgs in
rel_program samePathT where
    obj N
    input t : N ⟶ N from "t"
    output t to "out"
    output t to "out"

/-- error: line 81, col 5: output `x` to "x": `x` computes no whole table: it has parameters or object variables, or needs keys (§a); output a definition at declared objects whose source has a universe, as `x` after a set of its sources -/
#guard_msgs in
rel_program keysT where
    obj N
    x : N ⟶ N ≜ 𝟙
    output x to "x"

/-- error: line 88, col 5: output `f` to "f": `f` computes no whole table: it has parameters or object variables, or needs keys (§a); output a definition at declared objects whose source has a universe, as `f` after a set of its sources -/
#guard_msgs in
rel_program paramsT where
    obj N
    f(R : N ⟶ N) : N ⟶ N ≜ R
    output f to "f"

/-- error: line 94, col 5: output `y` to "y": `y` is not defined before it; an output names a definition or an input of the program -/
#guard_msgs in
rel_program undefinedT where
    obj N
    output y to "y"

/-- error: line 101, col 5: check reaches the input `t`, which has no table at elaboration; give one: `check … where t ≜ {…}`, a table N ⟶ N -/
#guard_msgs in
rel_program unboundT where
    obj N
    input t : N ⟶ N from "t"
    check t = t

/-- error: line 109, col 5: print reaches the input `t` (through `w`), which has no table at elaboration; give one: `print … where t ≜ {…}`, a table N ⟶ N -/
#guard_msgs in
rel_program unboundViaT where
    obj N
    input t : N ⟶ N from "t"
    w : N ⟶ N ≜ t t
    print w

/-- error: line 117, col 5: check: `c` in its `where` is no input; a `where` here gives the table of an input (`input c : A ⟶ B from …`) -/
#guard_msgs in
rel_program notInputT where
    obj N
    input t : N ⟶ N from "t"
    c : N ⟶ N ≜ {(1,2)}
    check t = c where c ≜ {(1,1)}

/-- error: line 124, col 5: `f` has parameters and mentions `t`, which has no table at elaboration; add the parameter `t : N ⟶ N` to `f` and pass `t` where `f` is used -/
#guard_msgs in
rel_program paramMentionT where
    obj N
    input t : N ⟶ N from "t"
    f(R : N ⟶ N) : N ⟶ N ≜ R t

/-- error: line 131, col 5: theorem `conv` mentions `t`, which has no table at elaboration; state it with `t` a parameter: `theorem conv(t : N ⟶ N, …)` -/
#guard_msgs in
rel_program theoremT where
    obj N
    input t : N ⟶ N from "t"
    theorem conv : t°° = t

-- an importer's inputs are its imports' (IO design A.2): `x` mentions `trades.bigPx`, which is run-time, so `x` is
-- `x(trades.bigPx : N ⟶ N)`, the imported name spelled as its constant
open trades in
rel_program importT where
    x : N ⟶ N ≜ bigPx

#guard importT.inputs == [("Rel.Lang.TestIO.trades.t", true, "trades.csv")]
#guard importT.outputs == []

-- any key object but the positions is a key column, `F ⟶ N` a keyed table of `f64` keys (ruling H); it was refused
-- (on disk `key/` and `val/`, as any keyed table)
rel_program floatKeyT where
    obj F : f64
    obj N
    input t : F ⟶ N from "t"
#guard floatKeyT.inputs == [("t", false, "t")]
/-! ## `n.io` (step I3): a CSV input, a positional and a keyed output, in a directory the test makes and removes -/

-- `big` keeps the rows of `t` whose qty is above 100, renumbered from 0 when written; `pxOf : K ⟶ N` (symbol ↦ px of
-- those rows) is keyed by `K`, so it is written as a key table and a value table
open Rel.Programs.prelude Rel.Programs.frame in
rel_program tradesIO where
    obj N
    obj K = {A,B,C}
    schema Trade = {sym : K, px : N, qty : N}
    schema Big   = {sym : K, px : N}
    input t : N ⟶ Trade from csv "/data/tmp/rel-test-io/trades.csv"
    big : N ⟶ Big ≜ filterBy(dom(col Trade "qty" dom(<°{(100,∗)})), t) ⟨col Trade "sym", col Trade "px"⟩
    pxOf : K ⟶ N ≜ (big col Big "sym")° big col Big "px"
    output big to "/data/tmp/rel-test-io/big"
    output pxOf to "/data/tmp/rel-test-io/pxof"

#guard tradesIO.inputs == [("t", true, "/data/tmp/rel-test-io/trades.csv")]
#guard tradesIO.outputs == [("big", false, "/data/tmp/rel-test-io/big"), ("pxOf", false, "/data/tmp/rel-test-io/pxof")]

-- an importer inherits `t`; its output reaches `t` through `tradesIO.big`, which its `io` computes by `big`'s twin
open tradesIO in
rel_program pxIO where
    px : N ⟶ N ≜ big col Big "px"
    output px to "/data/tmp/rel-test-io/px"

#guard pxIO.inputs == [("Rel.Lang.TestIO.tradesIO.t", true, "/data/tmp/rel-test-io/trades.csv")]
#guard pxIO.outputs == [("px", false, "/data/tmp/rel-test-io/px")]

/-- The names under the directory `d`, each directory's after it, sorted. -/
partial def tree (d : String) : IO (List String) := do
  let es := ((← System.FilePath.readDir d).map (·.fileName)).qsort (· < ·)
  es.toList.flatMapM fun (e : String) => do
    let p := (System.FilePath.mk d / e).toString
    if ← System.FilePath.isDir p then return e :: (← tree p).map (e ++ "/" ++ ·) else return [e]

-- by hand: qty 500 and 101 pass, rows (A,10) and (C,30) of three, A = 0 and C = 2; `big` renumbered 0, 1; `pxOf`
-- keyed by symbol; `px` the importer's, the px column of `big`
/--
info: ([(0, 0, 10), (1, 2, 30)], [(0, 10), (2, 30)], [(0, 10), (1, 30)],
  ["big", "big/.d.e", "big/.d.hi", "big/.d.lo", "big/px", "big/sym", "px", "px/.d.e", "px/.d.hi", "px/.d.lo", "px/val",
    "pxof", "pxof/key", "pxof/key/.d.e", "pxof/key/.d.hi", "pxof/key/.d.lo", "pxof/key/key", "pxof/val",
    "pxof/val/.d.e", "pxof/val/.d.hi", "pxof/val/.d.lo", "pxof/val/val", "trades.csv"])
-/
#guard_msgs in
#eval show IO _ from do
  let d := "/data/tmp/rel-test-io"
  if ← System.FilePath.pathExists d then IO.FS.removeDirAll d
  IO.FS.createDirAll d
  IO.FS.writeFile (d ++ "/trades.csv") "sym,px,qty\nA,10,500\nB,20,50\nC,30,101\n"
  tradesIO.io; pxIO.io
  let big ← Table.read [("sym", .long), ("px", .long)] (d ++ "/big")
  let pxOf ← Table.readKeyed [("key", .long)] [("val", .long)] (d ++ "/pxof")
  let px ← Table.read [("val", .long)] (d ++ "/px")
  let files ← tree d
  IO.FS.removeDirAll d
  return (big.toList, pxOf.toList, px.toList, files)

-- the refusal at run time before any file is written: an input whose files are missing, the OS error naming the file
rel_program missingIO where
    obj N
    input t : N ⟶ N from "/data/tmp/rel-test-io-none/t"
    output t to "/data/tmp/rel-test-io-none/out"

/--
info: no such file or directory (error code: 2)
  file: /data/tmp/rel-test-io-none/t/val
-/
#guard_msgs in
#eval show IO Unit from do
  match ← missingIO.io.toBaseIO with | .ok _ => IO.println "ok" | .error e => IO.println e

/-! ## `output … to csv` (step I9): CSV in, CSV out, read back by a second program's `from csv` -/

-- `tradesIO`'s `big` and `pxOf`, written to CSV: `big` keyed by positions, so its value columns only; `pxOf` keyed by
-- `K`, so the key column `key` then the value column `val`, one header
open Rel.Programs.prelude Rel.Programs.frame in
rel_program csvOutIO where
    obj N
    obj K = {A,B,C}
    schema Trade = {sym : K, px : N, qty : N}
    schema Big   = {sym : K, px : N}
    input t : N ⟶ Trade from csv "/data/tmp/rel-test-io-csv/trades.csv"
    big : N ⟶ Big ≜ filterBy(dom(col Trade "qty" dom(<°{(100,∗)})), t) ⟨col Trade "sym", col Trade "px"⟩
    pxOf : K ⟶ N ≜ (big col Big "sym")° big col Big "px"
    output big to csv "/data/tmp/rel-test-io-csv/big.csv"
    output pxOf to csv "/data/tmp/rel-test-io-csv/pxof.csv"

#guard csvOutIO.outputs ==
  [("big", true, "/data/tmp/rel-test-io-csv/big.csv"), ("pxOf", true, "/data/tmp/rel-test-io-csv/pxof.csv")]

-- the two files read back under the same types, each copied to a table directory
rel_program csvBackIO where
    obj N
    obj K = {A,B,C}
    schema Big = {sym : K, px : N}
    input b : N ⟶ Big from csv "/data/tmp/rel-test-io-csv/big.csv"
    input q : K ⟶ N from csv "/data/tmp/rel-test-io-csv/pxof.csv"
    output b to "/data/tmp/rel-test-io-csv/b"
    output q to "/data/tmp/rel-test-io-csv/q"

-- by hand: qty 500 and 101 pass, rows (A,10) and (C,30); A = 0, C = 2; the texts as the writer gives them (C.3: a
-- named element by its name, an integer in shortest decimal), the tables as read back
/--
info: ("sym,px\nA,10\nC,30\n", "key,val\nA,10\nC,30\n", [(0, 0, 10), (1, 2, 30)], [(0, 10), (2, 30)])
-/
#guard_msgs in
#eval show IO _ from do
  let d := "/data/tmp/rel-test-io-csv"
  if ← System.FilePath.pathExists d then IO.FS.removeDirAll d
  IO.FS.createDirAll d
  IO.FS.writeFile (d ++ "/trades.csv") "sym,px,qty\nA,10,500\nB,20,50\nC,30,101\n"
  csvOutIO.io; csvBackIO.io
  let big ← IO.FS.readFile (d ++ "/big.csv")
  let pxOf ← IO.FS.readFile (d ++ "/pxof.csv")
  let b ← Table.read [("sym", .long), ("px", .long)] (d ++ "/b")
  let q ← Table.readKeyed [("key", .long)] [("val", .long)] (d ++ "/q")
  IO.FS.removeDirAll d
  return (big, pxOf, b.toList, q.toList)

/-! ## A nullable and a text column in CSV (step I8) -/

-- `name : [C]` a text (the field's bytes, `"…"` quoted where they hold `,` `"` or a line end), `px : 1+N` nullable
-- (the empty field its null); read and written back unchanged
open Rel.Programs.prelude in
rel_program csvNullIO where
    obj N
    obj C : char
    schema Row = {name : [C], px : 1+N}
    input t : N ⟶ Row from csv "/data/tmp/rel-test-io-null/in.csv"
    output t to csv "/data/tmp/rel-test-io-null/out.csv"

-- by hand: the rows ("abc", 10), ("x,\"y\"", null), ("", 7); `px`'s values 10 and 7 at positions 0 and 1 of its right
-- side, the null at 0 of its left side (`inl ∗`); `name`'s cells `[0,3) [3,8) [8,8)` of the bytes `abcx,"y"`
/--
info: ("name,px\nabc,10\n\"x,\"\"y\"\"\",\n,7\n",
 [(0, [97, 98, 99], Sum.inr 10), (1, [120, 44, 34, 121, 34], Sum.inl ()), (2, [], Sum.inr 7)])
-/
#guard_msgs in
#eval show IO _ from do
  let d := "/data/tmp/rel-test-io-null"
  if ← System.FilePath.pathExists d then IO.FS.removeDirAll d
  IO.FS.createDirAll d
  IO.FS.writeFile (d ++ "/in.csv") "name,px\nabc,10\n\"x,\"\"y\"\"\",\n,7\n"
  csvNullIO.io
  let out ← IO.FS.readFile (d ++ "/out.csv")
  let (back, _) ← Table.readCsvDict (← IO.ofExcept Table.Dict.empty) [] [("name", .arr (.atom .char)), ("px", .opt .long)]
    [("name", .text, .char, []), ("px", Table.nullShape .long, .i64, [])] (d ++ "/out.csv")
  IO.FS.removeDirAll d
  return (out, back.toList)

-- refused at elaboration: a nullable column whose `1` is no one-element object, and a text of no `char`
/-- error: line 304, col 5: input `t` from csv "t.csv": column 'val' is N+N; a CSV field holds an atom, a nullable atom `1+V` (`1` an object of one element) or a text `[C]`; declare it a table directory (drop `csv`) -/
#guard_msgs in
rel_program csvSumT where
    obj N
    input t : N ⟶ N+N from csv "t.csv"

/-! ## The CSV columns follow the object: a record `1+S`, a product, a date key -/

-- `N×(1+Q)`: the factor `N` one column, `1+Q` one nullable column per field of `Q`, labelled by its factor (`Q.sym`,
-- `Q.bid`); both empty is the `1`
open Rel.Programs.prelude in
rel_program csvRecNullIO where
    obj N
    obj K = {A,B}
    schema Q = {sym : K, bid : N}
    input t : N ⟶ N×(1+Q) from csv "/data/tmp/rel-test-io-rec/in.csv"
    output t to csv "/data/tmp/rel-test-io-rec/out.csv"

-- `obj D : date` is no positions: its key is the column `key`, before `val`
rel_program csvDateKeyIO where
    obj D : date
    obj N
    input t : D ⟶ N from csv "/data/tmp/rel-test-io-rec/days.csv"
    output t to csv "/data/tmp/rel-test-io-rec/days-out.csv"

-- by hand: rows (5, (A,10)), (6, the `1`), (7, (B,0)), `1+Q`'s right side rows 0 and 2 at its positions 0, 1, its
-- left side row 1; the date keys written back in key order; a row with one field of `Q` empty and not the other
-- refused, naming the row and both columns
/--
info: ("N,Q.sym,Q.bid\n5,A,10\n6,,\n7,B,0\n",
 "key,val\n2024.01.15,1\n2024.01.16,3\n",
 [(0, 5, Sum.inr (0, 10)), (1, 6, Sum.inl ()), (2, 7, Sum.inr (1, 0))],
 [(19737, 1), (19738, 3)],
 "/data/tmp/rel-test-io-rec/bad.csv: data row 2: column 'Q.sym' is not empty and column 'Q.bid' is empty (null); the columns of one `1+S` are empty together, and all of them empty is the `1`")
-/
#guard_msgs in
#eval show IO _ from do
  let d := "/data/tmp/rel-test-io-rec"
  if ← System.FilePath.pathExists d then IO.FS.removeDirAll d
  IO.FS.createDirAll d
  IO.FS.writeFile (d ++ "/in.csv") "N,Q.sym,Q.bid\n5,A,10\n6,,\n7,B,0\n"
  IO.FS.writeFile (d ++ "/days.csv") "key,val\n2024.01.16,3\n2024.01.15,1\n"
  csvRecNullIO.io; csvDateKeyIO.io
  let out ← IO.FS.readFile (d ++ "/out.csv")
  let days ← IO.FS.readFile (d ++ "/days-out.csv")
  let cols : Db.CsvCols := [("N", .atom, .i64, []), ("Q.sym", .null, .i64, ["A", "B"]), ("Q.bid", .null, .i64, [])]
  let S : Schema := [("val", .prod .long (.opt (.prod .long .long)))]
  let (back, _) ← Table.readCsvDict (← IO.ofExcept Table.Dict.empty) [] S cols (d ++ "/out.csv")
  let (dback, _) ← Table.readCsvDict (← IO.ofExcept Table.Dict.empty) [("key", .atom .date)] [("val", .long)]
    [("key", .atom, .date, []), ("val", .atom, .i64, [])] (d ++ "/days-out.csv")
  IO.FS.writeFile (d ++ "/bad.csv") "N,Q.sym,Q.bid\n5,A,10\n6,A,\n"
  let bad ← try (do let _ ← Table.readCsvDict (← IO.ofExcept Table.Dict.empty) [] S cols (d ++ "/bad.csv"); pure "read") catch e => pure e.toString
  IO.FS.removeDirAll d
  return (out, days, back.toList, dback.toList, bad)

-- refused, the objects printed as written (`1`, not its constant): a nullable column of a nullable atom
open Rel.Programs.prelude in
/-- error: line 362, col 5: input `t` from csv "t.csv": column 'a' is 1+(1+N); a CSV field holds an atom, a nullable atom `1+V` (`1` an object of one element) or a text `[C]`; declare it a table directory (drop `csv`) -/
#guard_msgs in
rel_program csvNestT where
    obj N
    schema R = {a : 1+(1+N)}
    input t : N ⟶ R from csv "t.csv"

/-! ## A symbol column: the program's one dictionary -/

-- (PLAN 8.3) each CSV input's texts interned into the program's one dictionary (§0.2), in input order, and every
-- output decoded through it; so two files' equal texts are one id and `∪`, `∩` meet on ids
rel_program csvSymIO where
    obj N
    obj S : sym
    input a : N ⟶ S from csv "/data/tmp/rel-test-io-sym/a.csv"
    input b : N ⟶ S from csv "/data/tmp/rel-test-io-sym/b.csv"
    both : N ⟶ S ≜ a ∪ b
    common : N ⟶ S ≜ a ∩ b
    output a to csv "/data/tmp/rel-test-io-sym/a-out.csv"
    output both to csv "/data/tmp/rel-test-io-sym/u.csv"
    output common to csv "/data/tmp/rel-test-io-sym/i.csv"

-- by hand: `a` interns x, y as ids 0, 1; `b`'s x is id 0 again and its z the next id, 2. `a` written back is its
-- file; `both` = {(0,0),(1,1),(1,2)}, the pair (0,x) of the two files one row; `common` = {(0,0)}. Were `b` its own
-- dictionary (x 0, z 1), `both`'s (1,z) would read back as y
/--
info: ["val\nx\ny\n", "val\nx\ny\nz\n", "val\nx\n"]
-/
#guard_msgs in
#eval show IO _ from do
  let d := "/data/tmp/rel-test-io-sym"
  if ← System.FilePath.pathExists d then IO.FS.removeDirAll d
  IO.FS.createDirAll d
  IO.FS.writeFile (d ++ "/a.csv") "val\nx\ny\n"
  IO.FS.writeFile (d ++ "/b.csv") "val\nx\nz\n"
  csvSymIO.io
  let r ← [d ++ "/a-out.csv", d ++ "/u.csv", d ++ "/i.csv"].mapM fun f : String => IO.FS.readFile f
  IO.FS.removeDirAll d
  return r

/-! ## Own symbol columns: one dictionary per library (owner decisions N, Q, O) -/

-- each program writes one own table into the library `one` (the directory holding it), so its dictionary starts as
-- `one`'s and the texts it adds are appended there
rel_program libAIO where
    obj N
    obj S : sym
    input a : N ⟶ S from csv "/data/tmp/rel-test-io-lib/a.csv"
    output a to "/data/tmp/rel-test-io-lib/one/a"

rel_program libBIO where
    obj N
    obj S : sym
    input b : N ⟶ S from csv "/data/tmp/rel-test-io-lib/b.csv"
    output b to "/data/tmp/rel-test-io-lib/one/b"

rel_program libMeetIO where
    obj N
    obj S : sym
    input a : N ⟶ S from "/data/tmp/rel-test-io-lib/one/a"
    input b : N ⟶ S from "/data/tmp/rel-test-io-lib/one/b"
    input c : N ⟶ S from csv "/data/tmp/rel-test-io-lib/c.csv"
    common : N ⟶ S ≜ a ∩ b
    both : N ⟶ S ≜ a ∪ c
    output common to "/data/tmp/rel-test-io-lib/one/common"
    output both to "/data/tmp/rel-test-io-lib/one/both"

-- by hand: `libAIO` writes `a` = ibm aapl into `one` (ids 0 1, the dictionary `ibm aapl`); `libBIO` writes `b` =
-- msft aapl, interned into that dictionary: msft takes id 2 and aapl keeps 1. `libMeetIO` reads both as they lie and
-- `c.csv` = zz ibm into `one`'s dictionary (zz 3, ibm 0): `common` = a ∩ b = {(1,1)}, renumbered (0,1); `both` =
-- a ∪ c = {(0,0),(0,3),(1,0),(1,1)}, renumbered; the dictionary after is `ibm aapl msft zz`
/--
info: (["ibm", "aapl", "msft", "zz"], [[(0, 0), (1, 1)], [(0, 2), (1, 1)], [(0, 1)], [(0, 0), (1, 3), (2, 0), (3, 1)]])
-/
#guard_msgs in
#eval show IO _ from do
  let d := "/data/tmp/rel-test-io-lib"
  if ← System.FilePath.pathExists d then IO.FS.removeDirAll d
  IO.FS.createDirAll d
  IO.FS.writeFile (d ++ "/a.csv") "val\nibm\naapl\n"
  IO.FS.writeFile (d ++ "/b.csv") "val\nmsft\naapl\n"
  IO.FS.writeFile (d ++ "/c.csv") "val\nzz\nibm\n"
  libAIO.io; libBIO.io; libMeetIO.io
  let S : Schema := [("val", .atom .sym)]
  let D ← Table.libDict (d ++ "/one")
  let r ← ["a", "b", "common", "both"].mapM fun t => return (← Table.read S (d ++ "/one/" ++ t)).toList
  IO.FS.removeDirAll d
  let ts : List String := D.toList.map fun (_, b) => String.ofList (b.map fun c => Char.ofNat c.toNat)
  return (ts, r)

-- `dictionary D` is the program's one dictionary as the relation `S ⟶ [C]`: `unenum(a, D) = a D` writes each id of
-- `a` as its text. By hand: `ibm aapl ibm` interns as ids 0 1 0, so the texts are the file's own words
open Rel.Programs.prelude in
rel_program unenumIO where
    obj N
    obj S : sym
    obj C : char
    input a : N ⟶ S from csv "/data/tmp/rel-test-io-unenum/a.csv"
    dictionary D : S ⟶ [C]
    texts : N ⟶ [C] ≜ unenum(a, D)
    output texts to csv "/data/tmp/rel-test-io-unenum/t.csv"

/--
info: "val\nibm\naapl\nibm\n"
-/
#guard_msgs in
#eval show IO _ from do
  let d := "/data/tmp/rel-test-io-unenum"
  if ← System.FilePath.pathExists d then IO.FS.removeDirAll d
  IO.FS.createDirAll d
  IO.FS.writeFile (d ++ "/a.csv") "val\nibm\naapl\nibm\n"
  unenumIO.io
  let r ← IO.FS.readFile (d ++ "/t.csv")
  IO.FS.removeDirAll d
  return r

-- `<` at a symbol is the order of the texts, `rank(D) < rank(D)°` (`Elab.symOrd`): `b a c` interns as ids 0 1 2, whose
-- ranks are 1 0 2: `a < a°` on positions is (1,0) (1,2) (0,2), its values by position key 0 1 1 are 2 0 2 (a positional key is
-- not written), and `rank(D)` is b↦1 a↦0 c↦2 (the guard of `asc` at sym)
open Rel.Programs.prelude in
rel_program symLtIO where
    obj N
    obj S : sym
    obj C : char
    input a : N ⟶ S from csv "/data/tmp/rel-test-io-symlt/a.csv"
    dictionary D : S ⟶ [C]
    lts : N ⟶ N ≜ a < a°
    output lts to csv "/data/tmp/rel-test-io-symlt/t.csv"
    rk : S ⟶ N ≜ rank(D)
    output rk to csv "/data/tmp/rel-test-io-symlt/r.csv"

/--
info: "val\n2\n0\n2\n|key,val\nb,1\na,0\nc,2\n"
-/
#guard_msgs in
#eval show IO _ from do
  let d := "/data/tmp/rel-test-io-symlt"
  if ← System.FilePath.pathExists d then IO.FS.removeDirAll d
  IO.FS.createDirAll d
  IO.FS.writeFile (d ++ "/a.csv") "val\nb\na\nc\n"
  symLtIO.io
  let r ← IO.FS.readFile (d ++ "/t.csv")
  let r2 ← IO.FS.readFile (d ++ "/r.csv")
  IO.FS.removeDirAll d
  return r ++ "|" ++ r2

-- `asc` at a symbol is `asc(ran(P r)) (P r)°` with `r = rank(D)` (`Elab.symOrd`): the texts `b a c` (ids 0 1 2) come out as
-- `a b c`, though the ids are in insertion order; `lessThan` is a definition generic over its object, called at `sym`
open Rel.Programs.prelude in
rel_program symAscIO where
    obj N
    obj S : sym
    obj C : char
    input a : N ⟶ S from csv "/data/tmp/rel-test-io-symasc/a.csv"
    dictionary D : S ⟶ [C]
    srt : N ⟶ S ≜ asc(ran(a))
    sorted : N ⟶ [C] ≜ srt D
    output sorted to csv "/data/tmp/rel-test-io-symasc/t.csv"

/--
info: "val\na\nb\nc\n"
-/
#guard_msgs in
#eval show IO _ from do
  let d := "/data/tmp/rel-test-io-symasc"
  if ← System.FilePath.pathExists d then IO.FS.removeDirAll d
  IO.FS.createDirAll d
  IO.FS.writeFile (d ++ "/a.csv") "val\nb\na\nc\n"
  symAscIO.io
  let r ← IO.FS.readFile (d ++ "/t.csv")
  IO.FS.removeDirAll d
  return r

-- `lessThan : S ⟶ S ≜ <` is a definition that reads the dictionary `D` without naming it (`Expand.walk`): its body is
-- `symOrd`'s order of the texts
open Rel.Programs.prelude in
rel_program symPolyIO where
    obj N
    obj S : sym
    obj C : char
    input a : N ⟶ S from csv "/data/tmp/rel-test-io-sympoly/a.csv"
    dictionary D : S ⟶ [C]
    lessThan : S ⟶ S ≜ <
    lts : N ⟶ N ≜ a lessThan a°
    output lts to csv "/data/tmp/rel-test-io-sympoly/l.csv"

/--
info: "val\n2\n0\n2\n"
-/
#guard_msgs in
#eval show IO _ from do
  let d := "/data/tmp/rel-test-io-sympoly"
  if ← System.FilePath.pathExists d then IO.FS.removeDirAll d
  IO.FS.createDirAll d
  IO.FS.writeFile (d ++ "/a.csv") "val\nb\na\nc\n"
  symPolyIO.io
  let r ← IO.FS.readFile (d ++ "/l.csv")
  IO.FS.removeDirAll d
  return r

-- a dictionary before a CSV input with a symbol column would lack that input's texts: refused where it is elaborated
/--
error: line 568, col 5: input `b` has a symbol column and comes after `dictionary D`, which is bound to the texts of the inputs before it; move `dictionary D` after `input b`
-/
#guard_msgs in
rel_program dictFirstT where
    obj N
    obj S : sym
    obj C : char
    input a : N ⟶ S from csv "/data/tmp/rel-test-io-dictfirst/a.csv"
    dictionary D : S ⟶ [C]
    input b : N ⟶ S from csv "/data/tmp/rel-test-io-dictfirst/b.csv"
    output b to csv "/data/tmp/rel-test-io-dictfirst/t.csv"

-- two own inputs with symbol columns in two libraries, met by `∩`: refused where the program is elaborated
/--
error: rel_program expansion: the symbol columns of `a` are ids in the library /data/tmp/rel-test-io-lib/one and those of `b` in the library /data/tmp/rel-test-io-lib/two, two dictionaries, so they cannot meet; convert one to its texts with `unenum` (`I ≫ D`)
-/
#guard_msgs in
rel_program twoLibT where
    obj N
    obj S : sym
    input a : N ⟶ S from "/data/tmp/rel-test-io-lib/one/a"
    input b : N ⟶ S from "/data/tmp/rel-test-io-lib/two/b"
    common : N ⟶ S ≜ a ∩ b
    output common to "/data/tmp/rel-test-io-lib/one/common"
