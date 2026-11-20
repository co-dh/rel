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

/-- error: line 59, col 5: input `t` from csv "t.csv": column 'val' is K×N, no atom: a CSV field holds one atom; declare it a table directory (drop `csv`) -/
#guard_msgs in
rel_program csvProdT where
    obj K = {A,B}
    obj N
    input t : N ⟶ K×N from csv "t.csv"

/-- error: line 66, col 5: input `t` from csv "t.csv": column 'val' is a list column, which is not read from CSV yet (IO step I8) -/
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

/-- error: line 147, col 5: input `t` from "t": the key is positions, stored Rel.Obj.atom (Rel.QAtomicType.i64), and F ⟶ N stores it Rel.Obj.atom (Rel.QAtomicType.f64); declare the key an object stored i64 -/
#guard_msgs in
rel_program floatKeyT where
    obj F : f64
    obj N
    input t : F ⟶ N from "t"

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
  ["big", "big/px", "big/sym", "px", "px/val", "pxof", "pxof/key", "pxof/key/key", "pxof/val", "pxof/val/val",
    "trades.csv"])
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

-- the refusals at run time, each before any file is written: a CSV output (its writer is IO step I7), refused before
-- any read; an input whose files are missing, the OS error naming the file
rel_program missingIO where
    obj N
    input t : N ⟶ N from "/data/tmp/rel-test-io-none/t"
    output t to "/data/tmp/rel-test-io-none/out"

/--
info: output `bigPx` to csv "bigpx.csv": the CSV writer is IO step I7, not yet here; write a table directory (drop `csv`)
no such file or directory (error code: 2)
  file: /data/tmp/rel-test-io-none/t/val
-/
#guard_msgs in
#eval show IO Unit from do
  for r in [← trades.io.toBaseIO, ← missingIO.io.toBaseIO] do
    match r with | .ok _ => IO.println "ok" | .error e => IO.println e
