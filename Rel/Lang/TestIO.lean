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

/-- error: in the program `Rel.Lang.TestIO.trades`, line 17, col 5: input `t`: an imported program's inputs are not the importer's yet (IO step I3); declare it in the importing program and pass it to the definitions as a parameter -/
#guard_msgs in
open trades in
rel_program importT where
    x : N ⟶ N ≜ bigPx
