import Rel.Programs.FrameJoin

/-! A dataframe application (doc/dataframe-design.zh.typ F6): its four frames are `input` statements, its results
    `output` statements. Each check gives the inputs their tables in a `where`; expected rows worked by hand from `tt`,
    `qq`, `mm`, `vv` (sym `C` has no quote and no venue; A's quotes 2 and 3 tie at time 3). The `#eval` at the end
    runs `tradeApp.io` on the CSV texts of the four inputs and compares every written file with its text by hand. -/

namespace Rel.Lang.TestFrameApp

open Rel.Programs.prelude Rel.Programs.frame Rel.Programs.frameGroup Rel.Programs.frameJoin in
rel_program tradeApp where
    obj N
    obj K = {A,B,C}
    obj D : date
    obj Pr : f64
    obj C : char
    schema Trade = {sym : K, day : D, time : N, price : Pr, size : N}
    schema Quote = {sym : K, time : N, bid : N}
    schema Agg = {size : N, n : N}
    schema TradeBid = {sym : K, time : N, price : Pr, bid : 1+N}
    schema SymCum = {sym : K, cum : N}
    schema Venue = {sym : K, venue : [C]}
    schema TradeVenue = {sym : K, time : N, venue : [C]}
    schema Mark = {sym : K, px : 1+N}
    input trades : N ⟶ Trade from csv "trades.csv"
    input quotes : N ⟶ Quote from csv "quotes.csv"
    input venues : N ⟶ Venue from csv "venues.csv"
    input marks : N ⟶ Mark from csv "marks.csv"

    -- size ≥ 100, then per sym (sum of size, count): keyed by sym, so written as `key/` + `val/`
    big : N ⟶ Trade ≜ filterBy(dom(col Trade "size" dom(<°{(99,∗)})), trades)
    bySym : K ⟶ Agg ≜ agg((big col Trade "sym")°, ⟨F(big col Trade "size") sum, length⟩)
    -- the two largest prices
    top2 : N ⟶ Trade ≜ topK({(∗,2)}, col Trade "price", trades)
    -- the trades after the first day, and the size traded per day (a `date` filtered by order, then a group key)
    late : N ⟶ Trade ≜ filterBy(dom(col Trade "day" dom(<°{(2024.01.15,∗)})), trades)
    perDay : D ⟶ N ≜ agg((trades col Trade "day")°, F(trades col Trade "size") sum)
    -- each trade with the bid of its sym's latest quote at or before its time, null when there is none
    withBid : N ⟶ TradeBid ≜ aj(col Trade "sym", col Trade "time", col Quote "sym", col Quote "time", trades, quotes) ⟨π₁ ⟨⟨col Trade "sym", col Trade "time"⟩, col Trade "price"⟩, π₂ (𝟙 ⊕ col Quote "bid")⟩
    -- running size within each sym, in position order
    cumSize : N ⟶ SymCum ≜ ⟨trades col Trade "sym", sumsBy(trades col Trade "sym", trades col Trade "size")⟩
    -- every trade with each quote of its sym, or once with the null; the nulls are the trades of an unquoted sym
    lj : N ⟶ Trade×(1+Quote) ≜ leftJoin(col Trade "sym", col Quote "sym", trades, quotes)
    unquoted : 1 ⟶ N ≜ nulls(π₂, lj)
    -- a text column carried through a join: each trade with its sym's venue (C has none)
    tradeVenue : N ⟶ TradeVenue ≜ innerJoin(col Trade "sym", col Venue "sym", trades, venues) ⟨⟨π₁ col Trade "sym", π₁ col Trade "time"⟩, π₂ col Venue "venue"⟩
    -- a nullable input column: its null count, and q's fills on it
    markNulls : 1 ⟶ N ≜ nulls(col Mark "px", marks)
    filled : N ⟶ Mark ≜ ⟨marks col Mark "sym", fills(marks col Mark "px")⟩

    output big to csv "big.csv"
    output bySym to csv "bysym.csv"
    output top2 to csv "top2.csv"
    output withBid to csv "withbid.csv"
    output cumSize to csv "cumsize.csv"
    output unquoted to csv "unquoted.csv"
    output late to csv "late.csv"
    output perDay to csv "perday.csv"
    output lj to csv "lj.csv"
    output tradeVenue to csv "tradevenue.csv"
    output markNulls to csv "marknulls.csv"
    output filled to csv "filled.csv"

    tt : N ⟶ Trade ≜ {(0,((((A,2024.01.15),1),10.5),100)),(1,((((B,2024.01.15),2),20.25),50)),
      (2,((((A,2024.01.15),3),11.5),200)),(3,((((C,2024.01.16),3),7.75),300)),(4,((((B,2024.01.16),5),21.5),150)),
      (5,((((A,2024.01.17),5),12.5),50)),(6,((((C,2024.01.17),6),8.25),100))}
    qq : N ⟶ Quote ≜ {(0,((A,0),9)),(1,((B,1),19)),(2,((A,3),10)),(3,((A,3),11)),(4,((B,4),20)),(5,((A,6),13))}
    -- the marks: px null at rows 0 2 4 (a sum literal does not parse, so the null is built with `tot`)
    ms : N ⟶ K ≜ {(0,A),(1,B),(2,C),(3,A),(4,B)}
    mm : N ⟶ Mark ≜ ⟨ms, dom(ms) tot({(1,5),(3,7)})⟩
    vv : N ⟶ Venue ≜ {(0,(A,"NY")),(1,(B,"LN, main"))}

    -- kept rows 0 2 3 4 6: A 100+200, B 150, C 300+100
    check bySym = {(A,(300,2)),(B,(150,1)),(C,(400,2))} where trades ≜ tt
    -- prices 21.5 (row 4), 20.25 (row 1)
    check top2 = {(0,((((B,2024.01.16),5),21.5),150)),(1,((((B,2024.01.15),2),20.25),50))} where trades ≜ tt
    -- rows 3–6 are after 2024.01.15; per day 100+50+200, 300+150, 50+100
    check late = {(0,((((C,2024.01.16),3),7.75),300)),(1,((((B,2024.01.16),5),21.5),150)),
      (2,((((A,2024.01.17),5),12.5),50)),(3,((((C,2024.01.17),6),8.25),100))} where trades ≜ tt
    check perDay = {(2024.01.15,350),(2024.01.16,450),(2024.01.17,150)} where trades ≜ tt
    -- trades per day, untyped: rows 0–2, 3–4, 5–6
    check agg((trades col Trade "day")°, length) = {(2024.01.15,3),(2024.01.16,2),(2024.01.17,2)} where trades ≜ tt
    -- the trades of A and B in position order, each with its sym's one venue
    check tradeVenue = {(0,((A,1),"NY")),(1,((B,2),"LN, main")),(2,((A,3),"NY")),(3,((B,5),"LN, main")),
      (4,((A,5),"NY"))} where trades ≜ tt, venues ≜ vv
    -- A at 1 → q0 (9); B at 2 → q1 (19); A at 3 → q2, q3 tie, the later q3 (11); C none (null, read as 0);
    -- B at 5 → q4 (20); A at 5 → q3 (11)
    check withBid ⟨π₁, π₂ [{(∗,0)}, 𝟙]⟩ = {(0,(((A,1),10.5),9)),(1,(((B,2),20.25),19)),(2,(((A,3),11.5),11)),
      (3,(((C,3),7.75),0)),(4,(((B,5),21.5),20)),(5,(((A,5),12.5),11)),(6,(((C,6),8.25),0))} where trades ≜ tt, quotes ≜ qq
    check nulls(col TradeBid "bid", withBid) = {(∗,2)} where trades ≜ tt, quotes ≜ qq
    -- px · 5 · 7 ·: 3 nulls; fills 5 at row 2, 7 at row 4, the leading null stays (read as 0)
    check markNulls = {(∗,3)} where marks ≜ mm
    check filled ⟨π₁, π₂ [{(∗,0)}, 𝟙]⟩ = {(0,(A,0)),(1,(B,5)),(2,(C,5)),(3,(A,7)),(4,(B,7))} where marks ≜ mm
    -- A rows 0 2 5: 100 300 350; B rows 1 4: 50 200; C rows 3 6: 300 400
    check cumSize = {(0,(A,100)),(1,(B,50)),(2,(A,300)),(3,(C,300)),(4,(B,200)),(5,(A,350)),(6,(C,400))} where trades ≜ tt
    -- A 3 trades × 4 quotes, B 2 × 2, C 2 once each: 18 rows, 2 of them null (C's rows 3, 6)
    check count(lj) = {(∗,18)} where trades ≜ tt, quotes ≜ qq
    check unquoted = {(∗,2)} where trades ≜ tt, quotes ≜ qq
    check filterNothing(π₂, lj) π₁ ⟨col Trade "sym", col Trade "time"⟩ = {(0,(C,3)),(1,(C,6))} where trades ≜ tt, quotes ≜ qq

#guard tradeApp.failures.map toString == []

/-! ## `tradeApp.io`: the two CSV inputs read, every output written as CSV (IO step I9) -/

-- the CSV texts of `tt`, `qq`, `mm`: a header of the schema's columns, then one row per position, symbols by name,
-- a date `yyyy.mm.dd`, a null the empty field; the venues, a text quoted where it holds `,` (C has none)
def tradesCsv := "sym,day,time,price,size\nA,2024.01.15,1,10.5,100\nB,2024.01.15,2,20.25,50\n\
  A,2024.01.15,3,11.5,200\nC,2024.01.16,3,7.75,300\nB,2024.01.16,5,21.5,150\nA,2024.01.17,5,12.5,50\n\
  C,2024.01.17,6,8.25,100\n"
def quotesCsv := "sym,time,bid\nA,0,9\nB,1,19\nA,3,10\nA,3,11\nB,4,20\nA,6,13\n"
def venuesCsv := "sym,venue\nA,NY\nB,\"LN, main\"\n"
def marksCsv := "sym,px\nA,\nB,5\nC,\nA,7\nB,\n"

/-- The four inputs of `tradeApp` written to the current directory: the `#eval` below and `make native` (`relc run`
    names `tradeInputs`, runs its `io`) read the one copy of the texts. -/
def tradeInputs.io : IO Unit := do
  for (p, t) in [("trades.csv", tradesCsv), ("quotes.csv", quotesCsv), ("venues.csv", venuesCsv),
      ("marks.csv", marksCsv)] do IO.FS.writeFile p t

-- each declared output's text, by hand from the checks above: a positional output its value columns only, rows
-- renumbered; a keyed one the key column `key` first, rows in key order
def expected : List (String × String) := [
  ("big", "sym,day,time,price,size\nA,2024.01.15,1,10.5,100\nA,2024.01.15,3,11.5,200\nC,2024.01.16,3,7.75,300\n\
    B,2024.01.16,5,21.5,150\nC,2024.01.17,6,8.25,100\n"),
  ("bySym", "key,size,n\nA,300,2\nB,150,1\nC,400,2\n"),
  ("top2", "sym,day,time,price,size\nB,2024.01.16,5,21.5,150\nB,2024.01.15,2,20.25,50\n"),
  ("withBid", "sym,time,price,bid\nA,1,10.5,9\nB,2,20.25,19\nA,3,11.5,11\nC,3,7.75,\nB,5,21.5,20\nA,5,12.5,11\n\
    C,6,8.25,\n"),
  ("cumSize", "sym,cum\nA,100\nB,50\nA,300\nC,300\nB,200\nA,350\nC,400\n"),
  ("unquoted", "key,val\n∗,2\n"),
  ("late", "sym,day,time,price,size\nC,2024.01.16,3,7.75,300\nB,2024.01.16,5,21.5,150\nA,2024.01.17,5,12.5,50\n\
    C,2024.01.17,6,8.25,100\n"),
  ("perDay", "key,val\n2024.01.15,350\n2024.01.16,450\n2024.01.17,150\n"),
  -- each trade's quotes of its sym in quote order (A: q0 q2 q3 q5, B: q1 q4); C's rows once, the three `Quote`
  -- fields empty; a factor's columns are prefixed by its schema's name
  ("lj", "Trade.sym,Trade.day,Trade.time,Trade.price,Trade.size,Quote.sym,Quote.time,Quote.bid\n\
    A,2024.01.15,1,10.5,100,A,0,9\nA,2024.01.15,1,10.5,100,A,3,10\nA,2024.01.15,1,10.5,100,A,3,11\n\
    A,2024.01.15,1,10.5,100,A,6,13\nB,2024.01.15,2,20.25,50,B,1,19\nB,2024.01.15,2,20.25,50,B,4,20\n\
    A,2024.01.15,3,11.5,200,A,0,9\nA,2024.01.15,3,11.5,200,A,3,10\nA,2024.01.15,3,11.5,200,A,3,11\n\
    A,2024.01.15,3,11.5,200,A,6,13\nC,2024.01.16,3,7.75,300,,,\nB,2024.01.16,5,21.5,150,B,1,19\n\
    B,2024.01.16,5,21.5,150,B,4,20\nA,2024.01.17,5,12.5,50,A,0,9\nA,2024.01.17,5,12.5,50,A,3,10\n\
    A,2024.01.17,5,12.5,50,A,3,11\nA,2024.01.17,5,12.5,50,A,6,13\nC,2024.01.17,6,8.25,100,,,\n"),
  ("tradeVenue", "sym,time,venue\nA,1,NY\nB,2,\"LN, main\"\nA,3,NY\nB,5,\"LN, main\"\nA,5,NY\n"),
  ("markNulls", "key,val\n∗,3\n"),
  ("filled", "sym,px\nA,\nB,5\nC,5\nA,7\nB,7\n")]

-- `tradeApp.io` run in a fresh directory holding the inputs, its relative paths resolved there (IO design F.1); each
-- DECLARED output must be a CSV file with its expected text, so a missing, unread or different file fails the build
#eval show IO Unit from do
  let d := "/data/tmp/rel-test-frame-app"
  if ← System.FilePath.pathExists d then IO.FS.removeDirAll d
  IO.FS.createDirAll d
  let cwd ← IO.currentDir
  try
    IO.Process.setCurrentDir d
    tradeInputs.io
    tradeApp.io
  finally
    IO.Process.setCurrentDir cwd
  unless tradeApp.outputs.map (·.1) == expected.map (·.1) do
    throw (IO.userError s!"outputs declared {tradeApp.outputs.map (·.1)}, texts expected for {expected.map (·.1)}")
  for ((x, csv, p), (_, e)) in tradeApp.outputs.zip expected do
    unless csv do throw (IO.userError s!"output `{x}` to \"{p}\" is no CSV file")
    let t ← IO.FS.readFile (d ++ "/" ++ p)
    unless t == e do throw (IO.userError s!"output `{x}` wrote {d}/{p}:\n{t}expected:\n{e}")
  IO.FS.removeDirAll d

end Rel.Lang.TestFrameApp
