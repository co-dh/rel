import Rel.Programs.FrameJoin

/-! A dataframe application (doc/dataframe-design.zh.typ F6): its two frames are `input` statements, its results
    `output` statements; nothing is read or written here (IO step I3/I9). Each check gives the inputs their tables in
    a `where`; expected rows worked by hand from `tt`, `qq` (sym `C` has no quote; A's quotes 2 and 3 tie at time 3). -/

namespace Rel.Lang.TestFrameApp

open Rel.Programs.prelude Rel.Programs.frame Rel.Programs.frameGroup Rel.Programs.frameJoin in
rel_program tradeApp where
    obj N
    obj K = {A,B,C}
    schema Trade = {sym : K, time : N, price : N, size : N}
    schema Quote = {sym : K, time : N, bid : N}
    schema Agg = {size : N, n : N}
    schema TradeBid = {sym : K, time : N, price : N, bid : N}
    schema SymCum = {sym : K, cum : N}
    input trades : N ⟶ Trade from csv "trades.csv"
    input quotes : N ⟶ Quote from csv "quotes.csv"

    -- size ≥ 100, then per sym (sum of size, count): keyed by sym, so written as `key/` + `val/`
    big : N ⟶ Trade ≜ filterBy(dom(col Trade "size" dom(<°{(99,∗)})), trades)
    bySym : K ⟶ Agg ≜ agg((big col Trade "sym")°, ⟨F(big col Trade "size") sum, length⟩)
    -- the two largest prices
    top2 : N ⟶ Trade ≜ topK({(∗,2)}, col Trade "price", trades)
    -- each trade with the bid of its sym's latest quote at or before its time; no quote reads as bid 0
    withBid : N ⟶ TradeBid ≜ aj(col Trade "sym", col Trade "time", col Quote "sym", col Quote "time", trades, quotes) ⟨π₁ ⟨⟨col Trade "sym", col Trade "time"⟩, col Trade "price"⟩, π₂ [col Quote "bid", {(∗,0)}]⟩
    -- running size within each sym, in position order
    cumSize : N ⟶ SymCum ≜ ⟨trades col Trade "sym", sumsBy(trades col Trade "sym", trades col Trade "size")⟩
    -- every trade with each quote of its sym, or once with the null; the nulls are the trades of an unquoted sym
    lj : N ⟶ Trade×(Quote+1) ≜ leftJoin(col Trade "sym", col Quote "sym", trades, quotes)
    unquoted : 1 ⟶ N ≜ nulls(π₂, lj)

    output top2 to "top2"
    output bySym to "bysym"
    output withBid to csv "withbid.csv"

    tt : N ⟶ Trade ≜ {(0,(((A,1),10),100)),(1,(((B,2),20),50)),(2,(((A,3),11),200)),(3,(((C,3),7),300)),
      (4,(((B,5),21),150)),(5,(((A,5),12),50)),(6,(((C,6),8),100))}
    qq : N ⟶ Quote ≜ {(0,((A,0),9)),(1,((B,1),19)),(2,((A,3),10)),(3,((A,3),11)),(4,((B,4),20)),(5,((A,6),13))}

    -- kept rows 0 2 3 4 6: A 100+200, B 150, C 300+100
    check bySym = {(A,(300,2)),(B,(150,1)),(C,(400,2))} where trades ≜ tt
    -- prices 21 (row 4), 20 (row 1)
    check top2 = {(0,(((B,5),21),150)),(1,(((B,2),20),50))} where trades ≜ tt
    -- A at 1 → q0 (9); B at 2 → q1 (19); A at 3 → q2, q3 tie, the later q3 (11); C none (0); B at 5 → q4 (20);
    -- A at 5 → q3 (11)
    check withBid = {(0,(((A,1),10),9)),(1,(((B,2),20),19)),(2,(((A,3),11),11)),(3,(((C,3),7),0)),
      (4,(((B,5),21),20)),(5,(((A,5),12),11)),(6,(((C,6),8),0))} where trades ≜ tt, quotes ≜ qq
    -- A rows 0 2 5: 100 300 350; B rows 1 4: 50 200; C rows 3 6: 300 400
    check cumSize = {(0,(A,100)),(1,(B,50)),(2,(A,300)),(3,(C,300)),(4,(B,200)),(5,(A,350)),(6,(C,400))} where trades ≜ tt
    -- A 3 trades × 4 quotes, B 2 × 2, C 2 once each: 18 rows, 2 of them null (C's rows 3, 6)
    check count(lj) = {(∗,18)} where trades ≜ tt, quotes ≜ qq
    check unquoted = {(∗,2)} where trades ≜ tt, quotes ≜ qq
    check filterNothing(π₂, lj) π₁ ⟨col Trade "sym", col Trade "time"⟩ = {(0,(C,3)),(1,(C,6))} where trades ≜ tt, quotes ≜ qq

#guard tradeApp.failures.map toString == []

end Rel.Lang.TestFrameApp
