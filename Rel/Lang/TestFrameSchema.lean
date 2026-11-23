import Rel.Programs.FrameJoin

/-! The dataframe library on tables with named columns (PLAN D.9/D.11): each entry is a definition whose parameter is
    the input table at a schema, `t : N ⟶ Trade`, and whose target is the output schema; a column is `col S "c"`. The
    entries run here on the literal tables `tt`, `dd`; every expected row is worked by hand from them. -/

namespace Rel.Lang.TestFrameSchema

open Rel.Programs.prelude Rel.Programs.frame Rel.Programs.frameGroup Rel.Programs.frameJoin in
rel_program frameSchemaT where
    obj K = {A,B,C,D}
    obj S = {buy,sell}
    obj E = {tech,fin,na}
    obj N
    schema Trade = {sym : K, px : N, qty : N, side : S}
    schema Dim = {sym : K, sector : E}
    schema SymPx = {sym : K, px : N}
    schema TradeV = {sym : K, px : N, qty : N, side : S, val : N}
    schema BySym = {sym : K, qty : N, n : N}
    schema Enriched = {sym : K, px : N, sector : E}
    schema SymSector = {sym : K, sector : E}

    -- the input tables; `D` has no row in `dd`
    tt : N ⟶ Trade ≜ {(0,(((A,10),5),buy)),(1,(((B,20),3),sell)),(2,(((A,12),2),sell)),(3,(((C,7),10),buy)),
      (4,(((D,30),1),buy)),(5,(((B,18),4),buy)),(6,(((C,9),6),sell)),(7,(((A,11),8),buy))}
    dd : N ⟶ Dim ≜ {(0,(A,tech)),(1,(B,fin)),(2,(C,tech))}

    -- select
    sel(t : N ⟶ Trade) : N ⟶ SymPx ≜ t ⟨col Trade "sym", col Trade "px"⟩
    check sel(tt) = {(0,(A,10)),(1,(B,20)),(2,(A,12)),(3,(C,7)),(4,(D,30)),(5,(B,18)),(6,(C,9)),(7,(A,11))}
    -- the result's columns read by their names in `SymPx`
    check sel(tt) col SymPx "px" = {(0,10),(1,20),(2,12),(3,7),(4,30),(5,18),(6,9),(7,11)}

    -- filterBy: side = buy; qty > 4
    buys(t : N ⟶ Trade) : N ⟶ Trade ≜ filterBy(dom(col Trade "side" {(buy,buy)}), t)
    check buys(tt) = {(0,(((A,10),5),buy)),(1,(((C,7),10),buy)),(2,(((D,30),1),buy)),(3,(((B,18),4),buy)),
      (4,(((A,11),8),buy))}
    big(t : N ⟶ Trade) : N ⟶ Trade ≜ filterBy(dom(col Trade "qty" dom(<°{(4,∗)})), t)
    check big(tt) = {(0,(((A,10),5),buy)),(1,(((C,7),10),buy)),(2,(((C,9),6),sell)),(3,(((A,11),8),buy))}

    -- derive val = px × qty: `TradeV` is `Trade` with one more column, so `⟨𝟙, …⟩` reaches it
    derived(t : N ⟶ Trade) : N ⟶ TradeV ≜ t ⟨𝟙, ⟨col Trade "px", col Trade "qty"⟩times⟩
    check derived(tt) col TradeV "val" = {(0,50),(1,60),(2,24),(3,70),(4,30),(5,72),(6,54),(7,88)}
    check derived(tt) col TradeV "sym" = tt col Trade "sym"

    -- sortBy px
    byPx(t : N ⟶ Trade) : N ⟶ Trade ≜ sortBy(col Trade "px", t)
    check byPx(tt) = {(0,(((C,7),10),buy)),(1,(((C,9),6),sell)),(2,(((A,10),5),buy)),(3,(((A,11),8),buy)),
      (4,(((A,12),2),sell)),(5,(((B,18),4),buy)),(6,(((B,20),3),sell)),(7,(((D,30),1),buy))}

    -- aggregate by sym: sum of qty, count; groups in first-occurrence order A B C D
    bySym(t : N ⟶ Trade) : N ⟶ BySym ≜ aggregate(col Trade "sym", ⟨F(t col Trade "qty") sum, length⟩, t) ⟨⟨π₁, π₂ π₁⟩, π₂ π₂⟩
    check bySym(tt) = {(0,((A,15),3)),(1,((B,7),2)),(2,((C,16),2)),(3,((D,1),1))}

    -- innerJoin on sym: row 4 (`D`) has no match
    enrich(t : N ⟶ Trade, d : N ⟶ Dim) : N ⟶ Enriched ≜ innerJoin(col Trade "sym", col Dim "sym", t, d) ⟨⟨π₁ col Trade "sym", π₁ col Trade "px"⟩, π₂ col Dim "sector"⟩
    check enrich(tt, dd) = {(0,((A,10),tech)),(1,((B,20),fin)),(2,((A,12),tech)),(3,((C,7),tech)),
      (4,((B,18),fin)),(5,((C,9),tech)),(6,((A,11),tech))}

    -- leftJoin on sym: the missing `D` gets the sector `na`
    sector(t : N ⟶ Trade, d : N ⟶ Dim) : N ⟶ SymSector ≜ leftJoin(col Trade "sym", col Dim "sym", t, d) ⟨π₁ col Trade "sym", π₂ [{(∗,na)}, col Dim "sector"]⟩
    check sector(tt, dd) = {(0,(A,tech)),(1,(B,fin)),(2,(A,tech)),(3,(C,tech)),(4,(D,na)),(5,(B,fin)),
      (6,(C,tech)),(7,(A,tech))}

    -- topK by px
    top3(t : N ⟶ Trade) : N ⟶ Trade ≜ topK({(∗,3)}, col Trade "px", t)
    check top3(tt) = {(0,(((D,30),1),buy)),(1,(((B,20),3),sell)),(2,(((B,18),4),buy))}

#guard frameSchemaT.failures.map toString == []

end Rel.Lang.TestFrameSchema
