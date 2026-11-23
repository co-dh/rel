# 8.2h3g handoff

Done (committed): merge keep-82h3f (Closure/Scan conflicts: master's `kscan_nul_row` bind form kept); RepCols
`colMap_max_self` adapted; Canon `sumTab` summands `Opt.ofArr`; Canon + RepCols green. RepCast: `Vals.row` ->
`ValsB.row (o := false)`, `dsimp only [Vals.get]` in cast_holds `row`.

Left in Rel/RepCast.lean:
- 469/470: `rw` of `wd n x'.enc i` fails, target shows `wd n (ColB.enc (x', y').fst) i` (defeq; `change`/`show`).
- 550: unsolved goals in `arithOp_den`/sum case.
