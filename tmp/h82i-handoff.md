# 8.2i handoff (part): native on the dense sum layout

## Done (commit "8.2i (part)")
- Merged 76a6bce (keep-82g) onto base d33cf20.
- `Plan.Instr.readOpt` restored (37e1ad6): the 8.2 branch had dropped master's `readOpt` from `Rel/Run/Lang/Plan.lean`
  (constructor, `runI` case, `Plan.exec` read, builder `Plan.readOpt`) while `Rel/Lang/EmitC.lean` and `Rel/Run/Table.lean`
  still use it.
- `Rel/Lang/EmitC.lean` rewritten to the dense sum, builds green (`lake build Rel.Lang.EmitC Rel.Lang.TestNative`):
  - `Col.sum p tag x y` (no `l r idx`); `objLeaves`: `p.tag` then `p.l`, `p.r` leaves (no `p.idx`); `regsOf`/`withRegs`/`tysOf`.
  - `gatherCols` (now `partial`) gathers tag and both summand columns; `keysB` of a sum = tag key, keys of x, keys of y
    (all n rows, as `ValsB.cols`); `concatColB` joins tag and x, y as plain columns (`catSideB`/`catSummandB` deleted);
    `zeroCols`/`pairsOf` deleted (unused); `repath`, `noneB`, `colsOf` (tag register only), `flatB`, `packB`, `onesOf`
    (a summand `1` has the sum's n), `ownCountsB` (tag, then both summands at n) follow.
  - new `zerosB` = `Vals.zeros` (atom `nulsB n`; arr: n null lo/hi over no payload; band: `nulsB`; general sum: tag 0 over
    zeros); `injB` uses it: owned summand = X as is (`Vals.lift`), other = `zerosB n`.

## Build prerequisite (NOT committed)
`Rel.Lang.Table` imports `Rel.RepCols`, which fails (8.2h's files). In this worktree I left uncommitted: `Rel/Lang/Table.lean`
with `import Rel.RepCols` deleted and `frame_holds`' proof replaced by `sorry` (it uses `Arr.pos_get` from RepCols). Revert with
`git checkout Rel/Lang/Table.lean` once 8.2h's RepCols is in.

## Left
1. `Rel/Lang/EmitC.lean` CSV: `CsvCol.null tag idx vs` (csvCols, `csvSideB` ~l.1920-1950, csv write ~l.2030) still builds the sparse
   `idx` column and the non-null-only values; Lean's `Table.ofCsv`/`encVals` (Rel/Run/Table.lean ~l.450-466) now reads
   `ValsB.ofGen hb tag (lift x) (lift y)` with summands of the sum's n rows. Native must do the same (the compile gives no
   error for it because the register shapes are only paths; a test run will show it).
2. `Rel/Lang/TestNative.lean` `nativeIO` cases gm/gmi, gx/gxi, nd/nu, gy, gz, gw (not read, not changed) and the inputs
   `test/native/in/{gm,gmi,gx,gxi,nd,nu,gy,gz,gw}/*`: the old files hold `.idx` and sparse `.l`/`.r`; regenerate them from
   Lean's writer (`Plan.cols` -> `Db.Own`): `.tag`, then `.l`/`.r` columns of n rows, null-filled.
3. Lean-side caveat: `Table.readVals` (Rel/Run/Table.lean ~l.112-116) reads a general sum's `.l`/`.r` with `readVals` then
   `Vals.lift` ("every row owned; the ownership mask a file must carry is the later package"): its `readArr` refuses a column
   holding the null filler, so `relc run`/`relc lean` cannot read a dense sum file back. The gate's round trips for gm..gw
   fail until that reader reads `ValsB true` summands (`readOpt`, as band already does).
4. `/data/tmp/m82i-gate.sh` from `/data/tmp/m8c11-gate.sh` (set `W` to this worktree), run; the negative test (`gx/a.l`
   byte 11 part count) is about the old sparse `1` file and has to be re-derived or dropped.
