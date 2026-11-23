nullband3a handoff (see PLAN.md, nullband3a entry under nullband3).

Done (green with `cap lake build Rel.Run.Table Rel.Run.Lang.Plan`, plus Core/Gather/Cols/Canon/List/Struct):
- Rel/Run/Core.lean: `Obj.band`, `Obj.band_some`, `Obj.optEl`, `Obj.optOf`, `SumCols`, `Vals` sum branch,
  `SumV`, `Vals.view` (via `go` generalising `Obj.band a b`), `Vals.ofOpt`, `Vals.ofGen`, `SumV.vals`; `row`, `rowsImpl`.
- Gather `Vals.gather`; Cols `cellsOk`, `Opt.concat`, `concat`; Canon `cols`; List `pack`; Struct `none`, `Vals.optInl`,
  `Opt.nuls`, `inl`, `inr`, `inlConv`, `inrConv`; Table `readOpt`, `readArr`, `readVals`, `encVals`, `checkSyms`;
  Lang/Plan `SideCol` (now `Opt`), `cols`.

Pattern for every remaining `.sum` match: `| .sum _ _, _, s => match s.view with | .opt h x => … | .gen h l r tag idx x y => …`,
build back with `Vals.ofOpt h` / `Vals.ofGen h …`; where the band case comes from the type, `match h : Obj.band A B with`
(inside `Vals.none` write `.none`, `none` is the function itself).

First failure: Rel/Run/Lang/Gen.lean:53:3 `sumV` builds `⟨l, r, tag.1, idx.1, x.1, y.1⟩` (Invalid ⟨...⟩ notation: expected
type `match A.band B with …` is not an inductive type). Needs `optV` emitted by the code generator for a band side.
Then build the rest of Rel.Run.* and RelRun, then TestNullband round trips, CSV 3 → 1 (`csvEncs`).
Blocked on a kernel (explicit errors now): `Opt.concat` with a null on either side; `inl°`/`inr°` on a band column.
