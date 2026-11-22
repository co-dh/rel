# lohi2 handoff (PLAN 8.5, branch `lohi2`)

Done (committed):
- `cellBad` (Rel/Run/Cols.lean), the one cell check `readVals` makes (Rel/Run/Table.lean arr case).
- Rel/RepCols.lean: `Vals.WF`, `Tab.WF`, `cellBad_none` (readVals establishes the cell clause),
  `Vals.gather_wf`, `Vals.catSide_wf`, `Vals.catSummand_wf`, `Vals.concat_wf`.
- Rel/RepTabDiv.lean: `Vals.cells_spec` (split out of `cells_row`), `Vals.cells_wf`.

Not done: removing any clamp. Removing one makes its `*_holds`/`*_row` law need `Vals.WF` of its input, and the
inputs of those laws come from every `Tab` a program computes: `rowOK_mem` (GenSound:254) reads `X` from
`K.dom` of an arbitrary `Known`, and `Rel.Reps` (Rel/Rep.lean:32) quantifies over every `K`. Transitive
dependents of `concat_row`/`mem_holds`/`pack_row`/`cellSpan_spec`/`cellSpan_where`: 183 theorems
(GenSound 41, RepTabDiv 35, GenKFold 26, GenKBits 22, GenKSpec 18, ...). The slot that exists: `Rel.Wf`
(GenKBits:425, `.tab _ => True`), threaded through gen_sound by `Code.Wf`/`Sound`, 91 `_wf` lemmas.
Route: `Rel.Wf (.tab (.ok t)) := Tab.WF t`, `Known.WF` (dom/ran/pairs WF), `Reps` asked only at `Known.WF` K;
each of the 91 `_wf` lemmas then proves its op keeps `Tab.WF` (gather/concat/cells lemmas above are the base).
