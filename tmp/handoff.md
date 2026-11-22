# 8.5s2 step 2 handoff

Done (commits on this branch):
- merge of c8da7c7 (lohi11), conflicts resolved by HEAD's side (Tm.E gone: GenSound `case E`, RepTabDiv `E_lam`/`E_holds`/`E_den`).
- `Rel/Run/Cols.lean` `Vals.concat` arr side: `lo₁`/`hi₁` as is, `lo₂`/`hi₂` via new `Arr.shift m₁` (no clamp).
  `Rel/RepCols.lean` (builds green): new `Arr.shift_get`; `concat_wf` arr arm reworked; `concat_row` takes
  `Vals.WF x → Vals.WF y`; `catSummand_row` moved after `catSide_wf`, its `hcat` takes both sides' WF, it takes `hx₁ hx₂`.
- First caller layer, statements changed (WIP, not yet green):
  `Vals.code2_spec` (RepBits) takes `hx : Vals.WF x` `hy : Vals.WF y`;
  `Tab.concat_holds`, `Tab.concat_split` (RepSetOps) take `hR : R.WF` `hS : S.WF`.
  RepSetOps #guard at line 965: cell `(0, 2, 1)` (lo > hi, non-WF) changed to `(0, 1, 1)`; unverified.

Failing now (`lake build Rel.RepBits Rel.RepSetOps`, RepBits green):
- RepSetOps.lean:269 `union_holds`: `concat_holds hc` needs `hR hS` -> `union_holds` takes `R.WF`, `S.WF`.
- RepSetOps.lean:729, 807, 809: `hsplit w.1 w.2` / projections: `concat_split` now takes `hR hS` before `{a b}`.
- RepSetOps.lean:787: `concat_holds hcat a b` needs `hR hS`.

Left:
- Remaining callers of `Vals.concat_row`: `Tab.compOne_canon` (RepTabComp:789), `Tab.ldivOf_holds` (RepTabDiv:1521),
  `Tab.lamOf_canon` (RepTabDiv:2253), `Vals.cat_row` (RepTabDiv:715); callers of `code2_spec`: `compBits_holds`,
  `ldivBits_holds`, `code2_rep_inj`, `ldivTabMat_spec`, `index_spec`; then their transitive callers. Index count of
  `concat_row`'s transitive dependents: GenSound 42, GenKFold 24, GenKBits 22, GenKSpec 18, RepTabDiv 17, RepWFOps 12,
  RepSetOps 9, RepWF 8, RepBits 8, RepTabComp 7, others ~15.
- `cellSpan` (Rel/Run/List.lean:21): replace by `(lo, hi)` in pack/cat/zip/uncons/unsnoc/uncat/sumOn (List),
  Tab.map (Fix), length/atPos (Power), positions (Where); laws `cellSpan_spec`/`_where`/`_start_le`/`_width` (RepTabDiv)
  take `Vals.WF`. Transitive dependents: GenSound 63, RepWF 24, RepTabDiv 21, GenKFold 20, RepWFOps 15 ...
- PLAN.md line ~1205 bullet.
