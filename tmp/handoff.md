# 8.5s2c handoff (concat chain: thread `Tab.WF` / `Vals.WF` instead of the clamp)

Branch `worktree-agent-a548a38c7a7771465` (contains afaa894 and lohi11). Build per module with
`CAP_JOB=<name> CAP_MEM_MB=20000 /home/dh/repo/cc-guard/bin/cap lake -d <worktree> build <Mod>`; the log is
`/data/tmp/job/<name>.log` (cap writes nothing to stdout).

## Green
- `Rel.RepCols`, `Rel.RepSetOps`, `Rel.RepTabComp` build (all `#guard`s pass).
- RepSetOps: `concat_holds`, `concat_split`, `union_holds`, `select_ok`, `inter_holds`, `inter_sorted`,
  `diff_holds`, `diff_sorted`, `le_holds` take `(hR : R.WF) (hS : S.WF)` right after `h`.
  `#guard` cell at the old line 965 is `(0, 0, 1)` (payload of no rows, so only the empty cell is WF).
- RepTabComp: `compOne_canon`, `compBlock_holds`, `compBlocks_canon`, `compFrom_canon`, `comp_canon`, `comp_holds`
  take `hR hS`; `foldlM_union` takes `(hf : ∀ j X, f j = .ok X → X.WF)` and `acc.WF` after `h`.
  Arr `#guard`s near the end: cells made WF (`(-4,2,9)`→`(0,2,9)`, `(3,1,2)`→`(0,0,2)` over `[]`, the 4-row payload
  under `arrCells` got a fifth cell `(3,4,5)` since `arrCells` reaches `hi = 5`).
- Moved up (DRY: an op's `_wf` beside its `_holds`, so a `_holds` that needs an intermediate table's WF can get it):
  `okSplit` macro (now a plain `macro` in RepSetOps, the `local` one in RepWF deleted), `Tab.keep_wf`,
  `Tab.concat_wf`, `Tab.union_wf` → RepSetOps; `Tab.compExpand_wf`, `Tab.compOne_wf`, `Tab.compBlock_wf` →
  RepTabComp (before `foldlM_union`). Deleted from RepWF.

## Edited, not yet built
- RepBits: `compBits_holds` takes `hR hS` (code2 of `R.val`, `S.key`: `hR.2 hS.1`); `ldivBits_holds` takes
  `hR hS hUB hUC` (code2 pairs guessed as `(R.key,S.key)`, `(R.val,UB.key)`, `(S.val,UC.key)` → check the three
  `Vals.code2_spec … hX hY` lines against `Tab.ldivBits`' code2 arguments); `compBits_comp`, `ldivBits_ldiv`,
  `ldivSel_holdsBy`, `ldivSel_holds` take the same WF args; `compSel_holds` passes `hR hS` to `compFrom_canon`.
- RepStruct: `pair_holds` takes `hR hS` (the table `⟨R.n, (R.key, R.val), R.key⟩` is WF by `⟨⟨hR.1, hR.2⟩, hR.1⟩`).

## Failing (`lake build Rel.RepTabComp Rel.RepBits`, log `/data/tmp/job/85s2c-b4.log`)
- RepStruct.lean:186-195 `flat_holds`: `comp_holds h`, `inter_holds hJ`, `comp_holds hL`, `comp_holds hM` need the
  WF of `X`'s outl/outr/conv tables and of `R`. The `_wf` lemmas it needs (`outl_wf`, `outr_wf`, `conv_wf`,
  `inter_wf` → `select_wf` → `tagged_wf`) are in RepWF (RepWF.lean:93-129 now), DOWNSTREAM of RepStruct.
- RepStruct.lean:301-309 `inlConv_holds`, 354-362 `inrConv_holds`: `diff_holds hM`, `comp_holds hE` need WF.
- RepTabArith.lean:213-245 `Tab.succ_holds`, 471-499 `Tab.arith_holds`: `comp_holds`/`union_holds`/… need WF.
- Not reached yet: RepTabDiv (`Vals.cat_row` ~715, `ldivOf_holds` ~1521, `lamOf_canon` ~2253, `union_nodup`,
  `diag_holds`), RepWFOps (`mu_holds`, `star_holds`, `est_holds`, `thin_den`), GenKBits (`index_spec`,
  `code2_rep_inj`, `ldivTabMat_spec`, `inter_law`, `compR_sound`), GenKFold (`foldRounds_holds`, `filter_holds`,
  `takewhile_holds`, `merge_holds`, `thinL_holds`, `foldI_sound`), GenKFix (`nu_sound`, `inter_distinct`),
  GenKSpec (`join_sound`, `diff_sound`, `rdiv_sound`), GenKHylo (`hylo_sound`), GenSound.

## Recommended next step (the general fix, not per-lemma moves)
RepWF.lean:1-137 (`foldlM_keeps`, `dom_wf`, `ran_wf`, `idU_wf`, `conv_wf`, `outl_wf`, `outr_wf`, `tagged_wf`,
`select_wf`, `inter_wf`, `diff_wf`, `diag_wf`, …) and `ofBits_wf`, `cross_wf`, `prod_wf`, `inl_wf`, `inr_wf` use only
RepCols lemmas and the `Run` definitions. Move every op-level `_wf` that does not use a `_holds`/`_canon` lemma into
the module of that op's `_holds` (or into one module imported right after RepCols, before RepSetOps), so each
`_holds` that composes ops can discharge its intermediate tables' WF locally. Then thread `hR hS` up as done here.
Top-level callers have WF from `K.WF` / `Rel.Wf` and the GenK `_wf` lemmas (GenKBits/GenSound).
Then: PLAN.md 8.5 bullet; delete this file before the final commit; `cellSpan` is a later item, not this one.
