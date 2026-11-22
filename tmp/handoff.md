# 8.5s2d handoff (concat chain: thread `Tab.WF` / `Vals.WF` instead of the clamp)

Branch `worktree-agent-a071d373f81f7d312` = master a549fae + merge of 195bc94 (8.5s2c) + WIP commits. Build per
module with `CAP_JOB=<name> CAP_MEM_MB=20000 /home/dh/repo/cc-guard/bin/cap lake -d <worktree> build <Mod>`, then
`cap -w <name>`; the log is `/data/tmp/job/<name>.log`.

## Green (build)
`Rel.RepCols`, `Rel.RepSetOps`, `Rel.RepTabComp`, `Rel.RepStruct`, `Rel.RepTabArith`, `Rel.RepTabDiv`, `Rel.RepBits`,
`Rel.RepWF` (log `/data/tmp/job/85s2d-7.log`).

## Done in 8.5s2d (the rule: an op's `_wf` sits beside its `_holds`, so a `_holds` gets intermediate WF locally)
- Moved `foldlM_keeps`, `compBlocks_wf`, `compFrom_wf`, `comp_wf` RepStruct → RepTabComp (after `compBlock_wf`).
- Moved `Tab.uncons_wf`, `Tab.unsnoc_wf` RepWF → RepTabDiv (before `uncons_holds`); `Tab.mem_wf` RepWF → RepTabDiv
  (before `mem_canonical`).
- New `Vals.cat_lt` (RepTabDiv, before `Vals.cat_row`): `cat`'s `n < 2^63` guard without WF; `snoc_wf`/`cons_wf` use it.
- WF hypotheses added (all right after `h` unless noted):
  `Tab.succ_holds (hD : D.WF)`, `Tab.arith_holds (hD : D.WF)` (U's tables are atom-sided, so `⟨trivial, trivial⟩`);
  `Vals.cat_row (hX hY)`; `cat_holds`/`snoc_holds`/`cons_holds (hP : P.WF)`;
  `peel_holds (hrest huw hw₁ hw₂)` after `hr`; `peelL_holds`/`peelR_holds (hrest : rest.WF)`;
  `Tab.ldivOf_holds (hrw hsw hUB hUC)`; `Tab.ldiv_holds (hRw hSw hUB hUC)`; `Tab.rdiv_holds (hRw hSw hUA hUB)`;
  `lamOf_canon (wD : Vals.WF D) (wr : r.WF)` (its `r.n ≠ 0 → Vals.WF D → r.WF → U.WF` clause kept as is; now
  redundant premises, can be simplified to `r.n ≠ 0 → U.WF` with `lamOf_wf` updated);
  `lamOf_holds`/`lamOf_den (wD : Vals.WF D) (wr : r.WF)`; `lam_den (wD wR)`; `tau_den (wX)` before `a`;
  `setify_den` passes `mem_wf hG hw`; `diag_holds (hqw : ∀ D t, q D = .ok t → D.WF → t.WF)` after `hq`.
- RepBits `ldivBits_holds` code2 pairings fixed: `(R.val, UB.val)` = `hR.2 hUB.2`, `(S.val, UC.val)` = `hS.2 hUC.2`.

## Failing: `Rel.RepWFOps` (log `/data/tmp/job/85s2d-7.log`)
Errors at 159:64, 173:31, 179:90, 183:4, 191:40 (`est_holds`, 155–206); 214:89, 230:31, 232:90, 233:53, 238:16,
243:65, 244:8, 249:30 (`thin_den`, 211–); 411:87, 462:88, 474:96 (`mu_holds`/`star_holds` area). All are callers of
`_holds` that now take WF:
- `est_holds`/`thin_den`: `pair_holds hP` needs `(mem_wf hG hX) (mem_wf hG hX)`; `diff_holds hY`/`hY1`/`h` need both
  operands' WF (`ran_wf`, `diff_wf`, `pair_wf`, outl/outr_wf, `comp_wf`); `comp_holds hPO`/`hWD` likewise. The
  outputs of `q` need WF: add `(hqw : ∀ D t, q D = .ok t → D.WF → t.WF)` (as `diag_holds`, `diag_wf`), and pass it to
  `diag_holds hq hqw …`. `lam_den h` → `lam_den h wD wR`.
- RepWFOps 233 caller of `diag_holds`, GenKFold 1271/1449/1460 callers of `diag_holds` need `hqw`.

## Not reached
GenKBits, GenKFold (`peelL_holds hp`/`peelR_holds hp` at 236/275 need `hrest`; `arith_holds` 295 needs `hD`;
`snoc_holds`/`cons_holds`/`cat_holds` at 595/682/904/1059/1162/1295/1296/1479/1486 need `hP`), GenKFix, GenKSpec
(`ldivOf_holds` 463 needs 4 WF; `succ_holds` 486 needs `hD`), GenKHylo, GenSound (620/624/628: `GenK.after_row_sound
fun _ _ _ h => Tab.snoc_holds h` — the row-sound hook must pass the WF it has, cf. `GenK.after_wf`).
Then the full gate, PLAN.md 8.5 bullet, delete this file.
