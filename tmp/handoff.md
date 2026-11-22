# 8.5s2e handoff (concat chain: thread `Tab.WF` / `Vals.WF` instead of the clamp)

Branch `worktree-agent-a690ca983804d79b2` = master de81c61 + merge of 6ba4b20 (8.5s2d) + WIP commits. Build one module
with `CAP_JOB=<name> CAP_MEM_MB=20000 /home/dh/repo/cc-guard/bin/cap lake -d <worktree> build <Mod>`; log
`/data/tmp/job/<name>.log`. This worktree has its own index (`<worktree>/.lake/build/refactor-index.db`, built after
the merge); `use_site` (columns `name, decl_module, use_module, l1, ..., parent, is_definition`) lists callers.

## Merge resolution (done)
- `Rel/RepWF.lean`: 6ba4b20's side (the base `_wf` lemmas live in RepStruct now).
- `Rel/RepStruct.lean`: master's B2/B8 applied there: `prod_wf` deleted; `compPairs_wf` added before `pair_wf`;
  `pair_wf` uses `compPairs_wf`; `compPairs_holds` takes `(hR : R.WF) (hS : S.WF)` after `h`; `pair_holds` passes them.

## Green
Everything through `Rel.RepWFOps` (log 85s2e-1), `Rel.Lang.GenKSpec` (log 85s2e-3).

## Done in GenKSpec (the rule: a `_sound` lemma gets its operands' WF from their `Rel.Wf`)
- `lift1_sound` takes `(wR : R.Wf)` after `hR`; `lift2_sound` `(wR wS)` after `hS`; their `hf` receives the operand
  tables' `WF` right after the `f … = .ok t` hypothesis (`r.WF`, then `s.WF`).
- New WF premises: `conv_sound`/`dom_sound`/`ran_sound`/`lam_sound (wR)`, `join_sound (wR wS)`, `diff_sound (wR wS)`
  (was `wR` only), `rdiv_sound (wR wS wA wB)` after `hB`, `top_sound (wV)` after `hV`;
  `idU_comp_holds (hX hr)`, `comp_idU_holds (hL hl)` after the comp hyp; `cut_agrees (hK hr)` before `h`;
  `cut_holds (hk hl hr)` after `h`; `bound_spec (hK hr)` before `h`. Atom-sided tables pass `trivial`/`⟨trivial,
  trivial⟩` (cmp_side, cmp_sound).
- `pairOn_wf` moved GenKBits → GenKSpec (before `pairOn_sound`); `pairK_sound` uses it for `pair_holds`.
- GenSound callers to update (all have `code_wf (gen_wf X η hs.2)` at hand, cf. `pair`): `conv` 1257, `join` 1261,
  `diff` 1263 (add wS), `dom` 1265, `ran` 1266, `rdiv` 1268 (4 Wf), `lam` 1283, `top` 1248.

## GenKBits: in progress (log 85s2e-7, remaining errors)
Done: `Tab.index_spec`/`Tab.index_le (hxr hv)` after `h`; `Tab.keepBits_law (hT wx wy)`, `Tab.compTabMat_law (hr wx)`
at the end; `Vals.code2_rep_inj (wx wy)` after `h`; `Tab.ldivTabMat_spec`/`_law (hr hub huc wx wy)` at the end;
`Tab.ldivTabMat_wf`/`Tab.ldivTabMat_reads (hrw hub huc wx wy)` at the end; `inter_law (wR wS)`;
`keep_law` takes the whole `Rel.Wf` of a `bits` value (`BitsWf ∧ Vals.WF x ∧ Vals.WF y`) and `hT : ∀ u, T = .ok u
→ u.WF`; `meetOn_sound` passes WF to `bound_spec`; `compR_sound (wr ws)` before `H`; `compV_sound (wr)` before `wS`.
Remaining errors (line: what):
- 1838, 1843: `compV_sound` `tab` branch: `compR_sound H s rfl` / `H s hs` need `wr` and `s`'s WF
  (`wS.runE Known.wf_empty hs`).
- 1887, 1896, 1899: callers of `compV_sound` need `wr` before `wS` (the `r` there comes from a `runE`, use
  `wR.runE … hr`).
- 1930: a `compR_sound`/`lift` caller whose `fun a c ha hc x` now needs the extra WF args.
- 2101/2102: `ldivSel_holds ht b` needs `(hR hS hUB hUC)` before `b` (the `ldiv_sound` body).
- 2109: `ldiv_sound`'s `lift2_sound` call needs `wR wS` after `hS`, and its `hf` gets `wr ws` after `ht`.
- 2139: `Tab.ldivTabMat_reads wF.left hm` needs `(hrw hub huc wx wy)`: x,y WF from the `bits` value's `Rel.Wf`
  (`wF.2.1`, `wF.2.2`), r/ub/uc WF from their `runE`.
Then the callers of `ldivTabMat_wf` (search `use_site`), `Rel.RepWhere` 108 (`Tab.index_spec` in
`positions_spec` needs `hxr hv`), `Rel.RepAsc` 74 (`lift1_sound` in `GenK.ofRel_sound` needs `wR`, hf gets `r.WF`).

## Not reached (from the 8.5s2d handoff, still open)
GenKFold (`peelL_holds hp`/`peelR_holds hp` need `hrest`; `arith_holds` needs `hD`; `snoc/cons/cat_holds` need
`hP`; `diag_holds` needs `hqw`), GenKFix, GenKHylo, GenKEst (`est_holds`/`thin_den` need `hqw`), GenSound
(callers above; `GenK.after_row_sound fun _ _ _ h => Tab.snoc_holds h` at ~620/624/628: its `hf` already receives
`D.WF` — pass it). Then the full gate, `make decode-allow panic-allow bang-allow`, PLAN.md 8.5 bullet, delete this file.
