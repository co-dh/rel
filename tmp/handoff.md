# 8.5s2f handoff (thread `Tab.WF` / `Vals.WF` instead of the clamp)

Branch `worktree-agent-abc2762303a655130` = master 035657b + merge of da1e639 (8.5s2e) + WIP commits. Build one
module with `CAP_JOB=<name> CAP_MEM_MB=20000 /home/dh/repo/cc-guard/bin/cap lake -d <worktree> build <Mod>`; log
`/data/tmp/job/<name>.log`. Signatures of the changed `_holds`/`_wf` lemmas: read the error text (`has type r.WF → …`)
or the source; the main index is stale for every lemma 8.5s2d/e touched.

## Green
Everything through `Rel.Lang.GenKBits` (log 85s2f-2 → clean in 85s2f-3).

## Done in 8.5s2f
- GenKBits: `compV_sound` tab/lazy branches; `compT_sound` passes `(wr r rfl)`; `compS_sound` takes `(wR : R.Wf)`
  last (callers in `comp_sound` pass `wR`); `ldiv_sound` takes `(wR wS wB wC)` (order of `ldiv_wf`) — its GenSound
  caller must pass all four; `ldivSel_holds`/`ldivTabMat_law`/`_reads`/`_wf` get their WF args.
- RepAsc: `GenK.ofRel_sound` takes `(wR : R.Wf)` after `hR`; GenSound 808/830 pass `(hw _ (List.mem_singleton_self _))`
  (those two lines are now > 120 chars: wrap).
- GenKFold, the fold engine: `Tab.foldRounds_holds` lost its abstract `Wt` and `hpackw`; it is stated over `Tab.WF`
  (`hpeel` gets `rest.WF →`, `hpeelw`/`hstepw` over `Tab.WF`, conclusion takes `rest.WF → P.WF → out.WF →`).
  `foldRoundsL_holds`/`foldRoundsR_holds` lost `Wt`, `hpeelw`, `hpackw` (they supply `Tab.peelL_wf`/`peelR_wf`);
  callers drop those three args and pass `out.WF` after `P.WF`. `fold_sound`/`foldr_sound` done (`Tab.zero_wf hz`).
- `elemsTest_sound` takes `(wR : R.Wf)` last; its `hf` gets `P.WF → Vals.WF X →` after `f P X = .ok t`;
  `filter_sound`/`takewhile_sound` take `(wR : R.Wf)` after `hR` and pass `fun h _ _ xs ys => …`.

## Open (log 85s2f-5: 77 GenKFold errors, by line)
The rule every remaining error follows: a binary `Tab.*_holds h` takes its two operands' `WF` right after `h`
(`Tab.comp_holds hc wl wr k c`, `Tab.pair_holds hp wl wr a q`, `inter/union/diff_holds`), the WF from the op's `_wf`.
- Fixed in 85s2f-5: `arith_sound`, `pairStep_holds`, `foldI_sound`'s step and `z.WF`.
- 424 `foldI_sound`: `Tab.pair_holds hP k q` needs `wi` and the `comp_wf hc1 …` WF. 426: `Tab.comp_holds h p v`
  needs `out.WF` and `o2.WF`; `out` is the `foldRounds` result (`hout`), so its WF is `Tab.foldRounds_wf`
  (RepWFOps) with the same step proof as the `hstepw` lambda at 396 — bind that proof once (or let
  `foldRounds_holds` also conclude `res.WF`, which it can from its own `hpeelw`/`hstepw`) instead of copying it.
- 487/497, 516–534 `Tab.loop_holds`: the `foldRoundsL_holds` call (510) drops removed args, passes `out.WF`;
  `peelL_holds`/`peelR_holds` need `hrest`.
- 576/661/897/1053 `filter_holds`/`takewhile_holds`/`mapFold_holds`/`flatten_holds`: they instantiated
  `Wt := fun _ => True`; now they need real WF: add `(wP : P.WF) (wX : Vals.WF X)` (as `elemsTest_sound`'s `hf`
  now supplies), delete the `(fun {_ _} _ => True) (fun _ _ _ _ => ⟨trivial, trivial⟩) (fun _ _ _ _ => trivial)`
  args, give `hstepw` the step's `_wf` and the initial `rest/P0/z` their `_wf`. Their callers: `filter_sound`,
  `takewhile_sound` (pass `h wP wX`), `RepWFOps` unaffected.
- 787/817 (`Tab.comp_holds hC _ _` needs WF args; a `_canon` lemma whose hypothesis gained `.WF →`).
- 989, 1076/1084/1092 (`snoc/cons/cat_holds` need `hP`), 1147–1349 `merge_holds` (`diag_holds` needs `hqw`),
  1361–1500 `thinL_holds`.
- RepWhere `positions_spec` (line 42): add `(wP : P.WF) (wX : Vals.WF X)` after `h`, conclusion `∧ res.WF`;
  108: `Tab.index_spec hia (Tab.dom_wf hD wP).1 (Vals.gather_wf hv wX.2) ⟨t, ht⟩` (check `index`'s `xr` is `D.key`);
  callers RepWhere 220 (`positions_sound` → `elemsTest_sound … (fun h wP wX xs ys => (positions_spec h wP wX).1 xs ys)`,
  gets `(wR : R.Wf)`), GenSound 778 (`elems_wf` hook: `fun _ _ _ h wP hX => (positions_spec h wP hX).2`).
- Then GenKEst (`est_holds`/`thin_den` need `hqw`), GenKFix, GenKHylo, GenSound (callers 1248, 1257, 1261, 1263,
  1265, 1266, 1268, 1283 pass `code_wf (gen_wf X η hs.2)` as `pair` does; `ldiv`, `filter`, `takewhile`,
  `positions` rows pass `hw _ (List.mem_singleton_self _)`; `after_row_sound` hooks at ~620/624/628 pass the `D.WF`
  their `hf` receives).
- Then the full gate, `make -C <worktree> decode-allow panic-allow bang-allow`, PLAN.md 8.5 bullet, delete this file.
