# nullband3d handoff

Branch worktree-agent-ab63c0377eb407510, tip after this commit. Base: master 6592182 + merge of b4635dd (nullband chain).

## Done (green, committed)
- RepCanon: `asc_col_row` uses `raw_wordsFoR_of_bit` (local `hraw` gone); new `Opt.get_ofArr` (after `Opt.isNul_eq_false`).
- RepOrder: `Opt.lt_of_codes` (band case, `1+t` key order, null least); `Arr.lt_of_codes` is its no-null case
  through `Opt.ofArr`; `Vals.lt_of_codes` `.sum` branch through `s.view` (band case rewrites `Obj.optEl` to
  `Option.elim` by a local `e`).
- RepCols: new `Opt.concat_get` (after `Arr.concat_get`); `Vals.cellsOk_wf`, `Vals.concat_wf`, `Vals.concat_row`
  `.sum` branches through `s₁.view`/`s₂.view` (opt×gen cases absurd by `hb₁.symm.trans hb₂`). In `concat_row` the
  view hyps are `hs₁ hs₂` because `hv₁ hv₂` are taken by `Arr.concat_valid`.

## Left
Build: `CAP_JOB=nb3d CAP_MEM_MB=20000 /home/dh/repo/cc-guard/bin/cap lake -d <wt> build Rel.RepStruct Rel.RepWF Rel.Lang.GenKBits`
(RepWF and GenKBits not yet reached; they import RepStruct or are blocked behind it).

Rel/RepStruct.lean errors (first build after RepCols green):
- 44:18 `Vals.none_wf` `.sum`: `Vals.none` now `match h : Obj.band a b with | some t => ofOpt h (Opt.ofArr (← Arr.zeros t 0)) | none => ofGen …`;
  "Dependent elimination failed: Failed to solve equation Except.ok x = match Arr.zeros t 0 with …". Split on the band
  match first, opt case WF is `True` (`simp only [Vals.WF, Vals.view_ofOpt]`), gen case as before + `Vals.view_ofGen`.
- 48:19 same proof.
- 159-168 `inl_wf` / `inr_wf`: `⟨hX, hX, Vals.none_wf _⟩` no longer fits; val's WF is `match view` — split on band in
  `Tab.inl`/`Tab.inr` (Run/Struct.lean), opt case `True`.
- 430/448 `inl_holds` / `inr_holds`: `Tab.inl` band case is `canon ⟨n, X, Vals.ofOpt h (← Opt.nuls t n)⟩`; needs a
  lemma that every row of `Opt.nuls t n` is `none` (`Opt.ofAtoms` of all-`none`: every row flagged), and `Tab.inr`
  band case `Vals.optInr h Y` rows are `inr (Y.row k)` (`Opt.get_ofArr` after `Obj.band_some`).
- 465/520 `inlConv_holds` / `inrConv_holds`: `obtain ⟨l, r, tag, idx, x, y⟩ := X` → `rcases hv : X.view`; the opt
  case: `Tab.inlConv` throws on `.opt`, so `h` is an error = ok, `cases h`.
