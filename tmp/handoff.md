nullband3h4 handoff (tool budget reached)

Branch worktree-agent-a1c248448af4d8d5e. GREEN commits: 0606ff2 (merges of 15b73ae, nullband-int, 8b84e97 + kscanCols_lock /
raw_kscanChain generalised, nullOps lists .null; `lake build RelKernel RelRun` green), bf55cb0 (Tab.inrConvBand + inrConv
`.opt` branch + 4 #guards, built green as Rel.Run.Struct).

Step 1 conflict resolution: Rel/Kernel/ScanTest.lean had two `knul`; 3h3's is now `kflag` (sources as `(n, e)` pairs).
Step 3 law, done: `raw_kscanChain` no longer takes `hnl`; its columns clause reads
`∃ e₀ es₀ ws', es.map (·.2) = e₀ :: es₀ ∧ mapM … = .ok ws' ∧ c' :: cs' = if op = .null then foRNuls n e₀ :: ws'.drop 1 else ws'`.
`kscanCols_lock` likewise (`ws = fl.map foRNuls ++ ws'.drop fl.length`). `raw_kscan` keeps `hnl`; `kscan_last` dropped it.

Step 2: `Tab.inrConvBand h x` (Rel/Run/Struct.lean) = kscan .null false t .u1 n none [(n, x.enc)] [] [(.not,0)] -> whereCol ->
Vals.gather m sel (Vals.ofOpt h x), Arr.of t m (Opt.gather m sel x).enc. `inrConv`'s `.opt h x` branch calls it.

NOT DONE (module Rel.RepWF, Rel.RepStruct; nothing there is built, RepStruct's `.opt` branch of inrConv_holds still says `cases h`,
which no longer closes):
1. `inrConv_wf` (Rel/RepWF.lean, first bullet): proof written, UNBUILT. Shape: unfold Tab.inrConvBand at h; obtain ⟨rfl, rfl⟩ :=
   Obj.band_some hb; simp only [bind, Except.bind, pure, Except.pure, cast_eq, eq_mpr_eq_cast] at h; split off the 5 binds; then
   ⟨Vals.gather_wf _ (WF of a band side is True), trivial⟩ (Vals.WF of an atom/band side is True, RepCanon ~443).
2. `inrConv_holds` `.opt` branch (Rel/RepStruct.lean ~606). Plan, all lemmas exist:
   - kscan: `raw_kscanChain .null false t .u1 w n none [(n,x.enc)] [] [(.not,0)]` (w from `QAtomicType.u1.width`); `segAll n none`
     gives all-ones marks, so out₀[i] = (foRNuls n x.enc)[i]; chainAll_ok gives out[i] = out₀[i] ^^^ 1; raw word = that % 2.
     Flags are 0/1 (`foRNuls_bit`, RepCanon ~311), so word ≠ 0 ⟺ flag = 0 ⟺ `Opt.isNul x i = false` (`Opt.isNul_eq_false`, RepCanon 62).
   - whereCol: `whereCol_spec` (RepSetOps 34) needs `∀ i < n, word < 2` (same fact) and lists the kept positions ascending.
   - key side: `Vals.gather_row` (RepCanon) gives G.row j = X.row sel[j]; value side: `Opt.gather_row` (RepCanon ~330) gives
     y.get j = x.get sel[j]; `Arr.of` success gives a.enc = y.enc, so y = Opt.ofArr a and `Opt.get_ofArr` gives y.get j = some (a.get j).
   - the `keep_holds` proof (RepSetOps 194) is the template for the (→)/(←) split via `whereCol_spec` membership.
   - X.row i = Obj.optEl hb (x.get i) (`Vals.row`, `Vals.view_ofOpt`); `Core.Rel.inr b s` unfolds as in `inr_holds`/`holds_inr_of_row`.
   - Enc.Valid n x.enc: from `kgather_valid` on the successful `Opt.gather`.
Index note: /home/dh/repo/rel/.lake/build/refactor-index.db is older than this worktree (line numbers and new decls differ); read files by awk NR.
