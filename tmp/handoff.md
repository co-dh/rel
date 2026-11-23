nullband3g9 handoff

Done: merged 66c394c and e5b16d6 (only tmp/handoff.md conflicted); every proof module of `Rel` builds
(RepBits, RepTabDiv, RepWF, RepTabComp, RepStruct, GenKBits, TestNullband).

Left (not done): 11 test modules still fail at their `#guard ...failures == []` / `.ok`:
TestFrameSchema, TestGenericN(108,109), Test/Kern9(87,89), TestFrameCols(68,84), TestFrameScale(53), TestPivotDisk(137),
TestFrameApp(101,149), TestFrameQuery(65,82), TestFrameStat(122,158), TestFrameUnbounded(189,203), TestFrameBench(58).

Diagnosed for Kern9 (copy to Rel/Lang/Test/K9tmp.lean, replace `#guard kernT9.ok` by `#eval kernT9.failures`, run
`lake -d <wt> lean Rel/Lang/Test/K9tmp.lean`): every failure of `sub`, `leaf`, `ch`, `dbl` reads
  inr°: on a 1+t band column, whose values the law cannot yet read (Vals.WF carries no Enc.Valid); run the other
  operand first: a leaf on demand ran with its domain unknown
raised by `inrConv`, `.opt ..` arm, Rel/Run/Struct.lean:164 ("PLAN nullband3h"): a deliberate throw from line 3g8, not
a concat-null error. TestFrameApp:149 prints the same text. The other 9 modules were not inspected (do the same eval
with their failing program: frameSchemaT, paramNT, paramPT, frameDescribe, tradeApp, frameStatT, frameStatFloatT,
query3, query4, frameUnboundedT, frameDescribeU, bench2, frameCols, frameScaleN3, pivotT).

Not done: step 3 (TestGenericN 118 / TestPivotDisk 143 #guard_msgs at base), final build RelCore RelKernel RelRun.

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

DONE (nullband3h5): inrConv_wf and inrConv_holds (.opt branch) proved; inrConvBand casts by two Eq (a rfl cast unfolds to the body).
colMap_*/kscan_post_ok/colMap_ok/raw_kscan_rev/ordOp_ne/floatOps_ne take or give op ≠ .null. lake build Rel and RelCore RelKernel RelRun green.

