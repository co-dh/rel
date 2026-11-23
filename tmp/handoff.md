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
