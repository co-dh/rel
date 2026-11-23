# nullmaxmin handoff

Done (Lean, committed on branch worktree-agent-a74fe196a4a85486e):
- `Op.nulFold` (Rel/Kernel/Op.lean); `nulFillOf`, `fillNul`, `kscanCols` returning `List (Array UInt64)` flags, `kscan` folds
  flags with `nulFold`'s and/or (Rel/Kernel/Scan.lean).
- Lemmas take `hF : op.nulFold = none ∨ ∀ p ∈ es, hasNul p.2 = false` (`nulFillOf_none`, `kscanCols_lock`, `raw_kscanChain`,
  `raw_kscan`, `kscan_last`, `kscanCols_nul`, `kscan_closed`, `kscan_lock_closed`); autoParam tactic `nulfree` (Closure.lean);
  `colMap_closed/plain`, `colArr`, `scanArr`, `colMap_chain/get/raw/const_eq`, `colPrefix_*`, runScan*/groupFold_plain (hF last,
  `:= by rfl` for lemmas whose op is a generic non-min/max op).
- `Rel.Run.Arith` checks in-band-null-free operands at runtime for max/min and refuses an op with a null order in fstepArr/fmapCols.
- Green: Rel.Kernel.Scan, Rel.KernelSpec.Scan, Rel.KernelSpec.Closure, Rel.Run.*, Rel.RepCols, Rel.RepTabDiv, Rel.RepSetOps.

Left:
1. Rel/RepTabComp.lean errors (first: line 429:25 `could not synthesize default value for parameter 'hF'`, `Op.max.nulFold`
   is not definitionally equal to `none`; also 518:60, 571:39, 586:70 `colMap_plain ... hu` needs hF). These are real `.max`
   users (groupFold_plain / colMap_plain at `.max`/`.sub`): discharge with `Or.inr` from the plain (`Arr`) sources, or pass
   `(hF := Or.inr ...)`. `colMap_plain`/`colMap_closed` callers at concrete ops need `Or.inl rfl` as 5th arg when passed
   positionally. Then rebuild `Rel.Lang.GenKBits` and the rest up to `RelRun Rel` (more callers will surface the same way).
2. Rust crate/src/scan.rs: skip `first_nul` for ops 5/6; `Col::load` variant overwriting flagged words with identity after
   `chain(pre)` at `Scan::fold` (~447/452/460); `nul_bits` -> and/or flag fold; `summary` for ops 5/6 returns None when
   `meta.nul(b)`. Then `sh crate/build.sh syms`, `cargo test --lib`, Rust test beside `kscan_streams_its_sources`.
3. Guards in the kernel kscan test module: max(0N,5)=5, min(0N,5)=0N, max(0N,0N)=0N, one column-vs-column with nulls both sides.
4. Update the `kscan` doc comment (Rel/Kernel/Scan.lean ~267-290) "every other call refuses a null source row" for min/max.
