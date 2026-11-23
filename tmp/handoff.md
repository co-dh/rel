nullband3g1 handoff (budget reached; tool calls ran out before the Lean downstream)

DONE and green (commit 2872d28 + the KernelSpec/Scan.lean commit after it):
- Rel/Kernel/Scan.lean: `kscan ... (es : List (USize × Enc))`; new `kscanStream op es pre post` (op = .first, no chain,
  more than one source => the sources are ONE stream, their rows must sum to n); new `kscanCols` (returns the folded
  columns and the first column's null flags); lock-step requires every source to hold n rows and no null (`noNul "kscan"`);
  a stream writes `nulMap` of the flags carried like the words (kscanRow .first). Imports Rel.Kernel.Scatter. Checked by
  `lean` with the worktree's built olean (Rel.Kernel.Scan built via cap lake build, exit 0).
- crate/src/scan.rs: `Col::Cat` (segments (start,end,col)), `has_nul`, `first_nul`, `nul_bits`, `kscan(.., es: &[(usize,B)], ..)`;
  tests `kscan_streams_its_sources` (nulls in neither/x/y/both, rev, seg) pass; `cargo test --features std` 83 passed;
  `sh crate/build.sh syms` exit 0 (9 + 4 disjoint). `unit` no longer has the `first` arm (first over two sources is a stream).
- crate/src/ffi/scan.rs: es is a list of pairs (boxed USize, Enc).
- Rel/KernelSpec/Scan.lean: new `mapM_pairs`, `kscanCols_lock`; `raw_kscanChain`, `raw_kscan`, `kscan_last` take
  `hs : kscanStream op es pre post = false` and es : List (USize × Enc); the file compiles with `lean`.

NOT DONE:
1. Rel/KernelSpec/Closure.lean `kscan_closed` (line ~239): es is now List (USize × Enc); add hypothesis
   `hN : ∀ p ∈ es, hasNul p.2 = false` and prove `hasNul r.1 = false`. The proof's splits changed like raw_kscanChain's
   (extra `split` for `kscanCols` giving `c cs' ns`, and one for `nl`, as in raw_kscanChain); the `nul` is
   `if ns.any (· != 0) then nulMap .. else .empty`; need `ns.any (· != 0) = false`: ns = #[] when no stream
   (`kscanCols_lock`), and in a stream the foldl of `foRNuls p.1 p.2`, all zero when `hasNul p.2 = false` — that needs
   a lemma without WF (`hasNul_flags` needs WF): `nulAt md b` is `128 ≤ widthByte md b`, check `widthByte` is 0 past nblk.
   Then `wordsFoR_closed`/`hasNul_wordsFoR` apply as today. The kscan answer is `Enc.foR (Coc.encode 8 .. nul)` = `wordsFoR ws nul`.
2. Rel/KernelSpec/KGather (4 uses of kscan / raw_kscan): migrate `es` ↦ `es.map (n, ·)` and add the `hs` hypothesis
   (op is concrete and not `.first`, or one source: `by decide`/`rfl` on `kscanStream`).
3. Rel/Kernel/ScanTest.lean: migrate every `decide`/`#guard` pair (`kscan ... [a, b]` ↦ `[(n, a), (n, b)]`; any `.first` with
   two sources is now a stream error unless the counts sum to n) and add pairs for the stream: nulls in first only, second
   only, both, neither (build the sources with `wordsFoR ws nul`, expect `wordsFoR ws' nul'` of the concatenation).
4. Rel/Lang/EmitC.lean `mapB` (line ~112) and Rel/Run/Lang/Plan.lean `scanB` (line ~595): each source in `listB` must be
   a pair `ctorB 0 #[nReg, srcReg] #[]` (a scalar register in an object field is boxed, see Plan.lean line 35); `n` is the
   same n register. Other callers of kscan (build error list will name them) — `lake build RelKernel RelRun Rel`.
5. Gates not run: `lake build RelKernel` (only Rel.Kernel.Scan was built), then `RelRun Rel`; list the red ones.
