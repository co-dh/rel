# nativetm4 handoff

Merge of nativetm3b (f20d4c1) and nativetm3a (e581d7d): σ is `Vars`, `ldivSelB`/`groupsB` on the `Col` tree.

WIP after the merge:
- `≫` follows `Tab.compSel` (`compSelB`: bit matrix when `bitsWin`, else `compFromB`); fixes the Λ mismatch of `lm`/`lu`
  (GenK's `compSelM` read back empty cells at the first code's lo/hi). `relc lean` = `relc plan` on every semOut.
- `cellsBoundB` guards `n·m + n + m < 2^63` in pack and mem.
- Open: `make native` OOMs in `cc1 -O2` (20 GB) on the 7.8 MB `rel-native.c`; `-O1` compiles at 3.9 GB. `compSelB`
  builds both forms at every `≫`; emit it once as a plan function (`defFun`/`apply`, as gfun) to shrink the C.
- Open: `cellsMapB` (row `F`) fails on `fm ≜ lm F(rt)` with 0 images (C.n = 0): the domain passed to `R` or the
  path of `v` does not meet `rt`'s key. `fm`, `hy` are in native1a but not in semOuts.
- Not started: est, thin, fold/foldr/foldI (foldRounds on Instr.loop).
