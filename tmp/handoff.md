# 8.2h3j handoff

Worktree agent-a0205ef7e6ef73c50 (branch worktree-agent-a0205ef7e6ef73c50), base 386a52e + merge keep-82h3i (64e3058).

## Done
- fa9b0e5 kernel: `ascCol .cells` reads a row whose `lo` or `hi` is null as the empty cell
  (`cellFns c (nulWords n lo l) (nulWords n lo (nulWords n hi h))`), same in `Verify.ascKey`, Rust `Cells::span`
  (`Ix::nul` = `Coc::is_nul`, no decode) and `ffi/asc.rs` (no `no_nul` on lo/hi). AscTest lo/hi pins re-pinned to
  the sorted answers. `crate/build.sh syms` green; Rel.Kernel.Asc, Rel.KernelSpec.Asc, Rel.Kernel.AscTest green.
- RepCanon (uncommitted at writing): `ColB.get_i64`, `ValsB.cell_le`, `ValsB.row_arr` take a per-row null flag;
  new `ColB.flag_of_owned`, `ColB.flag_of_unowned`, `nulWords_get`, `nulWords_nul`, `seenKey_cells`,
  `cellFns_congr`, `seenKey_cells_raw`; `cols_arr` returns per-row flags from `WFOn`; `codes_of_unowned` arr case:
  both rows unowned, `lo` null, length 0, equal codes. Removed `ColB.owned_of_flat`, `Verify.ascCol_cells_flags`,
  `noNul_flags`. Callers fixed in RepOrder, GenSound, RepTabDiv.
- Quicksort, TestHylo, Test/Arith built green in the first run.

## Left
- Build `Rel.RepCanon Rel.RepOrder Rel.RepTabDiv Rel.Lang.GenSound` (job h82h3j-t2) green, then commit.
