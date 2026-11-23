nullband3b handoff (PLAN.md: nullband3b entry under nullband3). Rel.RepCanon does NOT build yet.

Done:
- merged nullband3a2 (00c486d); conflicts: doc/dataframe-design.zh.pdf recompiled; Rel/Programs/FrameJoin.lean
  resolved at `1+δ` (`pivotCol : κ ⟶ 1+δ`, `pivotWide` over `pivotOn`, `dummy` comment: `inr` = match, `inl` = rest);
  line 20 comment now `x × (𝟙 ⊕ y)`.
- RepCanon: `Vals.view_go_cast`, `@[simp] Vals.view_ofOpt`, `@[simp] Vals.view_ofGen` (before `Vals.gather_row`):
  a producer's `(Vals.ofGen …).view` reduces to `.gen …`. The rule for every proof: `rcases hv : s.view with
  ⟨hb, x⟩ | ⟨hb, l, r, tag, idx, x, y⟩ <;> simp only [hv] at h` (use simp, not rw: rw leaves the match unreduced and
  every later `split` count is off by one).
- Converted and compiling: `Vals.WF` (opt ↦ True), `Vals.gather_wf`, `Vals.cols_sum` (now takes `s` and
  `hv : s.view = .gen hb l r tag idx x y`), `gather_row` gen branch, `cols_wf` gen branch.

Left (check with `env LEAN_PATH=<wt>/.lake/build/lib/lean lean Rel/RepCanon.lean`):
1. `Opt.gather_row` (missing; used at RepCanon `Vals.gather_row` opt branch): `Opt.gather m ix x = .ok y →
   ∃ i, ix[j] = i ∧ y.get j = x.get i` — needs `kgather` moving the null flag (`raw_kgather`, `foRNuls`).
2. `Vals.cols_wf` opt branch: its claim `hasNul c.2 = false` is FALSE for a band key column (`Opt.plain_key` is a
   placeholder name, does not exist). Weaken the statement (drop `hasNul = false`, or `∨` the band case) and repair
   the consumers (`sorted_key`, `nub_sel`, `nub_sorted`, `kasc_grade` callers) to accept a null key column
   (`asc_col_row` already takes `h0 : hasNul e = false → nul = .empty`; `Verify.nulCodes_row` in KernelSpec/Asc).
3. `Vals.row_of_codes` (~line 1024) and `Vals.codes_of_row` (~line 1117): sum case still destructures
   `⟨l, r, tag, idx, x, y⟩`; convert to `s` + `rcases hv : s.view`, gen branch passes `hv` to `Vals.cols_sum`
   (`simp only [Vals.row, hv]` where it had `simp only [Vals.row, …]`); opt branch needs an `Opt` version of
   `Arr.eq_of_codes` / `Arr.codes_of_eq` (codes equal ↔ `Opt.get` equal, nulls included).
4. `Tab.canon_holds` (~1290): `Vals.nub_rows hn hw` type mismatch `R.WF` vs `Vals.WF (R.key, R.val)` — likely
   fallout of the `Vals.WF` def failing earlier; recheck after 1–3.
Then RepCols, RepOrder, RepStruct, RepWF, GenKBits, rest, Frame programs, TestFrame*.
