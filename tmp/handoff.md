# W3d handoff (branch w3arr2)

Done
- Task 1 (old layer at `pos`): `KernelWF.get_bytesOf` (Rel/KernelWF/RazeSpec.lean) proved at every encoding through
  `get_eq_raw` + `Verify.elemsW_bytesOf` (no case split); `Alg.long_enc` (Rel/KernelWF/CodesSpec.lean) restated:
  dense disjunct = `∃ b, b.size = n*8 ∧ groupIdsColumn t n e = some (groupIds .i64 n b) ∧ raw word i = bitsAt b (8i) 8
  ∧ (e = .bytes b ∨ e = .pos)`, users read `hg`/`hraw` (ofIds_long_faithful/wf) or rule `pos` out (rangeOffsets_spec,
  codes_long_eq, codes_long_group, codes_long_cut). Full build green after merge of master (b4).
- master merged. `colConst`/`colMap`/`colMap_closed` moved Rel/Run/Cols.lean -> Rel/Run/Canon.lean;
  `kscatter_words`/`colConst_raw`/`colConst_u1`/`colMap_get` moved Rel/RepCols.lean -> Rel/RepCanon.lean (section
  `open Ext.Enc`), names unchanged.
- Task 2, gather half: `Arr.gather` (Canon), `Vals.gather` sum case (gathers tag and idx, keeps payloads);
  `Arr.gather_row`, `Vals.gather_row` sum case, `Vals.gather_clamp`, `Arr.get_i64`, `clampFin_word`, `Arr.get_u1`,
  `Arr.eq_of_codes` (Rel/RepCanon.lean).

Left
- `Vals.cols` sum case + `Vals.row_of_codes` sum case. A full attempt (definition and proof) is in
  /data/tmp/w3arr2/Canon_attempt.lean (Vals.cols) and /data/tmp/w3arr2/RepCanon_attempt.lean (row_of_codes sum
  case, ~line 395). Definition compiles. The proof failed only at destructuring `hes`: after
  `simp only [bind, Except.bind, pure, Except.pure] at hes` the 4th `split at hes` hits the `if l.toNat = 0`
  (Decidable.rec) — "Dependent elimination failed". Fix: `by_cases hl0 : l.toNat = 0` / `hr0` and
  `simp only [hl0, hr0, if_true, if_false] at hes` before splitting the gather matches, or name the summand step
  as its own def. Everything after (`wx`/`wy`, `Vals.gather_clamp`, recursion) is written but unchecked.
- Task 3: #guards against old `canonC`/`CRel.ran`/`CRel.dom` on a table with a sum side (needs cols sum).
  Per coordinator: `Vals.codes_of_row` / `Vals.nub_distinct` belong to branch w3laws, not here.
