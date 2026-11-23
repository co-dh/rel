nullband3a2 handoff (PLAN.md: nullband3a2 entry under nullband3).

Done, RelRun green (`cap lake build Rel.Run.Lang.Gen Rel.Run.Lang.Expand Rel.Run.Lang.Elab Rel.Run.Table Rel.Run.Struct
Rel.ObjOrder` built RelRun:shared):
- merged nullband3a (abc765f), null1x (worktree-agent-a1fe2f64515129f21: `Obj.opt X = .sum .one X`, CSV `swapTag`),
  doc dataframe-design (worktree-agent-a4331af8e6924b5c3, PDF recompiled).
- nullorder flip reverted (`git revert 19fd603`): Obj.key inl ↦ 0::, Vals.cols keys on `tag`, `colMap_not_u1`,
  `Obj.lt_inr_inl`, tag foROk check gone; RepCanon/RepOrder/GenKBits proofs back to their pre-flip form (unbuilt).
- Obj.band at `1+t` (`| .one, .atom t`), band_some `a = .one ∧ b = .atom t`, optEl/optOf null = `inl ()`.
- Struct: `inl` on a band = `Opt.nuls`, `inr` = `Vals.optInr` (was optInl).
- Frame library and TestFrame* at `1+X` (types, inl/inr swapped, case `[d, 𝟙]`, `𝟙 ⊕ y`), unbuilt.
- Gen.optV, Gen.sumV takes `Obj.band A B = none`; Expand.bandRfl, valsE/valsEq via Vals.view; Elab empty sum
  literal (line ~1822) via Vals.none.

Left:
1. Build Rel lib modules in import order (ObjOrder done): RepCanon, RepCols, RepOrder, RepStruct, RepWF, GenKBits, ...
   Each `.sum` match on `Vals` needs the `s.view` pattern (see nullband3a handoff pattern in PLAN).
2. CSV 3 → 1: Rel/Run/Table.lean `toCsv`/`ofCsv` `.opt a` branch still expects tag/idx/1/v parts; a band `1+atom` side
   is now one `Opt` part (encVals/readVals band branch). Needs Db.Csv `null` shape as one in-band-null column (Rust too).
3. TestNullband round trips at 1+i64, 1+u1 (null first, gather, concat across blocks).
4. Fix FrameJoin.lean line 20 comment `x × (y ⊕ 𝟙)` → `x × (𝟙 ⊕ y)`.
Kernel stops (named errors, kept): Opt.concat with a null on either side; inl°/inr° on a band column.
