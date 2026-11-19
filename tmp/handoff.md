# W3d handoff (branch w3arr)

Done (step 1, `pos`): `Enc.WF .i64 .pos = True` (Rel/Kernel/Value.lean WF); `Arr.kgather_wf` pos case
(Rel/Run/Canon.lean); `Arr.get_raw_atom` + `Arr.get_eq_of_raw` over foR and pos (Rel/RepCanon.lean); old
`Enc.bytesOf` reads `.pos` at i64 (Rel/Kernel/Coc.lean ~479); pos cases in `bytesOf_size`
(Rel/Run/KernelWF/Raze.lean), `elemsW_bytesOf` (Rel/KernelSpec/Gather.lean); `long_cases` now has a third
disjunct `e = .pos` (Rel/Run/KernelWF/Gather.lean); `longWords`/`longBytes` read `.pos`, `Arr.dense_long` states
`longBytes m x.enc = some B` instead of the per-encoding disjunction (Rel/Run/Core.lean); callers updated
(KernelWF/CodesRec, PickRow, BagSpec `gradeColumn_long` pos branch, Run/Code.lean `longBytes_isSome`, proof only).

Left (step 2, sum sides): `Vals.cols`/`Vals.gather` in Rel/Run/Canon.lean still error on `arr`/`sum`.
Design: cols(sum) = `(.u1, tag.enc) :: xs ++ ys`; `nt = kscan .not false .u1 .i64 n ones [tag, tag]`;
`px = kscan .mul false .i64 .i64 n ones [idx, nt]`, `py` likewise with `tag`; `ones = kscatter .last 0 .pos .pos n 1`;
xs = [] when l = 0 else `Vals.cols` of x gathered at px. Gather of arr/sum gathers lo/hi (tag/idx), payload
shared. Helper lemmas drafted in /data/tmp/w3arr/s4.lean (`kfill_raw` proved; `sumPos_raw` last step open).
Laws (step 4) and arr kernel (step 3, branch mig-arrkey 369f095, 12 files) not started.
