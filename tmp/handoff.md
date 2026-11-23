State (WIP): Core.lean has Enc.starts, Arr.getWith/Opt.getWith/Opt.isNulWith (+ `get`/`isNul` as the #[] case), foRNul_starts,
Arr.getWith_starts, Opt.getWith_starts, hoisted rowsImpl (Arr, ColB true, ValsB opt sum). Table.lean leafFill/fillBad read
one element through Opt.get / Arr.rowsImpl, no Enc.raw. decode-allow.txt: Arr.get -> Arr.getWith, Opt.get -> Opt.getWith.
RepCanon.lean fixed for unfolding isNulWith (job decfix4 building Rel.Run.Core Rel.Run.Table Rel.RepStruct
Rel.Lang.GenSound Rel.Lang.TestTable, log /data/tmp/job/decfix4.log).
Left: fix any further downstream proof errors from unfolding Arr.get/Opt.get; make decode; bench with
Bench/ScratchRows.lean (uncommitted, old = Array.ofFn x.get, new = Arr.rowsImpl); TestTable pins (leafFill text unchanged;
fillBad tag text now "its tag is `true`, not `false`" if pinned).
