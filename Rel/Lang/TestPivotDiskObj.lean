import Rel.Lang.TestPivotDisk

/-! The program an importing test reads (`TestPivotDiskImport`): `obj V from "dir" c`, the distinct values of a
    column on disk, declared in one module for another to generate over. -/

namespace Rel.Lang.TestPivotDiskObj

open Rel Rel.Lang.Table

#eval Rel.Lang.TestPivotDisk.fixture "/data/tmp/rel-test-pivot-disk-import/t"

rel_program diskObj where
    obj V from "/data/tmp/rel-test-pivot-disk-import/t" c
    obj P
    obj N
    obj Y = {no, yes}
    schema T = {c : V, v : N}

end Rel.Lang.TestPivotDiskObj
