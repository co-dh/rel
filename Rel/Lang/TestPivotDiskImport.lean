import Rel.Lang.TestPivotDiskObj

/-! A finite object declared by another program (`obj V from "dir" c` in `TestPivotDiskObj`): `⟨v ∈ V ↦ e⟩`,
    `schema D = {c ∈ V : A}` and `getDummies` generate over it as over a same-module one (`TestPivotDisk.dummiesT`). -/

namespace Rel.Lang.TestPivotDiskImport

open Rel.Programs.prelude Rel.Programs.frame Rel.Programs.frameGroup Rel.Programs.frameJoin
  Rel.Lang.TestPivotDiskObj.diskObj in
rel_program importT where
    input x : P ⟶ T from "/data/tmp/rel-test-pivot-disk-import/t"
    schema D = {c ∈ V : 1+1}
    d : P ⟶ D ≜ ⟨e ∈ V ↦ dummy(col T "c", e, x)⟩
    check d col D "c_9" [{(∗,no)}, {(∗,yes)}] = {(0,no),(1,no),(2,no),(3,yes)} where x ≜ {(0,(7,10)),(1,(3,20)),(2,(7,30)),(3,(9,40))}
    g : P ⟶ D ≜ getDummies(col T "c", x)
    check g = d where x ≜ {(0,(7,10)),(1,(3,20)),(2,(7,30)),(3,(9,40))}

#guard importT.ok

end Rel.Lang.TestPivotDiskImport
