import Rel.Lang.TestNative
import Rel.Lang.TestFrameGroup
import Rel.Lang.TestFrameJoin
import Rel.Lang.TestFrameNull

/-! The dataframe library (`Frame`, `FrameGroup`, `FrameJoin`) runs natively: the plan of each closed definition of the
    `rel_program`s `frameGroupT`, `frameJoinT`, `frameNullT` (the programs of the tests that use it), run, writes the
    columns of the Lean value (the check the `rel-native` gate makes on `out/key`, `out/val`). A null column `1+N` is
    read by `injConvB` as the band column it is. -/

namespace Rel.Lang.TestNativeProgD

open Rel.Lang Rel.Lang.Plan Rel.Lang.TestNative

#eval show Lean.Meta.MetaM Unit from do
  writesAgree "ag3" (← planOfIn ``TestFrameGroup.frameGroupT "ag3") TestFrameGroup.frameGroupT.ag3
  writesAgree "vc2" (← planOfIn ``TestFrameGroup.frameGroupT "vc2") TestFrameGroup.frameGroupT.vc2
  writesAgree "vc" (← planOfIn ``TestFrameGroup.frameGroupT "vc") TestFrameGroup.frameGroupT.vc

#eval show Lean.Meta.MetaM Unit from do
  writesAgree "ij" (← planOfIn ``TestFrameJoin.frameJoinT "ij") TestFrameJoin.frameJoinT.ij
  writesAgree "ij2" (← planOfIn ``TestFrameJoin.frameJoinT "ij2") TestFrameJoin.frameJoinT.ij2
  writesAgree "cj" (← planOfIn ``TestFrameJoin.frameJoinT "cj") TestFrameJoin.frameJoinT.cj

#eval show Lean.Meta.MetaM Unit from do
  writesAgree "nc" (← planOfIn ``TestFrameNull.frameNullT "nc") TestFrameNull.frameNullT.nc
  writesAgree "xn" (← planOfIn ``TestFrameNull.frameNullT "xn") TestFrameNull.frameNullT.xn
  writesAgree "n2" (← planOfIn ``TestFrameNull.frameNullT "n2") TestFrameNull.frameNullT.n2
  writesAgree "lj" (← planOfIn ``TestFrameNull.frameNullT "lj") TestFrameNull.frameNullT.lj
  writesAgree "rj" (← planOfIn ``TestFrameNull.frameNullT "rj") TestFrameNull.frameNullT.rj
  writesAgree "fj" (← planOfIn ``TestFrameNull.frameNullT "fj") TestFrameNull.frameNullT.fj
  writesAgree "aq" (← planOfIn ``TestFrameNull.frameNullT "aq") TestFrameNull.frameNullT.aq
  writesAgree "pw" (← planOfIn ``TestFrameNull.frameNullT "pw") TestFrameNull.frameNullT.pw

end Rel.Lang.TestNativeProgD
