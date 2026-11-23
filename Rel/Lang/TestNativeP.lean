import Rel.Lang.TestNative

/-! The native recipes of `inits`, `tails`, `filter(p)` and `takewhile(p)` (`initsB`, `tailsB`, `filterB`, `takewhileB`):
    one program on literal tables, each definition's plan (`outputOf`, run by `Plan.run`) writing the own files
    `Db.ownFile` makes of the Lean value's columns, the check the `rel-native` gate makes on `out/key`, `out/val`. -/

namespace Rel.Lang.TestNativeP

open Tab Rel.Lang Rel.Lang.Plan Rel.Kernel Rel.Lang.TestNative

open Rel.Programs.prelude in
rel_program natP where
    obj X = {A,B,C}
    obj N = 0…9
    xs : X ⟶ [N] ≜ {(A,3 1 2),(B,[]),(C,5 4)}
    ev : N ⟶ N ≜ {(2,2),(4,4),(5,5)}
    lt : N ⟶ N ≜ {(1,1),(3,3),(5,5),(4,4)}
    ini : X ⟶ [[N]] ≜ xs inits
    tal : X ⟶ [[N]] ≜ xs tails
    fil : X ⟶ [N] ≜ xs filter(ev)
    tkw : X ⟶ [N] ≜ xs takewhile(lt)

#eval show Lean.Meta.MetaM Unit from do
  writesAgree "ini" (← planOfIn ``natP "ini") natP.ini
  writesAgree "tal" (← planOfIn ``natP "tal") natP.tal
  writesAgree "fil" (← planOfIn ``natP "fil") natP.fil
  writesAgree "tkw" (← planOfIn ``natP "tkw") natP.tkw

end Rel.Lang.TestNativeP
