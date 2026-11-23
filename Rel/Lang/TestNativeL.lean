import Rel.Lang.TestNative

/-! The native recipes of the list rows `cat`, `cons`, `zip`, `concat` (`Tab.flatten`): `catTabB`, `consB`, `zipB`,
    `flattenB` (`Rel/Lang/EmitC.lean`). The plan of each definition, run, writes the columns of the Lean value (the
    check the `rel-native` gate makes on `out/key`, `out/val`), on cells of three, none, one and two elements. -/

namespace Rel.Lang.TestNativeL

open Tab Rel.Lang Rel.Lang.Plan Rel.Kernel Rel.Lang.TestNative

open Rel.Programs.prelude in
rel_program natL where
    obj N = 0…9
    xs : N ⟶ [N] ≜ {(1,3 1 2),(2,[]),(3,1 2),(4,2 2)}
    ys : N ⟶ [N] ≜ {(1,7 7),(2,8 9),(3,[]),(4,5 6 7)}
    v : N ⟶ N ≜ {(1,0),(2,5),(3,6),(4,7)}
    ct : N ⟶ [N] ≜ ⟨xs, ys⟩ cat
    cn : N ⟶ [N] ≜ ⟨v, xs⟩ cons
    zp : N ⟶ [N×N] ≜ ⟨xs, ys⟩ zip
    fl : N ⟶ [N] ≜ ⟨xs τ, ys τ⟩ cat concat
    f3 : N ⟶ [N] ≜ ⟨⟨xs τ, ys τ⟩ cat, ⟨xs τ, ys τ⟩ cat⟩ cat concat

#eval show Lean.Meta.MetaM Unit from do
  writesAgree "ct" (← planOfIn ``natL "ct") natL.ct
  writesAgree "cn" (← planOfIn ``natL "cn") natL.cn
  writesAgree "zp" (← planOfIn ``natL "zp") natL.zp
  writesAgree "fl" (← planOfIn ``natL "fl") natL.fl
  writesAgree "f3" (← planOfIn ``natL "f3") natL.f3

end Rel.Lang.TestNativeL
