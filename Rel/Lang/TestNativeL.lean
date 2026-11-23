import Rel.Lang.EmitC
import Rel.Run.Lang.Embed
import Rel.Programs.Prelude

/-! The native recipes of the list rows `cat`, `cons`, `zip`, `concat` (`Tab.flatten`): `catTabB`, `consB`, `zipB`,
    `flattenB` (`Rel/Lang/EmitC.lean`). The plan of each definition, run, writes the columns of the Lean value (the
    check the `rel-native` gate makes on `out/key`, `out/val`), on cells of three, none, one and two elements. -/

namespace Rel.Lang.TestNativeL

open Tab Rel.Lang Rel.Lang.Plan Rel.Kernel

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

/-- The plan of `natL.NAME` writes the columns of the Lean value `R` (as `TestNative`'s check of `x`). -/
def agrees {A B : Obj} (name : String) (R : Except String (Tab A B)) : Lean.Meta.MetaM Unit := do
  let b ← match ← outputOf ``natL name "out" with | .ok b => pure b | .error e => throwError "{name}: {e}"
  let p ← match Bld.plan b with | .ok p => pure p | .error e => throwError "{name}: {e}"
  let (_, ws) ← match p.run abiOf with | .ok r => pure r | .error e => throwError "{name}: the plan fails with {e}"
  let x ← match R with | .ok x => pure x | .error e => throwError "{name}: {e}"
  let side (s : String) (cs : List (String × SideCol)) := cs.map fun (p, v) => ("out/" ++ s ++ p, v)
  let want ← match (side "key" (cols _ x.key "") ++ side "val" (cols _ x.val "")).filterMapM
      (fun (p, v) => do pure ((← ownFile p v).map fun f => (p, f))) with | .ok w => pure w | .error e => throwError e
  let got := ws.toList.filterMap fun (_, vs) => match vs.toList with
    | .str p :: c :: k :: n :: ps :: _ => (p, ·) <$> Reg.get? (α := Db.OwnFile) (.ctor 0 #[ps] #[c, k, n])
    | _ => none
  let flat (pf : String × Db.OwnFile) :=
    (pf.1, pf.2.code, pf.2.kind, pf.2.count.toNat, pf.2.parts.toList.map (·.toList))
  unless got.length == ws.size && got.map flat == want.map flat do
    throwError "the plan of `{name}` writes {got.length} of {ws.size} columns, not those of its Lean value"

#eval agrees "ct" natL.ct
#eval agrees "cn" natL.cn
#eval agrees "zp" natL.zp
#eval agrees "fl" natL.fl
#eval agrees "f3" natL.f3

end Rel.Lang.TestNativeL
