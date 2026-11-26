import Rel.Lang.TestNative
import Rel.Programs.Prelude

/-! An array in a sum summand written canonically (`ValsB.pack 0`, the `true, .arr` case): a result of type `N ⟶ [N]+N`
    whose `[N]` summand has cells over a payload with dead elements (`cat` then `tail`), in the rows `0`, `1`; row `2`
    is the other summand, whose cell bounds are null. The plan's `outSides` and the Lean writer agree
    (`writesAgree`). -/

namespace Rel.Lang.TestNativeProgSum

open Tab Rel.Lang Rel.Lang.Plan Rel.Kernel Rel.Lang.TestNative

open Rel.Programs.prelude in
rel_program natSum where
    obj N = 0…3
    r : 1 ⟶ [N] ≜ (𝟙÷∋)E(⊤{(0,0),(1,1)})
    c : 1 ⟶ [N] ≜ ⟨r,r⟩ cat tail
    s : N ⟶ [N]+N ≜ (dom({(0,0),(1,1)}) ⊤c inl) ∪ ({(2,2)} inr)
    mx : N ⟶ N+N ≜ ({(0,0),(1,1)} inl) ∪ ({(2,2)} inr)
    v : N ⟶ [N] ≜ dom({(0,0),(1,1)}) ⊤c
    w : N ⟶ [N]+N ≜ dom({(0,0),(1,1)}) ⊤c inl
    q1 : N ⟶ [N]+N ≜ {(2,2)} inr

#eval match natSum.s with
  | .ok t => match ValsB.pack 0 t.val with | .ok _ => "lean pack ok" | .error e => s!"lean pack: {e}"
  | .error e => s!"lean value: {e}"
#eval show Lean.Meta.MetaM Unit from do writesAgree "mx" (← planOfIn ``natSum "mx") natSum.mx
#eval show Lean.Meta.MetaM Unit from do writesAgree "v" (← planOfIn ``natSum "v") natSum.v
#eval show Lean.Meta.MetaM Unit from do writesAgree "w" (← planOfIn ``natSum "w") natSum.w
#eval show Lean.Meta.MetaM Unit from do writesAgree "q1" (← planOfIn ``natSum "q1") natSum.q1
#eval show Lean.Meta.MetaM Unit from do writesAgree "s" (← planOfIn ``natSum "s") natSum.s

end Rel.Lang.TestNativeProgSum
