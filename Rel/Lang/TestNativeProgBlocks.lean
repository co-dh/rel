import Rel.Lang.TestNative
import Rel.Programs.Blocks

/-! The blocks world (`Rel/Programs/Blocks.lean`) planned: the chosen path `plan` and its literal, run natively. -/

namespace Rel.Lang.TestNativeProgBlocks

open Tab Rel.Lang Rel.Lang.Plan Rel.Kernel Rel.Lang.TestNative

open Rel.Programs.prelude Rel.Programs.blocks in
rel_program natBlocks where
    pl : N ⟶ X×X ≜ ζσ
    pr : N ⟶ X×X ≜ {(0,(C,C)),(1,(B,C)),(2,(A,B))}


-- the plan computes each closed definition once (`shareB`): its globals, and `agree`'s plan and run times
#eval show Lean.Meta.MetaM Unit from do
  let t ← IO.monoMsNow
  let p ← planOfIn ``natBlocks "pl"
  let .ok p := p | throwError "plan: {repr p.toOption.isSome}"
  Lean.logInfo m!"funs {p.funs.size}, globals built {(p.globals.filter (!·.res.isEmpty)).size} of {p.globals.size}, plan {(← IO.monoMsNow) - t} ms"

#eval show Lean.Meta.MetaM Unit from agree ``natBlocks "pl" natBlocks.pl

end Rel.Lang.TestNativeProgBlocks
