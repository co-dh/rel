import Rel.Lang.TestNative
import Rel.Programs.Blocks

/-! The blocks world (`Rel/Programs/Blocks.lean`) planned: the chosen path `plan` and its literal, run natively. -/

namespace Rel.Lang.TestNativeProgBlocks

open Tab Rel.Lang Rel.Lang.Plan Rel.Kernel Rel.Lang.TestNative

open Rel.Programs.prelude Rel.Programs.blocks in
rel_program natBlocks where
    pl : N ⟶ X×X ≜ ζσ
    pr : N ⟶ X×X ≜ {(0,(C,C)),(1,(B,C)),(2,(A,B))}


/- Not run here: `writesAgree "pl" (← planOfIn ``natBlocks "pl") natBlocks.pl` takes about 116 s (the Lean value 2 s, the plan
   build 21 s, `Plan.run` the rest). The plan has 354 functions, no global and a one-instruction `main`: each closed
   definition (`s₀`, `Q`, `C`, `δ`, `σ`, ...) is compiled again at every use, so `Plan.run` makes about 46M kernel calls
   (scan 12M, scatter 11M, gather 10.6M, asc 2.6M, seen 2.4M) for what the Lean value computes once per constant. -/

end Rel.Lang.TestNativeProgBlocks
