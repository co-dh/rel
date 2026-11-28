import Rel.Programs.Prelude
import Rel.Lang.Laws.AopS2_50

/-! # Laws of freyd §2.5 (`Freyd/S2_50.lean`), in Rel

The theorem is named after the last component of its freyd declaration, with the declaration and the companion
position (chapter file : line) beside it. -/

namespace Rel.Programs

open Rel.Programs.prelude in
rel_program aopS2_50 where
    theorem interZero(R : α ⟶ β) : R ∩ 𝟘 = 𝟘 by Rel.Lang.Tm.inter_zero_den  -- Freyd.Alg.inter_zero, 00-laws.typ:180

end Rel.Programs
