import Rel.Lang.TestFrameCols
import Rel.Programs.FrameJoin

/-! `max`/`min` on `1+N` (in-band `Opt` column) order null below every value (CLAUDE.md, Null): `max(0N,5) = 5`,
    `min(0N,5) = 0N`, `max(0N,0N) = 0N`. A null is read back through an impute (40). -/

namespace Rel.Lang.TestNullMaxMin

open Rel.Programs.prelude Rel.Programs.frame Rel.Programs.frameGroup Rel.Programs.frameJoin
  Rel.Lang.TestFrameCols.frameData in
rel_program nmm where
    nc : P ⟶ 1+N ≜ dom(x) tot({(0,5),(2,5),(4,7),(7,3)})
    nd : P ⟶ 1+N ≜ dom(x) tot({(0,2),(1,9),(4,1),(6,6)})
    k5 : P ⟶ 1+N ≜ dom(x) tot({(0,5),(1,5),(2,5),(3,5),(4,5),(5,5),(6,5),(7,5)})
    maxO : (1+N)×(1+N) ⟶ 1+N ≜ ⟨π₁ inl°, π₂⟩ π₂ ∪ (⟨π₂ inl°, π₁⟩ π₂) ∪ (⟨π₁ inr°, π₂ inr°⟩ max inr)
    minO : (1+N)×(1+N) ⟶ 1+N ≜ π₁ inl° inl ∪ (π₂ inl° inl) ∪ (⟨π₁ inr°, π₂ inr°⟩ min inr)
    check ⟨nc, nd⟩ maxO [{(∗,40)}, 𝟙] = {(0,5),(1,9),(2,5),(3,40),(4,7),(5,40),(6,6),(7,3)}
    check ⟨nc, nd⟩ minO [{(∗,40)}, 𝟙] = {(0,2),(1,40),(2,40),(3,40),(4,1),(5,40),(6,40),(7,40)}
    -- the constant 5 beside a column, the fold of the set of values, null among them
    check ⟨nc, k5⟩ maxO [{(∗,40)}, 𝟙] = {(0,5),(1,5),(2,5),(3,5),(4,7),(5,5),(6,5),(7,5)}
    check ⟨nc, k5⟩ minO [{(∗,40)}, 𝟙] = {(0,5),(1,40),(2,5),(3,40),(4,5),(5,40),(6,40),(7,3)}
    ls : 1 ⟶ [1+N] ≜ Λ(⊤(1,P) nc)
    check ls ⦇[{(∗,∗)} inl, maxO]⦈ [{(∗,40)}, 𝟙] = {(∗,7)}
#guard nmm.ok

end Rel.Lang.TestNullMaxMin
