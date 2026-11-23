import Rel.Lang.Test.Common
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
    -- the verbs themselves at `1+N`: one `kscan` of `nulVerb`'s op, equal to the compositions `maxO`/`minO`
    check ⟨nc, nd⟩ max [{(∗,40)}, 𝟙] = {(0,5),(1,9),(2,5),(3,40),(4,7),(5,40),(6,6),(7,3)}
    check ⟨nc, nd⟩ min [{(∗,40)}, 𝟙] = {(0,2),(1,40),(2,40),(3,40),(4,1),(5,40),(6,40),(7,40)}
    check ⟨nc, k5⟩ max [{(∗,40)}, 𝟙] = {(0,5),(1,5),(2,5),(3,5),(4,7),(5,5),(6,5),(7,5)}
    check ⟨nc, k5⟩ min [{(∗,40)}, 𝟙] = {(0,5),(1,40),(2,5),(3,40),(4,5),(5,40),(6,40),(7,3)}
    -- `+ - *` propagate null (`nulVerb`'s `or`), as q's `1+0N = 0N`
    check ⟨nc, nd⟩ plus [{(∗,40)}, 𝟙] = {(0,7),(1,40),(2,40),(3,40),(4,8),(5,40),(6,40),(7,40)}
    check ⟨nc, nd⟩ minus [{(∗,40)}, 𝟙] = {(0,3),(1,40),(2,40),(3,40),(4,6),(5,40),(6,40),(7,40)}
    check ⟨nc, nd⟩ times [{(∗,40)}, 𝟙] = {(0,10),(1,40),(2,40),(3,40),(4,7),(5,40),(6,40),(7,40)}
    ls : 1 ⟶ [1+N] ≜ Λ(⊤(1,P) nc)
    check ls ⦇[{(∗,∗)} inl, maxO]⦈ [{(∗,40)}, 𝟙] = {(∗,7)}
#guard nmm.ok

-- a verb with no row at `1+i64` (`nulVerb`: a zero divisor drops a non-null row) is refused by name
open Rel.Lang.Test in
#eval errAt "obj N = 0…3\nf : (1+N)×(1+N) ⟶ 1+N ≜ div\n" 2 "div on 1+N: a nullable `1+N` runs the verbs `nulVerb` names"

end Rel.Lang.TestNullMaxMin
