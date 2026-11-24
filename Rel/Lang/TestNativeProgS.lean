import Rel.Lang.TestNative
import Rel.Programs.Knapsack
import Rel.Programs.JobShop
import Rel.Programs.Party
import Rel.Programs.Circuit
import Rel.Programs.CSP
import Rel.Programs.Wumpus

/-! The search programs of `Rel/Programs/` run natively with the answer they have in Lean: per program one
    `rel_program` opened on it, one definition per side of a table-valued `check`, and `writesAgree` of the plan of
    each definition (`planOfIn`) against its Lean value, the check the `rel-native` gate makes on `out/key`, `out/val`.
    Left out, each with the failure it gives (`Rel/Lang/ProbeK` etc. probes, one `#eval` per definition):
    - Knapsack `s`, `p`, `knap`, `knap ∩ s` and Party `gfold Λ(choose)est(R(rating)°)`, `best`, `root best`: the plan
      writes as many columns as the Lean value, "the plan of `k4` writes 5 of 5 columns, not those of its Lean value"
      (`y3`, `y4`, `y10`: 4 of 4): every one is `est(R)` with `R` an order built from `value`/`cost` (a fold `sum` of
      `F(π₁)`), the recipe of `est` is the gap.
    - Blocks: `plan` did not finish (its plan or its Lean value ran past 20 minutes).
    - Not yet planned: the `∩`, `𝟘` and literal sides of JobShop and the `∩`/literal sides of Party. -/

namespace Rel.Lang.TestNativeProgS

open Tab Rel.Lang Rel.Lang.Plan Rel.Kernel Rel.Lang.TestNative

open Rel.Programs.prelude Rel.Programs.knapsack in
rel_program natK where
    k1 : K ⟶ [N×N] ≜ X⦇[X nil, S]⦈
    k2 : K ⟶ [N×N] ≜ X subseq within(w)
    k7 : K ⟶ [N×N] ≜ {(a,(5,4) (6,5)),(b,(2,2) (9,8)),(c,[(1,9)]),(d,(5,4) (5,5)),(d,(5,4) (5,6))}
    k8 : K ⟶ [N×N] ≜ {(a,(5,4) (6,5)),(b,(2,2) (9,8)),(c,[(1,9)]),(d,(5,4) (5,5))}

open Rel.Programs.prelude Rel.Programs.jobshop in
rel_program natJ where
    j1 : Job ⟶ Job ≜ 𝟙(Job)
    j3 : N ⟶ N ≜ s° s
    j5 : 1 ⟶ [Job] ≜ jobs
    j6 : 1 ⟶ [Job] ≜ jobs ∩ (jobs ordered(∼pre°))
    j7 : Job ⟶ Job ≜ ⟨𝟙,s⟩ bad ⟨𝟙,s⟩°
    j9 : Job ⟶ N ≜ s

open Rel.Programs.prelude Rel.Programs.partyPlan in
rel_program natY where
    y1 : E ⟶ [E] ≜ party setify
    y2 : E ⟶ [E] ≜ Λ(under)subseq (𝟙 − dom(∋ ∩ (∋ boss)))setify
    y6 : E ⟶ [E] ≜ Λ(guests)
    y8 : E ⟶ N ≜ c max
    y9 : E ⟶ N ≜ best cost(rating)
    y12 : E ⟶ N ≜ root c max

open Rel.Programs.prelude Rel.Programs.circuit in
rel_program natC where
    c1 : [B] ⟶ B×B ≜ add
    c2 : [B] ⟶ B ≜ answer
    c3 : [B] ⟶ B ≜ {(0 1 1,0),(1 0 1,0),(1 1 0,0)}

open Rel.Programs.prelude Rel.Programs.csp in
rel_program natS where
    obj V = {x,y,z}
    obj D = 1…3
    arc : V ⟶ V ≜ {(x,y),(y,z)}
    lt : D ⟶ D ≜ <
    dom0 : V ⟶ D ≜ ⊤(V,D)
    a1 : V ⟶ D ≜ AC3(arc, lt, dom0)

open Rel.Programs.prelude Rel.Programs.wumpus in
rel_program natW where
    w1 : N ⟶ C×C ≜ next(V,B,S)
    w2 : N ⟶ C×C ≜ {(0,(12,12)),(0,(21,21)),(1,(12,12)),(2,(12,12)),(3,(22,22)),(4,(23,23)),(4,(32,32)),(5,(32,32))}

#eval show Lean.Meta.MetaM Unit from do
  agree ``natK "k1" natK.k1
  agree ``natK "k2" natK.k2
  agree ``natK "k7" natK.k7
  agree ``natK "k8" natK.k8
  agree ``natJ "j1" natJ.j1
  agree ``natJ "j3" natJ.j3
  agree ``natJ "j5" natJ.j5
  agree ``natJ "j6" natJ.j6
  agree ``natJ "j7" natJ.j7
  agree ``natJ "j9" natJ.j9
  agree ``natY "y1" natY.y1
  agree ``natY "y2" natY.y2
  agree ``natY "y6" natY.y6
  agree ``natY "y8" natY.y8
  agree ``natY "y9" natY.y9
  agree ``natY "y12" natY.y12
  agree ``natC "c1" natC.c1
  agree ``natC "c2" natC.c2
  agree ``natC "c3" natC.c3
  agree ``natS "a1" natS.a1
  agree ``natW "w1" natW.w1
  agree ``natW "w2" natW.w2

end Rel.Lang.TestNativeProgS
