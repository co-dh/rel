import Rel.Lang.TestNative

/-! The fixpoint rows `star`, `loop` run natively (`Plan.rowB`: `starB`, `loopB`): each definition's plan writes the
    columns `writeRel` writes of its Lean value (`writesAgree`, the `rel-native` gate's check). `ymd` has no recipe:
    the day count of a text has one source, `Db.Csv.ymd`, which no kernel of the plan ABI computes, so its plan is
    refused naming the row. -/

namespace Rel.Lang.TestNativeF

open Tab Rel.Lang Rel.Lang.Plan Rel.Lang.TestNative

open Rel.Programs.prelude in
rel_program nativeF where
    obj N = 0…9
    obj I
    obj C : char
    obj D : date
    -- a chain into a cycle `3 ↔ 5`: `star` stops when a round adds no row
    ed : N ⟶ N ≜ {(1,2),(2,3),(3,5),(5,3)}
    -- `star` on the range of a literal: `1`, `2` reach the cycle, `7` only itself; the same on `dom(ed)`
    sd : N ⟶ N ≜ {(0,1),(4,2),(6,7)} star(ed)
    check sd = {(0,1),(0,2),(0,3),(0,5),(4,2),(4,3),(4,5),(6,7)}
    se : N ⟶ N ≜ dom(ed) star(ed)
    -- `loop` from each start along its list: a sum (one state per round), an empty list (the start itself), and a
    -- step of two images (`π₁ ∪ π₂`: every element or the start reached)
    a0 : N ⟶ I ≜ {(1,0),(2,5),(3,1)}
    xs : N ⟶ [I] ≜ {(1,3 1 2),(2,[]),(3,4 4)}
    lp : N ⟶ I ≜ ⟨a0, xs⟩ loop(plus)
    check lp = {(1,6),(2,5),(3,9)}
    lq : N ⟶ I ≜ ⟨a0, xs⟩ loop(π₁ ∪ π₂)
    check lq = {(1,0),(1,1),(1,2),(1,3),(2,5),(3,1),(3,4)}
    tx : N ⟶ [C] ≜ {(1,"2024.01.15"),(2,"2024.02.30")}
    dy : N ⟶ D ≜ tx ymd

/-- The plan of `output x to "out"` in `nativeF`. -/
def planOf (x : String) : Lean.Meta.MetaM (Except String Plan) := return (← outputOf ``nativeF x "out") >>= Bld.plan

#eval show Lean.Meta.MetaM Unit from do
  writesAgree "sd" (← planOf "sd") nativeF.sd
  writesAgree "se" (← planOf "se") nativeF.se
  writesAgree "lp" (← planOf "lp") nativeF.lp
  writesAgree "lq" (← planOf "lq") nativeF.lq

-- the Lean values the plans match (the `check` lines), so an agreeing plan of a wrong value is caught here
#guard nativeF.failures.map toString == []

-- `ymd`'s plan is refused naming the row, never a wrong table
#eval show Lean.Meta.MetaM Unit from do
  match ← planOf "dy" with
  | .error e => unless (e.splitOn "row `ymd`").length == 2 do throwError "ymd's plan fails with {e}"
  | .ok _ => throwError "ymd has a plan, but no recipe computes it"

end Rel.Lang.TestNativeF
