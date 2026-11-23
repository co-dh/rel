import Rel.Lang.EmitC
import Rel.Run.Lang.Embed
import Rel.Programs.Prelude

/-! The native recipes of `setify`, `positions`, `thinL` and `merge` (`setifyB`'s `lamB ∘ memB`, `positionsB`, `thinLB`,
    `mergeB`): each definition of `natS`, on literal tables, is planned (`outputOf`) and the plan's `qlean_own_write`s
    are compared with the `OwnFile`s of its Lean value's columns, as `TestNative` compares `x`. A row at a source
    object no recipe reads refuses with the row's name. -/

namespace Rel.Lang.TestNativeS

open Tab Rel.Lang Rel.Lang.Plan Rel.Kernel

open Rel.Programs.prelude in
rel_program natS where
    obj N = 0…9
    xs : N ⟶ [N] ≜ {(1,3 1 2 3),(2,[]),(3,1 2),(4,2 2 2),(5,5 4 5 4 3)}
    ys : N ⟶ [N] ≜ {(1,2 4),(2,[1]),(3,[]),(4,5 6 7),(5,0 3)}
    pq : N ⟶ [N]×[N] ≜ ⟨xs, ys⟩
    ev : N ⟶ N ≜ {(1,1),(3,3),(4,4),(5,5)}
    -- `setify`: each cell to its elements, ascending and each once
    st : N ⟶ [N] ≜ xs setify
    -- `positions(ev)`: the positions of the elements in `dom ev`, a cell with none (`[]`), with one, with several
    po : N ⟶ [N] ≜ xs positions(ev)
    -- `thinL(≤)`, `merge(≤)`: the pair tests `up`, `down`, `lone` of a round, an empty cell, and both cells at once
    tn : N ⟶ [N] ≜ xs thinL(≤)
    mg : N ⟶ [N] ≜ pq merge(≤)
    -- a row on a source with a relation given a list of lists is run through `F`, `merge` of two empty cells
    me : N ⟶ [N] ≜ ⟨ys, ys⟩ merge(≤)

/-- The plan of `x` writes the `OwnFile`s `v`'s columns make (`ownFile`), column for column. -/
def agree {A B : Obj} (x : String) (v : Except String (Tab A B)) : Lean.Meta.MetaM Unit := do
  let p ← match ← outputOf ``natS x ("out/" ++ x) with
    | .ok b => match Bld.plan b with | .ok p => pure p | .error e => Lean.throwError "{x}: {e}"
    | .error e => Lean.throwError "{x}: {e}"
  let (_, ws) ← match p.run abiOf with | .ok r => pure r | .error e => Lean.throwError "{x}: {e}"
  let t ← match v with | .ok t => pure t | .error e => Lean.throwError "{x}: {e}"
  let side (s : String) (cs : List (String × SideCol)) := cs.map fun (p, v) => ("out/" ++ x ++ "/" ++ s ++ p, v)
  let want ← match (side "key" (cols _ t.key "") ++ side "val" (cols _ t.val "")).filterMapM
      (fun (p, v) => do pure ((← ownFile p v).map fun f => (p, f))) with | .ok w => pure w | .error e => Lean.throwError "{x}: {e}"
  let got := ws.toList.filterMap fun (_, vs) => match vs.toList with
    | .str p :: c :: k :: n :: ps :: _ => (p, ·) <$> Reg.get? (α := Db.OwnFile) (.ctor 0 #[ps] #[c, k, n])
    | _ => none
  let flat (pf : String × Db.OwnFile) :=
    (pf.1, pf.2.code, pf.2.kind, pf.2.count.toNat, pf.2.parts.toList.map (·.toList))
  unless got.length == ws.size && got.map flat == want.map flat do
    Lean.throwError "the plan of `{x}` writes {got.length} of {ws.size} columns, not those of its Lean value"

#eval agree "st" natS.st
#eval agree "po" natS.po
#eval agree "tn" natS.tn
#eval agree "mg" natS.mg
#eval agree "me" natS.me

end Rel.Lang.TestNativeS
