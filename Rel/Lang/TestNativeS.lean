import Rel.Lang.TestNative

/-! The native recipes of `setify`, `positions`, `thinL` and `merge` (`setifyB`'s `lamB ∘ memB`, `positionsB`, `thinLB`,
    `mergeB`): each definition of `natS`, on literal tables, is planned (`outputOf`) and the plan's `qlean_own_write`s
    are compared with the `OwnFile`s of its Lean value's columns, as `TestNative` compares `x`. A row at a source
    object no recipe reads refuses with the row's name. -/

namespace Rel.Lang.TestNativeS

open Tab Rel.Lang Rel.Lang.Plan Rel.Kernel Rel.Lang.TestNative

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

#eval show Lean.Meta.MetaM Unit from do
  writesAgree "st" (← planOfIn ``natS "st") natS.st
  writesAgree "po" (← planOfIn ``natS "po") natS.po
  writesAgree "tn" (← planOfIn ``natS "tn") natS.tn
  writesAgree "mg" (← planOfIn ``natS "mg") natS.mg
  writesAgree "me" (← planOfIn ``natS "me") natS.me

end Rel.Lang.TestNativeS
