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
    -- `asc` keys are `pos`; `F(tt)` on them runs `iteT` (a total `tt`: the `canonT` branch) and `F(ev)` the fold branch (a
    -- partial `ev`), so a key reaches the sink as the `if`'s result, `pos` in a branch and no literal there
    tt : N ⟶ N ≜ {(1,2),(2,3),(3,1),(4,5),(5,4)}
    ac : N ⟶ [N] ≜ asc(ran(xs))
    am : N ⟶ [N] ≜ asc(ran(xs)) F(tt)
    ap : N ⟶ [N] ≜ asc(ran(xs)) F(ev)

#eval show Lean.Meta.MetaM Unit from do
  writesAgree "st" (← planOfIn ``natS "st") natS.st
  writesAgree "po" (← planOfIn ``natS "po") natS.po
  writesAgree "tn" (← planOfIn ``natS "tn") natS.tn
  writesAgree "mg" (← planOfIn ``natS "mg") natS.mg
  writesAgree "me" (← planOfIn ``natS "me") natS.me
  writesAgree "ac" (← planOfIn ``natS "ac") natS.ac
  writesAgree "am" (← planOfIn ``natS "am") natS.am
  writesAgree "ap" (← planOfIn ``natS "ap") natS.ap

/-! An array bound that is `pos` (`.lo` the positions `0, 1, 2`): `flatB` writes it as the `foR` the file holds, the
    constructor read at run time as for a bound that is a kernel's answer. -/

/-- `flatB` of one array column over three rows whose `.lo` is `posB`, `.hi` is `lo + 1`: the plan's last register is
    the `.lo` `Enc` written. -/
def arrPos : Except String Plan := Bld.plan do
  let n ← lit (.size 3)
  let lo ← posB
  let hi ← mapB .add n lo (← wordsB n 1)
  let s ← flatB n [.arr "" n lo hi [.atom ".e" .i64 (← wordsB n 7)]]
  let some (_, rs) := s.head? | throw "flatB of one array: no side"
  let some e := rs.back? | throw "flatB: a side with no register"
  discard <| nth (← ite (← lit (.bit true)) (pure #[e]) (pure #[e])) 0 "if"

#eval show IO Unit from do
  let (rs, _) ← IO.ofExcept ((← IO.ofExcept arrPos).run abiOf)
  let some e := rs.back?.bind (Reg.get? (α := Enc)) | throw (IO.userError "arrPos: the last register is no Enc")
  unless e.ctorIdx == (Enc.foR .empty .empty).ctorIdx && (Enc.raw .i64 3 e).toList == [0, 1, 2] do
    throw (IO.userError s!"arrPos: the `.lo` written is not the foR of 0, 1, 2: {(Enc.raw .i64 3 e).toList}")

end Rel.Lang.TestNativeS
