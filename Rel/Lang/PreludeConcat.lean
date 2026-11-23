module

public import Rel.Lang.PreludeRows
public import Rel.Programs.Prelude

@[expose] public section

/-! `concat : [[α]] ⟶ [α] ≜ ⦇[nil, cat]⦈` (`Programs/Prelude.lean`) means the row `concat`'s `rowDens` term,
    `xss.flatten` (B10b): the definition's term is the left fold from `nil` of the row `cat`. -/

namespace Rel.Lang

open Rel.Core.Rel hiding id comp recip inter union zero le inl inr junc

/-- `concat` at `[[B]] ⟶ [B]`: the left fold from `nil` of the row `cat`. -/
def Tm.concatDef (B : Obj) : Tm (.arr (.arr B)) (.arr B) := .fold .nil (.prim (rowOf "cat"))

theorem Prim.den_cat {B : Obj} :
    Prim.den (rowOf "cat") (.prod (.arr B) (.arr B)) (.arr B) [] = fun p zs => zs = p.1 ++ p.2 := by
  have hs : (rowOf "cat").sig = ([], .prod (.list (.var {} "B")) (.list (.var {} "B")), .list (.var {} "B")) := rfl
  have ho : (rowOf "cat").objs (.prod (.arr B) (.arr B)) (.arr B) [] = some [B] := by
    simp [Prim.objs, Prim.vars, hs, Option.orElse, OExp.unify, OExp.vars, List.eraseDups, List.eraseDupsBy,
      List.eraseDupsBy.loop, List.lookup]
  have hf : rowDens.find? (·.1.sym == (rowOf "cat").sym) =
      some ⟨RowCode.cat, fun _ _ p zs => zs = p.1 ++ p.2⟩ := rfl
  unfold Prim.den; simp only [List.map_nil]
  rw [hf, ho]; dsimp only; rw [dif_pos ⟨rfl, rfl⟩]; rfl

theorem Prim.den_concat {B : Obj} :
    Prim.den (rowOf "concat") (.arr (.arr B)) (.arr B) [] = fun xss ys => ys = xss.flatten := by
  have hs : (rowOf "concat").sig = ([], .list (.list (.var {} "B")), .list (.var {} "B")) := rfl
  have ho : (rowOf "concat").objs (.arr (.arr B)) (.arr B) [] = some [B] := by
    simp [Prim.objs, Prim.vars, hs, Option.orElse, OExp.unify, OExp.vars, List.eraseDups, List.eraseDupsBy,
      List.eraseDupsBy.loop, List.lookup]
  have hf : rowDens.find? (·.1.sym == (rowOf "concat").sym) =
      some ⟨RowCode.concat, fun _ _ xss ys => ys = xss.flatten⟩ := rfl
  unfold Prim.den; simp only [List.map_nil]
  rw [hf, ho]; dsimp only; rw [dif_pos ⟨rfl, rfl⟩]; rfl

end Rel.Lang
