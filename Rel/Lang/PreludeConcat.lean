module

public import Rel.Lang.PreludeRows

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

/-- **The definition of `concat` means the row**: `ys` is the concatenation of the arrays of `xss`. -/
theorem Tm.concatDef_den (ρ : Val) {B : Obj} (xss : Obj.El (.arr (.arr B))) (ys : Obj.El (.arr B)) :
    (Tm.concatDef B).den ρ xss ys ↔ Prim.den (rowOf "concat") (.arr (.arr B)) (.arr B) [] xss ys := by
  rw [Prim.den_concat]
  have hd : (Tm.concatDef B).den ρ = foldDen nilDen (Prim.den (rowOf "cat") (.prod (.arr B) (.arr B)) (.arr B) []) := by
    simp only [Tm.concatDef, Tm.den, Tm.nil, Prim.den_nilRow]
  rw [hd]
  have h := foldDen_foldl (TS := Prim.den (rowOf "cat") (.prod (.arr B) (.arr B)) (.arr B) [])
    (f := fun acc x => acc ++ x) (fun a x w => by rw [Prim.den_cat]) xss [] ys
  refine h.trans ?_
  have gen : ∀ (xss : List (List B.El)) (acc : List B.El), xss.foldl (fun acc x => acc ++ x) acc = acc ++ xss.flatten := by
    intro xss
    induction xss with
    | nil => intro acc; simp
    | cons x xss ih => intro acc; simp [ih]
  rw [gen]; simp

end Rel.Lang
