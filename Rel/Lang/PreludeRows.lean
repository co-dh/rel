module

public import Rel.Lang.Den

-- exposed: every def body is a spec a downstream `rfl`/`decide`/`simp` may unfold (PLAN W.8)
@[expose] public section

/-! The rows of `prims` a prelude definition's text names (`τ`, `cons`, `uncat`, `snoc`), each at its list object as
    `rowDens` gives it, for the theorems "the definition's `Tm.den` is the row's `rowDens` term" (B10b). A row's
    signature is restated once, by `rfl`, so a drift of `prims` from it fails here. -/

namespace Rel.Lang

open Rel.Core.Rel hiding id comp recip inter union zero le inl inr junc

/-- The row of `prims` named `s`; a name no row has gives `default`, which no `rowDens` entry answers to, so a
    theorem about it fails to hold rather than holding of the wrong row. -/
def rowOf (s : String) : Prim := (prims.find? (·.sym == s)).getD default

private abbrev B1 : OExp := .var {} "B"

theorem Prim.den_tau {B : Obj} : Prim.den (rowOf "τ") B (.arr B) [] = fun a Y => Y = [a] := by
  have hs : (rowOf "τ").sig = ([], .var {} "A", .list (.var {} "A")) := rfl
  have ho : (rowOf "τ").objs B (.arr B) [] = some [B] := by
    simp [Prim.objs, Prim.vars, hs, Option.orElse, OExp.unify, OExp.vars, List.eraseDups, List.eraseDupsBy,
      List.eraseDupsBy.loop, List.lookup]
  have hf : rowDens.find? (·.1.sym == (rowOf "τ").sym) = some ⟨RowCode.tau, fun _ _ a Y => Y = [a]⟩ := rfl
  unfold Prim.den; simp only [List.map_nil]
  rw [hf, ho]; dsimp only; rw [dif_pos ⟨rfl, rfl⟩]; rfl

theorem Prim.den_cons {B : Obj} :
    Prim.den (rowOf "cons") (.prod B (.arr B)) (.arr B) [] = fun p ys => ys = p.1 :: p.2 := by
  have hs : (rowOf "cons").sig = ([], .prod B1 (.list B1), .list B1) := rfl
  have ho : (rowOf "cons").objs (.prod B (.arr B)) (.arr B) [] = some [B] := by
    simp [Prim.objs, Prim.vars, hs, Option.orElse, OExp.unify, OExp.vars, List.eraseDups, List.eraseDupsBy,
      List.eraseDupsBy.loop, List.lookup]
  have hf : rowDens.find? (·.1.sym == (rowOf "cons").sym) = some ⟨RowCode.cons, fun _ _ p ys => ys = p.1 :: p.2⟩ :=
    rfl
  unfold Prim.den; simp only [List.map_nil]
  rw [hf, ho]; dsimp only; rw [dif_pos ⟨rfl, rfl⟩]; rfl

theorem Prim.den_uncat {B : Obj} :
    Prim.den (rowOf "uncat") (.arr B) (.prod (.arr B) (.arr B)) [] = fun xs p => xs = p.1 ++ p.2 := by
  have hs : (rowOf "uncat").sig = ([], .list B1, .prod (.list B1) (.list B1)) := rfl
  have ho : (rowOf "uncat").objs (.arr B) (.prod (.arr B) (.arr B)) [] = some [B] := by
    simp [Prim.objs, Prim.vars, hs, Option.orElse, OExp.unify, OExp.vars, List.eraseDups, List.eraseDupsBy,
      List.eraseDupsBy.loop, List.lookup]
  have hf : rowDens.find? (·.1.sym == (rowOf "uncat").sym) =
      some ⟨RowCode.uncat, fun _ _ xs p => xs = p.1 ++ p.2⟩ := rfl
  unfold Prim.den; simp only [List.map_nil]
  rw [hf, ho]; dsimp only; rw [dif_pos ⟨rfl, rfl⟩]; rfl

theorem Prim.den_snoc {B : Obj} :
    Prim.den (rowOf "snoc") (.prod (.arr B) B) (.arr B) [] = fun p ys => ys = p.1 ++ [p.2] := by
  have hs : (rowOf "snoc").sig = ([], .prod (.list B1) B1, .list B1) := rfl
  have ho : (rowOf "snoc").objs (.prod (.arr B) B) (.arr B) [] = some [B] := by
    simp [Prim.objs, Prim.vars, hs, Option.orElse, OExp.unify, OExp.vars, List.eraseDups, List.eraseDupsBy,
      List.eraseDupsBy.loop, List.lookup]
  have hf : rowDens.find? (·.1.sym == (rowOf "snoc").sym) =
      some ⟨RowCode.snoc, fun _ _ p ys => ys = p.1 ++ [p.2]⟩ := rfl
  unfold Prim.den; simp only [List.map_nil]
  rw [hf, ho]; dsimp only; rw [dif_pos ⟨rfl, rfl⟩]; rfl

end Rel.Lang
