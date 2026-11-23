module

public import Rel.Lang.PreludeRows
public import Rel.Programs.Prelude

@[expose] public section

/-! `setify : [α] ⟶ [α] ≜ Λ(∋)` (`Programs/Prelude.lean`) means the row `setify`'s `rowDens` term, `lamDen memDen`
    (B10b): the definition's term is `Tm.lam Tm.mem`. -/

namespace Rel.Lang

open Rel.Core.Rel hiding id comp recip inter union zero le inl inr junc

/-- The prelude's `setify = Λ(∋)` at `[B] ⟶ [B]`. -/
def Tm.setifyDef (B : Obj) : Tm (.arr B) (.arr B) := .lam .mem

/-- **The definition of `setify` means the row**: `Λ(∋)`, the sorted elements of `xs` without repeats. -/
theorem Tm.setifyDef_row (ρ : Val) {B : Obj} (xs ys : Obj.El (.arr B)) :
    (Tm.setifyDef B).den ρ xs ys ↔ Prim.den (rowOf "setify") (.arr B) (.arr B) [] xs ys := by
  have hs : (rowOf "setify").sig = ([], .list (.var {} "B"), .list (.var {} "B")) := rfl
  have ho : (rowOf "setify").objs (.arr B) (.arr B) [] = some [B] := by
    simp [Prim.objs, Prim.vars, hs, Option.orElse, OExp.unify, OExp.vars, List.eraseDups, List.eraseDupsBy,
      List.eraseDupsBy.loop, List.lookup]
  have hf : rowDens.find? (·.1.sym == (rowOf "setify").sym) =
      some ⟨RowCode.setify, fun σ _ => lamDen (memDen (A := σ₁ σ))⟩ := rfl
  unfold Prim.den; simp only [List.map_nil]
  rw [hf, ho]; dsimp only; rw [dif_pos ⟨rfl, rfl⟩]; rfl

/-- **`setify`'s text means the row** (Q3 = H, as `Tm.prefixDef_den`). -/
theorem Tm.setifyDef_den (ph : List QAtomicType) (σ : List Obj) (ρ : Val) {t' : Tm ((Obj.atom .general).arr.inst ph σ)
    ((Obj.atom .general).arr.inst ph σ)} (ht : Rel.Programs.prelude.setify.body.instObj ph σ = .ok t')
    (xs ys : Obj.El ((Obj.atom .general).arr.inst ph σ)) :
    t'.den ρ xs ys ↔ Prim.den (rowOf "setify") ((Obj.atom .general).arr.inst ph σ) ((Obj.atom .general).arr.inst ph σ)
      [] xs ys := by
  obtain rfl : Tm.setifyDef ((Obj.atom .general).inst ph σ) = t' := Except.ok.inj ht
  exact Tm.setifyDef_row ρ xs ys

end Rel.Lang
