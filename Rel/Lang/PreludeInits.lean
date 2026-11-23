module

public import Rel.Lang.PreludeRows
public import Rel.Lang.GenSound
public import Rel.Programs.Prelude

@[expose] public section

/-! `inits : [α] ⟶ [[α]] ≜ Λ(prefix)` (`Programs/Prelude.lean`) means the row `inits`'s `rowDens` term, the prefixes
    of `xs`, shortest first (B10b): the definition's term is `Λ` of the row `prefix`, which the body keeps as a row. -/

namespace Rel.Lang

open Rel.Core.Rel hiding id comp recip inter union zero le inl inr junc

/-- The prelude's `inits = Λ(prefix)` at `[B] ⟶ [[B]]`. -/
def Tm.initsDef (B : Obj) : Tm (.arr B) (.arr (.arr B)) := .lam (.prim (rowOf "prefix"))

/-- **The definition of `inits` means the row**: `Λ(prefix)` lists the prefixes of `xs`, shortest first. -/
theorem Tm.initsDef_row (ρ : Val) {B : Obj} (xs : Obj.El (.arr B)) (yss : Obj.El (.arr (.arr B))) :
    (Tm.initsDef B).den ρ xs yss ↔ Prim.den (rowOf "inits") (.arr B) (.arr (.arr B)) [] xs yss := by
  have hs : (rowOf "inits").sig = ([], .list (.var {} "B"), .list (.list (.var {} "B"))) := rfl
  have ho : (rowOf "inits").objs (.arr B) (.arr (.arr B)) [] = some [B] := by
    simp [Prim.objs, Prim.vars, hs, Option.orElse, OExp.unify, OExp.vars, List.eraseDups, List.eraseDupsBy,
      List.eraseDupsBy.loop, List.lookup]
  have hf : rowDens.find? (·.1.sym == (rowOf "inits").sym) = some ⟨RowCode.inits, fun _ _ xs yss =>
      yss = (List.range (xs.length + 1)).map fun k => xs.take k⟩ := rfl
  have hps : (rowOf "prefix").sig = ([], .list (.var {} "B"), .list (.var {} "B")) := rfl
  have hpo : (rowOf "prefix").objs (.arr B) (.arr B) [] = some [B] := by
    simp [Prim.objs, Prim.vars, hps, Option.orElse, OExp.unify, OExp.vars, List.eraseDups, List.eraseDupsBy,
      List.eraseDupsBy.loop, List.lookup]
  have hpf : rowDens.find? (·.1.sym == (rowOf "prefix").sym) =
      some ⟨RowCode.prefix, fun σ _ => splitDen true (σ₁ σ).El⟩ := rfl
  have hr : ∀ ys, Prim.den (rowOf "prefix") (.arr B) (.arr B) [] xs ys ↔ (ys <+: xs) := fun ys => by
    unfold Prim.den; simp only [List.map_nil]
    rw [hpf, hpo]; dsimp only; rw [dif_pos ⟨rfl, rfl⟩]; exact splitDen_iff _ xs ys
  have hi : Prim.den (rowOf "inits") (.arr B) (.arr (.arr B)) [] xs yss ↔
      yss = (List.range (xs.length + 1)).map fun k => xs.take k := by
    unfold Prim.den; simp only [List.map_nil]
    rw [hf, ho]; dsimp only; rw [dif_pos ⟨rfl, rfl⟩]
  rw [hi]
  exact lamDen_inits xs hr yss

/-- **`inits`'s text means the row** (Q3 = H, as `Tm.prefixDef_den`). -/
theorem Tm.initsDef_den (ph : List QAtomicType) (σ : List Obj) (ρ : Val) {t' : Tm ((Obj.atom .general).arr.inst ph σ)
    ((Obj.atom .general).arr.arr.inst ph σ)} (ht : Rel.Programs.prelude.inits.body.instObj ph σ = .ok t')
    (xs yss) :
    t'.den ρ xs yss ↔ Prim.den (rowOf "inits") ((Obj.atom .general).arr.inst ph σ)
      ((Obj.atom .general).arr.arr.inst ph σ) [] xs yss := by
  obtain rfl : Tm.initsDef ((Obj.atom .general).inst ph σ) = t' := Except.ok.inj ht
  exact Tm.initsDef_row ρ xs yss

end Rel.Lang
