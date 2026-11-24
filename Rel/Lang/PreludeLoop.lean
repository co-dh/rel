module

public import Rel.Lang.PreludeRows
public import Rel.Lang.DfnLaw
public import Rel.Programs.Prelude

@[expose] public section

/-! `loop(T : χ×υ ⟶ χ) : χ×[υ] ⟶ χ ≜ foldI(⟨𝟙,𝟙⟩, ⟨π₁π₁, ⟨π₁π₂,π₂⟩T⟩)` (`Programs/Prelude.lean`) means the row
    `loop`'s `rowDens` term `loopDen` (B10b): the definition's term is `foldI` of the key as the start and the step
    keeping the key. -/

namespace Rel.Lang

open Rel.Core.Rel hiding id comp recip inter union zero le inl inr junc

/-- The prelude's `loop(T)` at `X×[Y] ⟶ X`: `foldI` seeded with `⟨𝟙,𝟙⟩`, the step `⟨π₁π₁, ⟨π₁π₂,π₂⟩T⟩`. -/
def Tm.loopDef {X Y : Obj} (T : Tm (.prod X Y) X) : Tm (.prod X (.arr Y)) X :=
  .arg (.arg (.prim foldIRow) (.pair .id .id : Tm X (.prod X X)))
    (.pair (.comp .outl .outl) (.comp (.pair (.comp .outl .outr) .outr) T) : Tm (.prod (.prod X X) Y) (.prod X X))

theorem Prim.den_loopRow {X Y : Obj} (T : Core.Rel (Obj.El (.prod X Y)) (Obj.El X)) :
    Prim.den (rowOf "loop") (.prod X (.arr Y)) X [⟨.prod X Y, X, T⟩] = loopDen T := by
  have hs : (rowOf "loop").sig = ([((.prod (.var {} "X") (.var {} "Y"), .var {} "X"), some false)],
      .prod (.var {} "X") (.list (.var {} "Y")), .var {} "X") := rfl
  have ho : (rowOf "loop").objs (.prod X (.arr Y)) X [(.prod X Y, X)] = some [X, Y] := by
    simp [Prim.objs, Prim.vars, hs, Option.orElse, OExp.unify, OExp.vars, List.eraseDups, List.eraseDupsBy,
      List.eraseDupsBy.loop, List.lookup]
  have hf : rowDens.find? (·.1.sym == (rowOf "loop").sym) = some ⟨RowCode.loop, fun σ =>
      Sem.one (X := .prod (σ₁ σ) (σ₂ σ)) (Y := σ₁ σ) loopDen⟩ := rfl
  unfold Prim.den; simp only [List.map_cons, List.map_nil]
  rw [hf, ho]; dsimp only; rw [dif_pos ⟨rfl, rfl⟩]
  simp only [Sem.one]; exact dif_pos ⟨rfl, rfl⟩

/-- **The definition of `loop(T)` means the row**: the left fold of `T` from the pair's own first component. -/
theorem Tm.loopDef_row (ρ : Val) {X Y : Obj} (T : Tm (.prod X Y) X) :
    (Tm.loopDef T).den ρ = Prim.den (rowOf "loop") (.prod X (.arr Y)) X [⟨.prod X Y, X, T.den ρ⟩] := by
  rw [Prim.den_loopRow]
  simp only [Tm.loopDef, Tm.den, Tm.argDen, Prim.den_foldIRow, loopDen]
  congr 1
  · funext x p; apply propext
    simp [Core.Rel.rpair, Core.Rel.id, Core.Rel.graph]
    constructor
    · rintro ⟨rfl, h⟩; exact Prod.ext rfl h.symm
    · rintro rfl; exact ⟨rfl, rfl⟩
  · funext x p; apply propext
    simp [Core.Rel.rpair, Core.Rel.rprodMap, Core.Rel.comp, Core.Rel.graph, Core.Rel.id]
    intro _; exact exists_congr fun a => exists_congr fun b => and_congr (and_congr Iff.rfl eq_comm) Iff.rfl

/-- **`loop`'s text means the row** (Q3 = H): the body the prelude elaborates, `prelude.loop.body` (placeholders
    `general`, `u1` of `χ`, `υ`; its parameter `T` the variable 2), at any objects `σ` (`Tm.instObj`) means the row. -/
theorem Tm.loopDef_den (ph : List QAtomicType) (σ : List Obj) (ρ : Val)
    {t' : Tm (((Obj.atom .general).prod (Obj.atom .u1).arr).inst ph σ) ((Obj.atom .general).inst ph σ)}
    (ht : Rel.Programs.prelude.loop.body.instObj ph σ = .ok t') (x y) :
    t'.den ρ x y ↔ Prim.den (rowOf "loop") (((Obj.atom .general).prod (Obj.atom .u1).arr).inst ph σ)
      ((Obj.atom .general).inst ph σ)
      [⟨((Obj.atom .general).prod (Obj.atom .u1)).inst ph σ, (Obj.atom .general).inst ph σ,
        (Tm.var 2 : Tm (((Obj.atom .general).prod (Obj.atom .u1)).inst ph σ) ((Obj.atom .general).inst ph σ)).den ρ⟩] x y := by
  unfold Rel.Programs.prelude.loop.body at ht
  simp [Tm.instObj] at ht
  obtain rfl : Tm.loopDef (.var 2) = t' := Except.ok.inj ht
  rw [Tm.loopDef_row]; exact Iff.rfl

end Rel.Lang
