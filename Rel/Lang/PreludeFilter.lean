module

public import Rel.Lang.PreludeRows
public import Rel.RepSums
public import Rel.Programs.Prelude

@[expose] public section

/-! `filter(p : α ⟶ α) : [α] ⟶ [α] ≜ ⦇[nil, dom(π₂p)snoc ∪ ((𝟙 − dom(π₂p))π₁)]⦈` (`Programs/Prelude.lean`) means the
    row `filter`'s `rowDens` term, `xs.filter` on the elements in `dom p` (B10b): the definition's term is built here. -/

namespace Rel.Lang

open Rel.Core.Rel hiding id comp recip inter union zero le inl inr junc
open Classical

/-- The step of `filter(P)` on `(acc, x)`: `acc` with `x` snoc'd when `x` is in `dom(P)`, else `acc`. -/
def Tm.filterStep {B : Obj} (P : Tm B B) : Tm (.prod (.arr B) B) (.arr B) :=
  let d : Tm (.prod (.arr B) B) (.prod (.arr B) B) := .dom (.comp (A := .prod (.arr B) B) .outr P)
  .join (.comp d (.prim (rowOf "snoc"))) (.comp (.diff .id d) .outl)

/-- `filter(P)` at `[B] ⟶ [B]`: the left fold from `nil` of `Tm.filterStep`. -/
def Tm.filterDef {B : Obj} (P : Tm B B) : Tm (.arr B) (.arr B) := .fold .nil (Tm.filterStep P)

theorem Prim.den_filter {B : Obj} (T : Core.Rel (Obj.El B) (Obj.El B)) :
    Prim.den (rowOf "filter") (.arr B) (.arr B) [⟨B, B, T⟩] =
      fun xs ys => ys = xs.filter fun x => decide (∃ y, T x y) := by
  have hs : (rowOf "filter").sig =
      ([((.var {} "B", .var {} "B"), some false)], .list (.var {} "B"), .list (.var {} "B")) := rfl
  have ho : (rowOf "filter").objs (.arr B) (.arr B) [(B, B)] = some [B] := by
    simp [Prim.objs, Prim.vars, hs, Option.orElse, OExp.unify, OExp.vars, List.eraseDups, List.eraseDupsBy,
      List.eraseDupsBy.loop, List.lookup]
  have hf : rowDens.find? (·.1.sym == (rowOf "filter").sym) = some ⟨RowCode.filter, fun σ =>
      Sem.one (X := σ₁ σ) (Y := σ₁ σ) fun T xs ys => ys = xs.filter fun x => decide (∃ y, T x y)⟩ := rfl
  unfold Prim.den; simp only [List.map_cons, List.map_nil]
  rw [hf, ho]; dsimp only; rw [dif_pos ⟨rfl, rfl⟩]
  simp only [Sem.one]; exact dif_pos ⟨rfl, rfl⟩

theorem Tm.filterStep_den (ρ : Val) {B : Obj} (P : Tm B B) (acc : List B.El) (x : B.El) (w : List B.El) :
    (Tm.filterStep P).den ρ (acc, x) w ↔ w = if ∃ y, P.den ρ x y then acc ++ [x] else acc := by
  simp only [Tm.filterStep, Tm.den, Tm.dom_den, Prim.den_snoc, Core.Rel.diff, Core.Rel.comp, Core.Rel.graph,
    Core.Rel.union, Core.Rel.inter, Core.Rel.id, Core.Rel.recip]
  by_cases h : ∃ y, den ρ P x y <;> simp [h, eq_comm]
  · obtain ⟨y, hy⟩ := h
    constructor
    · rintro (⟨a, b, ⟨⟨rfl, rfl⟩, _⟩, rfl⟩ | ⟨x₁, ⟨rfl, rfl⟩, hn⟩)
      · rfl
      · exact (hn rfl rfl y hy hy).elim
    · rintro rfl; exact Or.inl ⟨acc, x, ⟨⟨rfl, rfl⟩, y, hy, hy⟩, rfl⟩
  · constructor
    · rintro (⟨a, b, ⟨⟨rfl, rfl⟩, b₁, hb₁, _⟩, _⟩ | ⟨x₁, ⟨h₁, _⟩, _⟩)
      · exact (h ⟨b₁, hb₁⟩).elim
      · exact h₁
    · rintro rfl; exact Or.inr ⟨x, ⟨rfl, rfl⟩, fun _ _ x₂ hx _ => (h ⟨x₂, hx⟩).elim⟩

end Rel.Lang
