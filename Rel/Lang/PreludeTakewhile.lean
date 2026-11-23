module

public import Rel.Lang.PreludeRows
public import Rel.RepSums
public import Rel.Programs.Prelude

@[expose] public section

/-! `takewhile(p : α ⟶ α) : [α] ⟶ [α] ≜ ⦇[nil, dom(π₁p)cons ∪ ((𝟙 − dom(π₁p))nil)]⦈ʳ` (`Programs/Prelude.lean`) means the
    row `takewhile`'s `rowDens` term, `xs.takeWhile` on the elements in `dom p` (B10b): the definition's term is
    built here. -/

namespace Rel.Lang

open Rel.Core.Rel hiding id comp recip inter union zero le inl inr junc
open Classical

/-- The step of `takewhile(P)` on `(x, acc)`: `x :: acc` when `x` is in `dom(P)`, else `[]`. -/
def Tm.takewhileStep {B : Obj} (P : Tm B B) : Tm (.prod B (.arr B)) (.arr B) :=
  let d : Tm (.prod B (.arr B)) (.prod B (.arr B)) := .dom (.comp (A := .prod B (.arr B)) .outl P)
  .join (.comp d (.prim (rowOf "cons"))) (.comp (.diff .id d) .nil)

/-- `takewhile(P)` at `[B] ⟶ [B]`: the right fold from `nil` of `Tm.takewhileStep`. -/
def Tm.takewhileDef {B : Obj} (P : Tm B B) : Tm (.arr B) (.arr B) := .foldr .nil (Tm.takewhileStep P)

theorem Prim.den_takewhile {B : Obj} (T : Core.Rel (Obj.El B) (Obj.El B)) :
    Prim.den (rowOf "takewhile") (.arr B) (.arr B) [⟨B, B, T⟩] =
      fun xs ys => ys = xs.takeWhile fun x => decide (∃ y, T x y) := by
  have hs : (rowOf "takewhile").sig =
      ([((.var {} "B", .var {} "B"), some false)], .list (.var {} "B"), .list (.var {} "B")) := rfl
  have ho : (rowOf "takewhile").objs (.arr B) (.arr B) [(B, B)] = some [B] := by
    simp [Prim.objs, Prim.vars, hs, Option.orElse, OExp.unify, OExp.vars, List.eraseDups, List.eraseDupsBy,
      List.eraseDupsBy.loop, List.lookup]
  have hf : rowDens.find? (·.1.sym == (rowOf "takewhile").sym) = some ⟨RowCode.takewhile, fun σ =>
      Sem.one (X := σ₁ σ) (Y := σ₁ σ) fun T xs ys => ys = xs.takeWhile fun x => decide (∃ y, T x y)⟩ := rfl
  unfold Prim.den; simp only [List.map_cons, List.map_nil]
  rw [hf, ho]; dsimp only; rw [dif_pos ⟨rfl, rfl⟩]
  simp only [Sem.one]; exact dif_pos ⟨rfl, rfl⟩

theorem Tm.takewhileStep_den (ρ : Val) {B : Obj} (P : Tm B B) (x : B.El) (acc : List B.El) (w : List B.El) :
    (Tm.takewhileStep P).den ρ (x, acc) w ↔ w = if ∃ y, P.den ρ x y then x :: acc else [] := by
  simp only [Tm.takewhileStep, Tm.den, Tm.dom_den, Prim.den_cons, Tm.nil, Prim.den_nilRow, Core.Rel.diff, Core.Rel.comp,
    Core.Rel.graph, Core.Rel.union, Core.Rel.inter, Core.Rel.id, Core.Rel.recip]
  by_cases h : ∃ y, den ρ P x y <;> simp [h, eq_comm]
  · obtain ⟨y, hy⟩ := h
    constructor
    · rintro (⟨a, b, ⟨⟨rfl, rfl⟩, _⟩, rfl⟩ | ⟨hn, _⟩)
      · rfl
      · exact (hn y hy).elim
    · rintro rfl; exact Or.inl ⟨x, acc, ⟨⟨rfl, rfl⟩, y, hy, hy⟩, rfl⟩
  · constructor
    · rintro (⟨a, b, ⟨⟨rfl, rfl⟩, b₁, hb₁, _⟩, _⟩ | ⟨_, h₂⟩)
      · exact (h ⟨b₁, hb₁⟩).elim
      · exact h₂
    · rintro rfl; exact Or.inr ⟨fun y hy => h ⟨y, hy⟩, rfl⟩

/-- **The definition of `takewhile(P)` means the row**: the longest prefix of `xs` of elements in `dom P`. -/
theorem Tm.takewhileDef_row (ρ : Val) {B : Obj} (P : Tm B B) (xs ys : Obj.El (.arr B)) :
    (Tm.takewhileDef P).den ρ xs ys ↔
      Prim.den (rowOf "takewhile") (.arr B) (.arr B) [⟨B, B, P.den ρ⟩] xs ys := by
  rw [Prim.den_takewhile]
  have hd : (Tm.takewhileDef P).den ρ = foldrDen nilDen ((Tm.takewhileStep P).den ρ) := by
    simp only [Tm.takewhileDef, Tm.den, Tm.nil, Prim.den_nilRow]
  rw [hd]
  have h := foldrDen_foldr (TS := (Tm.takewhileStep P).den ρ) (I := fun _ => True)
    (f := fun x acc => if ∃ y, P.den ρ x y then x :: acc else [])
    (fun x a _ w => Tm.takewhileStep_den ρ P x a w) (fun _ _ _ => trivial) xs [] trivial ys
  refine h.trans ?_
  have gen : ∀ xs : List B.El, xs.foldr (fun x acc => if ∃ y, P.den ρ x y then x :: acc else []) [] =
      xs.takeWhile fun x => decide (∃ y, P.den ρ x y) := by
    intro xs
    induction xs with
    | nil => simp
    | cons x xs ih => by_cases hx : ∃ y, P.den ρ x y <;> simp [hx, ih]
  rw [gen]

end Rel.Lang
