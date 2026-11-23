module

public import Rel.Lang.PreludeRows
public import Rel.Lang.DfnLaw

@[expose] public section

/-! `tails : [α] ⟶ [[α]] ≜ ⦇[nil τ, ⟨⟨π₁,π₂head⟩cons,π₂⟩cons]⦈ʳ` (`Programs/Prelude.lean`) means the row `tails`'s
    `rowDens` term, the suffixes of `xs` longest first (B10b): the definition's term is built here, `head` as
    `Tm.at0`. -/

namespace Rel.Lang

open Rel.Core.Rel hiding id comp recip inter union zero le inl inr junc

/-- The step of `tails` on `(x, acc)`: `(x :: head acc) :: acc`. -/
def Tm.tailsStep (B : Obj) : Tm (.prod B (.arr (.arr B))) (.arr (.arr B)) :=
  .comp (B := .prod (.arr B) (.arr (.arr B)))
    (.pair (.comp (B := .prod B (.arr B)) (.pair .outl (.comp (B := .arr (.arr B)) .outr .at0)) (.prim (rowOf "cons")))
      .outr) (.prim (rowOf "cons"))

/-- `tails` at `[B] ⟶ [[B]]`: the right fold from `nil τ` of `Tm.tailsStep`. -/
def Tm.tailsDef (B : Obj) : Tm (.arr B) (.arr (.arr B)) :=
  .foldr (.comp (B := .arr B) .nil (.prim (rowOf "τ"))) (Tm.tailsStep B)

theorem Prim.den_tails {B : Obj} :
    Prim.den (rowOf "tails") (.arr B) (.arr (.arr B)) [] =
      fun xs yss => yss = (List.range (xs.length + 1)).map fun k => xs.drop k := by
  have hs : (rowOf "tails").sig = ([], .list (.var {} "B"), .list (.list (.var {} "B"))) := rfl
  have ho : (rowOf "tails").objs (.arr B) (.arr (.arr B)) [] = some [B] := by
    simp [Prim.objs, Prim.vars, hs, Option.orElse, OExp.unify, OExp.vars, List.eraseDups, List.eraseDupsBy,
      List.eraseDupsBy.loop, List.lookup]
  have hf : rowDens.find? (·.1.sym == (rowOf "tails").sym) = some ⟨RowCode.tails, fun _ _ xs yss =>
      yss = (List.range (xs.length + 1)).map fun k => xs.drop k⟩ := rfl
  unfold Prim.den; simp only [List.map_nil]
  rw [hf, ho]; dsimp only; rw [dif_pos ⟨rfl, rfl⟩]; rfl

theorem Tm.tailsStep_den (ρ : Val) {B : Obj} (x : B.El) (acc : List (List B.El)) (hacc : acc ≠ [])
    (w : List (List B.El)) : (Tm.tailsStep B).den ρ (x, acc) w ↔ w = (x :: acc.headD []) :: acc := by
  rcases acc with _ | ⟨a, as⟩
  · exact absurd rfl hacc
  simp only [Tm.tailsStep, Tm.den, Prim.den_cons, Tm.at0_den, Core.Rel.comp, Core.Rel.graph, Core.Rel.rpair]
  constructor
  · rintro ⟨b, ⟨⟨b₁, ⟨h1, c, rfl, h0, h2⟩, h3⟩, h4⟩, rfl⟩
    simp [h3, h4, h1, h2]
  · rintro rfl
    exact ⟨(x :: a, a :: as), ⟨⟨(x, a), ⟨rfl, a :: as, rfl, by simp, rfl⟩, rfl⟩, rfl⟩, rfl⟩

theorem Tm.tailsSeed_den (ρ : Val) {B : Obj} :
    (Tm.comp (B := .arr B) (A := .arr (.arr B)) Tm.nil (.prim (rowOf "τ"))).den ρ = (fun _ b => b = [[]] : Core.Rel (Obj.El (.arr (.arr B))) (Obj.El (.arr (.arr B)))) := by
  funext a v
  simp [Tm.den, Tm.nil, Prim.den_nilRow, Prim.den_tau, nilDen, Core.Rel.comp]

/-- **The definition of `tails` means the row**: the suffixes of `xs`, longest first. -/
theorem Tm.tailsDef_row (ρ : Val) {B : Obj} (xs : Obj.El (.arr B)) (yss : Obj.El (.arr (.arr B))) :
    (Tm.tailsDef B).den ρ xs yss ↔ Prim.den (rowOf "tails") (.arr B) (.arr (.arr B)) [] xs yss := by
  rw [Prim.den_tails]
  have hd : (Tm.tailsDef B).den ρ = foldrDen (fun _ b => b = [[]]) ((Tm.tailsStep B).den ρ) := by
    have hs := Tm.tailsSeed_den (B := B) ρ
    unfold Tm.tailsDef; simp only [Tm.den] at hs ⊢; rw [hs]
  rw [hd]
  have h := foldrDen_foldr (TS := (Tm.tailsStep B).den ρ) (I := fun a => a ≠ [])
    (f := fun x acc => (x :: acc.headD []) :: acc)
    (fun x a ha w => Tm.tailsStep_den ρ x a ha w) (fun _ _ _ => List.cons_ne_nil _ _) xs [[]]
    (List.cons_ne_nil _ _) yss
  refine h.trans ?_
  have gen : ∀ xs : List B.El, xs.foldr (fun x acc => (x :: acc.headD []) :: acc) [[]] =
      (List.range (xs.length + 1)).map fun k => xs.drop k := by
    intro xs
    induction xs with
    | nil => simp
    | cons x xs ih =>
      rw [List.foldr_cons, ih, List.length_cons]
      simp [List.range_succ_eq_map, Function.comp_def]
  rw [gen]

end Rel.Lang
