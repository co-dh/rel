module

public import Rel.Lang.PreludeRows
public import Rel.Lang.DfnLaw
public import Rel.Programs.Prelude

@[expose] public section

/-! `tails : [α] ⟶ [[α]] ≜ ⦇[nil τ, ⟨⟨π₁,π₂head⟩cons,π₂⟩cons]⦈ʳ` (`Programs/Prelude.lean`) means the row `tails`'s
    `rowDens` term, the suffixes of `xs` longest first (B10b): the definition's term is built here, `head` as
    `Tm.at0`. -/

namespace Rel.Lang

open Rel.Core.Rel hiding id comp recip inter union zero le inl inr junc

/-- The step of `tails` on `(x, acc)`, the head of `acc` read by `hd`: `(x :: hd acc) :: acc`. The prelude's body reads
    it by `call head`, `Tm.tailsDef` by `Tm.at0`; the two agree on a non-empty `acc`, the only one the fold reaches. -/
def Tm.tailsStep (B : Obj) (hd : Tm (.arr (.arr B)) (.arr B)) : Tm (.prod B (.arr (.arr B))) (.arr (.arr B)) :=
  .comp (B := .prod (.arr B) (.arr (.arr B)))
    (.pair (.comp (B := .prod B (.arr B)) (.pair .outl (.comp (B := .arr (.arr B)) .outr hd)) (.prim (rowOf "cons")))
      .outr) (.prim (rowOf "cons"))

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

/-- The step on a non-empty `acc`, wherever `hd` reads the head of a non-empty list. -/
theorem Tm.tailsStep_den (ρ : Val) {B : Obj} (hd : Tm (.arr (.arr B)) (.arr B))
    (hhd : ∀ a as w, hd.den ρ (a :: as) w ↔ w = a) (x : B.El) (acc : List (List B.El)) (hacc : acc ≠ [])
    (w : List (List B.El)) : (Tm.tailsStep B hd).den ρ (x, acc) w ↔ w = (x :: acc.headD []) :: acc := by
  rcases acc with _ | ⟨a, as⟩
  · exact absurd rfl hacc
  simp only [Tm.tailsStep, Tm.den, Prim.den_cons, Core.Rel.comp, Core.Rel.graph, Core.Rel.rpair]
  constructor
  · rintro ⟨b, ⟨⟨b₁, ⟨h1, c, rfl, h2⟩, h3⟩, h4⟩, rfl⟩
    simp [h3, h4, h1, (hhd _ _ _).1 h2]
  · rintro rfl
    exact ⟨(x :: a, a :: as), ⟨⟨(x, a), ⟨rfl, a :: as, rfl, (hhd _ _ _).2 rfl⟩, rfl⟩, rfl⟩, rfl⟩

/-- The fold of `tails`'s step from `[[]]` lists the suffixes, longest first. -/
theorem tails_foldr {α : Type} (xs : List α) : xs.foldr (fun x acc => (x :: acc.headD []) :: acc) [[]] =
    (List.range (xs.length + 1)).map fun k => xs.drop k := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    rw [List.foldr_cons, ih, List.length_cons]
    simp [List.range_succ_eq_map, Function.comp_def]


end Rel.Lang
