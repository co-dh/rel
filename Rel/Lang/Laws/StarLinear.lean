module

public import Rel.Lang.PreludeRows
public import Rel.Core.Fix

@[expose] public section

namespace Rel.Lang
open Rel.Kernel Tab Rel.Rep
open scoped Rel.Core.Rel
open Rel.Core.Rel hiding id comp recip inter union zero le inl inr junc

theorem Prim.den_star {B : Obj} (T : Core.Rel (Obj.El B) (Obj.El B)) :
    Prim.den (rowOf "star") B B [⟨B, B, T⟩] = Core.Rel.mu fun X => 𝟙 _ ∪ T ≫ X := by
  have hs : (rowOf "star").sig = ([((.var {} "B", .var {} "B"), some false)], .var {} "B", .var {} "B") := rfl
  have ho : (rowOf "star").objs B B [(B, B)] = some [B] := by
    simp [Prim.objs, Prim.vars, hs, Option.orElse, OExp.unify, OExp.vars, List.eraseDups, List.eraseDupsBy,
      List.eraseDupsBy.loop, List.lookup]
  have hf : rowDens.find? (·.1.sym == (rowOf "star").sym) = some ⟨RowCode.star, fun σ =>
      Sem.one (X := σ₁ σ) (Y := σ₁ σ) fun T => Core.Rel.mu fun X => 𝟙 _ ∪ T ≫ X⟩ := rfl
  unfold Prim.den; simp only [List.map_cons, List.map_nil]
  rw [hf, ho]; dsimp only; rw [dif_pos ⟨rfl, rfl⟩]
  simp only [Sem.one]; exact dif_pos ⟨rfl, rfl⟩

/-- The prelude's `starLinear`: the `μ` of `S ∪ R X` (`R`, `S` the variables 0, 1, `X` the variable 2) is `star(R) S`. -/
theorem Tm.starLinear_den {A B : Obj} {what : String} {cap : Nat} (ρ : Val) :
    (Tm.mu 2 what cap (.join (.var 1) (.comp (.var 0 : Tm A A) (.var 2 : Tm A B))) : Tm A B).den ρ =
      (Tm.comp (.arg (.prim (rowOf "star") : Tm A A) (.var 0 : Tm A A)) (.var 1 : Tm A B)).den ρ := by
  simp only [Tm.den, Tm.argDen, Prim.den_star, Val.bind_ne (show 0 ≠ 2 by decide),
    Val.bind_ne (show 1 ≠ 2 by decide), Val.bind, if_true]
  exact Core.Rel.starLinear _ _

end Rel.Lang
