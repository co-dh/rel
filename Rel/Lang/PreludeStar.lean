module

public import Rel.Lang.PreludeRows
public import Rel.Programs.Prelude

@[expose] public section

/-! `star(R : α ⟶ α) : α ⟶ α ≜ μX : 𝟙 ∪ (R X)` (`Programs/Prelude.lean`) means the row `star`'s `rowDens` term, whose
    body is the definition's `μ` body (B10b): the definition's term is built here, the variable `X` numbered `k`, a
    variable `R` does not mention. -/

namespace Rel.Lang

open Rel.Core.Rel hiding id comp recip inter union zero le inl inr junc

/-- `star(P)` at `B ⟶ B`: `μX : 𝟙 ∪ (P X)`, `X` the variable `k`. -/
def Tm.starDef {B : Obj} (k : Nat) (what : String) (cap : Nat) (P : Tm B B) : Tm B B :=
  .mu k what cap (.join .id (.comp P (.var k)))

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

/-- **The definition of `star(P)` means the row**: the least fixed point of `X ↦ 𝟙 ∪ P X`, `P` not mentioning `X`. -/
theorem Tm.starDef_row (ρ : Val) {B : Obj} (k : Nat) (what : String) (cap : Nat) (P : Tm B B)
    (hk : P.fv.contains k = false) (xs ys : Obj.El B) :
    (Tm.starDef k what cap P).den ρ xs ys ↔ Prim.den (rowOf "star") B B [⟨B, B, P.den ρ⟩] xs ys := by
  have hP : ∀ X : Core.Rel (Obj.El B) (Obj.El B), P.den (ρ.bind k X) = P.den ρ := fun X =>
    (P.den_congr _ _ fun i hi => Val.bind_ne (by rintro rfl; simp [hi] at hk)).1
  rw [Prim.den_star]
  have hb : (Tm.starDef k what cap P).den ρ = Core.Rel.mu fun X => 𝟙 _ ∪ P.den ρ ≫ X := by
    simp only [Tm.starDef, Tm.den, hP, Val.bind, if_true]
    rfl
  rw [hb]

/-- **`star`'s text means the row** (Q3 = H): the body the prelude elaborates, `prelude.star.body`, at any objects `σ`
    (`Tm.instObj`), means `star(R)` there, `R` its parameter, the variable 1. The body reads the universe of `α`, the
    variable 0, at the seed and the step (`0 ≫ (𝟙 ∪ R X)`); it is the row where that universe is `𝟙`, the unbounded
    one (`hU`), as `hx : Short` bounds `dom`'s. -/
theorem Tm.starDef_den (ph : List QAtomicType) (σ : List Obj) (ρ : Val)
    {t' : Tm ((Obj.atom .general).inst ph σ) ((Obj.atom .general).inst ph σ)}
    (ht : Rel.Programs.prelude.star.body.instObj ph σ = .ok t')
    (hU : ρ 0 ((Obj.atom .general).inst ph σ) ((Obj.atom .general).inst ph σ) = 𝟙 _) (xs ys) :
    t'.den ρ xs ys ↔ Prim.den (rowOf "star") ((Obj.atom .general).inst ph σ) ((Obj.atom .general).inst ph σ)
      [⟨_, _, ρ 1 ((Obj.atom .general).inst ph σ) ((Obj.atom .general).inst ph σ)⟩] xs ys := by
  obtain rfl := Except.ok.inj ht
  have h := Tm.starDef_row ρ 2 "" 1024 (.var 1 : Tm ((Obj.atom .general).inst ph σ) ((Obj.atom .general).inst ph σ))
    (by simp [Tm.fv]) xs ys
  simp only [Tm.den] at h ⊢
  rw [← h]
  simp only [Tm.starDef, Tm.den, Val.bind_ne (show 0 ≠ 2 by decide), Val.bind_ne (show 1 ≠ 2 by decide), hU]
  simp only [Core.Rel.id_comp]

end Rel.Lang
