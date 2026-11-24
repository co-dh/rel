module

public import Rel.Lang.PreludeRows
public import Rel.Lang.PreludeCat
public import Rel.Lang.PreludeTau
public import Rel.Programs.Prelude

@[expose] public section

/-! `snoc : [α]×α ⟶ [α] ≜ (𝟙×τ) cat` (`Programs/Prelude.lean`) means the row `snoc`'s `rowDens` term `xs ++ [x]`
    (B10b): the definition's term is the rows `τ` and `cat` composed, `τ` making the one-element list of `x`. -/

namespace Rel.Lang

open Rel.Core.Rel hiding id comp recip inter union zero le inl inr junc

/-- `snoc` at `[B]×B ⟶ [B]`: `prelude.snoc.body` as the term the elaborator builds, `(𝟙×τ)` as `⟨π₁ 𝟙, π₂ τ⟩`. -/
def Tm.snocDef (B : Obj) : Tm (.prod (.arr B) B) (.arr B) :=
  .comp (.pair (.comp .outl .id) (.comp .outr (.prim (rowOf "τ") : Tm B (.arr B)))) (.prim (rowOf "cat") : Tm (.prod (.arr B) (.arr B)) (.arr B))

/-- **The definition of `snoc` means the row**: `zs` is `xs ++ [x]`. -/
theorem Tm.snocDef_row (ρ : Val) {B : Obj} (p : (Obj.prod (.arr B) B).El) (zs : (Obj.arr B).El) :
    (Tm.snocDef B).den ρ p zs ↔ Prim.den (rowOf "snoc") (.prod (.arr B) B) (.arr B) [] p zs := by
  rw [Prim.den_snoc]
  obtain ⟨xs, x⟩ := p
  simp only [Tm.snocDef, Tm.den, Prim.den_tau, Prim.den_cat, Core.Rel.comp, Core.Rel.rpair, Core.Rel.graph,
    Core.Rel.id, Prod.exists]
  simp
  exact ⟨fun ⟨_, _, ⟨rfl, rfl⟩, h⟩ => h, fun h => ⟨_, _, ⟨rfl, rfl⟩, h⟩⟩

/-- **`snoc`'s text means the row** (Q3 = G): `prelude.snoc.body` at any objects `σ` means `snoc` there. -/
theorem Tm.snocDef_den (ph : List QAtomicType) (σ : List Obj) (ρ : Val)
    {t' : Tm (Obj.prod (Obj.arr ((Obj.atom .general).inst ph σ)) ((Obj.atom .general).inst ph σ))
      (Obj.arr ((Obj.atom .general).inst ph σ))}
    (ht : Rel.Programs.prelude.snoc.body.instObj ph σ = .ok t') (p zs) :
    t'.den ρ p zs ↔ Prim.den (rowOf "snoc") (.prod (.arr ((Obj.atom .general).inst ph σ)) ((Obj.atom .general).inst ph σ))
      (.arr ((Obj.atom .general).inst ph σ)) [] p zs := by
  obtain rfl : Tm.snocDef _ = t' := Except.ok.inj ht
  exact Tm.snocDef_row ρ p zs

end Rel.Lang
