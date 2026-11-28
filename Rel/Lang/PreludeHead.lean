module

public import Rel.Lang.PreludeMerge

@[expose] public section

/-! `head ≜ at(0)` (`Programs/Prelude.lean`) is a call whose body is `Tm.headAt`, and `head°` a call whose body is
    `at° ⟨π₁,π₂⟩ dom(π₂ ∩ π₁⊤₀) π₁` (the converse of a body is restricted to the index `0`). Both mean
    `xs[0] = b` on a nonempty `xs`. -/

namespace Rel.Lang

open Rel.Core.Rel hiding id comp recip inter union zero le inl inr junc

/-- The body of `head.conv` as the prelude elaborates it. -/
def Tm.headConvBody {B : Obj} : Tm B (.arr B) :=
  .comp (Tm.conv (Tm.prim indexRow : Tm (.prod (.arr B) (.atom .i64)) B))
    (.comp (.pair (.comp .outl .id) .outr) (.comp (.dom (.meet .outr (.comp .outl Tm.zeroTop))) .outl))

theorem Tm.zeroTop_den (ρ : Val) {A : Obj} (x : A.El) (n : Int64) : (Tm.zeroTop (A := A)).den ρ x n ↔ n = 0 := by
  have hz := Tm.zeroLit_den ρ
  simp only [Tm.den] at hz
  have h0 : ∀ i, ValsB.row (o := false) (A := .atom .i64) (zeroCol .i64 rfl) i = (0 : Int64) := fun i => by
    rw [zeroCol_row]; rfl
  simp only [Tm.zeroTop, Tm.den, Gen.atom_zero, hz, Core.Rel.comp, Core.Rel.recip, Core.Rel.graph, Core.Rel.top, h0]
  exact ⟨fun ⟨_, _, _, _, h⟩ => h, fun h => ⟨0, trivial, ⟨0, by simp⟩, rfl, h⟩⟩

theorem Tm.headConvBody_den (ρ : Val) {B : Obj} (b : B.El) (xs : List B.El) :
    (Tm.headConvBody (B := B)).den ρ b xs ↔ ∃ h : 0 < xs.length, b = xs[0]'h := by
  rw [← Tm.headAt_den ρ]
  simp only [Tm.headConvBody, Tm.headAt, Tm.den, Tm.dom_den, Core.Rel.comp, Core.Rel.recip, Core.Rel.graph, Core.Rel.id,
    Core.Rel.inter, Core.Rel.rpair, Tm.zeroTop_den, Prod.exists]
  grind

theorem Tm.headDef_den (ph : List QAtomicType) (σ : List Obj) (ρ : Val)
    {t' : Tm ((Obj.atom .general).inst ph σ).arr ((Obj.atom .general).inst ph σ)}
    (ht : Rel.Programs.prelude.head.body.instObj ph σ = .ok t')
    (xs : Obj.El ((Obj.atom .general).inst ph σ).arr) (b : Obj.El ((Obj.atom .general).inst ph σ)) :
    t'.den ρ xs b ↔ ∃ h : 0 < xs.length, b = xs[0]'h := by
  obtain rfl := Except.ok.inj ht
  exact Tm.headAt_den ρ xs b

end Rel.Lang
