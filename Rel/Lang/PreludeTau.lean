module

public import Rel.Lang.PreludeRows
public import Rel.Programs.Prelude
public import Rel.ObjOrder

@[expose] public section

/-! `τ : α ⟶ [α] ≜ Λ(𝟙)` (`Programs/Prelude.lean`) means the row `τ`'s `rowDens` term, `graph fun a => [a]`: the
    definition's term is `Tm.lam Tm.id`. -/

namespace Rel.Lang

open Rel.Core.Rel hiding id comp recip inter union zero le inl inr junc

/-- The prelude's `τ = Λ(𝟙)` at `B ⟶ [B]`. -/
def Tm.tauDef (B : Obj) : Tm B (.arr B) := .lam .id

/-- **The definition of `τ` means the row**: `Λ(𝟙)` sends `a` to the one list `[a]`. -/
theorem Tm.tauDef_row (ρ : Val) {B : Obj} (a : Obj.El B) (ys : Obj.El (.arr B)) :
    (Tm.tauDef B).den ρ a ys ↔ Prim.den (rowOf "τ") B (.arr B) [] a ys := by
  rw [Prim.den_tau]
  refine (lamDen_iff _ a ys).trans ⟨fun ⟨hp, h⟩ => ?_, fun h => ?_⟩
  · match ys, hp, h with
    | [], _, h => exact absurd ((h a).2 rfl) (List.not_mem_nil)
    | [b], _, h => have hb : a = b := (h b).1 (by simp); show [b] = [a]; rw [hb]
    | b :: c :: ys, hp, h =>
      have hb : a = b := (h b).1 (by simp)
      have hc : a = c := (h c).1 (by simp)
      have hl := (List.pairwise_cons.1 hp).1 c (by simp)
      obtain rfl : b = c := hb.symm.trans hc
      exact absurd hl (Obj.lt_asymm _ hl)
  · obtain rfl : ys = [a] := h
    exact ⟨by simp, fun b => ⟨fun hb => (List.mem_singleton.1 hb).symm, fun hb => by rw [← hb]; simp⟩⟩

/-- **`τ`'s text means the row** (Q3 = H, as `Tm.setifyDef_den`). -/
theorem Tm.τDef_den (ph : List QAtomicType) (σ : List Obj) (ρ : Val) {t' : Tm ((Obj.atom .general).inst ph σ)
    ((Obj.atom .general).arr.inst ph σ)} (ht : Rel.Programs.prelude.τ.body.instObj ph σ = .ok t')
    (a ys) :
    t'.den ρ a ys ↔ Prim.den (rowOf "τ") ((Obj.atom .general).inst ph σ) ((Obj.atom .general).arr.inst ph σ) [] a ys := by
  obtain rfl : Tm.tauDef ((Obj.atom .general).inst ph σ) = t' := Except.ok.inj ht
  exact Tm.tauDef_row ρ a ys

end Rel.Lang
