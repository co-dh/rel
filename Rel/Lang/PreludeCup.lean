module

public import Rel.Lang.PreludeConcat
public import Rel.Lang.PreludeSetify
public import Rel.Programs.Prelude

@[expose] public section

/-! `cup : [α]×[α] ⟶ [α] ≜ cat setify` (`Programs/Prelude.lean`): the union of two sets, the set of the joined lists.
    Its text is the composite of the rows `cat` and `setify`, so its meaning is `Λ(∋)` of the concatenation. -/

namespace Rel.Lang

open Rel.Core.Rel hiding id comp recip inter union zero le inl inr junc

/-- `cat setify` at the object `B`: the sorted elements, without repeats, of the two lists joined. -/
theorem Tm.cupRow (ρ : Val) {B : Obj} (p : Obj.El (.prod (.arr B) (.arr B))) (zs : Obj.El (.arr B)) :
    ((Tm.prim (rowOf "cat") : Tm (.prod (.arr B) (.arr B)) (.arr B)).comp (Tm.prim (rowOf "setify"))).den ρ p zs ↔
      lamDen (memDen (A := B)) (p.1 ++ p.2) zs := by
  simp only [Tm.den, Core.Rel.comp, Prim.den_cat]
  constructor
  · rintro ⟨q, rfl, h⟩
    exact (Tm.setifyDef_row ρ _ _).2 h
  · intro h
    exact ⟨_, rfl, (Tm.setifyDef_row ρ _ _).1 h⟩

/-- **`cup`'s text is the set of the concatenation**: the body the prelude elaborates, `prelude.cup.body`, at any
    objects `σ`. A law about a call of `cup` takes `(ht : prelude.cup.body.instObj [.general] [B] = .ok t' := by rfl)`
    and states the node `Tm.call [] ``Rel.Programs.prelude.cup cv os t'`. -/
theorem Tm.cupDef_den (ph : List QAtomicType) (σ : List Obj) (ρ : Val)
    {t' : Tm (.prod ((Obj.atom .general).arr.inst ph σ) ((Obj.atom .general).arr.inst ph σ))
      ((Obj.atom .general).arr.inst ph σ)}
    (ht : Rel.Programs.prelude.cup.body.instObj ph σ = .ok t')
    (p : Obj.El (.prod (.arr ((Obj.atom .general).inst ph σ)) (.arr ((Obj.atom .general).inst ph σ))))
    (zs : Obj.El (.arr ((Obj.atom .general).inst ph σ))) :
    t'.den ρ p zs ↔ lamDen memDen (p.1 ++ p.2) zs := by
  obtain rfl : ((Tm.prim (rowOf "cat") : Tm (.prod (.arr ((Obj.atom .general).inst ph σ)) (.arr ((Obj.atom .general).inst ph σ))) (.arr ((Obj.atom .general).inst ph σ))).comp (Tm.prim (rowOf "setify"))) = t' := Except.ok.inj ht
  exact Tm.cupRow ρ p zs

end Rel.Lang
