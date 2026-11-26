import Rel.Lang.Den

/-! A literal with one row is a map: `dom(T) = 𝟙` and `T°T ⊑ 𝟙`. The two laws are about any relation `T` (`dom_of_entire`,
    `simple_of_fun`); `Tm.dom_single` and `Tm.simple_single` read them off a `Tm.val` table of one row, the form a
    `{(∗,0)}` literal takes, so a `theorem t : dom(zero) = 𝟙 by Rel.Lang.Tm.dom_single` closes its goal as it stands. -/

namespace Rel.Lang
open Tab Rel.Rep
open scoped Rel.Core.Rel
open Rel.Core.Rel hiding id comp recip inter union zero le inl inr junc

/-- The domain coreflexive `𝟙 ∩ T T°` of a relation with an image at every point is the identity. -/
theorem dom_of_entire {α β : Type} {T : Core.Rel α β} (h : ∀ a, ∃ b, T a b) : 𝟙 α ∩ T ≫ T° = 𝟙 α :=
  funext fun a => funext fun _ => propext
    ⟨fun e => e.1, fun e => ⟨e, e ▸ (h a).elim fun b hb => ⟨b, hb, hb⟩⟩⟩

/-- A relation with at most one image at every point is simple: `T° T ⊑ 𝟙`. -/
theorem simple_of_fun {α β : Type} {T : Core.Rel α β} (h : ∀ a b b', T a b → T a b' → b = b') : T° ≫ T ⊑ 𝟙 β :=
  Core.Rel.le_iff.2 fun _ _ ⟨a, h₁, h₂⟩ => h a _ _ h₁ h₂

/-- The table `T` of one row at a key of `1` has the single position `0`: its relation is entire. -/
theorem Tab.entire_of_one {B : Obj} (T : Tab .one B) (hn : T.n.toNat = 1) : ∀ a, ∃ b, rep T a b :=
  fun _ => ⟨_, ⟨0, by omega⟩, rfl, rfl⟩

/-- … and simple: any two positions are `0`. -/
theorem Tab.simple_of_one {B : Obj} (T : Tab .one B) (hn : T.n.toNat = 1) : ∀ a b b', rep T a b → rep T a b' → b = b' :=
  fun _ _ _ ⟨i, _, hb⟩ ⟨i', _, hb'⟩ => hb.symm.trans (congrArg T.val.row (Fin.ext (by omega)) ▸ hb')

/-- A literal's length `USize.ofNat n` reads back as `n` on both word sizes. -/
theorem USize.toNat_ofNat_lt {n : Nat} (h : n < 2 ^ 32) : (USize.ofNat n).toNat = n := by
  rw [USize.toNat_ofNat']
  rcases System.Platform.numBits_eq with e | e <;> simp only [e] <;> omega

/-- `dom(T) = 𝟙` for a table `T : 1 ⟶ B` of one row, `U` a universe of `1` with a row (`Tm.uni U ≫ 𝟙` is the identity
    on its values). The side conditions are decided at the table, so the lemma applies by name. -/
theorem Tm.dom_single {B : Obj} {T : Tab .one B} {m : USize} {U : Vals .one m}
    (hn : T.n.toNat = 1 := by first | decide | simp [Rel.Lang.Gen.relV, Rel.Lang.USize.toNat_ofNat_lt]) (hm : 0 < m.toNat := by first | decide | simp [Rel.Lang.Gen.relV, Rel.Lang.USize.toNat_ofNat_lt]) (ρ : Val) :
    Tm.den ρ ((Tm.prim domRow).arg (Tm.val T)) = Tm.den ρ ((Tm.uni U).comp Tm.id) := by
  simp only [Tm.den, Tm.argDen, Prim.den_domRow, Core.Rel.comp_id]
  rw [dom_of_entire (Tab.entire_of_one T hn)]
  exact funext fun a => funext fun _ => propext
    ⟨fun e => ⟨⟨0, hm⟩, rfl, e ▸ rfl⟩, fun _ => rfl⟩

/-- `T° T ⊑ 𝟙` for a table `T : 1 ⟶ B` of one row, `U` a universe of `B` holding its value (`Tm.uni U ≫ 𝟙`). -/
theorem Tm.simple_single {B : Obj} {T : Tab .one B} {m : USize} {U : Vals B m} {k l : Nat}
    (hk : T.n.toNat = k := by exact Rel.Lang.USize.toNat_ofNat_lt (by omega))
    (hl : m.toNat = l := by exact Rel.Lang.USize.toNat_ofNat_lt (by omega))
    (hn : k = 1 := by decide)
    -- the one row is `0`; the lengths are read as literals (`System.Platform.numBits` is opaque to the kernel) and the
    -- column `Gen.atom` rebuilds is then decided by the kernel
    (hU : ∀ i : Fin k, ∃ j : Fin l, U.row (j.cast hl.symm) = T.val.row (i.cast hk.symm) := by
      intro i; obtain rfl : i = ⟨0, by omega⟩ := Fin.ext (by omega)
      simp only [Nat.reducePow, Nat.reduceLT, Rel.Lang.USize.toNat_ofNat_lt, Rel.Enc.wf?, Rel.Lang.Gen.atom,
        Rel.Lang.Gen.relV, Rel.ValsB.row, Rel.ColB.get, Rel.Arr.get, Rel.Arr.getWith, Rel.Enc.get]
      decide +kernel)
    (ρ : Val) :
    (Tm.den ρ ((Tm.val T).conv.comp (Tm.val T))).le (Tm.den ρ ((Tm.uni U).comp Tm.id)) := by
  simp only [Tm.den, Core.Rel.comp_id]
  refine Core.Rel.le_iff.2 fun b b' h => ?_
  obtain rfl : b = b' := Core.Rel.le_iff.1 (simple_of_fun (Tab.simple_of_one T (hk.trans hn))) b b' h
  obtain ⟨_, ⟨i, _, hb⟩, _⟩ := h
  obtain ⟨j, hj⟩ := hU (i.cast hk)
  exact ⟨j.cast hl.symm, (hj.trans hb).symm, (hj.trans hb).symm⟩

end Rel.Lang
