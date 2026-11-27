import Rel.Lang.Den
import Rel.RepSums

namespace Rel.Lang

/-- The atomic prelude `≥` contains the identity on its universe when `≤` holds on each diagonal pair.
    For integer-stored atoms `ordAt_int` supplies that condition. -/
theorem Tm.geq_refl {t : QAtomicType} {m : USize} {U : Vals (.atom t) m}
    (hrefl : ∀ i, leAt t (U.row i) (U.row i) := by
      intro i
      exact ((Rel.Lang.ordAt_int (by decide)).2 _ _).2 (.inr rfl))
    (ρ : Val) :
    (Tm.den ρ ((Tm.uni U).comp Tm.id)).le
      (Tm.den ρ ((Tm.call [0] `Rel.Programs.prelude.«≥» (some `Rel.Programs.prelude.«≥».conv) [.atom t]
        (Tm.leq (.var 0)).conv).arg (Tm.uni U))) := by
  simp only [Tm.leq, Tm.den, Tm.argDen, Val.args, Val.bind, if_true, and_self, dif_pos,
    Prim.den_cmpRelRow_le, Core.Rel.comp_id]
  refine Core.Rel.le_iff.2 ?_
  rintro a b ⟨i, rfl, rfl⟩
  exact (leqDen_iff t _ _ _).2 ⟨⟨_, i, rfl, rfl⟩, ⟨_, i, rfl, rfl⟩, hrefl i⟩

end Rel.Lang
