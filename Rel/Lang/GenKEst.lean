import Rel.Lang.GenKBits

/-! The `GenK` ops of the power operators `est` and `atPos`, each representing its constructor's case of `Tm.den`
    from the op's `Tab` law (`Tab.est_holds`, `Tab.atPos_holds`), in `GenKSpec`'s style (`ofVals_row_sound`). -/

namespace Rel.Lang

open Rel Rel.Rep Rel.Kernel Rel.Verify Gen
open scoped Rel.Core.Rel
open Rel.Core.Rel hiding id comp recip inter union zero le inl inr junc

namespace GenK

/-- `est(Q)` (`GenK.est`): `Q` run on the pairs `D` it is asked about represents `TQ` there (`side_some`). -/
theorem est_sound {B : Obj} {Q : Rel (.prod B B) (.prod B B)} {TQ : Den (.prod B B) (.prod B B)}
    (hQ : ∀ K, Q.Reps K TQ) : ∀ K, (GenK.est B Q).Reps K (estDen TQ) :=
  ofVals_row_sound fun _ _ _ h => Tab.est_holds
    (fun D _ hT p hp => (reps_iff ⟨some ⟨D.n, D.val⟩, none, none⟩ _ _).1 (hQ _) _ hT p _ ((side_some rfl p).2 hp) rfl trivial) h

/-- `thin(Q)` (`GenK.thin`): `Q` as in `est_sound`, and `Λ`'s order law at `[B] ⟶ B` (`lam_sound`'s `hB`). -/
theorem thin_sound {B : Obj} {Q : Rel (.prod B B) (.prod B B)} {TQ : Den (.prod B B) (.prod B B)}
    (hQ : ∀ K, Q.Reps K TQ)
    (hB : ∀ (m : USize) (x : Vals (.prod (.arr B) B) m) es, Vals.cols x = .ok es → ∀ i i' : Fin m.toNat,
      (x.row i).1 = (x.row i').1 → lexLe (ascKeys m es) i i' = true → seenKey m es i ≠ seenKey m es i' →
        B.lt (x.row i).2 (x.row i').2) :
    ∀ K, (GenK.thin B Q).Reps K (thinDen TQ) :=
  ofVals_row_sound fun _ _ _ h => Tab.thin_den
    (fun D _ hT p hp => (reps_iff ⟨some ⟨D.n, D.val⟩, none, none⟩ _ _).1 (hQ _) _ hT p _ ((side_some rfl p).2 hp) rfl trivial) h hB

theorem atPos_sound {B : Obj} (k : Nat) : ∀ K, (GenK.atPos B k).Reps K (atDen k) :=
  ofVals_row_sound fun _ _ _ h => Tab.atPos_holds h

end GenK

end Rel.Lang
