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
    (hQ : ∀ K, K.WF → Q.Reps K TQ) : ∀ K, K.WF → (GenK.est B Q).Reps K (estDen TQ) :=
  ofVals_row_sound fun _ _ _ hX h => Tab.est_holds (fun D _ wD hT p hp => (reps_iff ⟨some ⟨D.n, D.val⟩, none, none⟩ _ _).1
    (hQ _ ⟨wD.2, trivial, trivial⟩) _ hT p _ ((side_some rfl p).2 hp) rfl trivial) h hX

/-- `thin(Q)` (`GenK.thin`): `Q` as in `est_sound`. -/
theorem thin_sound {B : Obj} {Q : Rel (.prod B B) (.prod B B)} {TQ : Den (.prod B B) (.prod B B)}
    (hQ : ∀ K, K.WF → Q.Reps K TQ) : ∀ K, K.WF → (GenK.thin B Q).Reps K (thinDen TQ) :=
  ofVals_row_sound fun _ _ _ hX h => Tab.thin_den (fun D _ wD hT p hp => (reps_iff ⟨some ⟨D.n, D.val⟩, none, none⟩ _ _).1
    (hQ _ ⟨wD.2, trivial, trivial⟩) _ hT p _ ((side_some rfl p).2 hp) rfl trivial) h hX

theorem atPos_sound {B : Obj} (k : Nat) : ∀ K, K.WF → (GenK.atPos B k).Reps K (atDen k) :=
  ofVals_row_sound fun _ _ _ _ h => Tab.atPos_holds h

end GenK

end Rel.Lang
