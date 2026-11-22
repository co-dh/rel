import Rel.Lang.GenKBits

/-! The `GenK` ops of the power operators `est` and `atPos`, each representing its constructor's case of `Tm.den`
    from the op's `Tab` law (`Tab.est_holds`, `Tab.atPos_holds`), in `GenKSpec`'s style (`ofVals_row_sound`). -/

namespace Rel.Lang

open Rel Rel.Rep Rel.Kernel Rel.Verify Gen
open scoped Rel.Core.Rel
open Rel.Core.Rel hiding id comp recip inter union zero le inl inr junc

namespace GenK

/-- `est(Q)` (`estRow` under `GenK.testVals`): `Q` run on the pairs `D` it is asked about represents `TQ` there (`side_some`). -/
theorem est_sound {B : Obj} {Q : Rel (.prod B B) (.prod B B)} {TQ : Core.Rel (Obj.El (.prod B B)) (Obj.El (.prod B B))}
    (hQ : ∀ K, K.WF → Q.Reps K TQ) (wQ : Q.Wf) : ∀ K, K.WF → (GenK.testVals B (.arr B) B Q fun q X => Tab.est q X).Reps K (estDen TQ) :=
  ofVals_row_sound fun _ _ _ hX h => Tab.est_holds (fun D _ wD hT p hp => (reps_iff ⟨some ⟨D.n, D.val⟩, none, none⟩ _ _).1
    (hQ _ ⟨wD.2, trivial, trivial⟩) _ hT p _ ((side_some rfl p).2 hp) rfl trivial)
    (fun D _ hT wD => wQ.runE (show (⟨some ⟨D.n, D.val⟩, none, none⟩ : Known _ _).WF from ⟨wD.2, trivial, trivial⟩) hT)
    h hX

/-- `front(Q)` (`frontRow` under `GenK.testVals`): `Q` as in `est_sound`. -/
theorem front_sound {B : Obj} {Q : Rel (.prod B B) (.prod B B)} {TQ : Core.Rel (Obj.El (.prod B B)) (Obj.El (.prod B B))}
    (hQ : ∀ K, K.WF → Q.Reps K TQ) (wQ : Q.Wf) : ∀ K, K.WF → (GenK.testVals B (.arr B) (.arr B) Q fun q X => Tab.front q X).Reps K (frontDen TQ) :=
  ofVals_row_sound fun _ _ _ hX h => Tab.front_den (fun D _ wD hT p hp => (reps_iff ⟨some ⟨D.n, D.val⟩, none, none⟩ _ _).1
    (hQ _ ⟨wD.2, trivial, trivial⟩) _ hT p _ ((side_some rfl p).2 hp) rfl trivial)
    (fun D _ hT wD => wQ.runE (show (⟨some ⟨D.n, D.val⟩, none, none⟩ : Known _ _).WF from ⟨wD.2, trivial, trivial⟩) hT)
    h hX

theorem atPos_sound {B : Obj} (k : Nat) : ∀ K, K.WF → (GenK.atPos B k).Reps K (atDen k) :=
  ofVals_row_sound fun _ _ _ hX h => Tab.atPos_holds h hX

end GenK

end Rel.Lang
