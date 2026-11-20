import Rel.Run.Table
import Rel.RepCols

/-! The laws of a table directory (PLAN D.9); the code is `Rel.Run.Table`, which `n.io` calls. -/

namespace Rel.Lang.Table

open Rel Rel.Lang.Plan

/-- **The renumbering of a positional write, as a relation**: reading back `write S dir t.val` gives `frame t.val`
    (per column the round trip `ownParse_ownImage`, `ownEnc_ownParts`; over files only `#guard`ed), and that frame is
    `ι ≫ t` for `ι = {(j, t.key.row j)}`, new position ↦ old key, when no two rows of `t` share a key. -/
theorem frame_holds {K B : Obj} {t : Tab K B} {r : Tab .long B} (h : frame t.val = .ok r)
    (hk : ∀ j j', t.key.row j = t.key.row j' → j = j') (i : Int64) (y : B.El) :
    r.Holds i y ↔ ∃ k, (∃ j : Fin t.n.toNat, j.1.toUInt64.toInt64 = i ∧ t.key.row j = k) ∧ t.Holds k y := by
  unfold frame at h
  cases hP : Arr.pos t.n with
  | error e => rw [hP] at h; cases h
  | ok P =>
    rw [hP] at h; cases h
    constructor
    · rintro ⟨j, hj, hy⟩
      exact ⟨_, ⟨j, (Arr.pos_get hP j).symm.trans hj, rfl⟩, j, rfl, hy⟩
    · rintro ⟨k, ⟨j, hj, rfl⟩, j', hj', hy⟩
      obtain rfl := hk _ _ hj'
      exact ⟨j', (Arr.pos_get hP j').trans hj, hy⟩

end Rel.Lang.Table
