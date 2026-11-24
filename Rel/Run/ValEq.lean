module

/-
  Equality of payloads as Rel reads it: `encEq`, decided on the constructor and its fields.
-/
public import Rel.Kernel.Value

-- exposed: every def body is a spec a downstream `rfl`/`decide`/`simp` may unfold (PLAN W.8)
@[expose] public section

namespace Rel

open Rel

deriving instance DecidableEq for QAtom

/-- Payload equality: one constructor, equal fields. -/
def encEq : Enc → Enc → Bool
  | .foR m p, .foR m' p' => decide (m = m') && decide (p = p')
  | .pos, .pos => true
  | _, _ => false

theorem encEq_refl : (e : Enc) → encEq e e = true
  | .foR .. | .pos => by simp [encEq]

theorem encEq_sound : (e f : Enc) → encEq e f = true → e = f
  | .foR .., f, h | .pos, f, h => by cases f <;> simp_all [encEq]

end Rel
