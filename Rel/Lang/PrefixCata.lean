import Rel.Lang.PrefixFold
import Rel.Programs.Prefix

/-! B&dM's `prefix = ⦇[nil, nil ∪ cons]⦈` (p.126; `Programs/Prefix.lean`, the right fold) and the prelude's
    `prefix ≜ cat° π₁` (`Tm.prefixDef`) are one relation, `ys <+: xs`, at every object. -/

namespace Rel.Lang

open Rel.Core.Rel hiding id comp recip inter union zero le inl inr junc

/-- **The fold and the prelude's text of `prefix` are one relation**: the body the prelude elaborates,
    `prelude.prefix.body`, at any objects `σ` (`Tm.instObj`). -/
theorem Tm.prefixFold_den (ph : List QAtomicType) (σ : List Obj) (ρ ρ' : Val)
    {t' : Tm ((Obj.atom .general).arr.inst ph σ) ((Obj.atom .general).arr.inst ph σ)}
    (ht : Rel.Programs.prelude.prefix.body.instObj ph σ = .ok t')
    (e : Tm (.arr ((Obj.atom .general).inst ph σ)) (.arr ((Obj.atom .general).inst ph σ)))
    (he : ∀ v, (∃ a, e.den ρ a v) ↔ v = []) :
    (Tm.foldr e (.join .nil (.prim (rowOf "cons")))).den ρ = t'.den ρ' := by
  obtain rfl : Tm.prefixDef ((Obj.atom .general).inst ph σ) = t' := Except.ok.inj ht
  exact Tm.prefixFold_prefixDef ρ ρ' e he

-- The source-level check emits its kernel-checked proof.
#check Programs.prefixCata.proof.check0

private theorem denLeRefl {A B : Obj} {R : Tm A B} (ρ : Val) :
    Core.Rel.le (R.den ρ) (R.den ρ) :=
  Core.Rel.le_refl _

open Rel.Programs.prelude in
rel_program prefixInclusion where
    obj N = 0…9
    x : 1 ⟶ [N] ≜ {(∗,3 1 2)}
    check x ⊑ x by denLeRefl

#check prefixInclusion.proof.check0

-- Changing the claimed relation keeps the types but invalidates the proof.
/-- error: Type mismatch -/
#guard_msgs (substring := true) in
open Rel.Programs.prelude in
rel_program badPrefix where
    obj N = 0…9
    x : 1 ⟶ [N] ≜ {(∗,3 1 2)}
    prefixC : [α] ⟶ [α] ≜ ⦇[nil, nil ∪ cons]⦈ʳ
    check x prefixC = x nil by Rel.Lang.Tm.prefixFold_input

run_cmd do
  let env ← Lean.getEnv
  if env.contains `Rel.Lang.badPrefix.expanded || env.contains `Rel.Lang.badPrefix.x then
    throwError "a rejected relation proof exported executable code"

end Rel.Lang

#check Rel.Programs.prefixCata.proof.shares
