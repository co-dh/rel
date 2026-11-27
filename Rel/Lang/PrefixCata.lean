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

private theorem denEqRefl {A B : Obj} {R : Tm A B} (ρ : Val) : R.den ρ = R.den ρ := rfl

-- A theorem carries the proof as a check does: `n.proof.<theorem>`.
open Rel.Programs.prelude in
rel_program prefixTheorem where
    obj N = 0…9
    x : 1 ⟶ [N] ≜ {(∗,3 1 2)}
    theorem selfEq : x = x by denEqRefl

#check prefixTheorem.proof.selfEq

-- A `calc` theorem is certified step by step: `≜ y` is `rfl`, `selfEq` is the proof constant of a theorem above.
open Rel.Programs.prelude in
rel_program prefixCalc where
    obj N = 0…9
    x : 1 ⟶ [N] ≜ {(∗,3 1 2)}
    y : 1 ⟶ [N] ≜ x
    theorem selfEq : x = x by denEqRefl
    theorem viaY : y = x := calc
      _ = x := ≜ y
      _ = x := selfEq

#check prefixCalc.proof.viaY

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

-- A theorem with parameters carries `by lemma`: the parameters are the variables `∀ ρ` quantifies over, and its sides
-- are typed for the denotation only, so `[N]` as a source needs no universe. The builder reads `R°°` as `R`, so the
-- goal here is `den ρ (var 0) = den ρ (var 0)`.
rel_program convParam where
    obj N = 0…3
    theorem cc(R : N ⟶ N) : R°° = R by denEqRefl
    theorem nn(R : [N] ⟶ N) : R°° = R by denEqRefl

#check convParam.proof.cc
#check convParam.proof.nn

-- A hypothesis after `if` is a premise of the goal, over the same `ρ` and parameters: `R = S ⊢ R = S`.
private theorem hypId {A B : Obj} {R S : Tm A B} (ρ : Val) (h : R.den ρ = S.den ρ) : R.den ρ = S.den ρ := h

rel_program hypThm where
    obj N = 0…3
    theorem hy(R : N ⟶ N, S : N ⟶ N) if R = S : R = S by hypId

#check hypThm.proof.hy

open Rel.Programs.prelude in
rel_program hypCalc where
    obj N = 0…3
    x : 1 ⟶ [N] ≜ {(∗,3 1 2)}
    y : 1 ⟶ [N] ≜ x
    theorem cy(R : N ⟶ N, S : N ⟶ N) if R = S : y = x := calc
      _ = x := ≜ y
    theorem citeCy(R : N ⟶ N, S : N ⟶ N) if R = S : y = x := calc
      _ = x := cy

#check hypCalc.proof.cy
#check hypCalc.proof.citeCy

-- The parameter objects and the open object of `𝟙` are instantiated before reading the valuation.
rel_program genericTheorem where
    theorem gg(R : α ⟶ β) : R = R by denEqRefl
    theorem ii : 𝟙 ⊑ 𝟙 by denLeRefl
    theorem citeGg(R : α ⟶ β) : R = R := calc
      _ = R := gg
      _ = R := gg

#check genericTheorem.proof.gg
#check genericTheorem.proof.ii
#check genericTheorem.proof.citeGg

example (A B : Obj) (ρ : Val) : ρ 0 A B = ρ 0 A B :=
  genericTheorem.proof.citeGg [A, B] ρ

end Rel.Lang

#check Rel.Programs.prefixCata.proof.shares
