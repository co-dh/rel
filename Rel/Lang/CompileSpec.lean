import Rel.Lang.GenSpec
import Rel.Run.Lang.Compile

/-! The cases of `compile_sound` that `GenSpec` has no lemma for (`doc/rel-denotation-design.md` §7.2, §7.5): the
    binders `μ`, `ν`, their environment, and `flat`. Each is stated for every body, so the induction hypothesis
    of a body is already parametric in its variable. -/

namespace Rel.Lang

open Rel Rel.Alg Rel.Rep Rel.Kernel Gen
open scoped Rel.Core.Rel
open Rel.Core.Rel hiding id comp recip inter union zero le inl inr junc

/-- Every variable's plan computes its meaning under `ρ`. -/
def CodeEnv.Sound (η : CodeEnv) (ρ : Val) : Prop := ∀ k A B d, PSound (η k A B d) (ρ k A B)

/-- Binding `k` to a table keeps `CodeEnv.Sound`, the table's meaning bound in `ρ`. -/
theorem CodeEnv.Sound.bind {η : CodeEnv} {ρ : Val} (hη : η.Sound ρ) (k : Nat) {A B : Obj} (X : CRel A B) :
    (η.bind k X).Sound (ρ.bind k (rep X.rel)) := by
  intro j A' B' d D hD hb x y hx
  by_cases e : j = k
  · subst e
    by_cases h : A = A' ∧ B = B'
    · obtain ⟨rfl, rfl⟩ := h; simp [CodeEnv.bind, Val.bind, Tm.den]
    · simp [CodeEnv.bind, Val.bind, h, Tm.den]
  · simp only [CodeEnv.bind, Val.bind, e, if_false] at hb ⊢; exact hη j A' B' d D hD hb x y hx

/-- `μX : φ` by rounds from `𝟘`: where fewer than `cap` rounds ran, the least fixed point of a monotone `Φ`, each
    round sound at an ok table (`CRel.rep_fixOn`). -/
theorem mu_sound {A B : Obj} {cap : Nat} {φ : CRel A B → Fn false A B} {Φ : Den A B → Den A B}
    (hΦ : Monotonic Φ) (h : ∀ X : CRel A B, X.ok = true → Sound (φ X) (Φ (rep X.rel))) :
    Sound (Gen.mu A B cap φ) (Core.Rel.mu Φ) := fun ⟨⟩ _ hb x y _ => by
  simp only [Gen.mu, also, Bool.and_eq_true, decide_eq_true_eq] at hb ⊢
  obtain ⟨j, -, hj, -, hfix, hleast, -⟩ := CRel.rep_fixOn cap (fun X => φ X ()) ⟨Alg.zero, true⟩ Φ hb.2
    (fun D hD => (h ⟨D, true⟩ rfl).eq hD) hΦ (Or.inl (le_iff.2 fun a b h => by rw [rep_zero] at h; exact h.elim))
  have hfx := hfix (hj ▸ hb.1)
  have e := Core.Rel.le_antisymm
    (hleast _ (le_iff.2 fun a b h => by rw [rep_zero] at h; exact h.elim) (mu_prefixed hΦ)) (mu_le (by rw [hfx]; exact Core.Rel.le_refl _))
  rw [e]

/-- `νX : φ` by rounds from `S` down: the greatest fixed point of a monotone `Φ` below `⟦S⟧`. The chain of
    distinct-row tables below `S` is fixed within `S`'s row count plus one (`CRel.rep_fixOn`'s last clause). -/
theorem nu_sound {A B : Obj} {S : Fn false A B} {TS : Den A B} {φ : CRel A B → Fn false A B}
    {Φ : Den A B → Den A B} (hS : Sound S TS) (hΦ : Monotonic Φ) (hle : ∀ X, Φ X ⊑ TS)
    (h : ∀ X : CRel A B, X.ok = true → Sound (φ X) (Φ (rep X.rel))) :
    Sound (Gen.nu A B S φ) (Core.Rel.nu Φ) := fun ⟨⟩ _ hb x y _ => by
  simp only [Gen.nu] at hb ⊢
  have hs : (S ()).ok = true := by
    cases e : (S ()).ok
    · rw [CRel.fixOn, CRel.guard, e] at hb; exact absurd hb Bool.false_ne_true
    · rfl
  have hX : rep (S ()).rel = TS := hS.eq hs
  have hit : ∀ i, Nat.repeat Φ i (rep (S ()).rel) ⊑ rep (S ()).rel := fun i => by
    cases i with
    | zero => exact Core.Rel.le_refl _
    | succ i => show Φ _ ⊑ _; rw [hX]; exact hle _
  obtain ⟨j, -, hj, hr, hfix, -, hcnt⟩ := CRel.rep_fixOn _ (fun X => φ X ()) (S ()) Φ hb
    (fun D hD => (h ⟨D, true⟩ rfl).eq hD) hΦ (Or.inr (hX ▸ hle _))
  have hfx := hfix (hcnt _ hit (by omega))
  have hdown : ∀ i, Core.Rel.nu Φ ⊑ Nat.repeat Φ i (rep (S ()).rel) := fun i => by
    induction i with
    | zero => show _ ⊑ rep (S ()).rel; rw [hX, ← nu_fix hΦ]; exact hle _
    | succ i ih => show _ ⊑ Φ _; rw [← nu_fix hΦ]; exact hΦ _ _ ih
  have e := Core.Rel.le_antisymm (le_nu (by rw [hfx]; exact Core.Rel.le_refl _)) (hr ▸ hdown j)
  rw [e]

/-- `flat(R)`: `(i, a)` to `b` where `R` relates `i` to `(a, b)`, `R` run on the `i` in demand. -/
theorem flat_sound {I A B : Obj} {d : Bool} {R : Fn d I (.prod A B)} {TR : Den I (.prod A B)} (hR : Sound R TR) :
    Sound (flat I A B d R) (flatDen TR) := fun D hD hb x b hx => by
  simp only [flat, also, Bool.and_eq_true] at hb ⊢
  obtain ⟨hro, hc⟩ := hb
  have h1 := ok_and hc; rw [Bool.and_eq_true] at h1
  have h2 := ok_and h1.2; rw [Bool.and_eq_true] at h2
  have h3 := ok_and h2.1; rw [Bool.and_eq_true] at h3
  have hK := (CRel.rep_ofC hro).trans (rep_ranC (Alg.outl D) (CRel.ofC_ok hro).1)
  have hRk : ∀ i v, rep (CRel.ofC (ranC (Alg.outl D))).rel i i →
      (rep (R (Dem.of d (CRel.ofC (ranC (Alg.outl D))).rel)).rel i v ↔ TR i v) :=
    fun i v h => atKeys hR _ (fun a b h => by rw [hK] at h; exact h.1) h3.1 i v h
  have hi : rep (CRel.ofC (ranC (Alg.outl D))).rel x.1 x.1 := by
    have ho : rep (Alg.outl D) x x.1 := by rw [rep_outl]; exact ⟨x, hx, rfl⟩
    rw [hK]; exact ⟨rfl, x, ho, ho⟩
  dsimp only at h1 h2 h3 ⊢
  rw [CRel.rep_comp _ _ hc, CRel.rep_comp _ _ h1.2, rep_conv, CRel.rep_pair _ _ h2.1, rep_conv, rep_outl, rep_outr,
    CRel.rep_ran _ h3.2]
  constructor
  · rintro ⟨x', hd, q, ⟨hr, z, ⟨e1, -⟩, ez⟩, z', ⟨e2, -⟩, ez'⟩
    obtain rfl := hD x x' hd
    subst e1 e2
    have e : q = (x.2, b) := Prod.ext (by first | exact ez | exact ez.symm) (by first | exact ez' | exact ez'.symm)
    subst e
    exact (hRk x.1 _ hi).1 hr
  · intro t
    have hr := (hRk x.1 _ hi).2 t
    exact ⟨x, hx, (x.2, b), ⟨hr, (x.2, b), ⟨rfl, x.1, hr, hr⟩, rfl⟩, (x.2, b), ⟨rfl, x.1, hr, hr⟩, rfl⟩

end Rel.Lang
