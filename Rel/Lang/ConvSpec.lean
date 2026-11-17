import Rel.Lang.GenSpec
import Rel.Run.Lang.Elab

namespace Rel.Lang

open Rel.Core.Rel hiding id comp recip inter union zero le inl inr junc
open scoped Rel.Core.Rel

/-! ### `convTm` read back: the converse it builds means the converse (§4.2) -/

/-- `t°` as `Proj` holds it: `Zπ₁°` or `Zπ₂°`. -/
noncomputable def Proj.den (ρ : Val) {B A₁ A₂ : Obj} : Proj B A₁ A₂ → Den B (.prod A₁ A₂)
  | ⟨_, .inl z⟩ => z.den ρ ≫ (graph Prod.fst)°
  | ⟨_, .inr z⟩ => z.den ρ ≫ (graph Prod.snd)°

theorem Proj.den_pre (ρ : Val) {C B A₁ A₂ : Obj} {d : Bool} (p : Tm C B d) (x : Proj B A₁ A₂) :
    (Proj.pre p x).den ρ = p.den ρ ≫ x.den ρ := by
  rcases x with ⟨_, z | z⟩ <;> exact Core.Rel.comp_assoc _ _ _

theorem Proj.den_meet (ρ : Val) {B A₁ A₂ : Obj} (x y : Proj B A₁ A₂) :
    (∀ u, Proj.meet x y = .inl u → u.2.den ρ = x.den ρ ∩ y.den ρ) ∧
    (∀ z, Proj.meet x y = .inr z → z.den ρ = x.den ρ ∩ y.den ρ) := by
  rcases x with ⟨_, x | x⟩ <;> rcases y with ⟨_, y | y⟩
  · refine ⟨fun u hu => by simp only [Proj.meet, reduceCtorEq] at hu, fun z hz => ?_⟩
    simp only [Proj.meet, Sum.inr.injEq] at hz; subst hz; exact (Gen.meet_comp_conv_graph _ _ _).symm
  · refine ⟨fun u hu => ?_, fun z hz => by simp only [Proj.meet, reduceCtorEq] at hz⟩
    simp only [Proj.meet, Sum.inl.injEq] at hu; subst hu; exact (Gen.rpair_eq_meet_proj _ _).symm
  · refine ⟨fun u hu => ?_, fun z hz => by simp only [Proj.meet, reduceCtorEq] at hz⟩
    simp only [Proj.meet, Sum.inl.injEq] at hu; subst hu
    exact (Gen.rpair_eq_meet_proj _ _).symm.trans (funext fun _ => funext fun _ => propext and_comm)
  · refine ⟨fun u hu => by simp only [Proj.meet, reduceCtorEq] at hu, fun z hz => ?_⟩
    simp only [Proj.meet, Sum.inr.injEq] at hz; subst hz; exact (Gen.meet_comp_conv_graph _ _ _).symm

/-- What `convTm_den` needs of `t` under `ρ` at the nodes whose converse `convTm` takes as given: a variable and
    `own` are their own converse, a number verb's universe is a coreflexive, a shared term is closed. -/
def Tm.ConvOK (ρ : Val) : {A B : Obj} → {d : Bool} → Tm A B d → Prop
  | A, B, _, .var k => ρ k B A = (ρ k A B)°
  | _, _, _, .own R => (R.den ρ)° = R.den ρ
  | _, _, _, .succ U => ∀ x y, U.den ρ x y → x = y
  | _, _, _, .arith _ U => ∀ x y, U.den ρ x y → x = y
  | _, _, _, .share _ R => R.fv = [] ∧ R.ConvOK ρ
  | _, _, _, .comp R S => R.ConvOK ρ ∧ S.ConvOK ρ
  | _, _, _, .meet R S => R.ConvOK ρ ∧ S.ConvOK ρ
  | _, _, _, .join R S => R.ConvOK ρ ∧ S.ConvOK ρ
  | _, _, _, .diff R S => R.ConvOK ρ ∧ S.ConvOK ρ
  | _, _, _, .pair R S => R.ConvOK ρ ∧ S.ConvOK ρ
  | _, _, _, .arg f _ => f.ConvOK ρ
  | _, _, _, _ => True

theorem Tm.den_cast {A B : Obj} {d d' : Bool} (h : d = d') (t : Tm A B d) (ρ : Val) : (h ▸ t).den ρ = t.den ρ := by
  subst h; rfl

theorem convTm_of_false {A B : Obj} {d : Bool} (h : d = false) (t : Tm A B d) :
    convTm t = .ok ⟨false, .conv (h ▸ t)⟩ := by
  rw [convTm, dif_pos h]; rfl

theorem conv_false_den (ρ : Val) {A B : Obj} {d : Bool} (h : d = false) (t : Tm A B d) (u : (e : Bool) × Tm B A e)
    (hu : convTm t = .ok u) : u.2.den ρ = (t.den ρ)° := by
  rw [convTm_of_false h] at hu; cases hu; exact congrArg (·°) (Tm.den_cast h t ρ)

theorem recip_comp' {α β γ : Type} (R : Core.Rel α β) (S : Core.Rel β γ) : (R ≫ S)° = S° ≫ R° :=
  funext fun _ => funext fun _ => propext ⟨fun ⟨b, h1, h2⟩ => ⟨b, h2, h1⟩, fun ⟨b, h1, h2⟩ => ⟨b, h2, h1⟩⟩

/-- `⟨X,Y⟩° = π₁X° ∩ π₂Y°`: the converse `convTm` and `convProj` build for a pair. -/
theorem recip_rpair {α β γ : Type} (X : Core.Rel γ α) (Y : Core.Rel γ β) :
    (graph Prod.fst ≫ X° ∩ graph Prod.snd ≫ Y°) = (rpair X Y)° :=
  funext fun _ => funext fun _ => propext
    ⟨fun ⟨⟨_, e1, h1⟩, ⟨_, e2, h2⟩⟩ => ⟨e1 ▸ h1, e2 ▸ h2⟩, fun ⟨h1, h2⟩ => ⟨⟨_, rfl, h1⟩, ⟨_, rfl, h2⟩⟩⟩

macro "noproj" : tactic => `(tactic| (intro A₁ A₂ h p hp; cases h <;> (dsimp only at hp; unfold convProj at hp; cases hp)))
macro "noconv" : tactic => `(tactic| (intro u hu; rw [convTm, dif_neg (by decide)] at hu; cases hu))

theorem convTm_den (ρ : Val) : ∀ {A B : Obj} {d : Bool} (t : Tm A B d), t.ConvOK ρ →
    (∀ u, convTm t = .ok u → u.2.den ρ = (t.den ρ)°) ∧
    (∀ A₁ A₂ (h : A = .prod A₁ A₂) p, convProj (h ▸ t) = .ok p → p.den ρ = ((h ▸ t).den ρ)°) := by
  intro A B d t
  induction t with
  | val _ | uni _ | zero | conv _ _ | ran _ _ | ldiv _ _ _ _ _ _ _ _ | rdiv _ _ _ _ _ _ _ _ | prod _ _ _ _
  | junc _ _ _ _ | leq _ _ | lt _ _ | nu _ _ _ _ _ | mu _ _ _ _ _ =>
    exact fun _ => ⟨conv_false_den ρ rfl _, by noproj⟩
  | top _ _ | lam _ _ | E _ _ | est _ _ | thin _ _ | nil | atPos _ | fold _ _ _ _ | foldI _ _ _ _ | flat _ _
  | juncD _ _ _ _ | refold _ _ _ _ _ _ => exact fun _ => ⟨by noconv, by noproj⟩
  | id =>
    refine fun _ => ⟨fun u hu => ?_, by noproj⟩
    rw [convTm, dif_neg (by decide)] at hu; cases hu
    exact funext fun _ => funext fun _ => propext ⟨Eq.symm, Eq.symm⟩
  | outl =>
    refine fun _ => ⟨by noconv, fun A₁ A₂ h p hp => ?_⟩
    cases h; dsimp only at hp ⊢; unfold convProj at hp; cases hp; exact Core.Rel.id_comp _
  | outr =>
    refine fun _ => ⟨by noconv, fun A₁ A₂ h p hp => ?_⟩
    cases h; dsimp only at hp ⊢; unfold convProj at hp; cases hp; exact Core.Rel.id_comp _
  | @var _ _ d k =>
    refine fun hok => ⟨fun u hu => ?_, by noproj⟩
    by_cases hd : d = false
    · exact conv_false_den ρ hd _ u hu
    rw [convTm, dif_neg hd] at hu; cases hu; exact hok
  | @own _ d R _ =>
    refine fun hok => ⟨fun u hu => ?_, by noproj⟩
    by_cases hd : d = false
    · exact conv_false_den ρ hd _ u hu
    rw [convTm, dif_neg hd] at hu; cases hu; exact hok.symm
  | @dom _ _ d R _ =>
    refine fun _ => ⟨fun u hu => ?_, by noproj⟩
    by_cases hd : d = false
    · exact conv_false_den ρ hd _ u hu
    rw [convTm, dif_neg hd] at hu; cases hu
    exact funext fun _ => funext fun _ => propext
      ⟨fun ⟨e, c, h1, h2⟩ => ⟨e.symm, c, h2, h1⟩, fun ⟨e, c, h1, h2⟩ => ⟨e.symm, c, h2, h1⟩⟩
  | prim r =>
    refine fun _ => ⟨fun u hu => ?_, by noproj⟩
    rw [convTm, dif_neg (by decide)] at hu; dsimp only at hu
    split at hu
    · cases hu; exact funext fun _ => funext fun _ => propext Iff.rfl
    · cases hu
  | call d c os cv =>
    refine fun _ => ⟨fun u hu => ?_, by noproj⟩
    by_cases hd : d = false
    · exact conv_false_den ρ hd _ u hu
    rw [convTm, dif_neg hd] at hu; dsimp only at hu
    split at hu
    · cases hu; exact funext fun _ => funext fun _ => propext Iff.rfl
    · cases hu
  | @arg _ _ _ _ d _ f x ihf _ =>
    refine fun hok => ⟨fun u hu => ?_, by noproj⟩
    by_cases hd : d = false
    · exact conv_false_den ρ hd _ u hu
    rw [convTm, dif_neg hd] at hu
    cases hf : convTm f with
    | error l => simp only [hf] at hu; cases hu
    | ok f' =>
      obtain ⟨e, f'⟩ := f'
      simp only [hf] at hu; cases hu; exact funext fun _ => funext fun _ => propext Iff.rfl
  | @share _ _ d k R ih =>
    refine fun hok => ⟨fun u hu => ?_, fun A₁ A₂ h p hp => ?_⟩
    · by_cases hd : d = false
      · exact conv_false_den ρ hd _ u hu
      rw [convTm, dif_neg hd] at hu
      have e : R.den ρ = R.den Val.empty := (R.den_congr _ _ fun i hi => by simp [hok.1] at hi).1
      exact ((ih hok.2).1 u hu).trans (congrArg (·°) e)
    · cases h; dsimp only at hp ⊢; unfold convProj at hp
      have e : R.den ρ = R.den Val.empty := (R.den_congr _ _ fun i hi => by simp [hok.1] at hi).1
      exact ((ih hok.2).2 _ _ rfl p hp).trans (congrArg (·°) e)
  | @comp _ _ _ d _ R S ihR ihS =>
    refine fun hok => ⟨fun u hu => ?_, fun A₁ A₂ h p hp => ?_⟩
    · by_cases hd : d = false
      · exact conv_false_den ρ hd _ u hu
      rw [convTm, dif_neg hd] at hu
      cases hS : convTm S with
      | error l => simp only [hS] at hu; cases hu
      | ok s =>
        obtain ⟨e, s⟩ := s
        cases hR : convTm R with
        | error l => simp only [hS, hR] at hu; cases hu
        | ok r =>
          obtain ⟨e', r⟩ := r
          simp only [hS, hR] at hu; cases hu
          have hs : s.den ρ = (S.den ρ)° := (ihS hok.2).1 _ hS
          have hr : r.den ρ = (R.den ρ)° := (ihR hok.1).1 _ hR
          show s.den ρ ≫ r.den ρ = _; rw [hs, hr]; exact (recip_comp' _ _).symm
    · cases h; dsimp only at hp ⊢; unfold convProj at hp
      cases hS : convTm S with
      | error l => simp only [hS] at hp; cases hp
      | ok s =>
        obtain ⟨e, s⟩ := s
        cases hR : convProj R with
        | error l => simp only [hS, hR] at hp; cases hp
        | ok x =>
          simp only [hS, hR] at hp; cases hp
          have hs : s.den ρ = (S.den ρ)° := (ihS hok.2).1 _ hS
          rw [Proj.den_pre, hs, (ihR hok.1).2 _ _ rfl x hR]; exact (recip_comp' _ _).symm
  | @join _ _ d e R S ihR ihS | @diff _ _ d e R S ihR ihS =>
    refine fun hok => ⟨fun u hu => ?_, by noproj⟩
    by_cases hd : (d || e) = false
    · exact conv_false_den ρ hd _ u hu
    rw [convTm, dif_neg hd] at hu
    cases hR : convTm R with
    | error l => simp only [hR] at hu; cases hu
    | ok r =>
      obtain ⟨e, r⟩ := r
      cases hS : convTm S with
      | error l => simp only [hS, hR] at hu; cases hu
      | ok s =>
        obtain ⟨e', s⟩ := s
        simp only [hS, hR] at hu; cases hu
        have hs : s.den ρ = (S.den ρ)° := (ihS hok.2).1 _ hS
        have hr : r.den ρ = (R.den ρ)° := (ihR hok.1).1 _ hR
        first
          | (show r.den ρ ∪ s.den ρ = _; rw [hs, hr]; rfl)
          | (show diffDen (r.den ρ) (s.den ρ) = _; rw [hs, hr]; rfl)
  | succ U _ =>
    refine fun hok => ⟨fun u hu => ?_, by noproj⟩
    rw [convTm, dif_neg (by decide)] at hu; cases hu
    refine congrArg (·°) (funext fun a => funext fun w => propext ⟨fun ⟨v, hv, h⟩ => (hok _ _ hv) ▸ h, fun h => ⟨a, ?_, h⟩⟩)
    obtain ⟨v, hv⟩ := h.1; obtain rfl := hok _ _ hv; exact hv
  | arith k U _ =>
    refine fun hok => ⟨fun u hu => ?_, by noproj⟩
    rw [convTm, dif_neg (by decide)] at hu; cases hu
    have key : ∀ p w, arithDen k (U.den ρ) p w → U.den ρ p.1 p.1 ∧ U.den ρ p.2 p.2 := by
      rintro p w ⟨p', ⟨rfl, c, ⟨a', e1, h1⟩, -⟩, p'', ⟨rfl, c', ⟨b', e2, h2⟩, -⟩, -⟩
      subst e1 e2
      refine ⟨?_, ?_⟩
      · obtain rfl := hok _ _ h1; exact h1
      · obtain rfl := hok _ _ h2; exact h2
    refine congrArg (·°) (funext fun p => funext fun w => propext ⟨fun ⟨q, ⟨h1, h2⟩, ha⟩ => ?_, fun ha => ⟨p, key p w ha, ha⟩⟩)
    have e : p = q := Prod.ext (hok _ _ h1) (hok _ _ h2)
    subst e; exact ha
  | @meet A' _ d e R S ihR ihS =>
    refine fun hok => ⟨fun u hu => ?_, fun A₁ A₂ h p hp => ?_⟩
    · by_cases hd : (d || e) = false
      · exact conv_false_den ρ hd _ u hu
      rw [convTm, dif_neg hd] at hu
      cases hR : convTm R with
      | ok r =>
        cases hS : convTm S with
        | ok s =>
          obtain ⟨_, r⟩ := r; obtain ⟨_, s⟩ := s
          simp only [hR, hS] at hu; cases hu
          have hs : s.den ρ = (S.den ρ)° := (ihS hok.2).1 _ hS
          have hr : r.den ρ = (R.den ρ)° := (ihR hok.1).1 _ hR
          show r.den ρ ∩ s.den ρ = _; rw [hs, hr]; rfl
        | error l =>
          simp only [hR, hS] at hu
          clear hR hS hd
          cases A' with
          | prod A₁ A₂ =>
            dsimp only at hu
            cases hx : convProj R with
            | error _ => simp [hx] at hu
            | ok x =>
              cases hy : convProj S with
              | error _ => simp [hx, hy] at hu
              | ok y =>
                cases hm : Proj.meet x y with
                | inr _ => simp [hx, hy, hm] at hu
                | inl t =>
                  simp only [hx, hy, hm] at hu; cases hu
                  rw [(Proj.den_meet ρ x y).1 _ hm, (ihR hok.1).2 _ _ rfl x hx, (ihS hok.2).2 _ _ rfl y hy]; rfl
          | _ => simp at hu
      | error l =>
        simp only [hR] at hu
        clear hR hd
        cases A' with
        | prod A₁ A₂ =>
          dsimp only at hu
          cases hx : convProj R with
          | error _ => simp [hx] at hu
          | ok x =>
            cases hy : convProj S with
            | error _ => simp [hx, hy] at hu
            | ok y =>
              cases hm : Proj.meet x y with
              | inr _ => simp [hx, hy, hm] at hu
              | inl t =>
                simp only [hx, hy, hm] at hu; cases hu
                rw [(Proj.den_meet ρ x y).1 _ hm, (ihR hok.1).2 _ _ rfl x hx, (ihS hok.2).2 _ _ rfl y hy]; rfl
        | _ => simp at hu
    · cases h; dsimp only at hp ⊢; unfold convProj at hp
      cases hx : convProj R with
      | error l => simp only [hx] at hp; cases hp
      | ok x =>
        cases hy : convProj S with
        | error l => simp only [hx, hy] at hp; cases hp
        | ok y =>
          cases hm : Proj.meet x y with
          | inl _ => rw [hx, hy] at hp; dsimp only [Bind.bind, Except.bind] at hp; rw [hm] at hp; cases hp
          | inr z =>
            rw [hx, hy] at hp; dsimp only [Bind.bind, Except.bind] at hp; rw [hm] at hp; cases hp
            rw [(Proj.den_meet ρ x y).2 _ hm, (ihR hok.1).2 _ _ rfl x hx, (ihS hok.2).2 _ _ rfl y hy]; rfl
  | @pair A' _ _ d e R S ihR ihS =>
    refine fun hok => ⟨fun u hu => ?_, fun A₁ A₂ h p hp => ?_⟩
    · by_cases hd : (d || e) = false
      · exact conv_false_den ρ hd _ u hu
      rw [convTm, dif_neg hd] at hu
      cases hR : convTm R with
      | ok r =>
        obtain ⟨_, r⟩ := r
        have hr := (ihR hok.1).1 _ hR
        cases hS : convTm S with
        | ok s =>
          obtain ⟨_, s⟩ := s
          have hs : s.den ρ = (S.den ρ)° := (ihS hok.2).1 _ hS
          simp only [hR, hS] at hu; cases hu
          show graph Prod.fst ≫ r.den ρ ∩ graph Prod.snd ≫ s.den ρ = _; rw [hr, hs]; exact recip_rpair _ _
        | error l =>
          simp only [hR, hS] at hu; cases hu
          -- `⟨π₁R°,π₂⟩τ(S)π₁`: `(b,c) ↦ (a,c) ↦ a` with `a R b` and `a S c`
          show rpair (graph Prod.fst ≫ r.den ρ) (graph Prod.snd) ≫
            ((𝟙 _ ∩ (graph Prod.snd ∩ graph Prod.fst ≫ S.den ρ) ≫ (graph Prod.snd ∩ graph Prod.fst ≫ S.den ρ)°) ≫
              graph Prod.fst) = _
          rw [hr]; funext q a; apply propext
          simp only [Tm.den, Core.Rel.comp, Core.Rel.inter, Core.Rel.recip, Core.Rel.id, graph, rpair, Prod.exists,
            Prod.mk.injEq]
          constructor
          · rintro ⟨a1, c1, ⟨⟨b, rfl, h1⟩, rfl⟩, a2, c2, ⟨⟨rfl, rfl⟩, w, ⟨rfl, x, rfl, h2⟩, -⟩, rfl⟩
            exact ⟨h1, h2⟩
          · rintro ⟨h1, h2⟩
            exact ⟨a, q.2, ⟨⟨q.1, rfl, h1⟩, rfl⟩, a, q.2, ⟨⟨rfl, rfl⟩, q.2, ⟨rfl, a, rfl, h2⟩, rfl, a, rfl, h2⟩, rfl⟩
      | error l =>
        cases hS : convTm S with
        | ok s =>
          obtain ⟨_, s⟩ := s
          have hs : s.den ρ = (S.den ρ)° := (ihS hok.2).1 _ hS
          simp only [hR, hS] at hu; cases hu
          -- `⟨π₁,π₂S°⟩ swap τ(R) swap π₂`: `(b,c) ↦ (b,a) ↦ (a,b) ↦ (b,a) ↦ a` with `a S c` and `a R b`
          show rpair (graph Prod.fst) (graph Prod.snd ≫ s.den ρ) ≫
            (rpair (graph Prod.snd) (graph Prod.fst) ≫
              ((𝟙 _ ∩ (graph Prod.snd ∩ graph Prod.fst ≫ R.den ρ) ≫ (graph Prod.snd ∩ graph Prod.fst ≫ R.den ρ)°) ≫
                (rpair (graph Prod.snd) (graph Prod.fst) ≫ graph Prod.snd))) = _
          rw [hs]; funext q a; apply propext
          simp only [Tm.den, Core.Rel.comp, Core.Rel.inter, Core.Rel.recip, Core.Rel.id, graph, rpair, Prod.exists,
            Prod.mk.injEq]
          constructor
          · rintro ⟨b1, a1, ⟨rfl, c, rfl, h2⟩, a2, b2, ⟨rfl, rfl⟩, a3, b3, ⟨⟨rfl, rfl⟩, w, ⟨rfl, x, rfl, h1⟩, -⟩,
              b4, a4, ⟨rfl, rfl⟩, rfl⟩
            exact ⟨h1, h2⟩
          · rintro ⟨h1, h2⟩
            exact ⟨q.1, a, ⟨rfl, q.2, rfl, h2⟩, a, q.1, ⟨rfl, rfl⟩, a, q.1,
              ⟨⟨rfl, rfl⟩, q.1, ⟨rfl, a, rfl, h1⟩, rfl, a, rfl, h1⟩, q.1, a, ⟨rfl, rfl⟩, rfl⟩
        | error l' =>
          simp only [hR, hS] at hu
          clear hR hS hd
          cases A' with
          | prod A₁ A₂ =>
            dsimp only at hu
            cases hx : convProj R with
            | error _ => simp [hx] at hu
            | ok x =>
              cases hy : convProj S with
              | error _ => simp [hx, hy] at hu
              | ok y =>
                cases hm : Proj.meet (Proj.pre .outl x) (Proj.pre .outr y) with
                | inr _ => simp [hx, hy, hm] at hu
                | inl t =>
                  simp only [hx, hy, hm] at hu; cases hu
                  rw [(Proj.den_meet ρ _ _).1 _ hm, Proj.den_pre, Proj.den_pre, (ihR hok.1).2 _ _ rfl x hx,
                    (ihS hok.2).2 _ _ rfl y hy]
                  exact recip_rpair _ _
          | _ => simp at hu
    · cases h; dsimp only at hp ⊢; unfold convProj at hp
      cases hx : convProj R with
      | error l => simp only [hx] at hp; cases hp
      | ok x =>
        cases hy : convProj S with
        | error l => simp only [hx, hy] at hp; cases hp
        | ok y =>
          cases hm : Proj.meet (Proj.pre .outl x) (Proj.pre .outr y) with
          | inl _ => rw [hx, hy] at hp; dsimp only [Bind.bind, Except.bind] at hp; rw [hm] at hp; cases hp
          | inr z =>
            rw [hx, hy] at hp; dsimp only [Bind.bind, Except.bind] at hp; rw [hm] at hp; cases hp
            rw [(Proj.den_meet ρ _ _).2 _ hm, Proj.den_pre, Proj.den_pre, (ihR hok.1).2 _ _ rfl x hx,
              (ihS hok.2).2 _ _ rfl y hy]
            exact recip_rpair _ _

end Rel.Lang
