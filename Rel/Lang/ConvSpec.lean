import Rel.Lang.GenSpec
import Rel.Run.Lang.Elab

namespace Rel.Lang

open Rel.Core.Rel hiding id comp recip inter union zero le inl inr junc
open scoped Rel.Core.Rel

/-! ### `convTm` read back: the converse it builds means the converse (§4.2) -/

/-- `t°` as `Proj` holds it: `Zπ₁°` or `Zπ₂°`. -/
noncomputable def Proj.den (ρ : Val) {B A₁ A₂ : Obj} : Proj B A₁ A₂ → Den B (.prod A₁ A₂)
  | .inl z => z.den ρ ≫ (graph Prod.fst)°
  | .inr z => z.den ρ ≫ (graph Prod.snd)°

theorem Proj.den_pre (ρ : Val) {C B A₁ A₂ : Obj} (p : Tm C B) (x : Proj B A₁ A₂) :
    (Proj.pre p x).den ρ = p.den ρ ≫ x.den ρ := by
  rcases x with z | z <;> exact Core.Rel.comp_assoc _ _ _

theorem Proj.den_meet (ρ : Val) {B A₁ A₂ : Obj} (x y : Proj B A₁ A₂) :
    (∀ u, Proj.meet x y = .inl u → u.den ρ = x.den ρ ∩ y.den ρ) ∧
    (∀ z, Proj.meet x y = .inr z → z.den ρ = x.den ρ ∩ y.den ρ) := by
  rcases x with x | x <;> rcases y with y | y
  · refine ⟨fun u hu => by simp only [Proj.meet, reduceCtorEq] at hu, fun z hz => ?_⟩
    simp only [Proj.meet, Sum.inr.injEq] at hz; subst hz; exact (Gen.meet_comp_conv_graph _ _ _).symm
  · refine ⟨fun u hu => ?_, fun z hz => by simp only [Proj.meet, reduceCtorEq] at hz⟩
    simp only [Proj.meet, Sum.inl.injEq] at hu; subst hu; exact (Gen.rpair_eq_meet_proj _ _).symm
  · refine ⟨fun u hu => ?_, fun z hz => by simp only [Proj.meet, reduceCtorEq] at hz⟩
    simp only [Proj.meet, Sum.inl.injEq] at hu; subst hu
    exact (Gen.rpair_eq_meet_proj _ _).symm.trans (funext fun _ => funext fun _ => propext and_comm)
  · refine ⟨fun u hu => by simp only [Proj.meet, reduceCtorEq] at hu, fun z hz => ?_⟩
    simp only [Proj.meet, Sum.inr.injEq] at hz; subst hz; exact (Gen.meet_comp_conv_graph _ _ _).symm

/-- `Proj.meet` across the two projections is a pair, no row's spine. -/
theorem Proj.meet_argDen {B A₁ A₂ : Obj} (x y : Proj B A₁ A₂) (t : Tm B (.prod A₁ A₂))
    (h : Proj.meet x y = .inl t) (ρ : Val) (ss : List Sem) : t.argDen ρ ss = 𝟘 := by
  rcases x with x | x <;> rcases y with y | y <;> simp only [Proj.meet, reduceCtorEq, Sum.inl.injEq] at h <;>
    subst h <;> rfl

/-- A term not run on demand is no row's spine: a row is (`Tm.prim`), and `arg`, `share`, `own` keep the bit. -/
theorem Tm.argDen_false (ρ : Val) : ∀ {A B : Obj} (t : Tm A B), t.dem = false → ∀ ss, t.argDen ρ ss = 𝟘 := by
  intro A B t
  induction t generalizing ρ with
  | prim => intro h; simp [Tm.dem] at h
  | arg f x ihf _ => intro h ss; exact ihf ρ h _
  | share _ R ih => intro h ss; exact ih Val.empty h ss
  | own R ih => intro h ss; exact ih ρ h ss
  | _ => intro _ _; rfl

/-- `Prim.den` read off: the row's meaning at the object variables `σ` its constant's type takes at `A ⟶ B`. -/
theorem Prim.den_iff {r : Prim} {x : (c : RowCode) × RowDen c} (e : rowDens.find? (·.1.sym == r.sym) = some x)
    {A B : Obj} {ss : List Sem} {a : A.El} {b : B.El} : Prim.den r A B ss a b ↔
      ∃ σ, r.objs A B = some σ ∧ ∃ h : (x.1.ty σ).1 = A ∧ (x.1.ty σ).2 = B, (h.1 ▸ h.2 ▸ x.2 σ ss) a b := by
  unfold Prim.den; rw [e]
  cases r.objs A B with
  | none => exact ⟨fun h => False.elim h, fun ⟨_, h, _⟩ => by cases h⟩
  | some σ =>
    by_cases h : (x.1.ty σ).1 = A ∧ (x.1.ty σ).2 = B
    · simp [h]
    · simp [h]; exact ⟨fun h' => False.elim h', fun ⟨h', _⟩ => h'.elim⟩

/-- **Every row of `prims` with a converse row (`conv`) means that row's converse**, at all objects and arguments:
    `convTm`'s `prim` case. The rows are enumerated from `prims`, so a row given a `conv` it does not mean fails here. -/
theorem Prim.den_conv : ∀ r ∈ prims, ∀ s r', r.conv = some s → Prim.find? s = some r' →
    ∀ A B ss, Prim.den r' B A ss = (Prim.den r A B ss)° := by
  intro r hr s r' hs hr'
  simp only [prims, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp only [consRow, memRow, inlRow, inrRow, mapRow, reduceCtorEq, Option.some.injEq] at hs
  all_goals subst hs
  all_goals simp [Prim.find?, prims, consRow, memRow, inlRow, inrRow, mapRow] at hr'
  all_goals subst hr'
  all_goals
    intro A B ss
    funext b a; apply propext; rw [recip_apply, Prim.den_iff rfl, Prim.den_iff rfl]
    constructor
    all_goals
      rintro ⟨σ, -, ⟨rfl, rfl⟩, h⟩
      refine ⟨[σ₁ σ], ?_, ⟨rfl, rfl⟩, h⟩
      simp [Prim.objs, Prim.vars, OExp.vars, OExp.unify, List.eraseDups, List.eraseDupsBy, List.eraseDupsBy.loop,
        consRow, RowCode.cons, RowCode.uncons, RowCode.cat, RowCode.uncat, RowCode.snoc, RowCode.unsnoc, RowCode.plain]

/-- What `convTm_den` needs of `t` under `ρ` at the nodes whose converse `convTm` takes as given: a variable and
    `own` are their own converse (as a row's spine too), a number verb's universe is a coreflexive, a shared term
    is closed, a row is one of `prims` (whose `conv` `Prim.den_conv` checks). -/
def Tm.ConvOK (ρ : Val) : {A B : Obj} → Tm A B → Prop
  | A, B, .var _ k => ρ k B A = (ρ k A B)°
  | _, _, .own R => (R.den ρ)° = R.den ρ ∧ ∀ ss, (R.argDen ρ ss)° = R.argDen ρ ss
  | _, _, .prim r => r ∈ prims
  | _, _, .succ U => ∀ x y, U.den ρ x y → x = y
  | _, _, .arith _ U => ∀ x y, U.den ρ x y → x = y
  | _, _, .share _ R => R.fv = [] ∧ R.ConvOK ρ
  | _, _, .comp R S => R.ConvOK ρ ∧ S.ConvOK ρ
  | _, _, .meet R S => R.ConvOK ρ ∧ S.ConvOK ρ
  | _, _, .join R S => R.ConvOK ρ ∧ S.ConvOK ρ
  | _, _, .diff R S => R.ConvOK ρ ∧ S.ConvOK ρ
  | _, _, .pair R S => R.ConvOK ρ ∧ S.ConvOK ρ
  | _, _, .arg f _ => f.ConvOK ρ
  | _, _, _ => True

theorem convTm_of_false {A B : Obj} {t : Tm A B} (h : t.dem = false) : convTm t = .ok (.conv t) := by
  rw [convTm.eq_def, if_pos h]; rfl

theorem conv_false_den (ρ : Val) {A B : Obj} {t : Tm A B} (u : Tm B A) (hu : convTm t = .ok u) (h : t.dem = false) :
    u.den ρ = (t.den ρ)° ∧ ∀ ss, u.argDen ρ ss = (t.argDen ρ ss)° := by
  rw [convTm_of_false h] at hu; cases hu
  exact ⟨rfl, fun ss => by rw [Tm.argDen_false ρ t h ss]; rfl⟩

theorem recip_comp' {α β γ : Type} (R : Core.Rel α β) (S : Core.Rel β γ) : (R ≫ S)° = S° ≫ R° :=
  funext fun _ => funext fun _ => propext ⟨fun ⟨b, h1, h2⟩ => ⟨b, h2, h1⟩, fun ⟨b, h1, h2⟩ => ⟨b, h2, h1⟩⟩

/-- `⟨X,Y⟩° = π₁X° ∩ π₂Y°`: the converse `convTm` and `convProj` build for a pair. -/
theorem recip_rpair {α β γ : Type} (X : Core.Rel γ α) (Y : Core.Rel γ β) :
    (graph Prod.fst ≫ X° ∩ graph Prod.snd ≫ Y°) = (rpair X Y)° :=
  funext fun _ => funext fun _ => propext
    ⟨fun ⟨⟨_, e1, h1⟩, ⟨_, e2, h2⟩⟩ => ⟨e1 ▸ h1, e2 ▸ h2⟩, fun ⟨h1, h2⟩ => ⟨⟨_, rfl, h1⟩, ⟨_, rfl, h2⟩⟩⟩

macro "noproj" : tactic => `(tactic| (intro A₁ A₂ h p hp; cases h <;> (dsimp only at hp; unfold convProj at hp; cases hp)))
macro "noconv" : tactic => `(tactic| (intro u hu; rw [convTm.eq_def, if_neg (by simp [Tm.dem])] at hu; cases hu))

theorem convTm_den (ρ : Val) : ∀ {A B : Obj} (t : Tm A B), t.ConvOK ρ →
    (∀ u, convTm t = .ok u → u.den ρ = (t.den ρ)° ∧ ∀ ss, u.argDen ρ ss = (t.argDen ρ ss)°) ∧
    (∀ A₁ A₂ (h : A = .prod A₁ A₂) p, convProj (h ▸ t) = .ok p → p.den ρ = ((h ▸ t).den ρ)°) := by
  intro A B t
  induction t with
  | val _ | uni _ | zero | conv _ _ | ran _ _ | ldiv _ _ _ _ _ _ _ _ | rdiv _ _ _ _ _ _ _ _ | prod _ _ _ _
  | junc _ _ _ _ | leq _ _ | lt _ _ | nu _ _ _ _ _ | mu _ _ _ _ _ =>
    exact fun _ => ⟨fun u hu => conv_false_den ρ u hu rfl, by noproj⟩
  | top _ _ | lam _ _ | E _ _ | est _ _ | thin _ _ | nil | atPos _ | foldr _ _ _ _ | fold _ _ _ _ | foldI _ _ _ _
  | flat _ _
  | juncD _ _ _ _ | hylo _ _ _ _ => exact fun _ => ⟨by noconv, by noproj⟩
  | id =>
    refine fun _ => ⟨fun u hu => ?_, by noproj⟩
    rw [convTm.eq_def, if_neg (by simp [Tm.dem])] at hu; cases hu
    exact ⟨funext fun _ => funext fun _ => propext ⟨Eq.symm, Eq.symm⟩, fun _ => rfl⟩
  | outl =>
    refine fun _ => ⟨by noconv, fun A₁ A₂ h p hp => ?_⟩
    cases h; dsimp only at hp ⊢; unfold convProj at hp; cases hp; exact Core.Rel.id_comp _
  | outr =>
    refine fun _ => ⟨by noconv, fun A₁ A₂ h p hp => ?_⟩
    cases h; dsimp only at hp ⊢; unfold convProj at hp; cases hp; exact Core.Rel.id_comp _
  | @var A B d k =>
    refine fun hok => ⟨fun u hu => ?_, by noproj⟩
    by_cases hd : (Tm.var d k : Tm A B).dem = false
    · exact conv_false_den ρ u hu hd
    rw [convTm.eq_def, if_neg hd] at hu; cases hu; exact ⟨hok, fun _ => rfl⟩
  | own R _ =>
    refine fun hok => ⟨fun u hu => ?_, by noproj⟩
    by_cases hd : (Tm.own R).dem = false
    · exact conv_false_den ρ u hu hd
    rw [convTm.eq_def, if_neg hd] at hu; cases hu; exact ⟨hok.1.symm, fun ss => (hok.2 ss).symm⟩
  | dom R _ =>
    refine fun _ => ⟨fun u hu => ?_, by noproj⟩
    by_cases hd : (Tm.dom R).dem = false
    · exact conv_false_den ρ u hu hd
    rw [convTm.eq_def, if_neg hd] at hu; cases hu
    exact ⟨funext fun _ => funext fun _ => propext
      ⟨fun ⟨e, c, h1, h2⟩ => ⟨e.symm, c, h2, h1⟩, fun ⟨e, c, h1, h2⟩ => ⟨e.symm, c, h2, h1⟩⟩, fun _ => rfl⟩
  | prim r =>
    refine fun hok => ⟨fun u hu => ?_, by noproj⟩
    rw [convTm.eq_def, if_neg (by simp [Tm.dem])] at hu; dsimp only at hu
    split at hu
    · rename_i r' hr'; cases hu
      cases hc : r.conv with
      | none => rw [hc] at hr'; cases hr'
      | some s =>
        rw [hc] at hr'
        have e := Prim.den_conv r hok s r' hc hr'
        exact ⟨e _ _ [], fun ss => e _ _ ss⟩
    · cases hu
  | @call A B d c os cv =>
    refine fun _ => ⟨fun u hu => ?_, by noproj⟩
    by_cases hd : (Tm.call d c os cv : Tm A B).dem = false
    · exact conv_false_den ρ u hu hd
    rw [convTm.eq_def, if_neg hd] at hu; dsimp only at hu
    split at hu
    · cases hu; exact ⟨funext fun _ => funext fun _ => propext Iff.rfl, fun _ => rfl⟩
    · cases hu
  | arg f x ihf _ =>
    refine fun hok => ⟨fun u hu => ?_, by noproj⟩
    by_cases hd : (Tm.arg f x).dem = false
    · exact conv_false_den ρ u hu hd
    rw [convTm.eq_def, if_neg hd] at hu
    cases hf : convTm f with
    | error l => simp only [hf] at hu; cases hu
    | ok f' =>
      simp only [hf] at hu; cases hu
      exact ⟨((ihf hok).1 _ hf).2 _, fun _ => ((ihf hok).1 _ hf).2 _⟩
  | share k R ih =>
    refine fun hok => ⟨fun u hu => ?_, fun A₁ A₂ h p hp => ?_⟩
    · by_cases hd : (Tm.share k R).dem = false
      · exact conv_false_den ρ u hu hd
      rw [convTm.eq_def, if_neg hd] at hu
      have e := R.den_congr ρ Val.empty fun i hi => by simp [hok.1] at hi
      have ih' := (ih hok.2).1 u hu
      exact ⟨ih'.1.trans (congrArg (·°) e.1), fun ss => (ih'.2 ss).trans (congrArg (·°) (e.2 ss))⟩
    · cases h; dsimp only at hp ⊢; unfold convProj at hp
      have e : R.den ρ = R.den Val.empty := (R.den_congr _ _ fun i hi => by simp [hok.1] at hi).1
      exact ((ih hok.2).2 _ _ rfl p hp).trans (congrArg (·°) e)
  | comp R S ihR ihS =>
    refine fun hok => ⟨fun u hu => ?_, fun A₁ A₂ h p hp => ?_⟩
    · by_cases hd : (Tm.comp R S).dem = false
      · exact conv_false_den ρ u hu hd
      rw [convTm.eq_def, if_neg hd] at hu
      cases hS : convTm S with
      | error l => simp only [hS] at hu; cases hu
      | ok s =>
        cases hR : convTm R with
        | error l => simp only [hS, hR] at hu; cases hu
        | ok r =>
          simp only [hS, hR] at hu; cases hu
          have hs : s.den ρ = (S.den ρ)° := ((ihS hok.2).1 _ hS).1
          have hr : r.den ρ = (R.den ρ)° := ((ihR hok.1).1 _ hR).1
          refine ⟨?_, fun _ => rfl⟩
          show s.den ρ ≫ r.den ρ = _; rw [hs, hr]; exact (recip_comp' _ _).symm
    · cases h; dsimp only at hp ⊢; unfold convProj at hp
      cases hS : convTm S with
      | error l => simp only [hS] at hp; cases hp
      | ok s =>
        cases hR : convProj R with
        | error l => simp only [hS, hR] at hp; cases hp
        | ok x =>
          simp only [hS, hR] at hp; cases hp
          have hs : s.den ρ = (S.den ρ)° := ((ihS hok.2).1 _ hS).1
          rw [Proj.den_pre, hs, (ihR hok.1).2 _ _ rfl x hR]; exact (recip_comp' _ _).symm
  | join R S ihR ihS | diff R S ihR ihS =>
    refine fun hok => ⟨fun u hu => ?_, by noproj⟩
    by_cases hd : (R.dem || S.dem) = false
    · exact conv_false_den ρ u hu hd
    first | rw [convTm.eq_def, if_neg (show ¬ (Tm.join R S).dem = false from hd)] at hu | rw [convTm.eq_def, if_neg (show ¬ (Tm.diff R S).dem = false from hd)] at hu
    cases hR : convTm R with
    | error l => simp only [hR] at hu; cases hu
    | ok r =>
      cases hS : convTm S with
      | error l => simp only [hS, hR] at hu; cases hu
      | ok s =>
        simp only [hS, hR] at hu; cases hu
        have hs : s.den ρ = (S.den ρ)° := ((ihS hok.2).1 _ hS).1
        have hr : r.den ρ = (R.den ρ)° := ((ihR hok.1).1 _ hR).1
        refine ⟨?_, fun _ => rfl⟩
        first
          | (show r.den ρ ∪ s.den ρ = _; rw [hs, hr]; rfl)
          | (show diffDen (r.den ρ) (s.den ρ) = _; rw [hs, hr]; rfl)
  | succ U _ =>
    refine fun hok => ⟨fun u hu => ?_, by noproj⟩
    rw [convTm.eq_def, if_neg (by simp [Tm.dem])] at hu; cases hu
    refine ⟨?_, fun _ => rfl⟩
    refine congrArg (·°) (funext fun a => funext fun w => propext ⟨fun ⟨v, hv, h⟩ => (hok _ _ hv) ▸ h, fun h => ⟨a, ?_, h⟩⟩)
    obtain ⟨v, hv⟩ := h.1; obtain rfl := hok _ _ hv; exact hv
  | arith k U _ =>
    refine fun hok => ⟨fun u hu => ?_, by noproj⟩
    rw [convTm.eq_def, if_neg (by simp [Tm.dem])] at hu; cases hu
    refine ⟨?_, fun _ => rfl⟩
    have key : ∀ p w, arithDen k (U.den ρ) p w → U.den ρ p.1 p.1 ∧ U.den ρ p.2 p.2 := by
      rintro p w ⟨p', ⟨rfl, c, ⟨a', e1, h1⟩, -⟩, p'', ⟨rfl, c', ⟨b', e2, h2⟩, -⟩, -⟩
      subst e1 e2
      refine ⟨?_, ?_⟩
      · obtain rfl := hok _ _ h1; exact h1
      · obtain rfl := hok _ _ h2; exact h2
    refine congrArg (·°) (funext fun p => funext fun w => propext ⟨fun ⟨q, ⟨h1, h2⟩, ha⟩ => ?_, fun ha => ⟨p, key p w ha, ha⟩⟩)
    have e : p = q := Prod.ext (hok _ _ h1) (hok _ _ h2)
    subst e; exact ha
  | @meet A' _ R S ihR ihS =>
    refine fun hok => ⟨fun u hu => ?_, fun A₁ A₂ h p hp => ?_⟩
    · by_cases hd : (Tm.meet R S).dem = false
      · exact conv_false_den ρ u hu hd
      rw [convTm.eq_def, if_neg hd] at hu
      cases hR : convTm R with
      | ok r =>
        cases hS : convTm S with
        | ok s =>
          simp only [hR, hS] at hu; cases hu
          have hs : s.den ρ = (S.den ρ)° := ((ihS hok.2).1 _ hS).1
          have hr : r.den ρ = (R.den ρ)° := ((ihR hok.1).1 _ hR).1
          refine ⟨?_, fun _ => rfl⟩
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
                  refine ⟨?_, Proj.meet_argDen _ _ _ hm ρ⟩
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
                refine ⟨?_, Proj.meet_argDen _ _ _ hm ρ⟩
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
  | @pair A' _ _ R S ihR ihS =>
    refine fun hok => ⟨fun u hu => ?_, fun A₁ A₂ h p hp => ?_⟩
    · by_cases hd : (Tm.pair R S).dem = false
      · exact conv_false_den ρ u hu hd
      rw [convTm.eq_def, if_neg hd] at hu
      cases hR : convTm R with
      | ok r =>
        have hr := ((ihR hok.1).1 _ hR).1
        cases hS : convTm S with
        | ok s =>
          have hs : s.den ρ = (S.den ρ)° := ((ihS hok.2).1 _ hS).1
          simp only [hR, hS] at hu; cases hu
          refine ⟨?_, fun _ => rfl⟩
          show graph Prod.fst ≫ r.den ρ ∩ graph Prod.snd ≫ s.den ρ = _; rw [hr, hs]; exact recip_rpair _ _
        | error l =>
          simp only [hR, hS] at hu; cases hu
          refine ⟨?_, fun _ => rfl⟩
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
          have hs : s.den ρ = (S.den ρ)° := ((ihS hok.2).1 _ hS).1
          simp only [hR, hS] at hu; cases hu
          refine ⟨?_, fun _ => rfl⟩
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
                  refine ⟨?_, Proj.meet_argDen _ _ _ hm ρ⟩
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
