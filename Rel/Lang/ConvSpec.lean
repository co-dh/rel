import Rel.Lang.Den
import Rel.Run.Lang.Elab

namespace Rel.Lang

open Rel.Core.Rel hiding id comp recip inter union zero le inl inr junc
open scoped Rel.Core.Rel

/-! ### `convTm` read back: the converse it builds means the converse (§4.2) -/

/-- `t°` as `Proj` holds it: `Zπ₁°` or `Zπ₂°`. -/
noncomputable def Proj.den (ρ : Val) {B A₁ A₂ : Obj} : Proj B A₁ A₂ → Core.Rel (Obj.El B) (Obj.El (.prod A₁ A₂))
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
    simp only [Proj.meet, Sum.inr.injEq] at hz; subst hz; exact (Rep.meet_comp_conv_graph _ _ _).symm
  · refine ⟨fun u hu => ?_, fun z hz => by simp only [Proj.meet, reduceCtorEq] at hz⟩
    simp only [Proj.meet, Sum.inl.injEq] at hu; subst hu; exact (Rep.rpair_eq_meet_proj _ _).symm
  · refine ⟨fun u hu => ?_, fun z hz => by simp only [Proj.meet, reduceCtorEq] at hz⟩
    simp only [Proj.meet, Sum.inl.injEq] at hu; subst hu
    exact (Rep.rpair_eq_meet_proj _ _).symm.trans (funext fun _ => funext fun _ => propext and_comm)
  · refine ⟨fun u hu => by simp only [Proj.meet, reduceCtorEq] at hu, fun z hz => ?_⟩
    simp only [Proj.meet, Sum.inr.injEq] at hz; subst hz; exact (Rep.meet_comp_conv_graph _ _ _).symm

/-- `Proj.meet` across the two projections is a pair, no row's spine. -/
theorem Proj.meet_argDen {B A₁ A₂ : Obj} (x y : Proj B A₁ A₂) (t : Tm B (.prod A₁ A₂))
    (h : Proj.meet x y = .inl t) (ρ : Val) (ss : List Sem) : t.argDen ρ ss = 𝟘 := by
  rcases x with x | x <;> rcases y with y | y <;> simp only [Proj.meet, reduceCtorEq, Sum.inl.injEq] at h <;>
    subst h <;> rfl

/-- `Prim.den` read off: the row's meaning at the object variables `σ` its constant's type takes at `A ⟶ B`. -/
theorem Prim.den_iff {r : Prim} {x : (c : RowCode) × RowDen c} (e : rowDens.find? (·.1.sym == r.sym) = some x)
    {A B : Obj} {ss : List Sem} {a : A.El} {b : B.El} : Prim.den r A B ss a b ↔
      ∃ σ, r.objs A B (ss.map fun s => (s.1, s.2.1)) = some σ ∧
        ∃ h : (x.1.ty σ).1 = A ∧ (x.1.ty σ).2 = B, (h.1 ▸ h.2 ▸ x.2 σ ss) a b := by
  unfold Prim.den; rw [e]
  cases r.objs A B (ss.map fun s => (s.1, s.2.1)) with
  | none => exact ⟨fun h => False.elim h, fun ⟨_, h, _⟩ => by cases h⟩
  | some σ =>
    by_cases h : (x.1.ty σ).1 = A ∧ (x.1.ty σ).2 = B
    · simp [h]
    · simp [h]; exact ⟨fun h' => False.elim h', fun ⟨h', _⟩ => h'.elim⟩

/-- `Prim.objs` of a row with a converse, computed: the variables its constant's type names, as `Prim.den_conv` reads them. -/
local macro "objs_simp" : tactic => `(tactic| simp [Prim.objs, Option.orElse, Prim.vars, OExp.vars, OExp.unify, List.eraseDups,
  List.eraseDupsBy, List.eraseDupsBy.loop, consRow, RowCode.cons,
  RowCode.uncons, RowCode.cat, RowCode.uncat, RowCode.snoc, RowCode.unsnoc, List.lookup, σ₁, σ₂])

/-- A row whose meaning of its one argument is a coreflexive (`dom`, `ran`) relates a value only to itself. -/
theorem Sem.one_corefl {X Y A : Obj} {D : Core.Rel (Obj.El X) (Obj.El Y) → Core.Rel (Obj.El A) (Obj.El A)} (hD : ∀ T a b, D T a b → a = b) :
    ∀ ss a b, Sem.one D ss a b → a = b := by
  intro ss a b h; unfold Sem.one at h; split at h
  · split at h
    · exact hD _ _ _ h
    · exact (h : False).elim
  · exact (h : False).elim

/-- `Tm.instObj` of the rows `dom`, `ran` given their argument: one bind, as of any constructor with one part. -/
theorem Tm.instObj_dom (ph : List Rel.QAtomicType) (σ : List Obj) {A B : Obj} (R : Tm A B) :
    (Tm.dom R).instObj ph σ = (do return Tm.dom (← R.instObj ph σ)) := rfl

theorem Tm.instObj_ran (ph : List Rel.QAtomicType) (σ : List Obj) {A B : Obj} (R : Tm A B) :
    (Tm.ran R).instObj ph σ = (do return Tm.ran (← R.instObj ph σ)) := rfl

/-- **Every row of `prims` with a converse row (`conv`) means that row's converse**, at all objects and arguments:
    `convTm`'s `prim` case. The rows are enumerated from `prims`, so a row given a `conv` it does not mean fails here. -/
theorem Prim.den_conv : ∀ r ∈ prims, ∀ s r', r.conv = some s → Prim.find? s = some r' →
    ∀ A B ss, Prim.den r' B A ss = (Prim.den r A B ss)° := by
  -- one goal per row or mapped list, whatever the order of `prims`; a row with no converse (`floatOps`, `arithOps`, …)
  -- closes at `cases hs`
  simp only [prims, List.forall_mem_append, List.forall_mem_cons, List.forall_mem_map, List.mem_nil_iff,
    false_implies, implies_true, and_true]
  repeat' apply And.intro
  all_goals (try intro _ (_ : _ ∈ _)); intro s r' hs hr'; first | cases hs | simp at hs
  all_goals simp [Prim.find?, prims, consRow, mapRow, lengthRow,
    sumRow, flatRow, foldIRow, starRow, domRow, ranRow, nilRow, estRow, frontRow] at hr'
  all_goals subst hr'
  all_goals
    intro A B ss
    funext b a; apply propext; rw [recip_apply, Prim.den_iff rfl, Prim.den_iff rfl]
    constructor
    all_goals
      rintro ⟨σ, hσ, ⟨rfl, rfl⟩, h⟩
      -- the converse row lists the variables in its own order: one, two in order, or the two swapped (`inr`/`inr°`);
      -- a row that is its own converse (`dom`, `ran`) means a coreflexive, so its two ends are one
      first
        | exact ⟨[σ₁ σ], by objs_simp, ⟨rfl, rfl⟩, h⟩
        | exact ⟨[σ₁ σ, σ₂ σ], by objs_simp, ⟨rfl, rfl⟩, h⟩
        | exact ⟨[σ₂ σ, σ₁ σ], by objs_simp, ⟨rfl, rfl⟩, h⟩
        | (obtain rfl : b = a := by
             first
               | exact Sem.one_corefl (D := fun T => 𝟙 _ ∩ T ≫ T°) (fun _ _ _ h => h.1) ss _ _ h
               | exact (Sem.one_corefl (D := fun T => 𝟙 _ ∩ T ≫ T°) (fun _ _ _ h => h.1) ss _ _ h).symm
               | exact Sem.one_corefl (D := fun T => 𝟙 _ ∩ T° ≫ T°°) (fun _ _ _ h => h.1) ss _ _ h
               | exact (Sem.one_corefl (D := fun T => 𝟙 _ ∩ T° ≫ T°°) (fun _ _ _ h => h.1) ss _ _ h).symm
           exact ⟨σ, hσ, ⟨rfl, rfl⟩, h⟩)

/-- What `convTm_den` needs of `t` under `ρ` at the nodes whose converse `convTm` takes as given: a variable and
    `own` are their own converse (as a row's spine too), a number verb's universe is a coreflexive, a shared term
    is closed, a row is one of `prims` (whose `conv` `Prim.den_conv` checks). -/
def Tm.ConvOK (ρ : Val) : {A B : Obj} → Tm A B → Prop
  | A, B, .var _ k => ρ k B A = (ρ k A B)°
  | _, _, .own R => (R.den ρ)° = R.den ρ ∧ ∀ ss, (R.argDen ρ ss)° = R.argDen ρ ss
  | _, _, .prim r => r ∈ prims
  | _, _, .share _ R => R.fv = [] ∧ R.ConvOK ρ
  | _, _, .comp R S => R.ConvOK ρ ∧ S.ConvOK ρ
  | _, _, .meet R S => R.ConvOK ρ ∧ S.ConvOK ρ
  | _, _, .join R S => R.ConvOK ρ ∧ S.ConvOK ρ
  | _, _, .diff R S => R.ConvOK ρ ∧ S.ConvOK ρ
  | _, _, .pair R S => R.ConvOK ρ ∧ S.ConvOK ρ
  | _, _, .arg f _ => f.ConvOK ρ
  -- `convTm` swaps the bodies: that `u` means `b`'s converse under every binding of the arguments holds of every
  -- node `callTm` builds whose body is `ConvOK` there (`callTm_convOK`)
  | _, _, .callCv ks _ _ _ b u => ∀ ss, u.den (Val.args ks ss) = (b.den (Val.args ks ss))°
  | _, _, _ => True

theorem convTm_of_false {A B : Obj} {t : Tm A B} (h : t.dem = false) : convTm t = .ok (.conv t) := by
  rw [convTm.eq_def, if_pos h]; rfl

theorem conv_false_den (ρ : Val) {A B : Obj} {t : Tm A B} (u : Tm B A) (hu : convTm t = .ok u) (h : t.dem = false) :
    u.den ρ = (t.den ρ)° ∧ (t.dem = true → ∀ ss, u.argDen ρ ss = (t.argDen ρ ss)°) := by
  rw [convTm_of_false h] at hu; cases hu
  exact ⟨rfl, fun h' => absurd (h.symm.trans h') Bool.false_ne_true⟩

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
    (∀ u, convTm t = .ok u → u.den ρ = (t.den ρ)° ∧ (t.dem = true → ∀ ss, u.argDen ρ ss = (t.argDen ρ ss)°)) ∧
    (∀ A₁ A₂ (h : A = .prod A₁ A₂) p, convProj (h ▸ t) = .ok p → p.den ρ = ((h ▸ t).den ρ)°) := by
  intro A B t
  induction t with
  | val _ | uni _ | zero | ldiv _ _ _ _ _ _ _ _ | rdiv _ _ _ _ _ _ _ _
  | leq _ _ _ | lt _ _ _ | nu _ _ _ _ _ | mu _ _ _ _ _ =>
    exact fun _ => ⟨fun u hu => conv_false_den ρ u hu rfl, by noproj⟩
  | top _ _ | lam _ _ | mem | atPos _ | foldr _ _ _ _ | fold _ _ _ _
  | hylo _ _ _ _ => exact fun _ => ⟨by noconv, by noproj⟩
  -- an injection's converse is `conv` of it, which runs on demand (`Tm.dem`), and its converse the injection
  | inl | inr => exact fun _ => ⟨fun u hu => by
      rw [convTm.eq_def, if_neg (by simp [Tm.dem])] at hu; cases hu; exact ⟨rfl, fun _ _ => rfl⟩, by noproj⟩
  | conv R _ =>
    refine fun _ => ⟨fun u hu => ?_, by noproj⟩
    by_cases h : (Tm.conv R).dem = false
    · exact conv_false_den ρ u hu h
    · cases R <;> simp [Tm.dem] at h <;>
        (rw [convTm.eq_def, if_neg (by simp [Tm.dem])] at hu; cases hu; exact ⟨rfl, fun _ _ => rfl⟩)
  | id =>
    refine fun _ => ⟨fun u hu => ?_, by noproj⟩
    rw [convTm.eq_def, if_neg (by simp [Tm.dem])] at hu; cases hu
    exact ⟨funext fun _ => funext fun _ => propext ⟨Eq.symm, Eq.symm⟩, fun _ _ => rfl⟩
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
    rw [convTm.eq_def, if_neg hd] at hu; cases hu; exact ⟨hok, fun _ _ => rfl⟩
  | own R _ =>
    refine fun hok => ⟨fun u hu => ?_, by noproj⟩
    by_cases hd : (Tm.own R).dem = false
    · exact conv_false_den ρ u hu hd
    rw [convTm.eq_def, if_neg hd] at hu; cases hu; exact ⟨hok.1.symm, fun _ ss => (hok.2 ss).symm⟩
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
        exact ⟨e _ _ [], fun _ ss => e _ _ ss⟩
    · cases hu
  | @call A B ks c os b _ =>
    refine fun _ => ⟨fun u hu => ?_, by noproj⟩
    by_cases hd : (Tm.call ks c os b : Tm A B).dem = false
    · exact conv_false_den ρ u hu hd
    rw [convTm.eq_def, if_neg hd] at hu; dsimp only at hu; cases hu
  | @callCv A B ks c c' os b v _ _ =>
    refine fun hok => ⟨fun u hu => ?_, by noproj⟩
    by_cases hd : (Tm.callCv ks c c' os b v : Tm A B).dem = false
    · exact conv_false_den ρ u hu hd
    rw [convTm.eq_def, if_neg hd] at hu; dsimp only at hu; cases hu
    exact ⟨hok [], fun _ ss => hok ss⟩
  | arg f x ihf _ =>
    refine fun hok => ⟨fun u hu => ?_, by noproj⟩
    by_cases hd : (Tm.arg f x).dem = false
    · exact conv_false_den ρ u hu hd
    rw [convTm.eq_def, if_neg hd] at hu; dsimp only at hu
    by_cases hd' : f.dem = true
    case neg => rw [if_neg hd'] at hu; cases hu
    rw [if_pos hd'] at hu
    cases hf : convTm f with
    | error l => simp only [hf] at hu; cases hu
    | ok f' =>
      simp only [hf] at hu; cases hu
      exact ⟨((ihf hok).1 _ hf).2 hd' _, fun _ _ => ((ihf hok).1 _ hf).2 hd' _⟩
  | share k R ih =>
    refine fun hok => ⟨fun u hu => ?_, fun A₁ A₂ h p hp => ?_⟩
    · by_cases hd : (Tm.share k R).dem = false
      · exact conv_false_den ρ u hu hd
      rw [convTm.eq_def, if_neg hd] at hu
      have e := R.den_congr ρ Val.empty fun i hi => by simp [hok.1] at hi
      have ih' := (ih hok.2).1 u hu
      exact ⟨ih'.1.trans (congrArg (·°) e.1), fun h ss => (ih'.2 h ss).trans (congrArg (·°) (e.2 ss))⟩
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
          refine ⟨?_, fun _ _ => rfl⟩
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
    -- `join` needs keys where either operand does, `diff` where `R` does (`Tm.dem`): the alternative of `hu`'s term
    first
      | (by_cases hd : (Tm.join R S).dem = false
         · exact conv_false_den ρ u hu hd
         rw [convTm.eq_def, if_neg hd] at hu)
      | (by_cases hd : (Tm.diff R S).dem = false
         · exact conv_false_den ρ u hu hd
         rw [convTm.eq_def, if_neg hd] at hu)
    cases hR : convTm R with
    | error l => simp only [hR] at hu; cases hu
    | ok r =>
      cases hS : convTm S with
      | error l => simp only [hS, hR] at hu; cases hu
      | ok s =>
        simp only [hS, hR] at hu; cases hu
        have hs : s.den ρ = (S.den ρ)° := ((ihS hok.2).1 _ hS).1
        have hr : r.den ρ = (R.den ρ)° := ((ihR hok.1).1 _ hR).1
        refine ⟨?_, fun _ _ => rfl⟩
        first
          | (show r.den ρ ∪ s.den ρ = _; rw [hs, hr]; rfl)
          | (show diffDen (r.den ρ) (s.den ρ) = _; rw [hs, hr]; rfl)
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
          refine ⟨?_, fun _ _ => rfl⟩
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
                  refine ⟨?_, fun _ => Proj.meet_argDen _ _ _ hm ρ⟩
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
                refine ⟨?_, fun _ => Proj.meet_argDen _ _ _ hm ρ⟩
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
          refine ⟨?_, fun _ _ => rfl⟩
          show graph Prod.fst ≫ r.den ρ ∩ graph Prod.snd ≫ s.den ρ = _; rw [hr, hs]; exact recip_rpair _ _
        | error l =>
          simp only [hR, hS] at hu; cases hu
          refine ⟨?_, fun _ _ => rfl⟩
          -- `⟨π₁R°,π₂⟩τ(S)π₁`: `(b,c) ↦ (a,c) ↦ a` with `a R b` and `a S c`
          simp only [pairTest, ↓Tm.dom_den, Tm.dom_den, Tm.den]
          show rpair (graph Prod.fst ≫ r.den ρ) (graph Prod.snd) ≫
            ((𝟙 _ ∩ (graph Prod.snd ∩ graph Prod.fst ≫ S.den ρ) ≫ (graph Prod.snd ∩ graph Prod.fst ≫ S.den ρ)°) ≫
              graph Prod.fst) = _
          rw [hr]; funext q a; apply propext
          simp only [Core.Rel.comp, Core.Rel.inter, Core.Rel.recip, Core.Rel.id, graph, rpair, Prod.exists,
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
          refine ⟨?_, fun _ _ => rfl⟩
          -- `⟨π₁,π₂S°⟩ swap τ(R) swap π₂`: `(b,c) ↦ (b,a) ↦ (a,b) ↦ (b,a) ↦ a` with `a S c` and `a R b`
          simp only [pairTest, ↓Tm.dom_den, Tm.dom_den, Tm.den]
          show rpair (graph Prod.fst) (graph Prod.snd ≫ s.den ρ) ≫
            (rpair (graph Prod.snd) (graph Prod.fst) ≫
              ((𝟙 _ ∩ (graph Prod.snd ∩ graph Prod.fst ≫ R.den ρ) ≫ (graph Prod.snd ∩ graph Prod.fst ≫ R.den ρ)°) ≫
                (rpair (graph Prod.snd) (graph Prod.fst) ≫ graph Prod.snd))) = _
          rw [hs]; funext q a; apply propext
          simp only [Core.Rel.comp, Core.Rel.inter, Core.Rel.recip, Core.Rel.id, graph, rpair, Prod.exists,
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
                  refine ⟨?_, fun _ => Proj.meet_argDen _ _ _ hm ρ⟩
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

/-! ### `convTm` through `Tm.instObj`: a call's converse body means the converse of its body

`convOf` takes the converse of a definition's body at the placeholders, and `callTm` instantiates both at the
call's objects. `convTm` reads its term's objects (a `meet` or `pair` over a product source tries `convProj`), so
`convTm` of the instantiated body may take another branch; what holds is that the instantiated converse means the
converse of the instantiated body (`convTm_instObj_den`), which is what `Tm.ConvOK` asks of a `callCv`. -/

theorem bind_ok_iff {ε α β : Type} {x : Except ε α} {f : α → Except ε β} {b : β} :
    (x >>= f) = .ok b ↔ ∃ a, x = .ok a ∧ f a = .ok b :=
  match x with
  | .error _ => ⟨fun h => (nomatch h), fun ⟨_, h, _⟩ => (nomatch h)⟩
  | .ok a => ⟨fun h => ⟨a, rfl, h⟩, fun ⟨_, h, h'⟩ => by cases h; exact h'⟩

theorem pure_ok_iff {ε α : Type} {a b : α} : (pure a : Except ε α) = .ok b ↔ a = b := by
  simp [pure, Except.pure]

theorem mapError_ok_iff {ε ε' α : Type} {f : ε → ε'} {x : Except ε α} {b : α} :
    x.mapError f = .ok b ↔ x = .ok b := by
  cases x <;> simp [Except.mapError]

/-- A node `Tm.instObj.fixed` keeps: `σ` keeps its objects and the node is `t` itself, moved along that equality.
    Stated for any `X Y`, because at an atom in `varAtoms` (a float) `Obj.inst` does not reduce. -/
theorem fixed_ok (ph : List Rel.QAtomicType) (σ : List Obj) {X Y : Obj} {t : Tm X Y} {t'}
    (h : Tm.instObj.fixed ph σ t = .ok t') :
    ∃ e : X.inst ph σ = X ∧ Y.inst ph σ = Y, t' = cast (by rw [e.1, e.2]) t := by
  unfold Tm.instObj.fixed at h; split at h
  · rename_i e; exact ⟨e, (pure_ok_iff.1 h).symm⟩
  · cases h

/-- `fixed_ok` backwards (`Tm.instObj.back`). -/
theorem back_ok (ph : List Rel.QAtomicType) (σ : List Obj) {X Y : Obj} {t : Tm (X.inst ph σ) (Y.inst ph σ)} {t'}
    (h : Tm.instObj.back ph σ t = .ok t') :
    ∃ e : X.inst ph σ = X ∧ Y.inst ph σ = Y, t' = cast (by rw [e.1, e.2]) t := by
  unfold Tm.instObj.back at h; split at h
  · rename_i e; exact ⟨e, (pure_ok_iff.1 h).symm⟩
  · cases h

/-- `p` at the objects `σ`: its term's `Tm.instObj`. -/
def Proj.instObj (ph : List Rel.QAtomicType) (σ : List Obj) {B A₁ A₂ : Obj} :
    Proj B A₁ A₂ → Except String (Proj (B.inst ph σ) (A₁.inst ph σ) (A₂.inst ph σ))
  | .inl z => return .inl (← z.instObj ph σ)
  | .inr z => return .inr (← z.instObj ph σ)

theorem Proj.instObj_pre (ph : List Rel.QAtomicType) (σ : List Obj) {C B A₁ A₂ : Obj} (s : Tm C B) (x : Proj B A₁ A₂) {p'}
    (h : (Proj.pre s x).instObj ph σ = .ok p') :
    ∃ s' x', s.instObj ph σ = .ok s' ∧ x.instObj ph σ = .ok x' ∧ p' = Proj.pre s' x' := by
  rcases x with z | z <;> simp only [Proj.pre, Proj.instObj, Tm.instObj, bind_ok_iff, pure_ok_iff] at h <;>
    obtain ⟨_, ⟨s', hs, z', hz, rfl⟩, rfl⟩ := h
  · exact ⟨s', .inl z', hs, by simp only [Proj.instObj, hz]; rfl, rfl⟩
  · exact ⟨s', .inr z', hs, by simp only [Proj.instObj, hz]; rfl, rfl⟩

theorem Proj.instObj_meet_inl (ph : List Rel.QAtomicType) (σ : List Obj) {B A₁ A₂ : Obj} (x y : Proj B A₁ A₂) {t} (hm : Proj.meet x y = .inl t)
    {t'} (ht : t.instObj ph σ = .ok t') :
    ∃ x' y', x.instObj ph σ = .ok x' ∧ y.instObj ph σ = .ok y' ∧ Proj.meet x' y' = .inl t' := by
  rcases x with x | x <;> rcases y with y | y <;> simp only [Proj.meet, reduceCtorEq, Sum.inl.injEq] at hm <;>
    subst hm <;> simp only [Tm.instObj, bind_ok_iff, pure_ok_iff] at ht <;> obtain ⟨a, ha, b, hb, rfl⟩ := ht
  · exact ⟨.inl a, .inr b, by simp only [Proj.instObj, ha]; rfl, by simp only [Proj.instObj, hb]; rfl, rfl⟩
  · exact ⟨.inr b, .inl a, by simp only [Proj.instObj, hb]; rfl, by simp only [Proj.instObj, ha]; rfl, rfl⟩

theorem Proj.instObj_meet_inr (ph : List Rel.QAtomicType) (σ : List Obj) {B A₁ A₂ : Obj} (x y : Proj B A₁ A₂) {z} (hm : Proj.meet x y = .inr z)
    {z'} (hz : z.instObj ph σ = .ok z') :
    ∃ x' y', x.instObj ph σ = .ok x' ∧ y.instObj ph σ = .ok y' ∧ Proj.meet x' y' = .inr z' := by
  rcases x with x | x <;> rcases y with y | y <;> simp only [Proj.meet, reduceCtorEq, Sum.inr.injEq] at hm <;>
    subst hm <;> simp only [Proj.instObj, Tm.instObj, bind_ok_iff, pure_ok_iff] at hz <;>
    obtain ⟨_, ⟨a, ha, b, hb, rfl⟩, rfl⟩ := hz
  · exact ⟨.inl a, .inl b, by simp only [Proj.instObj, ha]; rfl, by simp only [Proj.instObj, hb]; rfl, rfl⟩
  · exact ⟨.inr a, .inr b, by simp only [Proj.instObj, ha]; rfl, by simp only [Proj.instObj, hb]; rfl, rfl⟩

/-- `conv_false_den` through `Tm.instObj`: a term that needs no keys is conversed whole. -/
theorem inst_false_den (ph : List Rel.QAtomicType) (σ : List Obj) (ρ : Val) {A B : Obj} {t : Tm A B} {t' : Tm (A.inst ph σ) (B.inst ph σ)} {u : Tm B A}
    {u' : Tm (B.inst ph σ) (A.inst ph σ)} (h : t.dem = false) (hu : convTm t = .ok u) (hu' : u.instObj ph σ = .ok u')
    (ht : t.instObj ph σ = .ok t') :
    u'.den ρ = (t'.den ρ)° ∧ (t.dem = true → ∀ ss, u'.argDen ρ ss = (t'.argDen ρ ss)°) := by
  rw [convTm_of_false h] at hu; cases hu
  simp only [Tm.instObj, bind_ok_iff, pure_ok_iff, ht, Except.ok.injEq, exists_eq_left'] at hu'
  subst hu'; exact ⟨rfl, fun h' => absurd (h.symm.trans h') Bool.false_ne_true⟩

macro "noproj'" : tactic =>
  `(tactic| (intro A₁ A₂ h p p' hp hp'; cases h <;> (dsimp only at hp; unfold convProj at hp; cases hp)))
macro "noconv'" : tactic =>
  `(tactic| (intro u u' hu hu'; rw [convTm.eq_def, if_neg (by simp [Tm.dem])] at hu; cases hu))

/-- **`convTm_den` at the objects `σ`**: `u = convTm t`, both instantiated (`Tm.instObj ph σ`), `u` means the converse
    of `t` wherever the instantiated `t` is `ConvOK`; and the same of `convProj`. Every constructor `instObj`
    handles, by the case of `convTm` the term at the placeholders took. -/
theorem convTm_instObj_den (ph : List Rel.QAtomicType) (σ : List Obj) (ρ : Val) : ∀ {A B : Obj} (t : Tm A B) (t' : Tm (A.inst ph σ) (B.inst ph σ)),
    t.instObj ph σ = .ok t' → t'.ConvOK ρ →
    (∀ u u', convTm t = .ok u → u.instObj ph σ = .ok u' →
      u'.den ρ = (t'.den ρ)° ∧ (t.dem = true → ∀ ss, u'.argDen ρ ss = (t'.argDen ρ ss)°)) ∧
    (∀ A₁ A₂ (h : A = .prod A₁ A₂) p p', convProj (h ▸ t) = .ok p → p.instObj ph σ = .ok p' →
      p'.den ρ = ((h ▸ t' : Tm ((Obj.prod A₁ A₂).inst ph σ) (B.inst ph σ)).den ρ)°) := by
  intro A B t
  induction t with
  | val _ | uni _ | zero | ldiv _ _ _ _ _ _ _ _ | rdiv _ _ _ _ _ _ _ _
  | leq _ _ _ | lt _ _ _ | nu _ _ _ _ _ | mu _ _ _ _ _ =>
    exact fun t' ht _ => ⟨fun u u' hu hu' => inst_false_den ph σ ρ rfl hu hu' ht, by noproj'⟩
  | top _ _ | lam _ _ | mem | atPos _ | foldr _ _ _ _ | fold _ _ _ _
  | hylo _ _ _ _ => exact fun _ _ _ => ⟨by noconv', by noproj'⟩
  | id =>
    refine fun t' ht _ => ⟨fun u u' hu hu' => ?_, by noproj'⟩
    rw [convTm.eq_def, if_neg (by simp [Tm.dem])] at hu; cases hu
    simp only [Tm.instObj, pure_ok_iff] at ht hu'; subst ht hu'
    exact ⟨funext fun _ => funext fun _ => propext ⟨Eq.symm, Eq.symm⟩, fun _ _ => rfl⟩
  | inl | inr =>
    refine fun t' ht _ => ⟨fun u u' hu hu' => ?_, by noproj'⟩
    rw [convTm.eq_def, if_neg (by simp [Tm.dem])] at hu; cases hu
    simp only [Tm.instObj, bind_ok_iff, pure_ok_iff] at ht hu'; obtain ⟨_, rfl, rfl⟩ := hu'; subst ht
    exact ⟨rfl, fun _ _ => rfl⟩
  | conv R _ =>
    refine fun t' ht _ => ⟨fun u u' hu hu' => ?_, by noproj'⟩
    by_cases hd : (Tm.conv R).dem = false
    · exact inst_false_den ph σ ρ hd hu hu' ht
    cases R <;> simp [Tm.dem] at hd <;>
      (rw [convTm.eq_def, if_neg (by simp [Tm.dem])] at hu; cases hu
       simp only [Tm.instObj, bind_ok_iff, pure_ok_iff] at ht hu'; obtain ⟨_, rfl, rfl⟩ := ht; subst hu'
       exact ⟨rfl, fun _ _ => rfl⟩)
  | outl =>
    refine fun t' ht _ => ⟨by noconv', fun A₁ A₂ h p p' hp hp' => ?_⟩
    cases h; dsimp only at hp ⊢; unfold convProj at hp; cases hp
    simp only [Tm.instObj, Proj.instObj, bind_ok_iff, pure_ok_iff] at ht hp'
    obtain ⟨_, rfl, rfl⟩ := hp'; subst ht; exact Core.Rel.id_comp _
  | outr =>
    refine fun t' ht _ => ⟨by noconv', fun A₁ A₂ h p p' hp hp' => ?_⟩
    cases h; dsimp only at hp ⊢; unfold convProj at hp; cases hp
    simp only [Tm.instObj, Proj.instObj, bind_ok_iff, pure_ok_iff] at ht hp'
    obtain ⟨_, rfl, rfl⟩ := hp'; subst ht; exact Core.Rel.id_comp _
  | @var A B d k =>
    refine fun t' ht hok => ⟨fun u u' hu hu' => ?_, by noproj'⟩
    by_cases hd : (Tm.var d k : Tm A B).dem = false
    · exact inst_false_den ph σ ρ hd hu hu' ht
    rw [convTm.eq_def, if_neg hd] at hu; cases hu
    simp only [Tm.instObj, pure_ok_iff] at ht hu'; subst ht hu'; exact ⟨hok, fun _ _ => rfl⟩
  | own R _ =>
    refine fun t' ht hok => ⟨fun u u' hu hu' => ?_, by noproj'⟩
    by_cases hd : (Tm.own R).dem = false
    · exact inst_false_den ph σ ρ hd hu hu' ht
    rw [convTm.eq_def, if_neg hd] at hu; cases hu
    cases hu'.symm.trans ht
    simp only [Tm.instObj, bind_ok_iff, pure_ok_iff] at ht; obtain ⟨_, _, rfl⟩ := ht
    exact ⟨hok.1.symm, fun _ ss => (hok.2 ss).symm⟩
  | prim r =>
    refine fun t' ht hok => ⟨fun u u' hu hu' => ?_, by noproj'⟩
    simp only [Tm.instObj, pure_ok_iff] at ht; subst ht
    rw [convTm.eq_def, if_neg (by simp [Tm.dem])] at hu; dsimp only at hu
    split at hu
    · rename_i r' hr'; cases hu
      simp only [Tm.instObj, pure_ok_iff] at hu'; subst hu'
      cases hc : r.conv with
      | none => rw [hc] at hr'; cases hr'
      | some s =>
        rw [hc] at hr'
        have e := Prim.den_conv r hok s r' hc hr'
        exact ⟨e _ _ [], fun _ ss => e _ _ ss⟩
    · cases hu
  | @call A B ks c os b _ =>
    refine fun t' ht _ => ⟨fun u u' hu hu' => ?_, by noproj'⟩
    by_cases hd : (Tm.call ks c os b : Tm A B).dem = false
    · exact inst_false_den ph σ ρ hd hu hu' ht
    rw [convTm.eq_def, if_neg hd] at hu; dsimp only at hu; cases hu
  | @callCv A B ks c c' os b v _ _ =>
    refine fun t' ht hok => ⟨fun u u' hu hu' => ?_, by noproj'⟩
    by_cases hd : (Tm.callCv ks c c' os b v : Tm A B).dem = false
    · exact inst_false_den ph σ ρ hd hu hu' ht
    rw [convTm.eq_def, if_neg hd] at hu; dsimp only at hu; cases hu
    simp only [Tm.instObj, bind_ok_iff, pure_ok_iff] at ht hu'
    obtain ⟨b', hb, v', hv, rfl⟩ := ht
    obtain ⟨v'', hv', b'', hb', rfl⟩ := hu'
    rw [hv] at hv'; cases hv'; rw [hb] at hb'; cases hb'
    exact ⟨hok [], fun _ ss => hok ss⟩
  | arg f x ihf _ =>
    refine fun t' ht hok => ⟨fun u u' hu hu' => ?_, by noproj'⟩
    by_cases hd : (Tm.arg f x).dem = false
    · exact inst_false_den ph σ ρ hd hu hu' ht
    rw [convTm.eq_def, if_neg hd] at hu; dsimp only at hu
    by_cases hd' : f.dem = true
    case neg => rw [if_neg hd'] at hu; cases hu
    rw [if_pos hd'] at hu
    cases hf : convTm f with
    | error l => simp only [hf] at hu; cases hu
    | ok f₀ =>
      simp only [hf] at hu; cases hu
      simp only [Tm.instObj, bind_ok_iff, pure_ok_iff] at ht hu'
      obtain ⟨F', hF, x', hx, rfl⟩ := ht
      obtain ⟨f', hf', x'', hx', rfl⟩ := hu'
      rw [hx] at hx'; cases hx'
      have e := ((ihf F' hF hok).1 f₀ f' hf hf').2 hd'
      exact ⟨e _, fun _ _ => e _⟩
  | share k R ih =>
    refine fun t' ht hok => ?_
    have ht0 := ht
    simp only [Tm.instObj, bind_ok_iff, pure_ok_iff] at ht
    obtain ⟨R', hR, rfl⟩ := ht
    have e := R'.den_congr ρ Val.empty fun i hi => by simp [hok.1] at hi
    refine ⟨fun u u' hu hu' => ?_, fun A₁ A₂ h p p' hp hp' => ?_⟩
    · by_cases hd : (Tm.share k R).dem = false
      · exact inst_false_den ph σ ρ hd hu hu' ht0
      rw [convTm.eq_def, if_neg hd] at hu
      have ih' := (ih R' hR hok.2).1 u u' hu hu'
      exact ⟨ih'.1.trans (congrArg (·°) e.1), fun h ss => (ih'.2 h ss).trans (congrArg (·°) (e.2 ss))⟩
    · cases h; dsimp only at hp ⊢; unfold convProj at hp
      exact ((ih R' hR hok.2).2 _ _ rfl p p' hp hp').trans (congrArg (·°) e.1)
  | comp R S ihR ihS =>
    refine fun t' ht hok => ?_
    have ht0 := ht
    simp only [Tm.instObj, bind_ok_iff, pure_ok_iff] at ht
    obtain ⟨R', hR', S', hS', rfl⟩ := ht
    refine ⟨fun u u' hu hu' => ?_, fun A₁ A₂ h p p' hp hp' => ?_⟩
    · by_cases hd : (Tm.comp R S).dem = false
      · exact inst_false_den ph σ ρ hd hu hu' ht0
      rw [convTm.eq_def, if_neg hd] at hu
      cases hS : convTm S with
      | error l => simp only [hS] at hu; cases hu
      | ok s =>
        cases hR : convTm R with
        | error l => simp only [hS, hR] at hu; cases hu
        | ok r =>
          simp only [hS, hR] at hu; cases hu
          simp only [Tm.instObj, bind_ok_iff, pure_ok_iff] at hu'
          obtain ⟨s', hs', r', hr', rfl⟩ := hu'
          have hs : s'.den ρ = (S'.den ρ)° := ((ihS S' hS' hok.2).1 _ _ hS hs').1
          have hr : r'.den ρ = (R'.den ρ)° := ((ihR R' hR' hok.1).1 _ _ hR hr').1
          refine ⟨?_, fun _ _ => rfl⟩
          show s'.den ρ ≫ r'.den ρ = _; rw [hs, hr]; exact (recip_comp' _ _).symm
    · cases h; dsimp only at hp ⊢; unfold convProj at hp
      cases hS : convTm S with
      | error l => simp only [hS] at hp; cases hp
      | ok s =>
        cases hR : convProj R with
        | error l => simp only [hS, hR] at hp; cases hp
        | ok x =>
          simp only [hS, hR] at hp; cases hp
          obtain ⟨s', x', hs', hx', rfl⟩ := Proj.instObj_pre ph σ s x hp'
          have hs : s'.den ρ = (S'.den ρ)° := ((ihS S' hS' hok.2).1 _ _ hS hs').1
          rw [Proj.den_pre, hs, (ihR R' hR' hok.1).2 _ _ rfl x x' hR hx']; exact (recip_comp' _ _).symm
  | join R S ihR ihS | diff R S ihR ihS =>
    refine fun t' ht hok => ?_
    have ht0 := ht
    simp only [Tm.instObj, bind_ok_iff, pure_ok_iff] at ht
    obtain ⟨R', hR', S', hS', rfl⟩ := ht
    refine ⟨fun u u' hu hu' => ?_, by noproj'⟩
    first
      | (by_cases hd : (Tm.join R S).dem = false
         · exact inst_false_den ph σ ρ hd hu hu' ht0
         rw [convTm.eq_def, if_neg hd] at hu)
      | (by_cases hd : (Tm.diff R S).dem = false
         · exact inst_false_den ph σ ρ hd hu hu' ht0
         rw [convTm.eq_def, if_neg hd] at hu)
    cases hR : convTm R with
    | error l => simp only [hR] at hu; cases hu
    | ok r =>
      cases hS : convTm S with
      | error l => simp only [hS, hR] at hu; cases hu
      | ok s =>
        simp only [hS, hR] at hu; cases hu
        simp only [Tm.instObj, bind_ok_iff, pure_ok_iff] at hu'
        obtain ⟨r', hr', s', hs', rfl⟩ := hu'
        have hs : s'.den ρ = (S'.den ρ)° := ((ihS S' hS' hok.2).1 _ _ hS hs').1
        have hr : r'.den ρ = (R'.den ρ)° := ((ihR R' hR' hok.1).1 _ _ hR hr').1
        refine ⟨?_, fun _ _ => rfl⟩
        first
          | (show r'.den ρ ∪ s'.den ρ = _; rw [hs, hr]; rfl)
          | (show diffDen (r'.den ρ) (s'.den ρ) = _; rw [hs, hr]; rfl)
  | @meet A' _ R S ihR ihS =>
    refine fun t' ht hok => ?_
    have ht0 := ht
    simp only [Tm.instObj, bind_ok_iff, pure_ok_iff] at ht
    obtain ⟨R', hR', S', hS', rfl⟩ := ht
    refine ⟨fun u u' hu hu' => ?_, fun A₁ A₂ h p p' hp hp' => ?_⟩
    · by_cases hd : (Tm.meet R S).dem = false
      · exact inst_false_den ph σ ρ hd hu hu' ht0
      rw [convTm.eq_def, if_neg hd] at hu
      cases hR : convTm R with
      | ok r =>
        cases hS : convTm S with
        | ok s =>
          simp only [hR, hS] at hu; cases hu
          simp only [Tm.instObj, bind_ok_iff, pure_ok_iff] at hu'
          obtain ⟨r', hr', s', hs', rfl⟩ := hu'
          have hs : s'.den ρ = (S'.den ρ)° := ((ihS S' hS' hok.2).1 _ _ hS hs').1
          have hr : r'.den ρ = (R'.den ρ)° := ((ihR R' hR' hok.1).1 _ _ hR hr').1
          refine ⟨?_, fun _ _ => rfl⟩
          show r'.den ρ ∩ s'.den ρ = _; rw [hs, hr]; rfl
        | error l =>
          simp only [hR, hS] at hu
          clear hR hS hd ht0
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
                  obtain ⟨x', y', hx', hy', hm'⟩ := Proj.instObj_meet_inl ph σ x y hm hu'
                  refine ⟨?_, fun _ => Proj.meet_argDen _ _ _ hm' ρ⟩
                  exact ((Proj.den_meet ρ x' y').1 _ hm').trans (by
                    rw [(ihR R' hR' hok.1).2 _ _ rfl x x' hx hx', (ihS S' hS' hok.2).2 _ _ rfl y y' hy hy']; rfl)
          | _ => simp at hu
      | error l =>
        simp only [hR] at hu
        clear hR hd ht0
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
                obtain ⟨x', y', hx', hy', hm'⟩ := Proj.instObj_meet_inl ph σ x y hm hu'
                refine ⟨?_, fun _ => Proj.meet_argDen _ _ _ hm' ρ⟩
                exact ((Proj.den_meet ρ x' y').1 _ hm').trans (by
                  rw [(ihR R' hR' hok.1).2 _ _ rfl x x' hx hx', (ihS S' hS' hok.2).2 _ _ rfl y y' hy hy']; rfl)
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
            obtain ⟨x', y', hx', hy', hm'⟩ := Proj.instObj_meet_inr ph σ x y hm hp'
            rw [(Proj.den_meet ρ x' y').2 _ hm', (ihR R' hR' hok.1).2 _ _ rfl x x' hx hx',
              (ihS S' hS' hok.2).2 _ _ rfl y y' hy hy']; rfl
  | @pair A' _ _ R S ihR ihS =>
    refine fun t' ht hok => ?_
    have ht0 := ht
    simp only [Tm.instObj, bind_ok_iff, pure_ok_iff] at ht
    obtain ⟨R', hR', S', hS', rfl⟩ := ht
    refine ⟨fun u u' hu hu' => ?_, fun A₁ A₂ h p p' hp hp' => ?_⟩
    · by_cases hd : (Tm.pair R S).dem = false
      · exact inst_false_den ph σ ρ hd hu hu' ht0
      rw [convTm.eq_def, if_neg hd] at hu
      cases hR : convTm R with
      | ok r =>
        have hr' := fun r' (h : r.instObj ph σ = .ok r') => ((ihR R' hR' hok.1).1 _ r' hR h).1
        cases hS : convTm S with
        | ok s =>
          simp only [hR, hS] at hu; cases hu
          simp only [Tm.instObj, bind_ok_iff, pure_ok_iff] at hu'
          obtain ⟨_, ⟨_, rfl, r', hr, rfl⟩, _, ⟨_, rfl, s', hs', rfl⟩, rfl⟩ := hu'
          have hs : s'.den ρ = (S'.den ρ)° := ((ihS S' hS' hok.2).1 _ _ hS hs').1
          refine ⟨?_, fun _ _ => rfl⟩
          show graph Prod.fst ≫ r'.den ρ ∩ graph Prod.snd ≫ s'.den ρ = _; rw [hr' r' hr, hs]; exact recip_rpair _ _
        | error l =>
          simp only [hR, hS] at hu; cases hu
          simp only [Tm.instObj, ↓Tm.instObj_dom, pairTest, bind_ok_iff, pure_ok_iff] at hu'
          obtain ⟨_, ⟨_, ⟨_, rfl, r', hr, rfl⟩, _, rfl, rfl⟩, _,
            ⟨_, ⟨_, ⟨_, rfl, _, ⟨_, rfl, S'', hS'', rfl⟩, rfl⟩, rfl⟩, _, rfl, rfl⟩, rfl⟩ := hu'
          rw [hS'] at hS''; cases hS''
          refine ⟨?_, fun _ _ => rfl⟩
          -- `⟨π₁R°,π₂⟩τ(S)π₁`: `(b,c) ↦ (a,c) ↦ a` with `a R b` and `a S c`
          simp only [↓Tm.dom_den, Tm.dom_den, Tm.den]
          show rpair (graph Prod.fst ≫ r'.den ρ) (graph Prod.snd) ≫
            ((𝟙 _ ∩ (graph Prod.snd ∩ graph Prod.fst ≫ S'.den ρ) ≫ (graph Prod.snd ∩ graph Prod.fst ≫ S'.den ρ)°) ≫
              graph Prod.fst) = _
          rw [hr' r' hr]; funext q a; apply propext
          simp only [Core.Rel.comp, Core.Rel.inter, Core.Rel.recip, Core.Rel.id, graph, rpair, Prod.exists,
            Prod.mk.injEq]
          constructor
          · rintro ⟨a1, c1, ⟨⟨b, rfl, h1⟩, rfl⟩, a2, c2, ⟨⟨rfl, rfl⟩, w, ⟨rfl, x, rfl, h2⟩, -⟩, rfl⟩
            exact ⟨h1, h2⟩
          · rintro ⟨h1, h2⟩
            exact ⟨a, q.2, ⟨⟨q.1, rfl, h1⟩, rfl⟩, a, q.2, ⟨⟨rfl, rfl⟩, q.2, ⟨rfl, a, rfl, h2⟩, rfl, a, rfl, h2⟩, rfl⟩
      | error l =>
        cases hS : convTm S with
        | ok s =>
          have hs := fun s' (h : s.instObj ph σ = .ok s') => ((ihS S' hS' hok.2).1 _ s' hS h).1
          simp only [hR, hS] at hu; cases hu
          simp only [Tm.instObj, ↓Tm.instObj_dom, pairTest, swapTm, bind_ok_iff, pure_ok_iff] at hu'
          obtain ⟨_, ⟨_, rfl, _, ⟨_, rfl, s', hs', rfl⟩, rfl⟩, _, ⟨_, ⟨_, rfl, _, rfl, rfl⟩, _,
            ⟨_, ⟨_, ⟨_, rfl, _, ⟨_, rfl, R'', hR'', rfl⟩, rfl⟩, rfl⟩, _, ⟨_, ⟨_, rfl, _, rfl, rfl⟩, _, rfl, rfl⟩, rfl⟩,
            rfl⟩, rfl⟩ := hu'
          rw [hR'] at hR''; cases hR''
          refine ⟨?_, fun _ _ => rfl⟩
          -- `⟨π₁,π₂S°⟩ swap τ(R) swap π₂`: `(b,c) ↦ (b,a) ↦ (a,b) ↦ (b,a) ↦ a` with `a S c` and `a R b`
          simp only [↓Tm.dom_den, Tm.dom_den, Tm.den]
          show rpair (graph Prod.fst) (graph Prod.snd ≫ s'.den ρ) ≫
            (rpair (graph Prod.snd) (graph Prod.fst) ≫
              ((𝟙 _ ∩ (graph Prod.snd ∩ graph Prod.fst ≫ R'.den ρ) ≫ (graph Prod.snd ∩ graph Prod.fst ≫ R'.den ρ)°) ≫
                (rpair (graph Prod.snd) (graph Prod.fst) ≫ graph Prod.snd))) = _
          rw [hs s' hs']; funext q a; apply propext
          simp only [Core.Rel.comp, Core.Rel.inter, Core.Rel.recip, Core.Rel.id, graph, rpair, Prod.exists,
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
          clear hR hS hd ht0
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
                  obtain ⟨a', b', ha', hb', hm'⟩ := Proj.instObj_meet_inl ph σ _ _ hm hu'
                  obtain ⟨o₁, x', ho₁, hx', rfl⟩ := Proj.instObj_pre ph σ _ _ ha'
                  obtain ⟨o₂, y', ho₂, hy', rfl⟩ := Proj.instObj_pre ph σ _ _ hb'
                  simp only [Tm.instObj, pure_ok_iff] at ho₁ ho₂; subst ho₁ ho₂
                  refine ⟨?_, fun _ => Proj.meet_argDen _ _ _ hm' ρ⟩
                  exact ((Proj.den_meet ρ _ _).1 _ hm').trans (by
                    rw [Proj.den_pre, Proj.den_pre, (ihR R' hR' hok.1).2 _ _ rfl x x' hx hx',
                      (ihS S' hS' hok.2).2 _ _ rfl y y' hy hy']
                    exact recip_rpair _ _)
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
            obtain ⟨a', b', ha', hb', hm'⟩ := Proj.instObj_meet_inr ph σ _ _ hm hp'
            obtain ⟨o₁, x', ho₁, hx', rfl⟩ := Proj.instObj_pre ph σ _ _ ha'
            obtain ⟨o₂, y', ho₂, hy', rfl⟩ := Proj.instObj_pre ph σ _ _ hb'
            simp only [Tm.instObj, pure_ok_iff] at ho₁ ho₂; subst ho₁ ho₂
            rw [(Proj.den_meet ρ _ _).2 _ hm', Proj.den_pre, Proj.den_pre, (ihR R' hR' hok.1).2 _ _ rfl x x' hx hx',
              (ihS S' hS' hok.2).2 _ _ rfl y y' hy hy']
            exact recip_rpair _ _

/-- **The `callCv` premise of `Tm.ConvOK`, derived**: a `callCv` node `callTm` builds from a body `b` and its converse
    `u = convTm b` (what `Expand.convOf` registers) is `ConvOK` under every `ρ` once its instantiated body is
    `ConvOK` under every binding of its arguments. -/
theorem callTm_convOK (objs : Objs) (mc : Lean.MetavarContext) (dp pos : Pos) (c c' : Lean.Name)
    (us : List (OTy × Bool × Bool)) (ks : List Nat) (ph : List Rel.QAtomicType) {X Y : Obj} (b : Tm X Y) (u : Tm Y X) (hu : convTm b = .ok u)
    {A B : Obj} {ks₁ : List Nat} {c₁ c₁' : Lean.Name} {os : List Obj} {b' : Tm A B} {u' : Tm B A}
    (h : callTm objs mc dp pos c us ks ph ⟨X, Y, b⟩ (some (c', ⟨Y, X, u⟩)) A B = .ok (.callCv ks₁ c₁ c₁' os b' u'))
    (hok : ∀ ss, b'.ConvOK (Val.args ks₁ ss)) (ρ : Val) : (Tm.callCv ks₁ c₁ c₁' os b' u').ConvOK ρ := by
  unfold callTm at h
  simp only [bind_ok_iff, pure_ok_iff, mapError_ok_iff] at h
  obtain ⟨σ, -, b₁, ⟨b₀, hb, hb₁⟩, u₁, ⟨u₀, hu₀, hu₁⟩, he⟩ := h
  split at hb₁
  · rename_i hX
    obtain ⟨rfl, rfl⟩ := hX
    rw [dif_pos ⟨rfl, rfl⟩] at hu₁
    simp only [pure_ok_iff] at hb₁ hu₁
    subst hb₁ hu₁
    cases he
    exact fun ss => ((convTm_instObj_den ph σ (Val.args ks ss) b _ hb (hok ss)).1 u _ hu hu₀).1
  · simp [internal, throw, throwThe, MonadExceptOf.throw] at hb₁

end Rel.Lang
