import Rel.Run.Lang.Gen
import Rel.Lang.BitsSpecRun
import Rel.CRelRel
import Rel.Run.CRelRelDef
import Rel.CRelArith
import Rel.Run.CRelArithDef
import Rel.CRelFold
import Rel.Run.CRelFoldDef
import Rel.CRelPower
import Rel.CRelLoop
import Rel.CRelThin
import Rel.CRelEst

/-! The code of `Gen` read back: one lemma per combinator, saying that where its ok bit is set its relation is
    the allegory's operation on its parts' relations, so `Expand` assembles the correctness of a definition from
    these lemmas structurally over its term. A term that runs on demand is read only at the keys it is given
    (§a), so `Sound f T` says that `f` and `T` agree on those keys: `D ≫ rep(f D) = D ≫ T`, pointwise. A closed
    term has no keys, and there it is the equation `rep(f ()) = T` (`Sound.eq`). -/

namespace Rel.Lang.Gen

open Tab Rel.Alg Rel.Rep Rel.Kernel
open scoped Rel.Core.Rel
open Rel.Core.Rel hiding id comp recip inter union zero le inl inr junc

/-- The keys `D` as a relation: the coreflexive itself on demand, `𝟙` for a closed term. -/
def keys : {d : Bool} → {A : Obj} → Dem d A → Den A A
  | true, _, D => rep D
  | false, _, _ => 𝟙 _

/-- The keys a term is given form a coreflexive. -/
def Cor : {d : Bool} → {A : Obj} → Dem d A → Prop
  | true, _, D => ∀ x y, rep D x y → x = y
  | false, _, _ => True

/-- `f` computes `T` in every context: what it computes there agrees with `T` on the sides the context knows. -/
def Sound {A B : Obj} (f : Rel A B) (T : Den A B) : Prop := ∀ K, f.Reps K T

/-- Code on keys computes `T` there: given a coreflexive `D` and its ok bit, `x {rep(g D)} y ↔ x {T} y` at each
    key `x` of `D`. The form the combinators are proved in until 3.6 (`KSound.reps`, `Sound.at`). -/
def KSound {d : Bool} {A B : Obj} (g : Dem d A → CRel A B) (T : Den A B) : Prop :=
  ∀ D : Dem d A, Cor D → (g D).ok = true → ∀ x y, keys D x x → (rep (g D).rel x y ↔ T x y)

/-- `idU X` is a coreflexive: composed with itself it is itself. -/
theorem idU_idem {A : Obj} {m : USize} (X : Vals A m) : rep (idU X) ≫ rep (idU X) = rep (idU X) :=
  Core.Rel.ext fun x y => ⟨fun ⟨z, h, k⟩ => ((idU_holds X x z).1 h).1 ▸ k,
    fun h => ⟨x, (idU_holds X x x).2 ⟨rfl, ((idU_holds X x y).1 h).2⟩, h⟩⟩

/-- Where `P ≫ R ≫ 𝟙 = P ≫ S ≫ 𝟙` and `x` is a key of the coreflexive `P`, `R` and `S` agree at `x`. -/
theorem atKey {A B : Obj} {P : Den A A} {R S : Den A B} (hP : ∀ x y, P x y → x = y)
    (E : P ≫ R ≫ 𝟙 _ = P ≫ S ≫ 𝟙 _) {x : A.El} (hx : P x x) (y : B.El) : R x y ↔ S x y := by
  have f : ∀ R' S' : Den A B, P ≫ R' ≫ 𝟙 _ = P ≫ S' ≫ 𝟙 _ → R' x y → S' x y := by
    intro R' S' E' r
    have h : (P ≫ R' ≫ 𝟙 _) x y := ⟨x, hx, y, r, rfl⟩
    rw [E'] at h; obtain ⟨z, p, w, s, e⟩ := h; cases hP x z p; cases (e : w = y); exact s
  exact ⟨f R S E, f S R E.symm⟩

/-- A table represents `T` in `K` where, when present, it agrees with `T` on `K`'s sides. -/
theorem tab_reps {A B : Obj} {K : Known A B} {c : CRel A B} {T : Den A B}
    (h : c.ok = true → K.den.1 ≫ rep c.rel ≫ K.den.2 = K.den.1 ≫ T ≫ K.den.2) : Rel.Reps K (.tab c) T :=
  match c, h with
  | none, _ => trivial
  | some _, h => h rfl

/-- `cut K r` agrees in `K` with what `r` computes: it cuts to the coreflexives `Reps` compares on, and those are
    idempotent. -/
theorem cut_reps {A B : Obj} (K : Known A B) {r : CRel A B} {T : Den A B} (h : r.ok = true → rep r.rel = T)
    (hb : (cut K r).ok = true) : K.den.1 ≫ rep (cut K r).rel ≫ K.den.2 = K.den.1 ≫ T ≫ K.den.2 := by
  rcases K with ⟨_ | ⟨n, X⟩, _ | ⟨m, Y⟩⟩
  · show 𝟙 _ ≫ rep r.rel ≫ 𝟙 _ = 𝟙 _ ≫ T ≫ 𝟙 _; rw [h hb]
  · replace hb : (CRel.comp r (some (idU Y))).ok = true := hb
    show 𝟙 _ ≫ rep (CRel.comp r (some (idU Y))).rel ≫ rep (idU Y) = 𝟙 _ ≫ T ≫ rep (idU Y)
    rw [CRel.rep_comp _ _ hb, h (Bool.and_eq_true_iff.1 (CRel.guard_ok_left hb)).1, CRel.some_rel, comp_assoc,
      idU_idem]
  · replace hb : (CRel.comp (some (idU X)) r).ok = true := hb
    show rep (idU X) ≫ rep (CRel.comp (some (idU X)) r).rel ≫ 𝟙 _ = rep (idU X) ≫ T ≫ 𝟙 _
    rw [CRel.rep_comp _ _ hb, h (Bool.and_eq_true_iff.1 (CRel.guard_ok_left hb)).2, CRel.some_rel]
    simp only [comp_assoc]; rw [← comp_assoc (rep (idU X)) (rep (idU X)), idU_idem]
  · replace hb : (CRel.comp (CRel.comp (some (idU X)) r) (some (idU Y))).ok = true := hb
    have h1 := Bool.and_eq_true_iff.1 (CRel.guard_ok_left hb)
    show rep (idU X) ≫ rep (CRel.comp (CRel.comp (some (idU X)) r) (some (idU Y))).rel ≫ rep (idU Y) =
      rep (idU X) ≫ T ≫ rep (idU Y)
    rw [CRel.rep_comp _ _ hb, CRel.rep_comp _ _ h1.1, h (Bool.and_eq_true_iff.1 (CRel.guard_ok_left h1.1)).2,
      CRel.some_rel, CRel.some_rel]
    simp only [comp_assoc]; rw [idU_idem, ← comp_assoc (rep (idU X)) (rep (idU X)), idU_idem]

/-- A closed leaf is `Sound` where its table, when ok, is `T`. -/
theorem const_sound {A B : Obj} {c : CRel A B} {T : Den A B} (h : c.ok = true → rep c.rel = T) :
    Sound (const A B c) T := fun _ => tab_reps fun hb => by rw [h hb]

/-- A leaf on demand is `Sound` where, on the coreflexive of the values `X` it is given, its table is `T`. -/
theorem ofVals_sound {A B : Obj} {f : {n : USize} → Vals A n → CRel A B} {T : Den A B}
    (h : ∀ {n : USize} (X : Vals A n), (f X).ok = true → rep (idU X) ≫ rep (f X).rel = rep (idU X) ≫ T) :
    Sound (ofVals A B f) T := fun K => by
  rcases K with ⟨_ | ⟨n, X⟩, L⟩
  · trivial
  · show Rel.Reps _ (.tab (f X)) T
    match e : f X with
    | none => trivial
    | some t =>
      have ht : rep (idU X) ≫ rep t = rep (idU X) ≫ T := by have := h X (by rw [e]; rfl); rwa [e] at this
      show rep (idU X) ≫ rep t ≫ _ = rep (idU X) ≫ T ≫ _
      rw [← comp_assoc, ← comp_assoc, ht]

/-- `ofVals_sound` read at the keys: where, at each value of `X`, `f X` relates as `T`. -/
theorem ofVals_keys {A B : Obj} {f : {n : USize} → Vals A n → CRel A B} {T : Den A B}
    (h : ∀ {n : USize} (X : Vals A n), (f X).ok = true → ∀ x y, rep (idU X) x x → (rep (f X).rel x y ↔ T x y)) :
    Sound (ofVals A B f) T := ofVals_sound fun X hb => by
  have hc : ∀ x y, rep (idU X) x y → x = y := fun x y k => ((idU_holds X x y).1 k).1
  exact Core.Rel.ext fun x y =>
    ⟨fun ⟨z, k, r⟩ => ⟨z, k, (h X hb z y (hc x z k ▸ k)).1 r⟩,
     fun ⟨z, k, r⟩ => ⟨z, k, (h X hb z y (hc x z k ▸ k)).2 r⟩⟩

/-- The bridge from the combinators' form: code on keys that computes `T` there is `Sound` as a `Fn` — closed,
    its equation; on demand, run on the keys `idU X` of a known domain, it agrees with `T` after `rep (idU X)`. -/
theorem KSound.reps {d : Bool} {A B : Obj} {g : Dem d A → CRel A B} {T : Den A B} (h : KSound g T) :
    Sound (Fn.ofDem g) T := by
  cases d
  · exact const_sound fun hb => Core.Rel.ext fun x y => h () trivial hb x y rfl
  · exact ofVals_keys fun X hb => h (idU X) (fun x y k => ((idU_holds X x y).1 k).1) hb

/-- The converse view: a `Sound` term computes `T` on any keys it is given (`Fn.at`). -/
theorem Sound.at {d : Bool} {A B : Obj} {f : Fn d A B} {T : Den A B} (h : Sound f T) : KSound (Fn.at f) T := by
  cases d
  · intro ⟨⟩ _ hb x y _
    obtain ⟨t, e⟩ := Option.isSome_iff_exists.1 hb
    rw [show Fn.at f () = some t from e]
    exact atKey (P := 𝟙 _) (fun _ _ e => e) (Rel.Reps.run (h {}) e) rfl y
  · intro D _ hb x y hx
    obtain ⟨t, e⟩ := Option.isSome_iff_exists.1 hb
    rw [show Fn.at f D = some t from e]
    exact atKey (fun x y k => ((idU_holds D.val x y).1 k).1) (Rel.Reps.run (h ⟨some ⟨D.n, D.val⟩, none⟩) e)
      ((idU_holds D.val x x).2 ⟨rfl, let ⟨i, _, e⟩ := hx; ⟨i, e⟩⟩) y

/-- A closed term's `Sound` is the equation of its relation. -/
theorem Sound.eq {A B : Obj} {f : Fn false A B} {T : Den A B} (h : Sound f T) (hb : (f.at ()).ok = true) :
    rep (f.at ()).rel = T :=
  Core.Rel.ext fun x y => Sound.at (d := false) h () trivial hb x y rfl

/-- What a context knows of each side is a coreflexive. -/
theorem _root_.Rel.Known.cor {A B : Obj} (K : Known A B) : (∀ x y, K.den.1 x y → x = y) ∧ (∀ x y, K.den.2 x y → x = y) := by
  have e : ∀ {C : Obj} (o : Option ((n : USize) × Vals C n)) (x y : C.El),
      o.elim (𝟙 _) (fun c => rep (idU c.2)) x y → x = y := fun o x y h => by
    cases o with
    | none => exact h
    | some c => exact ((idU_holds c.2 x y).1 h).1
  exact ⟨e K.dom, e K.ran⟩

/-- `X` and `Y` agree on the sides `K` knows. -/
def Agree {A B : Obj} (K : Known A B) (X Y : Den A B) : Prop :=
  ∀ x y, K.den.1 x x → K.den.2 y y → (X x y ↔ Y x y)

/-- Inside `K`'s sides, `X` cut to them is `X`. -/
theorem restrict {A B : Obj} (K : Known A B) {X : Den A B} {x : A.El} {y : B.El} (hx : K.den.1 x x)
    (hy : K.den.2 y y) : (K.den.1 ≫ X ≫ K.den.2) x y ↔ X x y :=
  ⟨fun ⟨a, p, b, r, q⟩ => by cases K.cor.1 x a p; cases K.cor.2 b y q; exact r, fun r => ⟨x, hx, y, r, hy⟩⟩

/-- A table, where present, that agrees with `T` on `K`'s sides represents `T` there. -/
theorem reps_ok {A B : Obj} {K : Known A B} {c : CRel A B} {T : Den A B}
    (h : c.ok = true → Agree K (rep c.rel) T) : (Rel.tab c).Reps K T := by
  match c, h with
  | none, _ => trivial
  | some t, h =>
    exact Core.Rel.ext fun x y =>
      ⟨fun ⟨a, p, b, r, q⟩ => by
        cases K.cor.1 x a p; cases K.cor.2 b y q; exact ⟨x, p, y, (h rfl x y p q).1 r, q⟩,
       fun ⟨a, p, b, r, q⟩ => by
        cases K.cor.1 x a p; cases K.cor.2 b y q; exact ⟨x, p, y, (h rfl x y p q).2 r, q⟩⟩

/-- A `Sound` term's table `t` in `K` agrees with `T` on `K`'s sides. -/
theorem Sound.agree_some {A B : Obj} {f : Rel A B} {T : Den A B} (h : Sound f T) {K : Known A B} {t : Tab A B}
    (e : f.run K = some t) : Agree K (rep t) T := fun x y hx hy => by
  have k : (K.den.1 ≫ rep t ≫ K.den.2) x y = (K.den.1 ≫ T ≫ K.den.2) x y := by rw [Rel.Reps.run (h K) e]
  rw [restrict K hx hy, restrict K hx hy] at k
  rw [k]

/-- The same where its ok bit is set. -/
theorem Sound.agree {A B : Obj} {f : Rel A B} {T : Den A B} (h : Sound f T) {K : Known A B}
    (hb : CRel.ok (f.run K) = true) : Agree K (rep (CRel.rel (f.run K))) T := by
  obtain ⟨t, e⟩ := Option.isSome_iff_exists.1 hb
  rw [e]; exact h.agree_some e

/-- A `Sound` term run with nothing known, where present, is `T`. -/
theorem Sound.run_eq {A B : Obj} {f : Rel A B} {T : Den A B} (h : Sound f T)
    (hb : CRel.ok (f.run {}) = true) : rep (CRel.rel (f.run {})) = T :=
  Core.Rel.ext fun x y => h.agree hb x y (show _ = _ from rfl) (show _ = _ from rfl)

theorem lift1_reps {A B C D : Obj} {f : CRel A B → CRel C D} {k : Known C D → Known A B} {R : Rel A B}
    {K : Known C D} {T : Den C D} (h : (Rel.tab (f (R.run (k K)))).Reps K T) : (lift1 f k R).Reps K T := by
  cases R <;> exact h

theorem lift2_reps {A B C D E F : Obj} {f : CRel A B → CRel C D → CRel E F} {kl : Known E F → Known A B}
    {kr : Known E F → Known C D} {R : Rel A B} {S : Rel C D} {K : Known E F} {T : Den E F}
    (h : (Rel.tab (f (R.run (kl K)) (S.run (kr K)))).Reps K T) : (lift2 f kl kr R S).Reps K T := by
  cases R <;> cases S <;> exact h

/-- A plan's value `p` on the keys `D`: where its bit is set, at each key of `D` it relates as `T`, read by `⟦−⟧`
    at `Val.empty` (a plan is closed). -/
def PlOK {A B : Obj} (p : Tm A B false × Bool) (D : Den A A) (T : Den A B) : Prop :=
  p.2 = true → ∀ x y, D x x → (p.1.den Val.empty x y ↔ T x y)

/-- A plan computes `T`: closed, at every point; on keys, at the keys of each coreflexive it is given. -/
def PSound {A B : Obj} : Pl A B → Den A B → Prop
  | .closed p, T => PlOK p.get (𝟙 _) T
  | .on f, T => ∀ D : Tab A A, (∀ x y, rep D x y → x = y) → PlOK (f D) (rep D) T

/-- A sound plan on the keys `D` (`Pl.at`), whichever its form. -/
theorem PSound.at {A B : Obj} {P : Pl A B} {T : Den A B} (h : PSound P T) (D : Tab A A)
    (hD : ∀ x y, rep D x y → x = y) : PlOK (P.at D) (rep D) T := by
  cases P with
  | closed p => exact fun hb x y _ => h hb x y rfl
  | on f => exact h D hD

/-- A sound plan where no key is given (`Pl.get`): one on keys has its bit false there. -/
theorem PSound.get {A B : Obj} {P : Pl A B} {T : Den A B} (h : PSound P T) : PlOK P.get (𝟙 _) T := by
  cases P with
  | closed p => exact h
  | on f => intro hb; simp [Pl.get] at hb

/-- `Pl.map2 f` is sound where `f` keeps soundness on any keys. -/
theorem Pl.map2_sound {A B C E : Obj} {f : Tm A B false × Bool → Tm A C false × Bool → Tm A E false × Bool}
    {R : Pl A B} {S : Pl A C} {TR : Den A B} {TS : Den A C} {T : Den A E}
    (hf : ∀ r s (D : Den A A), PlOK r D TR → PlOK s D TS → PlOK (f r s) D T) (hR : PSound R TR)
    (hS : PSound S TS) : PSound (Pl.map2 f R S) T := by
  cases R <;> cases S
  · exact hf _ _ _ hR hS
  all_goals exact fun D hD => hf _ _ _ (hR.at D hD) (hS.at D hD)

/-- A coreflexive `K` given as the keys of `S`: `S` agrees with `T` at every key of `K`. -/
theorem atKeys {B C : Obj} {e : Bool} {S : Fn e B C} {T : Den B C} (hS : Sound S T) (K : Tab B B)
    (hc : ∀ x y, rep K x y → x = y) (hb : (S.at (Dem.of e K)).ok = true) :
    ∀ b c, rep K b b → (rep (S.at (Dem.of e K)).rel b c ↔ T b c) := by
  cases e
  · exact fun b c _ => hS.at () trivial hb b c rfl
  · exact fun b c hk => hS.at K hc hb b c hk

/-- A coreflexive's row values: on the keys of `D`, every key is one of `D.val`'s rows. -/
theorem keyRow {A : Obj} {D : Tab A A} {x : A.El} (h : rep D x x) : ∃ i, D.val.row i = x :=
  let ⟨i, _, e⟩ := h; ⟨i, e⟩

theorem rowKey {A : Obj} {D : Tab A A} (hD : ∀ x y, rep D x y → x = y) {x : A.El} :
    (∃ i, D.val.row i = x) → rep D x x := by
  rintro ⟨i, rfl⟩
  have h : rep D (D.key.row i) (D.val.row i) := ⟨i, rfl, rfl⟩
  rw [hD _ _ h] at h; exact h

/-- `ranC`'s and `CRel.ran`'s relation: the coreflexive on `R`'s values. -/
theorem ran_iff {A B : Obj} (R : Den A B) (y y' : B.El) :
    (𝟙 _ ∩ R° ≫ R°° : Den B B) y y' ↔ y = y' ∧ ∃ x, R x y ∧ R x y' := Iff.rfl

/-- Where `also b r` is ok, `b` and `r`'s bit are set and its table is `r`'s. -/
theorem also_ok_rel {A B : Obj} {b : Bool} {r : CRel A B} (h : (also b r).ok = true) :
    (b = true ∧ r.ok = true) ∧ (also b r).rel = r.rel :=
  let ⟨h, e⟩ := CRel.mk_ok_rel (r := r.rel) (b := b && r.ok) h; ⟨Bool.and_eq_true_iff.1 h, e⟩

/-! ### Leaves -/

theorem val_sound {A B : Obj} (R : Tab A B × Bool) : Sound (val A B R) (rep R.1) :=
  const_sound CRel.rep_ofC

theorem uni_sound {A : Obj} {m : USize} (U : Vals A m × Bool) : Sound (uni A m U) (rep (idU U.1)) :=
  const_sound fun hb => congrArg rep (CRel.mk_ok_rel hb).2

/-- `succ`, `arith`, `≤`, `<` on a declared object's universe `uni` read its literal `U` directly: the one
    definition of each is also the literal form, so no second copy can drift from it. -/
theorem uni_lits {m : USize} (U : Vals .long m × Bool) :
    succ (uni .long m U) = ofVals _ _ (fun X => also U.2 (CRel.comp (some (idU X)) (CRel.succ U.1))) ∧
    leq (uni .long m U) = .lazy (fun K => .tab (also U.2 (cut K (CRel.leq U.1)))) ∧
    lt (uni .long m U) = .lazy (fun K => .tab (also U.2 (cut K (CRel.lt U.1)))) := by
  obtain ⟨U, b⟩ := U
  cases b <;> refine ⟨?_, ?_, ?_⟩ <;>
    simp only [uni, const, succ, leq, lt, Fn.at, Rel.run, also, CRel.mk_ok, CRel.mk_rel, CRel.mk_false,
      CRel.none_ok, Bool.false_and, Bool.true_and] <;> rfl

theorem zero_sound {A B : Obj} : Sound (zero A B) 𝟘 := const_sound fun _ => rep_zero

/-- `R` relates exactly the values listed in `X`, each by `T`, so on them it is `T`: how a kernel's pointwise
    lemma reads as the form `ofVals_sound` takes. -/
theorem idU_ext {A B : Obj} {n : USize} {X : Vals A n} {R T : Den A B}
    (h : ∀ x y, R x y ↔ (∃ j, X.row j = x) ∧ T x y) : rep (idU X) ≫ R = rep (idU X) ≫ T := by
  have e : R = rep (idU X) ≫ T := Core.Rel.ext fun x y => by
    rw [h, comp_apply, rep_idU]
    exact ⟨fun ⟨hx, t⟩ => ⟨x, ⟨rfl, hx⟩, t⟩, fun ⟨_, ⟨e, hx⟩, t⟩ => by subst e; exact ⟨hx, t⟩⟩
  rw [e, ← comp_assoc, idU_idem]

theorem id_sound {A : Obj} : Sound (id A) (𝟙 _) := ofVals_sound fun X hb => by
  rw [CRel.rep_ofC hb, comp_id]; exact idU_idem X

theorem outl_sound {A B : Obj} : Sound (outl A B) (graph Prod.fst) := ofVals_sound fun X hb => by
  rw [CRel.rep_ofC hb]; show _ ≫ rep (Alg.outl (idU X)) = _; rw [rep_outl, ← comp_assoc, idU_idem]

theorem outr_sound {A B : Obj} : Sound (outr A B) (graph Prod.snd) := ofVals_sound fun X hb => by
  rw [CRel.rep_ofC hb]; show _ ≫ rep (Alg.outr (idU X)) = _; rw [rep_outr, ← comp_assoc, idU_idem]

theorem inl_sound {A B : Obj} : Sound (ofVals A (.sum A B) CRel.inl) (Core.Rel.inl (α := A.El) (β := B.El)) :=
  ofVals_sound fun X hb => by rw [CRel.rep_inl X hb, ← rep_idU, ← comp_assoc, idU_idem]

theorem inr_sound {A B : Obj} : Sound (ofVals B (.sum A B) CRel.inr) (Core.Rel.inr (α := A.El) (β := B.El)) :=
  ofVals_sound fun X hb => by rw [CRel.rep_inr X hb, ← rep_idU, ← comp_assoc, idU_idem]

theorem mem_sound {B : Obj} : Sound (ofVals (.arr B) B CRel.mem) (fun xs x => x ∈ xs) :=
  ofVals_sound fun X hb => idU_ext fun xs x => CRel.rep_mem X hb xs x

/-! ### The rows of `prims` -/

/-- A row composed after its keys computes `T` where its kernel is `P` then `T`. -/
theorem after_sound {A B : Obj} {f : {K : Obj} → CRel K A → CRel K B} {T : Den A B}
    (h : ∀ {K : Obj} (P : CRel K A), (f P).ok = true → rep (f P).rel = rep P.rel ≫ T) :
    Sound (after A B f) T := ofVals_sound fun X hb => by rw [h _ hb, CRel.some_rel, ← comp_assoc, idU_idem]

theorem τ_sound {A : Obj} : Sound (ofVals A (.arr A) fun X => CRel.τ X) (fun a Y => Y = [a]) :=
  ofVals_sound fun X hb => idU_ext <| by
    unfold CRel.τ at hb ⊢; rw [CRel.rep_ofC hb]
    obtain ⟨hX, -, hx, -, hWk, hW, h63⟩ := transposeC_ok (idU X) (CRel.ofC_ok hb).1
    exact rep_tau_list X hX hx hWk hW h63

theorem uncons_sound {B : Obj} :
    Sound (ofVals (.arr B) (.prod B (.arr B)) fun X => CRel.uncons X) (fun xs p => xs = p.1 :: p.2) :=
  ofVals_sound fun X hb => idU_ext fun xs _ => CRel.rep_uncons X hb xs _ _

theorem unsnoc_sound {B : Obj} :
    Sound (ofVals (.arr B) (.prod (.arr B) B) fun X => CRel.unsnoc X) (fun xs p => xs = p.1 ++ [p.2]) :=
  ofVals_sound fun X hb => idU_ext fun xs _ => CRel.rep_unsnoc X hb xs _ _

theorem uncat_sound {B : Obj} :
    Sound (ofVals (.arr B) (.prod (.arr B) (.arr B)) fun X => CRel.uncat X) (fun xs p => xs = p.1 ++ p.2) :=
  ofVals_sound fun X hb => idU_ext fun xs _ => CRel.rep_uncat X hb xs _ _

theorem length_sound {B : Obj} :
    Sound (ofVals (.arr B) .long fun X => CRel.length X) (fun xs w => w = Int64.ofNat xs.length) :=
  ofVals_sound fun X hb => idU_ext <| CRel.rep_length X hb

/-- `sum` adds in `Int64`: its kernel has no row at an array holding `nul` or one whose partial sums leave the
    `Int64` range, so this is its relation, not `foldr (+) 0` on every array. -/
theorem sum_sound : Sound (ofVals (.arr .long) .long fun X => CRel.Arr.sum X) (fun xs w =>
    (∀ t, t ≤ xs.length → -2 ^ 63 < List.sum (List.map Int64.toInt (List.drop t xs)) ∧
      List.sum (List.map Int64.toInt (List.drop t xs)) < 2 ^ 63) ∧ (∀ x ∈ xs, x ≠ nul) ∧
      w = xs.foldr (· + ·) 0) :=
  ofVals_sound fun X hb => idU_ext <| CRel.Arr.rep_sum X hb

theorem inits_sound {B : Obj} : Sound (ofVals (.arr B) (.arr (.arr B)) fun X => CRel.inits X)
    (fun xs yss => yss = (List.range (xs.length + 1)).map fun k => xs.take k) :=
  ofVals_sound fun X hb => idU_ext <| CRel.rep_inits X hb

theorem tails_sound {B : Obj} : Sound (ofVals (.arr B) (.arr (.arr B)) fun X => CRel.tails X)
    (fun xs yss => yss = (List.range (xs.length + 1)).map fun k => xs.drop k) :=
  ofVals_sound fun X hb => idU_ext <| CRel.rep_tails X hb

theorem prefix_sound {B : Obj} : Sound (ofVals (.arr B) (.arr B) fun X => CRel.«prefix» X) (fun xs ys => ys <+: xs) :=
  ofVals_sound fun X hb => idU_ext <| CRel.rep_prefix X hb

theorem suffix_sound {B : Obj} : Sound (ofVals (.arr B) (.arr B) fun X => CRel.suffix X) (fun xs ys => ys <:+ xs) :=
  ofVals_sound fun X hb => idU_ext <| CRel.rep_suffix X hb

theorem concat_sound {B : Obj} :
    Sound (ofVals (.arr (.arr B)) (.arr B) fun X => CRel.concat X) (fun xss ys => ys = xss.flatten) :=
  ofVals_sound fun X hb => idU_ext <| CRel.rep_concat X hb

open Classical in
theorem distinct_sound {B : Obj} :
    Sound (ofVals (.arr B) (.arr B) fun X => CRel.distinct X) (fun xs ys => ys = xs.eraseDups) :=
  ofVals_sound fun X hb => idU_ext fun xs ys => by
    obtain ⟨h1, h2⟩ := CRel.rep_distinct X hb
    refine ⟨h1 xs ys, fun ⟨hx, e⟩ => ?_⟩
    obtain ⟨Y, hY⟩ := (h2 xs).2 hx
    rwa [e, ← (h1 xs Y hY).2]

open Classical in
/-- `elems`' relation run on the elements of the arrays in demand: at every element of a key `xs`, its test (some
    `y` related) is `TR`'s. -/
theorem elems_test {B C : Obj} {d : Bool} {R : Fn d B C} {TR : Den B C} (hR : Sound R TR) (D : Tab (.arr B) (.arr B))
    (hk : (CRel.ran (CRel.mem D.val)).ok = true) (hr : (R.at (Dem.of d (CRel.ran (CRel.mem D.val)).rel)).ok = true)
    {xs : (Obj.arr B).El} (hx : rep D xs xs) : ∀ x ∈ xs,
      decide (∃ y, rep (R.at (Dem.of d (CRel.ran (CRel.mem D.val)).rel)).rel x y) = decide (∃ y, TR x y) :=
  fun x hin => by
    have hK := CRel.rep_ran _ hk
    have h1 : rep (CRel.mem D.val).rel xs x := (CRel.rep_mem _ (CRel.guard_ok_left hk) xs x).2 ⟨keyRow hx, hin⟩
    have hs := atKeys hR _ (fun a b h => ((ran_iff _ a b).1 (hK ▸ h)).1) hr
    exact decide_eq_decide.2 (exists_congr fun y => hs x y (hK ▸ (ran_iff _ x x).2 ⟨rfl, xs, h1, h1⟩))

open Classical in
/-- `filter(R)` keeps the elements `TR` relates to something. -/
theorem filter_sound {B : Obj} {d : Bool} {R : Fn d B B} {TR : Den B B} (hR : Sound R TR) :
    Sound (elems B B (.arr B) d R CRel.filter) (fun xs ys => ys = xs.filter fun x => decide (∃ y, TR x y)) :=
  KSound.reps fun D _ hb xs ys hx => by
    dsimp only at hb ⊢; obtain ⟨hb', e⟩ := also_ok_rel hb; rw [e]
    rw [CRel.rep_filter _ _ hb'.2, List.filter_congr (elems_test hR D hb'.1 (CRel.guard_ok_left hb'.2) hx)]
    exact ⟨And.right, fun t => ⟨keyRow hx, t⟩⟩

open Classical in
/-- `takewhile(R)` keeps the longest prefix of elements `TR` relates to something. -/
theorem takewhile_sound {B : Obj} {d : Bool} {R : Fn d B B} {TR : Den B B} (hR : Sound R TR) :
    Sound (elems B B (.arr B) d R CRel.takewhile) (fun xs ys => ys = xs.takeWhile fun x => decide (∃ y, TR x y)) :=
  KSound.reps fun D _ hb xs ys hx => by
    dsimp only at hb ⊢; obtain ⟨hb', e⟩ := also_ok_rel hb; rw [e]
    have hc := elems_test hR D hb'.1 (CRel.guard_ok_left hb'.2) hx
    rw [CRel.rep_takewhile _ _ hb'.2]
    suffices e : ∀ {p q : B.El → Bool} (l : List B.El), (∀ x ∈ l, p x = q x) → l.takeWhile p = l.takeWhile q by
      rw [e xs hc]; exact ⟨And.right, fun t => ⟨keyRow hx, t⟩⟩
    intro p q l; induction l with
    | nil => intro _; rfl
    | cons a l ih => intro h; simp only [List.takeWhile_cons, h a List.mem_cons_self,
        ih fun x hx => h x (List.mem_cons_of_mem _ hx)]

theorem cons_sound {B : Obj} :
    Sound (after (.prod B (.arr B)) (.arr B) fun P => CRel.cons P) (fun p ys => ys = p.1 :: p.2) :=
  after_sound fun P hb => Core.Rel.ext fun k ys => (CRel.rep_cons P hb k ys).trans
    ⟨fun ⟨_, _, h, e⟩ => ⟨_, h, e⟩, fun ⟨_, h, e⟩ => ⟨_, _, h, e⟩⟩

theorem snoc_sound {B : Obj} :
    Sound (after (.prod (.arr B) B) (.arr B) fun P => CRel.snoc P) (fun p ys => ys = p.1 ++ [p.2]) :=
  after_sound fun P hb => Core.Rel.ext fun k ys => (CRel.rep_snoc P hb k ys).trans
    ⟨fun ⟨_, _, h, e⟩ => ⟨_, h, e⟩, fun ⟨_, h, e⟩ => ⟨_, _, h, e⟩⟩

theorem cat_sound {B : Obj} :
    Sound (after (.prod (.arr B) (.arr B)) (.arr B) fun P => CRel.cat P) (fun p zs => zs = p.1 ++ p.2) :=
  after_sound fun P hb => Core.Rel.ext fun k zs => (CRel.rep_cat P hb k zs).trans
    ⟨fun ⟨_, _, h, e⟩ => ⟨_, h, e⟩, fun ⟨_, h, e⟩ => ⟨_, _, h, e⟩⟩

theorem zip_sound {A B : Obj} :
    Sound (after (.prod (.arr A) (.arr B)) (.arr (.prod A B)) fun P => CRel.zip P) (fun p zs => zs = p.1.zip p.2) :=
  after_sound fun P hb => Core.Rel.ext fun k zs => (CRel.rep_zip P hb k zs).trans
    ⟨fun ⟨_, _, h, e⟩ => ⟨_, h, e⟩, fun ⟨_, h, e⟩ => ⟨_, _, h, e⟩⟩

theorem tic_sound {B : Obj} : Sound (after (.prod B (.arr B)) (.arr (.arr B)) fun P => CRel.tic P)
    (fun p zss => zss = (List.range (p.2.length + 1)).map fun j => (p.1 :: p.2).take (j + 1)) :=
  after_sound fun P hb => Core.Rel.ext fun k zss => (CRel.rep_tic P hb k zss).trans
    ⟨fun ⟨_, _, h, e⟩ => ⟨_, h, e⟩, fun ⟨_, h, e⟩ => ⟨_, _, h, e⟩⟩

open Classical in
/-- A test `Q` read as an order on the coreflexives a kernel runs it on: `a` before `b` where `Q` relates `(a, b)` to
    something. -/
theorem test_le {B : Obj} {Q : Fn true (.prod B B) (.prod B B)} {TQ : Den (.prod B B) (.prod B B)} (hQ : Sound Q TQ) :
    ∀ (E : Tab (.prod B B) (.prod B B)) (S : (Obj.prod B B).El → Prop),
      rep E = corefl (α := (Obj.prod B B).El) S → (Q.at E).ok = true →
      ∀ a b, S (a, b) → ((∃ c, rep (Q.at E).rel (a, b) c) ↔ decide (∃ c, TQ (a, b) c) = true) :=
    fun E S hE hb a b hS => by
  have hC : Cor (d := true) E := fun u v h => (show corefl S u v by rw [← hE]; exact h).1
  have hk : rep E (a, b) (a, b) := by rw [hE]; exact ⟨rfl, hS⟩
  rw [decide_eq_true_iff]; exact exists_congr fun c => hQ.at E hC hb _ c hk

/-- `F(R)`, the list relator: arrays of one length, related position by position by `TR`. -/
theorem map_sound {A B : Obj} {d : Bool} {R : Fn d A B} {TR : Den A B} (hR : Sound R TR) :
    Sound (elems A B (.arr B) d R CRel.map) (fun xs ys => ys.length = xs.length ∧
      ∀ t (ht : t < xs.length) (ht' : t < ys.length), TR (xs[t]'ht) (ys[t]'ht')) :=
  KSound.reps fun D _ hb xs ys hx => by
    dsimp only at hb ⊢; obtain ⟨hb', e⟩ := also_ok_rel hb; rw [e]
    have hK := CRel.rep_ran _ hb'.1
    have hs := atKeys hR _ (fun a b h => ((ran_iff _ a b).1 (hK ▸ h)).1) (CRel.guard_ok_left hb'.2)
    have hin : ∀ x ∈ xs, ∀ y, rep (R.at (Dem.of d (CRel.ran (CRel.mem D.val)).rel)).rel x y ↔ TR x y := fun x hx' y => by
      have h1 : rep (CRel.mem D.val).rel xs x := (CRel.rep_mem _ (CRel.guard_ok_left hb'.1) xs x).2 ⟨keyRow hx, hx'⟩
      exact hs x y (hK ▸ (ran_iff _ x x).2 ⟨rfl, xs, h1, h1⟩)
    rw [CRel.rep_map _ _ hb'.2]
    exact ⟨fun ⟨_, hl, h⟩ => ⟨hl, fun t ht ht' => (hin _ (List.getElem_mem ht) _).1 (h t ht ht')⟩,
      fun ⟨hl, h⟩ => ⟨keyRow hx, hl, fun t ht ht' => (hin _ (List.getElem_mem ht) _).2 (h t ht ht')⟩⟩

open Classical in
/-- `merge(Q)` merges by the test `Q` read as an order (`test_le`). -/
theorem merge_sound {B : Obj} {Q : Fn true (.prod B B) (.prod B B)} {TQ : Den (.prod B B) (.prod B B)}
    (hQ : Sound Q TQ) : Sound (testAfter B (.prod (.arr B) (.arr B)) (.arr B) Q fun q P => CRel.mergeOn q P)
      (fun p zs => zs = List.merge p.1 p.2 fun a b => decide (∃ c, TQ (a, b) c)) :=
    KSound.reps fun D hD hb x zs hx => by
  have hb' : (CRel.mergeOn (fun P => Q.at P.rel) (some D)).ok = true := hb
  exact (CRel.rep_mergeOn (fun P => Q.at P.rel) (some D) (fun a b => decide (∃ c, TQ (a, b) c)) (test_le hQ) hb' x
    zs).trans ⟨fun ⟨_, _, h, e⟩ => hD x _ h ▸ e, fun e => ⟨x.1, x.2, hx, e⟩⟩

open Classical in
/-- `thinL(Q)` bumps each element into the thinned rest by the test `Q` read as an order (`test_le`). -/
theorem thinL_sound {B : Obj} {Q : Fn true (.prod B B) (.prod B B)} {TQ : Den (.prod B B) (.prod B B)}
    (hQ : Sound Q TQ) : Sound (testVals B (.arr B) (.arr B) Q fun q X => CRel.thinLOn q X)
      (thinLDen fun a b => decide (∃ c, TQ (a, b) c)) :=
  ofVals_sound (f := @fun _ X => CRel.thinLOn (fun P => Q.at P.rel) X) fun X hb => idU_ext <|
    CRel.rep_thinLOn _ _ X (test_le hQ) hb

/-- A round's pairs `K` have a row, so `onKeys` runs `S` on their values, where it agrees with `TS`. -/
theorem onKeys_round {P V : Obj} {S : Rel P V} {TS : Den P V} (hS : Sound S TS) (K : CRel P P) (p w)
    (hp : ∃ a, rep K.rel a p) (hc : ∀ a b, rep K.rel a b → a = b) (hok : (onKeys S K).ok = true) :
    rep (onKeys S K).rel p w ↔ TS p w := by
  obtain ⟨a, ha⟩ := hp
  have h0 : (K.rel.n == 0) = false := by
    obtain ⟨j, -⟩ := ha
    cases h : K.rel.n == 0
    · rfl
    · have : K.rel.n.toNat = 0 := by simp [beq_iff_eq.1 h]
      exact absurd j.2 (by omega)
  simp only [onKeys, h0, Bool.false_eq_true, if_false] at hok ⊢
  exact hS.agree hok p w ((idU_holds K.rel.val p p).2 ⟨rfl, keyRow (hc a p ha ▸ ha)⟩) rfl

/-- A step run on a round's coreflexive `D` of the pairs `S` (`onKeys`) computes `T` at those pairs: `D` has a
    row, so the step ran. -/
theorem onKeys_sound {A B : Obj} {F : Rel A B} {T : Den A B} (hF : Sound F T) (D : Tab A A)
    (S : A.El → Prop) (hD : rep D = corefl (α := A.El) S) (hb : (onKeys F (some D)).ok = true) :
    ∀ x y, S x → (rep (onKeys F (some D)).rel x y ↔ T x y) := fun x y hx =>
  have hk : rep D x x := by rw [hD]; exact ⟨rfl, hx⟩
  onKeys_round hF (some D) x y ⟨x, hk⟩ (fun a b h => (show corefl S a b by rw [← hD]; exact h).1) hb

/-- `loop(F)` folds the step `F` along each array from the left, from the seed. -/
theorem loop_sound {X Y : Obj} {d : Bool} {F : Fn d (.prod X Y) X} {TF : Den (.prod X Y) X} (hF : Sound F TF) :
    Sound (stepAfter (.prod X Y) X (.prod X (.arr Y)) X d F fun G P => CRel.loopOn G P)
      (fun p c => ∃ g : Nat → X.El, g 0 = p.1 ∧ (∀ t (ht : t < p.2.length), TF (g t, p.2[t]'ht) (g (t + 1))) ∧
        c = g p.2.length) :=
  after_sound (f := @fun _ P => CRel.loopOn (onKeys F) P) fun P hb => Core.Rel.ext fun k c =>
    (CRel.rep_loopOn _ P hb TF (fun D S hD hb' cy c' hS => (onKeys_sound hF D S hD hb' cy c' hS).symm) k c).trans
      ⟨fun ⟨c₀, xs, h, g⟩ => ⟨(c₀, xs), h, g⟩, fun ⟨⟨c₀, xs⟩, h, g⟩ => ⟨c₀, xs, h, g⟩⟩

/-! ### The allegory's operations -/

theorem comp_sound {A B C : Obj} {e : Bool} {R : Fn true A B} {S : Fn e B C} {TR : Den A B} {TS : Den B C}
    (hR : Sound R TR) (hS : Sound S TS) : Sound (comp A B C e R S) (TR ≫ TS) := by
  -- `r` agrees with `TR` on `K`'s domain, `S` on `r`'s values and `K`'s range: so `r S` with `TR ≫ TS` on `K`.
  have ag : ∀ {K : Known A C} {r : Tab A B} (D : (n : USize) × Vals B n),
      (∀ {x y}, rep r x y → rep (idU D.2) y y) → Agree ⟨K.dom, none⟩ (rep r) TR →
      (CRel.comp (some r) (S.run ⟨some D, K.ran⟩)).ok = true →
      Agree K (rep (CRel.comp (some r) (S.run ⟨some D, K.ran⟩)).rel) (TR ≫ TS) :=
    fun {K r} D vk hr hb x z hx hz => by
      have hc := CRel.guard_ok_left hb; rw [Bool.and_eq_true] at hc
      have hs := hS.agree hc.2
      rw [CRel.rep_comp _ _ hb]
      exact ⟨fun ⟨y, h1, h2⟩ => ⟨y, (hr x y hx rfl).1 h1, (hs y z (vk h1) hz).1 h2⟩,
        fun ⟨y, h1, h2⟩ => have h1' := (hr x y hx rfl).2 h1; ⟨y, h1', (hs y z (vk h1') hz).2 h2⟩⟩
  have hT : ∀ {K : Known A C} {c : CRel A B}, (∀ t, c = some t → Agree ⟨K.dom, none⟩ (rep t) TR) →
      (compT c S).Reps K (TR ≫ TS) := by
    intro K c hr
    cases c with
    | none => trivial
    | some r =>
    cases S with
    | tab s => exact reps_ok (ag ⟨r.n, r.val⟩ (fun h =>
        (idU_holds r.val _ _).2 ⟨rfl, let ⟨i, _, e⟩ := h; ⟨i, e⟩⟩) (hr r rfl))
    | lazy g =>
      simp only [compT]; split
      · rename_i h0
        refine reps_ok fun _ x z hx _ => ?_
        show rep (Alg.zero : Tab A C) x z ↔ _
        rw [rep_zero]
        refine ⟨False.elim, fun ⟨y, hy, _⟩ => ?_⟩
        obtain ⟨i, -⟩ := (hr r rfl x y hx rfl).2 hy
        have : r.n.toNat = 0 := by simp [beq_iff_eq.1 h0]
        exact absurd i.2 (by omega)
      · refine reps_ok fun hb => ?_
        obtain ⟨⟨hd, hc⟩, e⟩ := also_ok_rel hb
        rw [e]
        refine ag _ (fun {x y} h => (idU_holds _ _ _).2 ⟨rfl, ?_⟩) (hr r rfl) hc
        have h' : rep (ranC r).1 y y := by rw [rep_ranC r hd]; exact ⟨rfl, x, h, h⟩
        exact let ⟨i, e, _⟩ := h'; ⟨i, e⟩
  -- Only the range known: `s` agrees with `TS` on it, `R` with `TR` on `s`'s keys, so `R s` with `TR ≫ TS`.
  have hS' : ∀ {L : (n : USize) × Vals C n} {c : CRel B C}, (∀ t, c = some t → Agree ⟨none, some L⟩ (rep t) TS) →
      (compS R c).Reps ⟨none, some L⟩ (TR ≫ TS) := by
    intro L c hs
    cases c with
    | none => trivial
    | some s =>
    refine reps_ok fun hb x z _ hz => ?_
    have hc := CRel.guard_ok_left hb; rw [Bool.and_eq_true] at hc
    have hr := hR.agree hc.1
    have hs := hs s rfl
    have kk : ∀ {y}, rep s y z → rep (idU s.key) y y := fun h =>
      (idU_holds s.key _ _).2 ⟨rfl, let ⟨i, e, _⟩ := h; ⟨i, e⟩⟩
    rw [CRel.rep_comp _ _ hb]
    exact ⟨fun ⟨y, h1, h2⟩ => ⟨y, (hr x y rfl (kk h2)).1 h1, (hs y z rfl hz).1 h2⟩,
      fun ⟨y, h1, h2⟩ => have h2' := (hs y z rfl hz).2 h2; ⟨y, (hr x y rfl (kk h2')).2 h1, h2'⟩⟩
  intro K
  cases R with
  | tab r => exact hT fun _ e => hR.agree_some (K := ⟨K.dom, none⟩) e
  | lazy f =>
    rcases K with ⟨_ | D, _ | L⟩
    · exact hT fun _ e => hR.agree_some (K := ⟨none, none⟩) e
    · exact hS' fun _ e => hS.agree_some e
    · exact hT fun _ e => hR.agree_some (K := ⟨some D, none⟩) e
    · exact hT fun _ e => hR.agree_some (K := ⟨some D, none⟩) e

theorem conv_sound {A B : Obj} {R : Fn false A B} {T : Den A B} (hR : Sound R T) : Sound (conv A B R) T° :=
  fun _ => lift1_reps <| reps_ok fun hb y x hy hx => by
    rw [CRel.rep_ofC hb, rep_conv]; exact hR.agree (CRel.ofC_ok hb).1 x y hx hy

theorem meet_sound {A B : Obj} {d e : Bool} {R : Fn d A B} {S : Fn e A B} {TR TS : Den A B}
    (hR : Sound R TR) (hS : Sound S TS) : Sound (meet A B d e R S) (TR ∩ TS) :=
  fun _ => lift2_reps <| reps_ok fun hb x y hx hy => by
    have hc := CRel.guard_ok_left hb; rw [Bool.and_eq_true] at hc
    rw [CRel.rep_inter _ _ hb]; exact and_congr (hR.agree hc.1 x y hx hy) (hS.agree hc.2 x y hx hy)

theorem join_sound {A B : Obj} {d e : Bool} {R : Fn d A B} {S : Fn e A B} {TR TS : Den A B}
    (hR : Sound R TR) (hS : Sound S TS) : Sound (join A B d e R S) (TR ∪ TS) :=
  fun _ => lift2_reps <| reps_ok fun hb x y hx hy => by
    have hc := CRel.guard_ok_left hb; rw [Bool.and_eq_true] at hc
    rw [CRel.rep_union _ _ hb]; exact or_congr (hR.agree hc.1 x y hx hy) (hS.agree hc.2 x y hx hy)

theorem diff_sound {A B : Obj} {d e : Bool} {R : Fn d A B} {S : Fn e A B} {TR TS : Den A B}
    (hR : Sound R TR) (hS : Sound S TS) : Sound (diff A B d e R S) (diffDen TR TS) :=
  fun _ => lift2_reps <| reps_ok fun hb x y hx hy => by
    have hc := CRel.guard_ok_left hb; rw [Bool.and_eq_true] at hc
    rw [CRel.rep_diff _ _ hb]
    exact and_congr (hR.agree hc.1 x y hx hy) (not_congr (hS.agree hc.2 x y hx hy))

theorem dom_sound {A B : Obj} {d : Bool} {R : Fn d A B} {T : Den A B} (hR : Sound R T) :
    Sound (dom A B d R) (𝟙 _ ∩ T ≫ T°) := fun _ => lift1_reps <| reps_ok fun hb x x' hx _ => by
  have a := hR.agree (CRel.guard_ok_left hb)
  rw [CRel.rep_dom _ hb]
  exact ⟨fun ⟨e, y, h, _⟩ => ⟨e, y, (a x y hx rfl).1 h, e ▸ (a x y hx rfl).1 h⟩,
    fun ⟨e, y, h, _⟩ => ⟨e, y, (a x y hx rfl).2 h, e ▸ (a x y hx rfl).2 h⟩⟩

theorem ran_sound {A B : Obj} {R : Fn false A B} {T : Den A B} (hR : Sound R T) :
    Sound (ran A B R) (𝟙 _ ∩ T° ≫ T°°) := fun _ => lift1_reps <| reps_ok fun hb y y' hy _ => by
  have a := hR.agree (CRel.guard_ok_left hb)
  rw [CRel.rep_ran _ hb, ran_iff, ran_iff]
  exact ⟨fun ⟨e, x, h1, h2⟩ => ⟨e, x, (a x y rfl hy).1 h1, (a x y' rfl (e ▸ hy)).1 h2⟩,
    fun ⟨e, x, h1, h2⟩ => ⟨e, x, (a x y rfl hy).2 h1, (a x y' rfl (e ▸ hy)).2 h2⟩⟩

theorem pair_sound {A B C : Obj} {d e : Bool} {R : Fn d A B} {S : Fn e A C} {TR : Den A B} {TS : Den A C}
    (hR : Sound R TR) (hS : Sound S TS) : Sound (pair A B C d e R S) (rpair TR TS) :=
  fun _ => lift2_reps <| reps_ok fun hb x p hx _ => by
    have hc := CRel.guard_ok_left hb; rw [Bool.and_eq_true] at hc
    rw [CRel.rep_pair _ _ hb]; exact and_congr (hR.agree hc.1 x p.1 hx rfl) (hS.agree hc.2 x p.2 hx rfl)

/-- `⟨X,Y⟩ = Xπ₁° ∩ Yπ₂°`: the converse `convTm` gives two sides each read through one projection
    (`Proj.meet`), which is how `(P×Q)° = P°×Q°` runs on demand. -/
theorem rpair_eq_meet_proj {A B C : Obj} (X : Den C A) (Y : Den C B) :
    (X ≫ (graph Prod.fst : Den (.prod A B) A)° ∩ Y ≫ (graph Prod.snd : Den (.prod A B) B)°) = rpair X Y :=
  funext fun _ => funext fun _ => propext
    ⟨fun ⟨⟨_, ha, ea⟩, ⟨_, hb, eb⟩⟩ => ⟨ea ▸ ha, eb ▸ hb⟩, fun ⟨ha, hb⟩ => ⟨⟨_, ha, rfl⟩, ⟨_, hb, rfl⟩⟩⟩

/-- `Xf° ∩ Yf° = (X∩Y)f°` for a map `f`: two sides read through one projection stay so (`Proj.meet`). -/
theorem meet_comp_conv_graph {A B C : Obj} (f : A.El → B.El) (X Y : Den C B) :
    (X ≫ (graph f : Den A B)° ∩ Y ≫ (graph f : Den A B)°) = (X ∩ Y) ≫ (graph f : Den A B)° :=
  funext fun _ => funext fun a => propext
    ⟨fun ⟨⟨w, hx, ex⟩, ⟨w', hy, ey⟩⟩ =>
      ⟨w, ⟨hx, ((show w' = f a from ey).trans (show w = f a from ex).symm) ▸ hy⟩, ex⟩,
      fun ⟨_, ⟨hx, hy⟩, e⟩ => ⟨⟨_, hx, e⟩, ⟨_, hy, e⟩⟩⟩

theorem prod_sound {A B C D : Obj} {R : Fn false A B} {S : Fn false C D} {TR : Den A B} {TS : Den C D}
    (hR : Sound R TR) (hS : Sound S TS) : Sound (prod A B C D R S) (rprodMap TR TS) :=
  fun _ => lift2_reps <| reps_ok fun hb x y _ _ => by
    have hc := CRel.guard_ok_left hb; rw [Bool.and_eq_true] at hc
    rw [CRel.rep_prod _ _ hb, hR.run_eq hc.1, hS.run_eq hc.2]

theorem junc_sound {A B C : Obj} {R : Fn false A C} {S : Fn false B C} {TR : Den A C} {TS : Den B C}
    (hR : Sound R TR) (hS : Sound S TS) : Sound (junc A B C R S) (Core.Rel.junc TR TS) :=
  fun _ => lift2_reps <| reps_ok fun hb x y _ _ => by
    have hc := CRel.guard_ok_left hb; rw [Bool.and_eq_true] at hc
    rw [CRel.rep_junc _ _ hb, hR.run_eq hc.1, hS.run_eq hc.2]

/-- A relation's key rows are the keys its `rep` relates. -/
theorem keyRowRep {A B : Obj} (U : Tab A B) (a : A.El) : (∃ p, U.key.row p = a) ↔ ∃ b, rep U a b :=
  ⟨fun ⟨p, e⟩ => ⟨U.val.row p, p, e, rfl⟩, fun ⟨_, p, e, _⟩ => ⟨p, e⟩⟩

theorem nil_sound {A B : Obj} : Sound (nil A B) nilDen := ofVals_sound fun X hb => idU_ext fun x Y => by
  rw [CRel.rep_ofC hb, rep_topC _ _ (CRel.ofC_ok hb).1]
  constructor
  · rintro ⟨_, ⟨e1, hx⟩, _, _, e, j, hj⟩; subst e1; subst e; exact ⟨hx, by rw [← hj, nilVal_row]⟩
  · rintro ⟨hx, e⟩; exact ⟨x, ⟨rfl, hx⟩, Y, trivial, rfl, ⟨0, by simp⟩, by rw [e, nilVal_row]⟩

theorem atPos_sound {B : Obj} (k : Nat) : Sound (atPos B k) (atDen k) :=
  ofVals_sound (f := fun X => CRel.atPos k X) fun X hb => idU_ext <| CRel.rep_atPos k X hb

/-- `succ` on the universe `U`: `u` and its successor both in `U`. -/
theorem succ_sound {U : Fn false .long .long} {TU : Den .long .long} (hU : Sound U TU) :
    Sound (succ U) (succDen TU) := ofVals_sound fun X hb => by
  dsimp only at hb ⊢; obtain ⟨⟨hu, hc⟩, e⟩ := also_ok_rel hb
  have h2 := Bool.and_eq_true_iff.1 (CRel.guard_ok_left hc)
  rw [e, CRel.rep_comp _ _ hc, CRel.some_rel, ← comp_assoc, idU_idem]
  exact congrArg _ (Core.Rel.ext fun u w => show _ ↔ (∃ v, TU u v) ∧ w = Ew.intStep Ew.add nul u 1 ∧ ∃ v, TU w v by
    rw [CRel.rep_succ _ h2.2, keyRowRep, keyRowRep, hU.eq hu])

theorem leq_sound {U : Fn false .long .long} {TU : Den .long .long} (hU : Sound U TU) :
    Sound (leq U) (leqDen TU) := fun K => tab_reps fun hb => by
  obtain ⟨⟨hu, hc⟩, e⟩ := also_ok_rel hb; rw [e]
  exact cut_reps K (fun hr => Core.Rel.ext fun a b => by
    rw [CRel.rep_leq _ _ hr, keyRowRep, keyRowRep, hU.eq hu]) hc

theorem lt_sound {U : Fn false .long .long} {TU : Den .long .long} (hU : Sound U TU) :
    Sound (lt U) (ltDen TU) := fun K => tab_reps fun hb => by
  obtain ⟨⟨hu, hc⟩, e⟩ := also_ok_rel hb; rw [e]
  exact cut_reps K (fun hr => Core.Rel.ext fun a b => by
    rw [CRel.rep_lt _ _ hr, keyRowRep, keyRowRep, hU.eq hu]) hc

/-- A value verb `k` on the universe `U`: both inputs in `U`, `Int64`'s step, not the null and, for `+ - *`, not
    wrapped, then within `U` (`rep_arith`). -/
theorem arith_sound (k : UInt8) {U : Fn false .long .long} {TU : Den .long .long} (hU : Sound U TU) :
    Sound (arith k U) (arithDen k TU) := by
  have hs : Sound (ofVals _ _ fun X => CRel.comp (some (Alg.arith k X)) (U.at ()) : Fn true (.prod .long .long) .long)
      (stepDen k ≫ TU) := ofVals_sound fun X hb => idU_ext fun p w => by
    have hc := Bool.and_eq_true_iff.1 (CRel.guard_ok_left hb)
    rw [CRel.rep_comp _ _ hb, hU.eq hc.2, Core.Rel.comp_apply, Core.Rel.comp_apply]
    obtain ⟨a, b⟩ := p
    exact ⟨fun ⟨v, h1, h2⟩ => let ⟨hj, s⟩ := (rep_arith k X a b v).1 h1; ⟨hj, v, s, h2⟩,
      fun ⟨hj, v, s, h2⟩ => ⟨v, (rep_arith k X a b v).2 ⟨hj, s⟩, h2⟩⟩
  exact comp_sound (dom_sound (comp_sound outl_sound hU)) (comp_sound (dom_sound (comp_sound outr_sound hU)) hs)

/-- `fold(e, S)`: a chain of values `ys`, its last from `e`, each the step `S` of the element and the next value
    (`rep_foldOn`, `S` run on each round's pairs by `onKeys`). -/
theorem foldr_sound {E V : Obj} {d : Bool} {e : Fn false V V} {S : Fn d (.prod E V) V} {Te : Den V V}
    {TS : Den (.prod E V) V} (he : Sound e Te) (hS : Sound S TS) :
    Sound (foldr E V d e S) (foldrDen Te TS) := ofVals_sound fun X hb => idU_ext fun xs w => by
  dsimp only at hb ⊢; obtain ⟨hb, e⟩ := also_ok_rel hb; rw [e]
  refine (CRel.rep_foldOn false pairC Prod.mk Rep.pairC_pt _ _ _ hb.2 _ rfl _ rfl _ (fun _ _ => rfl) _ (fun _ => rfl) _
    (fun _ => rfl) _ (fun _ => rfl) (fun _ => TS) ?_ xs w).trans ?_
  · intro i _ _ hbi p w hp hc
    simp only [demandStepC, Bool.and_eq_true] at hbi
    exact onKeys_round hS _ p w hp hc hbi.1.2
  · exact and_congr_right fun _ => exists_congr fun ys => exists_congr fun hy => and_congr_left fun _ =>
      (valRow _ _).trans (by rw [he.run_eq hb.1]; exact Iff.rfl)

/-- `⦇e, S⦈`, the left fold: `rep_foldOn` from the start (`l = true`), the round's pair `(acc, x)`, is the right
    chain over `xs.reverse` (`foldlDen_rev`). -/
theorem fold_sound {E V : Obj} {d : Bool} {e : Fn false V V} {S : Fn d (.prod V E) V} {Te : Den V V}
    {TS : Den (.prod V E) V} (he : Sound e Te) (hS : Sound S TS) :
    Sound (fold E V d e S) (foldDen Te TS) := ofVals_sound fun X hb => idU_ext fun xs w => by
  dsimp only at hb ⊢; obtain ⟨hb, e⟩ := also_ok_rel hb; rw [e]
  refine (CRel.rep_foldOn true (fun el p => pairC p el) (fun e u => (u, e))
    (fun el p h r q => (Rep.pairC_pt p el h r q).trans
      ⟨fun ⟨u, e, hu, he, hq⟩ => ⟨e, u, he, hu, hq⟩, fun ⟨e, u, he, hu, hq⟩ => ⟨u, e, hu, he, hq⟩⟩)
    _ _ _ hb.2 _ rfl _ rfl _ (fun _ _ => rfl) _ (fun _ => rfl) _ (fun _ => rfl) _ (fun _ => rfl) (fun _ => TS) ?_
    xs w).trans ?_
  · intro i _ _ hbi p w hp hc
    simp only [demandStepC, Bool.and_eq_true] at hbi
    exact onKeys_round hS _ p w hp hc hbi.1.2
  · rw [foldDen_rev]; simp only [ordL, cond_true]
    exact and_congr_right fun _ => exists_congr fun ys => exists_congr fun hy => and_congr_left fun _ =>
      (valRow _ _).trans (by rw [he.run_eq hb.1])

open Rel.KernelWF Rel.Rep.FoldN Rel.Rep.OpsN Rel.Rep.Prim in
/-- `est(Q)` keeps `b` of `xs` unless some other `c` of `xs` fails `Q` at `(b, c)`; `Q` runs on the pairs of
    values of one array (`estOnC_ok`'s `pair` and `ran` bits read them back). -/
theorem est_sound {B : Obj} {Q : Fn true (.prod B B) (.prod B B)} {TQ : Den (.prod B B) (.prod B B)}
    (hQ : Sound Q TQ) :
    Sound (est B Q) (estDen TQ) := KSound.reps fun D _ hb xs b hx => by
  have hb' : (CRel.estOn (fun P => Q.at P.rel) (CRel.mem D.val)).ok = true := hb
  have hG : (CRel.mem D.val).ok = true := CRel.guard_ok_left hb'
  obtain ⟨hq, h⟩ := CRel.rep_estOn _ _ hb'
  have e : CRel.estOn (fun P => Q.at P.rel) (CRel.mem D.val) = _ := CRel.guard_eq CRel.ok hb'
  rw [e] at hb'; replace hb' := (CRel.ofC_ok hb').1
  obtain ⟨-, ⟨hPf, hP'⟩, ⟨hDf, hDp⟩, -⟩ := estOnC_ok _ _ hb' _ rfl _ rfl _ rfl _ rfl _ rfl _ rfl _ rfl _ rfl
  obtain ⟨p1, p2, p3, p4, p5⟩ := hP' _ rfl
  have eD : ∀ x x', rep (Alg.ran (Alg.pair (CRel.mem D.val).rel (CRel.mem D.val).rel)) x x' ↔
      x = x' ∧ ∃ a, rep (CRel.mem D.val).rel a x.1 ∧ rep (CRel.mem D.val).rel a x.2 := fun x x' => by
    rw [rep_ran_corefl _ (one_ok _ hDf) hDp, rep_pair _ _ (codes_faithful_wf _ _ hPf).1 p1 p2 p3 p4 p5]; exact Iff.rfl
  have hC : Cor (d := true) (Alg.ran (Alg.pair (CRel.mem D.val).rel (CRel.mem D.val).rel)) :=
    fun x x' h => ((eD x x').1 h).1
  have hr := keyRow hx
  show rep (CRel.estOn (fun P => Q.at P.rel) (CRel.mem D.val)).rel xs b ↔ _
  rw [h xs b, CRel.rep_mem _ hG, and_iff_right hr]
  refine and_congr_right fun hbx => not_congr (exists_congr fun c => ?_)
  rw [CRel.rep_mem _ hG]
  have hk c (hc : c ∈ xs) : rep (Alg.ran (Alg.pair (CRel.mem D.val).rel (CRel.mem D.val).rel)) (b, c) (b, c) :=
    (eD _ _).2 ⟨rfl, xs, (CRel.rep_mem _ hG xs b).2 ⟨hr, hbx⟩, (CRel.rep_mem _ hG xs c).2 ⟨hr, hc⟩⟩
  exact ⟨fun ⟨⟨_, hc⟩, hne, hn⟩ => ⟨hc, hne, fun t => hn ((hQ.at _ hC hq _ _ (hk c hc)).2 t)⟩,
    fun ⟨hc, hne, hn⟩ => ⟨⟨hr, hc⟩, hne, fun t => hn ((hQ.at _ hC hq _ _ (hk c hc)).1 t)⟩⟩

/-- `X × L`: on a known domain `X`, `𝟙(X) ⊤` then the values of `V` cut to the known range, which `Reps` reads on
    that range only (`cut_reps`). -/
theorem top_sound {A B : Obj} {V : Fn false B B} {TV : Den B B} (hV : Sound V TV) :
    Sound (top A B V) (Core.Rel.top ≫ TV) := fun K => by
  rcases K with ⟨_ | ⟨n, X⟩, L⟩
  · trivial
  refine tab_reps fun hb => ?_
  obtain ⟨⟨hv, hc⟩, e⟩ := also_ok_rel hb
  rw [e, CRel.rep_ofC hc, rep_topC _ _ (CRel.ofC_ok hc).1, ← rep_idU, ← rep_idU]
  have hcut := cut_reps ⟨none, L⟩ (fun hr => hV.eq hr) hv
  generalize cut ⟨none, L⟩ (V.at ()) = v at hcut ⊢
  have ht : (Core.Rel.top : Den A B) ≫ rep (idU v.rel.val) = Core.Rel.top ≫ rep v.rel := Core.Rel.ext fun x y => by
    rw [comp_apply, comp_apply]
    constructor
    · rintro ⟨z, -, hz⟩; rw [rep_idU] at hz; obtain ⟨rfl, hz⟩ := hz
      obtain ⟨a, h⟩ := (valRow _ _).1 hz; exact ⟨a, trivial, h⟩
    · rintro ⟨a, -, h⟩; exact ⟨y, trivial, by rw [rep_idU]; exact ⟨rfl, (valRow _ _).2 ⟨a, h⟩⟩⟩
  simp only [Known.den, Option.elim, id_comp] at hcut ⊢
  simp only [comp_assoc]
  rw [← comp_assoc (rep (idU X)) (rep (idU X)), idU_idem, ← comp_assoc Core.Rel.top, ht, comp_assoc, hcut]

theorem rdiv_sound {A B C : Obj} {R : Fn false A C} {S : Fn false B C} {UA : Fn false A A} {UB : Fn false B B}
    {TR : Den A C} {TS : Den B C} {TA : Den A A} {TB : Den B B} (hR : Sound R TR) (hS : Sound S TS)
    (hA : Sound UA TA) (hB : Sound UB TB) :
    Sound (rdiv A B C R S UA UB)
      (rdivDen TR TS TA TB) :=
  fun _ => lift2_reps <| reps_ok fun hb x y _ _ => by
    dsimp only at hb ⊢; obtain ⟨hb, e⟩ := also_ok_rel hb; rw [e]; simp only [Bool.and_eq_true] at hb
    have hc := CRel.guard_ok_left hb.2; rw [Bool.and_eq_true] at hc
    rw [CRel.rep_rightDiv _ _ _ _ hb.2, hR.run_eq hc.1, hS.run_eq hc.2, valRow, valRow, hA.run_eq hb.1.1,
      hB.run_eq hb.1.2]

/-! ### The bit-matrix plans -/

/-- **`runC`'s answer is the plan's relation** under its bit, on either path, in check mode too (`die` is its
    argument). -/
theorem rep_runC {A B : Obj} {d : Bool} (p : Tm A B d) (hb : (Bits.runC p).2 = true) (a : A.El) (b : B.El) :
    rep (Bits.runC p).1 a b ↔ p.den Val.empty a b := by
  by_cases hv : p.isVal = true
  · simp only [Bits.runC, hv, if_true] at hb ⊢; exact Bits.rep_tableC p hb a b
  · simp only [Bits.runC, hv, Bool.false_eq_true, if_false] at hb ⊢
    revert hb; split
    · rename_i R h; simp only [dbgTrace, Bits.die, ite_self]; exact fun _ => Bits.bits_table h a b
    · by_cases hc : (Bits.checkOn == 0) = true
      · rw [if_pos hc]; exact fun hb => Bits.rep_tableC _ hb a b
      · rw [if_neg hc]; simp only [dbgTrace]; exact fun hb => Bits.rep_table _ hb a b

/-- The demand `demP` hands `S` in `R S`: a coreflexive holding every value of `R`'s plan. -/
theorem demP_spec {A B : Obj} (r : Tm A B false) (hb : (demP r).2 = true) :
    (∀ x y, rep (demP r).1 x y → x = y) ∧ ∀ a b, r.den Val.empty a b → rep (demP r).1 b b := by
  simp only [demP, Bool.and_eq_true] at hb
  have hK := rep_ranC _ hb.2
  have hR := rep_runC r hb.1
  refine ⟨fun a b h => ?_, fun a b h => ?_⟩
  · have h' : rep (ranC (Bits.runC r).1).1 a b := h
    rw [hK] at h'; exact h'.1
  · show rep (ranC (Bits.runC r).1).1 b b
    rw [hK]; exact ⟨rfl, a, (hR a b).2 h, (hR a b).2 h⟩

theorem pleaf_sound {A B : Obj} {d : Bool} {f : Fn d A B} {T : Den A B} (hf : Sound f T) :
    PSound (pleaf A B d f) T := by
  cases d
  · exact fun hb x y _ => hf.at () trivial hb x y rfl
  · exact fun D hD hb x y hx => hf.at D hD hb x y hx

/-- `R S` on whatever keys `R`'s plan `r` was given, `S`'s plan closed or run on `ran(r)`. -/
theorem compPl_sound {A B C : Obj} {r : Tm A B false × Bool} {S : Pl B C} {D : Den A A} {TR : Den A B}
    {TS : Den B C} (hr : PlOK r D TR) (hS : PSound S TS) : PlOK (compPl r S) D (TR ≫ TS) := by
  cases S with
  | closed s =>
    intro hb x z hx
    simp only [compPl, Bool.and_eq_true] at hb
    have hs := hS hb.2
    exact ⟨fun ⟨b, p1, p2⟩ => ⟨b, (hr hb.1 x b hx).1 p1, (hs b z rfl).1 p2⟩,
      fun ⟨b, p1, p2⟩ => ⟨b, (hr hb.1 x b hx).2 p1, (hs b z rfl).2 p2⟩⟩
  | on g =>
    intro hb x z hx
    simp only [compPl, Bool.and_eq_true] at hb
    obtain ⟨⟨h1, h2⟩, h3⟩ := hb
    obtain ⟨kc, kk⟩ := demP_spec _ h2
    have hs := hS _ kc h3
    exact ⟨fun ⟨b, p1, p2⟩ => ⟨b, (hr h1 x b hx).1 p1, (hs b z (kk x b p1)).1 p2⟩,
      fun ⟨b, p1, p2⟩ => have p1' := (hr h1 x b hx).2 p1; ⟨b, p1', (hs b z (kk x b p1')).2 p2⟩⟩

theorem pcomp_sound {A B C : Obj} {R : Pl A B} {S : Pl B C} {TR : Den A B} {TS : Den B C}
    (hR : PSound R TR) (hS : PSound S TS) : PSound (pcomp A B C R S) (TR ≫ TS) := by
  cases R with
  | closed r => exact compPl_sound hR hS
  | on f => exact fun D hD => compPl_sound (hR D hD) hS

theorem pconv_sound {A B : Obj} {R : Pl A B} {T : Den A B} (hR : PSound R T) : PSound (pconv A B R) T° :=
  fun hb y x _ => hR.get hb x y rfl

theorem pmeet_sound {A B : Obj} {R S : Pl A B} {TR TS : Den A B} (hR : PSound R TR) (hS : PSound S TS) :
    PSound (pmeet A B R S) (TR ∩ TS) :=
  Pl.map2_sound (fun _ _ _ hr hs hb x y hx => by
    simp only [Bool.and_eq_true] at hb; exact and_congr (hr hb.1 x y hx) (hs hb.2 x y hx)) hR hS

theorem pjoin_sound {A B : Obj} {R S : Pl A B} {TR TS : Den A B} (hR : PSound R TR) (hS : PSound S TS) :
    PSound (pjoin A B R S) (TR ∪ TS) :=
  Pl.map2_sound (fun _ _ _ hr hs hb x y hx => by
    simp only [Bool.and_eq_true] at hb; exact or_congr (hr hb.1 x y hx) (hs hb.2 x y hx)) hR hS

theorem pdiff_sound {A B : Obj} {R S : Pl A B} {TR TS : Den A B} (hR : PSound R TR) (hS : PSound S TS) :
    PSound (pdiff A B R S) (diffDen TR TS) :=
  Pl.map2_sound (fun _ _ _ hr hs hb x y hx => by
    simp only [Bool.and_eq_true] at hb; exact and_congr (hr hb.1 x y hx) (not_congr (hs hb.2 x y hx))) hR hS

theorem pldiv_sound {A B C : Obj} {R : Pl A B} {S : Pl A C} {UB : Fn false B B} {UC : Fn false C C}
    {TR : Den A B} {TS : Den A C} {TB : Den B B} {TC : Den C C} (hR : PSound R TR) (hS : PSound S TS)
    (hB : Sound UB TB) (hC : Sound UC TC) : PSound (pldiv A B C R S UB UC) (ldivDen TR TS TB TC) :=
  fun hb b c _ => by
    replace hb : (R.get.2 && S.get.2 && (UB.at ()).ok && (UC.at ()).ok) = true := hb
    simp only [Bool.and_eq_true] at hb
    obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := hb
    have r a b := hR.get h1 a b rfl
    have s a c := hS.get h2 a c rfl
    show ldivDen (R.get.1.den Val.empty) (S.get.1.den Val.empty) (rep (UB.at ()).rel) (rep (UC.at ()).rel) b c ↔ _
    rw [hB.eq h3, hC.eq h4]
    simp only [ldivDen, r, s]

/-- A plan's value run as bits is `Sound` where, at every point, it computes `T`. -/
theorem runPl_sound {A B : Obj} {p : Tm A B false × Bool} {T : Den A B} (hp : PlOK p (𝟙 _) T) :
    Sound (.tab (runPl p)) T := const_sound fun hb => by
  simp only [runPl] at hb ⊢; obtain ⟨hb, e⟩ := also_ok_rel hb; rw [e, CRel.rep_ofC hb.2]
  exact Core.Rel.ext fun x y => (rep_runC _ (CRel.ofC_ok hb.2).1 x y).trans (hp hb.1 x y rfl)

/-- A plan run as bits (`Bits.runC`), its leaves' bits kept: the plan's relation, on its keys. -/
theorem ofPl_sound {A B : Obj} {p : Pl A B} {T : Den A B} (hp : PSound p T) : Sound (ofPl A B p) T := by
  cases p with
  | closed p => exact runPl_sound hp
  | on f =>
    refine ofVals_keys fun X hb x y hx => ?_
    simp only [runPl] at hb ⊢; obtain ⟨hb, e⟩ := also_ok_rel hb; rw [e, CRel.rep_ofC hb.2]
    exact (rep_runC _ (CRel.ofC_ok hb.2).1 x y).trans
      (hp (idU X) (fun x y k => ((idU_holds X x y).1 k).1) hb.1 x y hx)

theorem compB_sound {A B C : Obj} {R : Pl A B} {S : Pl B C} {TR : Den A B} {TS : Den B C}
    (hR : PSound R TR) (hS : PSound S TS) : Sound (compB A B C R S) (TR ≫ TS) :=
  runPl_sound (pcomp_sound hR hS).get

theorem meetB_sound {A B : Obj} {R S : Pl A B} {TR TS : Den A B} (hR : PSound R TR) (hS : PSound S TS) :
    Sound (meetB A B R S) (TR ∩ TS) :=
  runPl_sound (pmeet_sound hR hS).get

theorem diffB_sound {A B : Obj} {R S : Pl A B} {TR TS : Den A B} (hR : PSound R TR) (hS : PSound S TS) :
    Sound (diffB A B R S) (diffDen TR TS) :=
  runPl_sound (pdiff_sound hR hS).get

theorem ldivB_sound {A B C : Obj} {R : Pl A B} {S : Pl A C} {UB : Fn false B B} {UC : Fn false C C}
    {TR : Den A B} {TS : Den A C} {TB : Den B B} {TC : Den C C} (hR : PSound R TR) (hS : PSound S TS)
    (hB : Sound UB TB) (hC : Sound UC TC) : Sound (ldivB A B C R S UB UC) (ldivDen TR TS TB TC) :=
  runPl_sound (pldiv_sound hR hS hB hC).get

/-- **`Λ(R)` on the keys `D` names each key's canonical list** (`lamDen`, D2 = C): `rep_lamOn` gives the list's
    members and a list at every key, `lamOnC_asc` that it ascends with no repeat, `B.KeyInj` that it ascends
    strictly, and `eq_of_pairwise` that the strictly ascending list of one set is the one `lamDen` names. -/
theorem lam_sound {A B : Obj} {d : Bool} {R : Fn d A B} {TR : Den A B} (hR : Sound R TR) (ho : B.Ordered)
    (hi : B.KeyInj) : Sound (lam A B d R) (lamDen TR) :=
  KSound.reps fun D hD hb a ys ha => by
    have hs := atKeys hR D hD (CRel.guard_ok_left hb)
    obtain ⟨h1, h2⟩ := CRel.rep_lamOn _ _ hb
    have e : CRel.lamOn (R.at (Dem.of d D)) D.val = _ := CRel.guard_eq CRel.ok hb
    have hc := e ▸ hb
    have asc : ∀ Y, rep (CRel.lamOn (R.at (Dem.of d D)) D.val).rel a Y → Y.Pairwise B.lt := fun Y h => by
      obtain ⟨hn, hp⟩ := lamOnC_asc _ _ ho (CRel.ofC_ok hc).1 a Y (by rw [← CRel.rep_ofC hc, ← e]; exact h)
      exact (hn.and hp).imp fun ⟨ne, nl⟩ =>
        (B.lt_trichotomy _ _).resolve_right fun h => h.elim (fun k => ne (hi _ _ k)) nl
    refine ⟨fun h => ⟨asc ys h, fun b => (h1 a ys h b).trans (hs a b ha)⟩, fun ⟨hp, hm⟩ => ?_⟩
    obtain ⟨Y, hY⟩ := (h2 a).2 (.inr (keyRow ha))
    rwa [← eq_of_pairwise (Obj.lt_irrefl _) (Obj.lt_trans _) (asc Y hY) hp
      fun b => (h1 a Y hY b).trans ((hs a b ha).trans (hm b).symm)]

end Rel.Lang.Gen
