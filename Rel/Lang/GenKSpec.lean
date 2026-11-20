import Rel.Run.Lang.GenK
import Rel.RepBits
import Rel.RepTabArith

/-! Each `GenK` op whose `Tab` law exists represents its constructor's case of `Tm.den`: given parts that represent
    their meanings in every context, the op represents the right-hand side `Tm.den` gives that constructor, in every
    context. Everything goes through `reps_iff`, which reads `Reps` off `runE`, so an op's lemma is about the table it
    computes. Two ops read a bit matrix through an op with no law yet (`Tab.compTabMat`, `Tab.keepBits`); their lemmas
    take that law as a hypothesis (`CompTabMatLaw`, `KeepBitsLaw`). -/

namespace Rel.Lang

open Rel Rel.Rep Rel.Kernel Rel.Verify Gen
open scoped Rel.Core.Rel
open Rel.Core.Rel hiding id comp recip inter union zero le inl inr junc

namespace GenK

variable {A B C D : Obj}

/-! ### Reading `Reps` off `runE` -/

/-- `P` and `Q` agree at every pair whose two values `K` admits. -/
def Agrees (K : Known A B) (P Q : Core.Rel A.El B.El) : Prop :=
  ∀ x y, K.den.1 x x → K.den.2 y y → (P x y ↔ Q x y)

theorem agrees_iff (K : Known A B) (P Q : Core.Rel A.El B.El) :
    K.den.1 ≫ P ≫ K.den.2 = K.den.1 ≫ Q ≫ K.den.2 ↔ Agrees K P Q := by
  refine ⟨fun E x y hx hy => ?_, fun h => Core.Rel.ext fun a b => ?_⟩
  · have e := restrict K (X := Q) hx hy; rw [← E] at e; exact (restrict K (X := P) hx hy).symm.trans e
  · constructor <;> rintro ⟨a', p, b', r, q⟩ <;> obtain rfl := K.cor.1 a a' p <;> obtain rfl := K.cor.2 b' b q
    · exact ⟨_, p, _, (h _ _ p q).1 r, q⟩
    · exact ⟨_, p, _, (h _ _ p q).2 r, q⟩

/-- In the empty context agreeing is being equal. -/
theorem agrees_empty {P Q : Core.Rel A.El B.El} (h : Agrees {} P Q) : Q = P :=
  Core.Rel.ext fun a b => (h a b rfl rfl).symm

/-- A known side admits exactly its values. -/
theorem side_some {o : Option ((n : USize) × Vals C n)} {n : USize} {X : Vals C n} (h : o = some ⟨n, X⟩)
    (x : C.El) : o.elim (𝟙 _) (fun c => (graph c.2.row)° ≫ graph c.2.row) x x ↔ ∃ i, X.row i = x := by
  subst h; exact ⟨fun ⟨i, e, _⟩ => ⟨i, e.symm⟩, fun ⟨i, e⟩ => ⟨i, e.symm, e.symm⟩⟩

/-- `r` represents `X` in `K` iff every table `r` computes there agrees with `X` on `K`'s sides. -/
theorem reps_iff (K : Known A B) (r : Rel A B) (X : Core.Rel A.El B.El) :
    r.Reps K X ↔ ∀ t, r.runE K = .ok t → Agrees K (rep t) X := by
  induction r with
  | tab t => cases t <;> simp [Rel.Rel.Reps, Rel.Rel.runE, agrees_iff]
  | lazy f ih => simp only [Rel.Rel.Reps, Rel.Rel.runE]; exact ih K
  | bits g w o x ra y rc => simp only [Rel.Rel.Reps, Rel.Rel.runE]; split <;> simp_all [agrees_iff]

theorem bind_ok {α β : Type} {x : Except String α} {f : α → Except String β} {b : β} (h : (x >>= f) = .ok b) :
    ∃ a, x = .ok a ∧ f a = .ok b := by
  cases x with
  | error e => nomatch h
  | ok a => exact ⟨a, rfl, h⟩

/-- Forcing runs nothing new: the forced value computes, in any context, what `r` computes in `K`. -/
theorem force_runE (r : Rel A B) (K K' : Known A B) : (r.force K).runE K' = r.runE K := by
  induction r with
  | lazy f ih => simp only [Rel.Rel.force, Rel.Rel.runE]; exact ih K
  | tab _ => rfl
  | bits => rfl

/-! ### The lifting: an op on tables (`lift1`, `lift2`, `ofVals`) is sound where its table step is -/

theorem lift1_runE (f : Tab A B → Except String (Tab C D)) (k : Known C D → Known A B) (R : Rel A B)
    (K : Known C D) : (lift1 f k R).runE K = R.runE (k K) >>= f := by cases R <;> rfl

theorem lift2_runE {E F : Obj} (f : Tab A B → Tab C D → Except String (Tab E F)) (kl : Known E F → Known A B)
    (kr : Known E F → Known C D) (R : Rel A B) (S : Rel C D) (K : Known E F) :
    (lift2 f kl kr R S).runE K = (R.runE (kl K) >>= fun r => S.runE (kr K) >>= f r) := by
  cases R <;> cases S <;> rfl

theorem lift1_sound {f : Tab A B → Except String (Tab C D)} {k : Known C D → Known A B} {R : Rel A B}
    {X : Core.Rel A.El B.El} {Y : Core.Rel C.El D.El} (hR : ∀ K, R.Reps K X)
    (hf : ∀ K r t, f r = .ok t → Agrees (k K) (rep r) X → Agrees K (rep t) Y) (K : Known C D) :
    (lift1 f k R).Reps K Y := by
  rw [reps_iff, lift1_runE]; intro t h
  obtain ⟨r, hr, ht⟩ := bind_ok h
  exact hf K r t ht ((reps_iff _ _ _).1 (hR _) r hr)

theorem lift2_sound {E F : Obj} {f : Tab A B → Tab C D → Except String (Tab E F)} {kl : Known E F → Known A B}
    {kr : Known E F → Known C D} {R : Rel A B} {S : Rel C D} {X : Core.Rel A.El B.El} {Y : Core.Rel C.El D.El}
    {Z : Core.Rel E.El F.El} (hR : ∀ K, R.Reps K X) (hS : ∀ K, S.Reps K Y)
    (hf : ∀ K r s t, f r s = .ok t → Agrees (kl K) (rep r) X → Agrees (kr K) (rep s) Y → Agrees K (rep t) Z)
    (K : Known E F) : (lift2 f kl kr R S).Reps K Z := by
  rw [reps_iff, lift2_runE]; intro t h
  obtain ⟨r, hr, h⟩ := bind_ok h
  obtain ⟨s, hs, ht⟩ := bind_ok h
  exact hf K r s t ht ((reps_iff _ _ _).1 (hR _) r hr) ((reps_iff _ _ _).1 (hS _) s hs)

theorem ofVals_sound {f : {n : USize} → Vals A n → Except String (Tab A B)} {Y : Core.Rel A.El B.El}
    (hf : ∀ K n (X : Vals A n) t, K.dom = some ⟨n, X⟩ → f X = .ok t → Agrees K (rep t) Y) (K : Known A B) :
    (ofVals A B f).Reps K Y := by
  rw [reps_iff]; intro t h
  cases hK : K.dom with
  | none => simp [ofVals, Rel.Rel.runE, hK] at h
  | some c => obtain ⟨n, X⟩ := c; simp only [ofVals, Rel.Rel.runE, hK, Option.elim] at h; exact hf K n X t hK h

/-- A leaf on demand whose `Tab` law is "a key in demand, related by `P`": `id outl outr nil`, and the rows
    `∋ inl inr` (`τ`, `setify` given their `Obj.lt` hypothesis) run under `ofVals`. -/
theorem ofVals_row_sound {f : {n : USize} → Vals A n → Except String (Tab A B)} {P : Core.Rel A.El B.El}
    (hf : ∀ n (X : Vals A n) t, f X = .ok t → ∀ a b, t.Holds a b ↔ (∃ i, X.row i = a) ∧ P a b) :
    ∀ K, (ofVals A B f).Reps K P :=
  ofVals_sound fun _ _ _ _ hK h a b ha _ => (hf _ _ _ h a b).trans (and_iff_right ((side_some hK a).1 ha))

/-! ### Structural ops: `id comp conv meet join zero top dom ran` -/

theorem zero_sound : ∀ K, (GenK.zero A B).Reps K 𝟘 :=
  fun _ => (reps_iff _ _ _).2 fun _ h x y _ _ => Tab.zero_holds h x y

theorem val_sound (R : Tab A B × Bool) : ∀ K, (GenK.val A B R).Reps K (rep R.1) := fun K => by
  rw [reps_iff]; intro t h; unfold GenK.val const at h
  split at h
  · exact fun x y _ _ => Tab.canon_holds h x y
  · nomatch h

theorem uni_sound {m : USize} (U : Vals A m × Bool) :
    ∀ K, (GenK.uni A m U).Reps K ((graph U.1.row)° ≫ graph U.1.row) := fun K => by
  rw [reps_iff]; intro t h; unfold GenK.uni const at h
  split at h
  · refine fun x y _ _ => (Tab.idU_holds h x y).trans ⟨?_, ?_⟩
    · rintro ⟨rfl, i, rfl⟩; exact ⟨i, rfl, rfl⟩
    · rintro ⟨i, rfl, rfl⟩; exact ⟨rfl, i, rfl⟩
  · nomatch h

theorem id_sound : ∀ K, (GenK.id A).Reps K (𝟙 _) :=
  ofVals_row_sound fun _ _ _ h a b => (Tab.idU_holds h a b).trans and_comm

theorem conv_sound {R : Rel A B} {X : Core.Rel A.El B.El} (hR : ∀ K, R.Reps K X) :
    ∀ K, (GenK.conv A B R).Reps K X° :=
  lift1_sound hR fun _ _ _ ht hr x y hx hy => (Tab.conv_holds ht x y).trans (hr y x hy hx)

theorem join_sound {d e : Bool} {R S : Rel A B} {X Y : Core.Rel A.El B.El} (hR : ∀ K, R.Reps K X)
    (hS : ∀ K, S.Reps K Y) : ∀ K, (GenK.join A B d e R S).Reps K (X ∪ Y) :=
  lift2_sound hR hS fun _ _ _ _ ht hr hs x y hx hy =>
    (Tab.union_holds ht x y).trans (or_congr (hr x y hx hy) (hs x y hx hy))

theorem dom_sound {d : Bool} {R : Rel A B} {X : Core.Rel A.El B.El} (hR : ∀ K, R.Reps K X) :
    ∀ K, (GenK.dom A B d R).Reps K (𝟙 _ ∩ X ≫ X°) :=
  lift1_sound hR fun _ r _ ht hr x x' hx _ => by
    have e : ∀ y, (rep r x y ↔ X x y) := fun y => hr x y hx rfl
    refine (Tab.dom_holds ht x x').trans ⟨?_, ?_⟩
    · rintro ⟨rfl, y, h⟩; exact ⟨rfl, y, (e y).1 h, (e y).1 h⟩
    · rintro ⟨rfl, y, h, -⟩; exact ⟨rfl, y, (e y).2 h⟩

theorem ran_sound {R : Rel A B} {X : Core.Rel A.El B.El} (hR : ∀ K, R.Reps K X) :
    ∀ K, (GenK.ran A B R).Reps K (𝟙 _ ∩ X° ≫ X°°) :=
  lift1_sound hR fun _ r _ ht hr y y' hy _ => by
    have e : ∀ x, (rep r x y ↔ X x y) := fun x => hr x y rfl hy
    refine (Tab.ran_holds ht y y').trans (Iff.trans ⟨?_, ?_⟩ (ran_iff X y y').symm)
    · rintro ⟨rfl, x, h⟩; exact ⟨rfl, x, (e x).1 h, (e x).1 h⟩
    · rintro ⟨rfl, x, h, -⟩; exact ⟨rfl, x, (e x).2 h⟩

theorem idU_comp_holds {n : USize} {X : Vals A n} {d : Tab A A} {r l : Tab A B} (hd : Tab.idU X = .ok d)
    (hl : d.comp r = .ok l) (x : A.El) (y : B.El) : l.Holds x y ↔ (∃ i, X.row i = x) ∧ r.Holds x y := by
  rw [Tab.comp_holds hl]
  exact ⟨fun ⟨b, h, hr⟩ => by obtain ⟨rfl, hx⟩ := (Tab.idU_holds hd x b).1 h; exact ⟨hx, hr⟩,
    fun ⟨hx, hr⟩ => ⟨x, (Tab.idU_holds hd x x).2 ⟨rfl, hx⟩, hr⟩⟩

theorem comp_idU_holds {m : USize} {L : Vals B m} {d : Tab B B} {l w : Tab A B} (hd : Tab.idU L = .ok d)
    (hw : l.comp d = .ok w) (x : A.El) (y : B.El) : w.Holds x y ↔ l.Holds x y ∧ ∃ j, L.row j = y := by
  rw [Tab.comp_holds hw]
  exact ⟨fun ⟨b, h, h'⟩ => by obtain ⟨rfl, hy⟩ := (Tab.idU_holds hd b y).1 h'; exact ⟨h, hy⟩,
    fun ⟨h, hy⟩ => ⟨y, h, (Tab.idU_holds hd y y).2 ⟨rfl, hy⟩⟩⟩

/-- `cut K r` is `r` on `K`'s sides. -/
theorem cut_agrees {K : Known A B} {r w : Tab A B} (h : cut K r = .ok w) : Agrees K (rep w) (rep r) := by
  obtain ⟨_ | ⟨n, X⟩, _ | ⟨m, L⟩⟩ := K <;> intro x y hx hy
  · obtain rfl := Except.ok.inj (show Except.ok r = .ok w from h); exact Iff.rfl
  · obtain ⟨d, hd, h⟩ := bind_ok (show (Tab.idU L >>= fun d => r.comp d) = .ok w from h)
    exact (comp_idU_holds hd h x y).trans (and_iff_left ((side_some rfl y).1 hy))
  · obtain ⟨d, hd, h⟩ := bind_ok h
    obtain ⟨l, hl, h⟩ := bind_ok h; obtain rfl := Except.ok.inj h
    exact (idU_comp_holds hd hl x y).trans (and_iff_right ((side_some rfl x).1 hx))
  · obtain ⟨d, hd, h⟩ := bind_ok h
    obtain ⟨l, hl, h⟩ := bind_ok h; obtain ⟨d', hd', h⟩ := bind_ok h
    exact (comp_idU_holds hd' h x y).trans ((and_iff_left ((side_some rfl y).1 hy)).trans
      ((idU_comp_holds hd hl x y).trans (and_iff_right ((side_some rfl x).1 hx))))

theorem top_sound {V : Rel B B} {Y : Core.Rel B.El B.El} (hV : ∀ K, V.Reps K Y) :
    ∀ K, (GenK.top A B V).Reps K (Core.Rel.top ≫ Y) := fun K => by
  rw [reps_iff]; intro t h
  cases hK : K.dom with
  | none => simp [GenK.top, Rel.Rel.runE, hK] at h
  | some c =>
    obtain ⟨n, X⟩ := c
    simp only [GenK.top, Rel.Rel.runE, hK] at h
    obtain ⟨v, hv, h⟩ := bind_ok h
    obtain ⟨w, hw, ht⟩ := bind_ok h
    have ev := (reps_iff _ _ _).1 (hV {}) v hv
    have ew := cut_agrees hw
    intro a b ha hb
    refine (Tab.top_val_holds ht a b).trans
      ⟨fun ⟨_, c, _, h⟩ => ⟨c, trivial, ?_⟩, fun ⟨c, _, h⟩ => ⟨(side_some hK a).1 ha, c, trivial, ?_⟩⟩
    · exact (ev c b rfl rfl).1 ((ew c b rfl hb).1 h)
    · exact (ew c b rfl hb).2 ((ev c b rfl rfl).2 h)

/-- The law `Tab.keepBits` lacks: the rows it keeps are `T`'s met with the matrix, which reads as rows wherever the
    result does. -/
def KeepBitsLaw : Prop := ∀ {A C : Obj} {n m : USize} (T : Tab A C) (g w : USize) (o : Enc) (x : Vals A n)
    (ra : Enc) (y : Vals C m) (rc : Enc) (u : Tab A C), Tab.keepBits T g w o x ra y rc = .ok u →
    match Tab.ofBits g w o x ra y rc with | .ok s => rep u = rep T ∩ rep s | .error _ => False

theorem meet_runE {d e : Bool} (R S : Rel A B) (K : Known A B) :
    (GenK.meet A B d e R S).runE K = (meetV (R.force K) (S.force K)).runE K := by
  cases R <;> cases S <;> rfl

theorem inter_case {R S : Rel A B} {K : Known A B} {X Y : Core.Rel A.El B.El} {t : Tab A B}
    (h : (do Tab.inter (← R.runE {}) (← S.runE {})) = .ok t) (eR : ∀ r, R.runE {} = .ok r → Agrees K (rep r) X)
    (eS : ∀ s, S.runE {} = .ok s → Agrees K (rep s) Y) : Agrees K (rep t) (X ∩ Y) := by
  obtain ⟨r, hr, h⟩ := bind_ok h
  obtain ⟨s, hs, ht⟩ := bind_ok h
  exact fun x y hx hy => (Tab.inter_holds ht x y).trans (and_congr (eR r hr x y hx hy) (eS s hs x y hx hy))

theorem keep_case (hk : KeepBitsLaw) {K : Known A B} {P Q : Core.Rel A.El B.El} {n m : USize} {T : Except String (Tab A B)}
    {g w : USize} {o ra rc : Enc} {x : Vals A n} {y : Vals B m} {t : Tab A B}
    (h : (T >>= (Tab.keepBits · g w o x ra y rc)) = .ok t) (eT : ∀ u, T = .ok u → Agrees K (rep u) P)
    (eM : ∀ s, Tab.ofBits g w o x ra y rc = .ok s → Agrees K (rep s) Q) : Agrees K (rep t) (P ∩ Q) := by
  obtain ⟨u, hu, h⟩ := bind_ok h
  have hm := hk u g w o x ra y rc t h
  rcases hs : Tab.ofBits g w o x ra y rc with e | s
  · simp [hs] at hm
  · simp only [hs] at hm; rw [hm]
    exact fun a c ha hc => and_congr (eT u hu a c ha hc) (eM s hs a c ha hc)

theorem meet_sound (hk : KeepBitsLaw) {d e : Bool} {R S : Rel A B} {X Y : Core.Rel A.El B.El}
    (hR : ∀ K, R.Reps K X) (hS : ∀ K, S.Reps K Y) : ∀ K, (GenK.meet A B d e R S).Reps K (X ∩ Y) := fun K => by
  have eR := (reps_iff _ _ _).1 (hR K); have eS := (reps_iff _ _ _).1 (hS K)
  rw [reps_iff, meet_runE]
  have fR := force_runE R K; have fS := force_runE S K
  generalize R.force K = R' at fR; generalize S.force K = S' at fS
  have eR' : ∀ K' r, R'.runE K' = .ok r → Agrees K (rep r) X := fun K' r h => eR r ((fR K').symm.trans h)
  have eS' : ∀ K' s, S'.runE K' = .ok s → Agrees K (rep s) Y := fun K' s h => eS s ((fS K').symm.trans h)
  intro t h
  cases R' <;> cases S' <;> first
    | exact inter_case h (eR' {}) (eS' {})
    | exact keep_case hk h (eR' K) (eS' K)
    | exact fun x y hx hy => (keep_case hk h (eS' K) (eR' K) x y hx hy).trans and_comm

/-- The law `Tab.compTabMat` lacks: the matrix it returns, read as rows, is `r` composed with the matrix it was given,
    which reads as rows wherever the result does. -/
def CompTabMatLaw : Prop := ∀ {A B C : Obj} {n m M : USize} (r : Tab A B) (g w ka : USize) (o o' ra ra' rc : Enc)
    (x : Vals B n) (key : Vals A M) (y : Vals C m) (t : Tab A C),
    Tab.compTabMat r g w o x ra = .ok (ka, o', ⟨M, key⟩, ra') → Tab.ofBits ka w o' key ra' y rc = .ok t →
    match Tab.ofBits g w o x ra y rc with | .ok s => rep t = rep r ≫ rep s | .error _ => False

theorem compR_runE (r : Tab A B) (s : Tab B C) (K : Known A C) :
    (compR r s).runE K = Tab.compSel Tab.bitsMax r s := by
  unfold compR Tab.compSel
  rcases Tab.compSelM Tab.bitsMax r s with e | t | ⟨g, w, o, ra, rc⟩ <;> rfl

theorem compR_sound {r : Tab A B} {s : Tab B C} {K : Known A C} {Z : Core.Rel A.El C.El}
    (H : Agrees K (rep r ≫ rep s) Z) : (compR r s).Reps K Z := by
  rw [reps_iff, compR_runE]; intro t ht x z hx hz
  exact (Tab.compSel_holds ht x z).trans (H x z hx hz)

theorem compV_sound (hm : CompTabMatLaw) {r : Tab A B} {S : Rel B C} {K : Known A C} {Z : Core.Rel A.El C.El}
    (H : ∀ s, S.runE {} = .ok s → Agrees K (rep r ≫ rep s) Z) : (compV r S).Reps K Z := by
  cases S with
  | bits g w o x ra y rc =>
    rcases hc : Tab.compTabMat r g w o x ra with e | ⟨ka, o', ⟨M, key⟩, ra'⟩
    · simp only [compV, hc]; rw [reps_iff]; intro t ht; nomatch ht
    · simp only [compV, hc]
      split
      · rw [reps_iff]; intro t ht
        have hq := hm r g w ka o o' ra ra' rc x key y t hc ht
        rcases hs : Tab.ofBits g w o x ra y rc with e | s
        · simp [hs] at hq
        · simp only [hs] at hq; rw [hq]; exact H s hs
      · rcases hs : Tab.ofBits g w o x ra y rc with e | s
        · rw [reps_iff]; intro t ht; nomatch ht
        · exact compR_sound (H s hs)
  | tab t0 =>
    cases t0 with
    | error e => rw [reps_iff]; intro t ht; nomatch ht
    | ok s => exact compR_sound (H s rfl)
  | lazy f =>
    show (match (Rel.lazy f).runE {} with | .ok s => compR r s | .error e => .tab (.error e)).Reps K Z
    rcases hs : (Rel.lazy f).runE {} with e | s
    · rw [reps_iff]; intro t ht; nomatch ht
    · exact compR_sound (H s hs)

theorem compT_sound (hm : CompTabMatLaw) {r' : Except String (Tab A B)} {S : Rel B C} {K : Known A C}
    {X : Core.Rel A.El B.El} {Y : Core.Rel B.El C.El}
    (hr : ∀ r, r' = .ok r → Agrees ⟨K.dom, none⟩ (rep r) X) (hS : ∀ K, S.Reps K Y) :
    (compT r' S).Reps K (X ≫ Y) := by
  rcases r' with e | r
  · rw [reps_iff]; intro t ht; nomatch ht
  have er := hr r rfl
  cases S with
  | lazy g =>
    simp only [compT]
    split
    · next hn =>
      rw [reps_iff]; intro t ht x z hx _
      refine (Tab.zero_holds ht x z).trans ⟨False.elim, fun ⟨b, h, _⟩ => ?_⟩
      obtain ⟨i, _, _⟩ := (er x b hx rfl).2 h
      have := i.2; simp [beq_iff_eq.1 hn] at this
    · simp only [Rel.Rel.Reps]
      rcases hd : Tab.ran r with e | d
      · rw [reps_iff]; intro t ht; nomatch ht
      refine compV_sound hm fun s hs a c ha hc => exists_congr fun b => ?_
      rw [force_runE] at hs
      have es := (reps_iff _ _ _).1 (hS _) s hs
      have inRan : rep r a b → (⟨some ⟨d.n, d.key⟩, K.ran⟩ : Known B C).den.1 b b := fun h =>
        (side_some rfl b).2 ((keyRowRep d b).2 ⟨b, (Tab.ran_holds hd b b).2 ⟨rfl, a, h⟩⟩)
      have e1 := er a b ha rfl
      exact ⟨fun ⟨h1, h2⟩ => ⟨e1.1 h1, (es b c (inRan h1) hc).1 h2⟩,
        fun ⟨h1, h2⟩ => ⟨e1.2 h1, (es b c (inRan (e1.2 h1)) hc).2 h2⟩⟩
  | tab t0 =>
    exact compV_sound hm fun (s : Tab B C) hs a c ha _ => exists_congr fun b =>
      and_congr (er a b ha rfl) ((reps_iff _ _ _).1 (hS {}) s hs b c rfl rfl)
  | bits g w o x ra y rc =>
    exact compV_sound hm fun (s : Tab B C) hs a c ha _ => exists_congr fun b =>
      and_congr (er a b ha rfl) ((reps_iff _ _ _).1 (hS {}) s hs b c rfl rfl)

theorem compS_sound {R : Rel A B} {s' : Except String (Tab B C)}
    {L : (n : USize) × Vals C n} {X : Core.Rel A.El B.El} {Y : Core.Rel B.El C.El} (hR : ∀ K, R.Reps K X)
    (hs : ∀ s, s' = .ok s → Agrees ⟨none, some L⟩ (rep s) Y) : (compS R s').Reps ⟨none, some L⟩ (X ≫ Y) := by
  rcases s' with e | s
  · rw [reps_iff]; intro t ht; nomatch ht
  have es := hs s rfl
  simp only [compS]
  rcases hr : R.runE ⟨none, some ⟨s.n, s.key⟩⟩ with e | r
  · rw [reps_iff]; intro t ht; nomatch ht
  have er := (reps_iff _ R X).1 (hR _) r hr
  refine compR_sound fun a c _ hc => exists_congr fun b => ?_
  have key : ∀ {b}, rep s b c → (⟨none, some ⟨s.n, s.key⟩⟩ : Known A B).den.2 b b := fun h =>
    (side_some rfl _).2 ((keyRowRep s _).2 ⟨c, h⟩)
  exact ⟨fun ⟨h1, h2⟩ => ⟨(er a b rfl (key h2)).1 h1, (es b c rfl hc).1 h2⟩,
    fun ⟨h1, h2⟩ => have h2' := (es b c rfl hc).2 h2; ⟨(er a b rfl (key h2')).2 h1, h2'⟩⟩

theorem comp_sound (hm : CompTabMatLaw) {e : Bool} {R : Rel A B} {S : Rel B C} {X : Core.Rel A.El B.El}
    {Y : Core.Rel B.El C.El} (hR : ∀ K, R.Reps K X) (hS : ∀ K, S.Reps K Y) :
    ∀ K, (GenK.comp A B C e R S).Reps K (X ≫ Y) := fun K => by
  have eR := fun K => (reps_iff K R X).1 (hR K)
  cases R with
  | tab r => exact compT_sound hm (eR _) hS
  | bits g w o x ra y rc => exact compT_sound hm (fun t h => eR ⟨K.dom, none⟩ t h) hS
  | lazy f =>
    simp only [GenK.comp, Rel.Rel.Reps]
    split
    · split
      · exact compT_sound hm (eR _) hS
      · exact compS_sound (fun K => hR K) ((reps_iff _ _ _).1 (hS _))
    · exact compT_sound hm (eR _) hS

/-! ### Products and sums: `pair prod outl outr junc flat` (`outl outr` by `ofVals_row_sound`) -/

theorem pair_sound {d e : Bool} {R : Rel A B} {S : Rel A C} {X : Core.Rel A.El B.El} {Y : Core.Rel A.El C.El}
    (hR : ∀ K, R.Reps K X) (hS : ∀ K, S.Reps K Y) : ∀ K, (GenK.pair A B C d e R S).Reps K (rpair X Y) :=
  lift2_sound hR hS fun _ _ _ _ ht hr hs a q ha _ =>
    (Tab.pair_holds ht a q).trans (and_congr (hr a q.1 ha rfl) (hs a q.2 ha rfl))

theorem prod_sound {R : Rel A B} {S : Rel C D} {X : Core.Rel A.El B.El} {Y : Core.Rel C.El D.El}
    (hR : ∀ K, R.Reps K X) (hS : ∀ K, S.Reps K Y) : ∀ K, (GenK.prod A B C D R S).Reps K (rprodMap X Y) :=
  lift2_sound hR hS fun _ _ _ _ ht hr hs p q _ _ =>
    (Tab.prod_holds ht p q).trans (and_congr (hr p.1 q.1 rfl rfl) (hs p.2 q.2 rfl rfl))

theorem junc_sound {R : Rel A C} {S : Rel B C} {X : Core.Rel A.El C.El} {Y : Core.Rel B.El C.El}
    (hR : ∀ K, R.Reps K X) (hS : ∀ K, S.Reps K Y) : ∀ K, (GenK.junc A B C R S).Reps K (Core.Rel.junc X Y) :=
  lift2_sound hR hS fun _ _ _ _ ht hr hs x c _ _ => by
    rw [agrees_empty hr, agrees_empty hs]; exact Tab.junc_holds ht x c

theorem flat_sound {I : Obj} {d : Bool} {R : Rel I (.prod A B)} {X : Core.Rel I.El (Obj.prod A B).El}
    (hR : ∀ K, R.Reps K X) : ∀ K, (GenK.flat I A B d R).Reps K (flatDen X) :=
  ofVals_sound fun _ _ Xs _ hK h p b hp _ => by
    obtain ⟨r, hr, ht⟩ := bind_ok h
    have er := (reps_iff _ _ _).1 (hR _) r hr
    obtain ⟨i, rfl⟩ := (side_some hK p).1 hp
    exact (Tab.flat_holds ht _ b).trans ((and_iff_right ⟨i, rfl⟩).trans (er _ _ ((side_some rfl _).2 ⟨i, rfl⟩) rfl))

example : ∀ K, (GenK.outl A B).Reps K (graph Prod.fst) := ofVals_row_sound fun _ _ _ h => Tab.outl_holds h
example : ∀ K, (GenK.outr A B).Reps K (graph Prod.snd) := ofVals_row_sound fun _ _ _ h => Tab.outr_holds h

/-! ### `diff ldiv rdiv lam nil succ leq lt` (`nil` by `ofVals_row_sound`, `leq lt` by `cmp_sound`) -/

theorem diff_sound {d e : Bool} {R S : Rel A B} {X Y : Core.Rel A.El B.El} (hR : ∀ K, R.Reps K X)
    (hS : ∀ K, S.Reps K Y) : ∀ K, (GenK.diff A B d e R S).Reps K (diffDen X Y) :=
  lift2_sound hR hS fun _ _ _ _ ht hr hs x y hx hy =>
    (Tab.diff_holds ht x y).trans (and_congr (hr x y hx hy) (not_congr (hs x y hx hy)))

theorem ldiv_sound {R : Rel A B} {S : Rel A C} {UB : Rel B B} {UC : Rel C C} {X : Core.Rel A.El B.El}
    {Y : Core.Rel A.El C.El} {TB : Core.Rel B.El B.El} {TC : Core.Rel C.El C.El} (hR : ∀ K, R.Reps K X)
    (hS : ∀ K, S.Reps K Y) (hB : ∀ K, UB.Reps K TB) (hC : ∀ K, UC.Reps K TC) :
    ∀ K, (GenK.ldiv A B C R S UB UC).Reps K (ldivDen X Y TB TC) :=
  lift2_sound hR hS fun _ _ _ _ ht hr hs => by
    obtain ⟨ub, hub, ht⟩ := bind_ok ht
    obtain ⟨uc, huc, ht⟩ := bind_ok ht
    rw [agrees_empty hr, agrees_empty hs, agrees_empty ((reps_iff _ _ _).1 (hB {}) ub hub),
      agrees_empty ((reps_iff _ _ _).1 (hC {}) uc huc)]
    exact fun b c _ _ => Tab.ldivSel_holds ht b c

theorem rdiv_sound {R : Rel A C} {S : Rel B C} {UA : Rel A A} {UB : Rel B B} {X : Core.Rel A.El C.El}
    {Y : Core.Rel B.El C.El} {TA : Core.Rel A.El A.El} {TB : Core.Rel B.El B.El} (hR : ∀ K, R.Reps K X)
    (hS : ∀ K, S.Reps K Y) (hA : ∀ K, UA.Reps K TA) (hB : ∀ K, UB.Reps K TB) :
    ∀ K, (GenK.rdiv A B C R S UA UB).Reps K (rdivDen X Y TA TB) :=
  lift2_sound hR hS fun _ r s _ ht hr hs => by
    obtain ⟨sc, hsc, ht⟩ := bind_ok ht
    obtain ⟨rc, hrc, ht⟩ := bind_ok ht
    obtain ⟨ub, hub, ht⟩ := bind_ok ht
    obtain ⟨ua, hua, ht⟩ := bind_ok ht
    obtain ⟨q, hq, ht⟩ := bind_ok ht
    rw [agrees_empty hr, agrees_empty hs, agrees_empty ((reps_iff _ _ _).1 (hA {}) ua hua),
      agrees_empty ((reps_iff _ _ _).1 (hB {}) ub hub)]
    intro x y _ _
    refine (Tab.conv_holds ht x y).trans ((Tab.ldivSel_holds hq y x).trans ?_)
    simp only [ldivDen, rdivDen, rep_apply, Tab.conv_holds hsc, Tab.conv_holds hrc]
    exact and_congr Iff.rfl (or_congr Iff.rfl and_comm)

theorem lam_sound {d : Bool} {R : Rel A B} {X : Core.Rel A.El B.El} (hR : ∀ K, R.Reps K X)
    (hB : ∀ (m : USize) (x : Vals (.prod A B) m) es, Vals.cols x = .ok es → ∀ i i' : Fin m.toNat,
      (x.row i).1 = (x.row i').1 → lexLe (ascKeys m es) i i' = true → seenKey m es i ≠ seenKey m es i' →
        B.lt (x.row i).2 (x.row i').2) :
    ∀ K, (GenK.lam A B d R).Reps K (lamDen X) :=
  ofVals_sound fun _ _ _ _ hK h a ys ha _ => by
    obtain ⟨r, hr, ht⟩ := bind_ok h
    have er := (reps_iff _ _ _).1 (hR _) r hr
    have ha' := (side_some hK a).1 ha
    exact (Tab.lam_den ht hB a ys).trans ((and_iff_right ha').trans (and_congr Iff.rfl
      (forall_congr' fun b => iff_congr Iff.rfl (er a b ((side_some rfl a).2 ha') rfl))))

example : ∀ K, (GenK.nil A B).Reps K nilDen := ofVals_row_sound fun _ _ _ h => Tab.nil_holds h

theorem succ_sound {U : Rel .long .long} {TU : Core.Rel Int64 Int64} (hU : ∀ K, U.Reps K TU) :
    ∀ K, (GenK.succ U).Reps K (succDen TU) := by
  unfold GenK.succ after
  exact ofVals_sound fun _ _ _ _ hK h x w hx _ => by
    obtain ⟨D, hD, h⟩ := bind_ok h
    obtain ⟨u, hu, ht⟩ := bind_ok h
    rw [agrees_empty ((reps_iff _ _ _).1 (hU {}) u hu)]
    refine (Tab.succ_holds ht x w).trans
      ⟨fun ⟨v, hv, h⟩ => ?_, fun h => ⟨x, (Tab.idU_holds hD x x).2 ⟨rfl, (side_some hK x).1 hx⟩, h⟩⟩
    obtain ⟨rfl, -⟩ := (Tab.idU_holds hD x v).1 hv; exact h

theorem cmp_side {u d : Tab .long .long} (hd : u.dom = .ok d) {o : Option ((n : USize) × Vals .long n)}
    {k : (n : USize) × Vals .long n}
    (h : (o.elim (pure ⟨d.n, d.key⟩) (fun c => do let t ← (← Tab.idU c.2).comp d; pure ⟨t.n, t.key⟩) :
      Except String ((n : USize) × Vals .long n)) = .ok k)
    {a : Int64} (ha : o.elim (𝟙 _) (fun c => (graph c.2.row)° ≫ graph c.2.row) a a) :
    (∃ i, k.2.row i = a) ↔ ∃ v, rep u a v := by
  have key : (∃ i, d.key.row i = a) ↔ ∃ v, rep u a v := by
    rw [keyRowRep]
    exact ⟨fun ⟨_, h⟩ => ((Tab.dom_holds hd _ _).1 h).2, fun ⟨v, h⟩ => ⟨a, (Tab.dom_holds hd a a).2 ⟨rfl, v, h⟩⟩⟩
  cases o with
  | none => obtain rfl := Except.ok.inj h; exact key
  | some c =>
    obtain ⟨n, X⟩ := c
    obtain ⟨e, he, h⟩ := bind_ok h
    obtain ⟨t, ht, h⟩ := bind_ok h
    obtain rfl := Except.ok.inj h
    exact (keyRowRep t a).trans ((exists_congr fun b => (idU_comp_holds he ht a b).trans
      (and_iff_right ((side_some (C := .long) rfl a).1 ha))).trans ((keyRowRep d a).symm.trans key))

/-- `cmp f U` is `f`'s relation on `U`'s domain, where `f`'s law is "a key of the first side, a key of the second,
    related by `P`": `leq` (`Tab.leq_holds`) and `lt` (`Tab.lt_holds`), whose right-hand sides are `leqDen`, `ltDen`. -/
theorem cmp_sound {f : {n m : USize} → Vals .long n → Vals .long m → Except String (Tab .long .long)}
    {P : Int64 → Int64 → Prop}
    (hf : ∀ {n m : USize} (k : Vals .long n) (l : Vals .long m) t, f k l = .ok t →
      ∀ a c, t.Holds a c ↔ (∃ i, k.row i = a) ∧ (∃ j, l.row j = c) ∧ P a c)
    {U : Rel .long .long} {TU : Core.Rel Int64 Int64} (hU : ∀ K, U.Reps K TU) :
    ∀ K, (GenK.cmp f U).Reps K (fun a b => (∃ v, TU a v) ∧ (∃ v, TU b v) ∧ P a b) := fun K => by
  rw [reps_iff]; intro t h
  obtain ⟨u, hu, h⟩ := bind_ok h
  obtain ⟨d, hd, h⟩ := bind_ok h
  obtain ⟨k, hk, h⟩ := bind_ok h
  obtain ⟨l, hl, ht⟩ := bind_ok h
  rw [agrees_empty ((reps_iff _ _ _).1 (hU {}) u hu)]
  exact fun a c ha hc => (hf _ _ t ht a c).trans (and_congr (cmp_side hd hk ha) (and_congr (cmp_side hd hl hc) Iff.rfl))

example {U : Rel .long .long} {TU : Core.Rel Int64 Int64} (hU : ∀ K, U.Reps K TU) :
    ∀ K, (GenK.leq U).Reps K (leqDen TU) := cmp_sound (fun _ _ _ h => Tab.leq_holds h) hU
example {U : Rel .long .long} {TU : Core.Rel Int64 Int64} (hU : ∀ K, U.Reps K TU) :
    ∀ K, (GenK.lt U).Reps K (ltDen TU) := cmp_sound (fun _ _ _ h => Tab.lt_holds h) hU

/-! ### The rows with a law, under `ofVals` (the wrapper `Expand.primE` fits a row on values alone to) -/

example : ∀ K, (ofVals (.arr A) A fun X => Tab.mem X).Reps K (fun xs b => b ∈ xs) :=
  ofVals_row_sound fun _ _ _ h => Tab.mem_holds h
example : ∀ K, (ofVals A (.sum A B) fun X => Tab.inl X).Reps K Core.Rel.inl :=
  ofVals_row_sound fun _ _ _ h => Tab.inl_holds h
example : ∀ K, (ofVals B (.sum A B) fun X => Tab.inr X).Reps K Core.Rel.inr :=
  ofVals_row_sound fun _ _ _ h => Tab.inr_holds h
example (hB : ∀ (m : USize) (x : Vals (.prod A A) m) es, Vals.cols x = .ok es → ∀ i i' : Fin m.toNat,
      (x.row i).1 = (x.row i').1 → lexLe (ascKeys m es) i i' = true → seenKey m es i ≠ seenKey m es i' →
        A.lt (x.row i).2 (x.row i').2) :
    ∀ K, (ofVals A (.arr A) fun X => Tab.tau X).Reps K (fun a ys => ys = [a]) :=
  ofVals_row_sound fun _ _ _ h => Tab.tau_den h hB
example (hB : ∀ (m : USize) (x : Vals (.prod (.arr B) B) m) es, Vals.cols x = .ok es → ∀ i i' : Fin m.toNat,
      (x.row i).1 = (x.row i').1 → lexLe (ascKeys m es) i i' = true → seenKey m es i ≠ seenKey m es i' →
        B.lt (x.row i).2 (x.row i').2) :
    ∀ K, (ofVals (.arr B) (.arr B) fun X => Tab.setify X).Reps K (lamDen fun xs b => b ∈ xs) :=
  ofVals_row_sound fun _ _ _ h => Tab.setify_den h hB

end GenK

end Rel.Lang
