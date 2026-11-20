import Rel.Run.Lang.GenK
import Rel.RepBits
import Rel.RepTabArith

/-! Each `GenK` op whose `Tab` law exists represents its constructor's case of `Tm.den`: given parts that represent
    their meanings in every context, the op represents the right-hand side `Tm.den` gives that constructor, in every
    context. Everything goes through `reps_iff`, which reads `Reps` off `runE`, so an op's lemma is about the table it
    computes. The two ops that read a bit matrix (`comp`, `meet`) are in `GenKBits`, beside the laws they read it by. -/

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

/-- A value both sides of `K` admit is admitted by whichever side is known first (`GenK.dom`, `GenK.ran`). -/
theorem side_or {K : Known A A} {x : A.El} (h₁ : K.den.1 x x) (h₂ : K.den.2 x x) :
    (K.dom <|> K.ran).elim (𝟙 _) (fun c => (graph c.2.row)° ≫ graph c.2.row) x x := by
  obtain ⟨_ | _, _⟩ := K
  · exact h₂
  · exact h₁

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
  lift1_sound hR fun _ r _ ht hr x x' hx hx' => by
    refine (Tab.dom_holds ht x x').trans ⟨?_, ?_⟩
    · rintro ⟨rfl, y, h⟩; have e := hr _ y (side_or hx hx') rfl; exact ⟨rfl, y, e.1 h, e.1 h⟩
    · rintro ⟨rfl, y, h, -⟩; exact ⟨rfl, y, (hr _ y (side_or hx hx') rfl).2 h⟩

theorem ran_sound {R : Rel A B} {X : Core.Rel A.El B.El} (hR : ∀ K, R.Reps K X) :
    ∀ K, (GenK.ran A B R).Reps K (𝟙 _ ∩ X° ≫ X°°) :=
  lift1_sound hR fun _ r _ ht hr y y' hy hy' => by
    refine (Tab.ran_holds ht y y').trans (Iff.trans ⟨?_, ?_⟩ (ran_iff X y y').symm)
    · rintro ⟨rfl, x, h⟩; have e := hr x _ rfl (side_or hy hy'); exact ⟨rfl, x, e.1 h, e.1 h⟩
    · rintro ⟨rfl, x, h, -⟩; exact ⟨rfl, x, (hr x _ rfl (side_or hy hy')).2 h⟩

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

/-- `bound K r` is `r` on `K`'s sides, and every pair of it lies inside the context it hands the other operand. -/
theorem bound_spec {K : Known A B} {r : Tab A B} {p : Tab A B × Known A B} (h : bound K r = .ok p) :
    Agrees K (rep p.1) (rep r) ∧ ∀ x y, rep p.1 x y → p.2.den.1 x x ∧ p.2.den.2 y y := by
  obtain ⟨t, ht, h⟩ := bind_ok h
  obtain ⟨d, hd, h⟩ := bind_ok h
  obtain ⟨l, hl, h⟩ := bind_ok h
  obtain rfl := Except.ok.inj h
  exact ⟨cut_agrees ht, fun x y hxy => ⟨(side_some rfl x).2 ((keyRowRep d x).2 ⟨x, (Tab.dom_holds hd x x).2 ⟨rfl, y, hxy⟩⟩),
    (side_some rfl y).2 ((keyRowRep l y).2 ⟨y, (Tab.ran_holds hl y y).2 ⟨rfl, x, hxy⟩⟩)⟩⟩

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

/-! ### Products and sums: `pair prod outl outr junc flat` (`outl outr` by `ofVals_row_sound`) -/

theorem pair_sound {d e : Bool} {R : Rel A B} {S : Rel A C} {X : Core.Rel A.El B.El} {Y : Core.Rel A.El C.El}
    (hR : ∀ K, R.Reps K X) (hS : ∀ K, S.Reps K Y) : ∀ K, (GenK.pair A B C d e R S).Reps K (rpair X Y) :=
  lift2_sound hR hS fun _ _ _ _ ht hr hs a q ha _ =>
    (Tab.pair_holds ht a q).trans (and_congr (hr a q.1 ha rfl) (hs a q.2 ha rfl))

/-- `o ≫ r` on the pairs `Z`, `o` a projection `f` on `Z` (`Tab.outl`, `Tab.outr`): each pair to what `r` relates
    its `f`-side to. -/
theorem proj_comp_holds {P : Obj} {n : USize} {Z : Vals (.prod A C) n} {f : (Obj.prod A C).El → P.El}
    {o : Tab (.prod A C) P} {r : Tab P B} {l : Tab (.prod A C) B} {X : Core.Rel P.El B.El}
    (ho : ∀ p a, o.Holds p a ↔ (∃ i, Z.row i = p) ∧ graph f p a) (hl : o.comp r = .ok l)
    (er : ∀ i b, r.Holds (f (Z.row i)) b ↔ X (f (Z.row i)) b) (i : Fin n.toNat) (b : B.El) :
    l.Holds (Z.row i) b ↔ X (f (Z.row i)) b :=
  (Tab.comp_holds hl _ _).trans ⟨fun ⟨_, h1, h2⟩ => by obtain ⟨-, rfl⟩ := (ho _ _).1 h1; exact (er i b).1 h2,
    fun h => ⟨_, (ho _ _).2 ⟨⟨i, rfl⟩, rfl⟩, (er i b).2 h⟩⟩

theorem prod_sound {R : Rel A B} {S : Rel C D} {X : Core.Rel A.El B.El} {Y : Core.Rel C.El D.El}
    (hR : ∀ K, R.Reps K X) (hS : ∀ K, S.Reps K Y) : ∀ K, (GenK.prod A B C D R S).Reps K (rprodMap X Y) := fun K => by
  rw [reps_iff]; intro t h
  cases hK : K.dom with
  | none =>
    simp only [GenK.prod, Rel.Rel.runE, hK] at h
    obtain ⟨r, hr, h⟩ := bind_ok h
    obtain ⟨s, hs, ht⟩ := bind_ok h
    have er := (reps_iff _ _ _).1 (hR {}) r hr; have es := (reps_iff _ _ _).1 (hS {}) s hs
    exact fun p q _ _ => (Tab.prod_holds ht p q).trans (and_congr (er p.1 q.1 rfl rfl) (es p.2 q.2 rfl rfl))
  | some c =>
    obtain ⟨n, Z⟩ := c
    simp only [GenK.prod, Rel.Rel.runE, hK] at h
    obtain ⟨o₁, ho₁, h⟩ := bind_ok h
    obtain ⟨r, hr, h⟩ := bind_ok h
    obtain ⟨l, hl, h⟩ := bind_ok h
    obtain ⟨o₂, ho₂, h⟩ := bind_ok h
    obtain ⟨s, hs, h⟩ := bind_ok h
    obtain ⟨m, hm, ht⟩ := bind_ok h
    have er := (reps_iff _ _ _).1 (hR _) r hr
    have es := (reps_iff _ _ _).1 (hS _) s hs
    intro p q hp _
    obtain ⟨i, rfl⟩ := (side_some hK p).1 hp
    exact (Tab.pair_holds ht _ q).trans (and_congr
      (proj_comp_holds (Tab.outl_holds ho₁) hl (fun j b => er _ b ((side_some rfl _).2 ⟨j, rfl⟩) rfl) i q.1)
      (proj_comp_holds (Tab.outr_holds ho₂) hm (fun j d => es _ d ((side_some rfl _).2 ⟨j, rfl⟩) rfl) i q.2))

theorem flat_sound {I : Obj} {d : Bool} {R : Rel I (.prod A B)} {X : Core.Rel I.El (Obj.prod A B).El}
    (hR : ∀ K, R.Reps K X) : ∀ K, (GenK.flat I A B d R).Reps K (flatDen X) :=
  ofVals_sound fun _ _ Xs _ hK h p b hp _ => by
    obtain ⟨r, hr, ht⟩ := bind_ok h
    have er := (reps_iff _ _ _).1 (hR _) r hr
    obtain ⟨i, rfl⟩ := (side_some hK p).1 hp
    exact (Tab.flat_holds ht _ b).trans ((and_iff_right ⟨i, rfl⟩).trans (er _ _ ((side_some rfl _).2 ⟨i, rfl⟩) rfl))

example : ∀ K, (GenK.outl A B).Reps K (graph Prod.fst) := ofVals_row_sound fun _ _ _ h => Tab.outl_holds h
example : ∀ K, (GenK.outr A B).Reps K (graph Prod.snd) := ofVals_row_sound fun _ _ _ h => Tab.outr_holds h

/-! ### `diff rdiv lam nil succ leq lt` (`nil` by `ofVals_row_sound`, `leq lt` by `cmp_sound`) -/

theorem diff_sound {d e : Bool} {R S : Rel A B} {X Y : Core.Rel A.El B.El} (hR : ∀ K, R.Reps K X)
    (hS : ∀ K, S.Reps K Y) : ∀ K, (GenK.diff A B d e R S).Reps K (diffDen X Y) := by
  unfold GenK.diff; split
  · intro K; rw [reps_iff]; intro t h
    obtain ⟨r, hr, h⟩ := bind_ok h
    obtain ⟨p, hp, h⟩ := bind_ok h
    obtain ⟨s, hs, ht⟩ := bind_ok h
    obtain ⟨hu, hK⟩ := bound_spec hp
    have er := (reps_iff _ _ _).1 (hR K) r hr
    have es := (reps_iff _ _ _).1 (hS p.2) s hs
    intro x y hx hy
    refine (Tab.diff_holds ht x y).trans ⟨fun ⟨a, b⟩ => ⟨(er x y hx hy).1 ((hu x y hx hy).1 a),
      fun q => b ((es x y (hK x y a).1 (hK x y a).2).2 q)⟩, fun ⟨a, b⟩ => ?_⟩
    have a' := (hu x y hx hy).2 ((er x y hx hy).2 a)
    exact ⟨a', fun q => b ((es x y (hK x y a').1 (hK x y a').2).1 q)⟩
  · exact lift2_sound hR hS fun _ _ _ _ ht hr hs x y hx hy =>
      (Tab.diff_holds ht x y).trans (and_congr (hr x y hx hy) (not_congr (hs x y hx hy)))

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
    obtain ⟨D, hD, ht⟩ := bind_ok h
    have hu : ∀ n (X : Vals .long n) t, U.runE ⟨some ⟨n, X⟩, none⟩ = .ok t → ∀ a v, (∃ i, X.row i = a) →
        (t.Holds a v ↔ TU a v) := fun n X t h a v ha =>
      (reps_iff _ _ _).1 (hU ⟨some ⟨n, X⟩, none⟩) t h a v ((side_some rfl a).2 ha) rfl
    refine (Tab.succ_holds hu ht x w).trans
      ⟨fun ⟨v, hv, h⟩ => ?_, fun h => ⟨x, (Tab.idU_holds hD x x).2 ⟨rfl, (side_some hK x).1 hx⟩, h⟩⟩
    obtain ⟨rfl, -⟩ := (Tab.idU_holds hD x v).1 hv; exact h

theorem cmp_side {op w : String} {U : Rel .long .long} {TU : Core.Rel Int64 Int64} (hU : ∀ K, U.Reps K TU)
    {o : Option ((n : USize) × Vals .long n)} {k : (n : USize) × Vals .long n} (h : GenK.cmpSide op w U o = .ok k)
    {a : Int64} (ha : o.elim (𝟙 _) (fun c => (graph c.2.row)° ≫ graph c.2.row) a a) :
    (∃ i, k.2.row i = a) ↔ ∃ v, TU a v := by
  obtain ⟨u, hu', h⟩ := bind_ok h
  have hu : U.runE ⟨o, none⟩ = .ok u := by
    cases e : U.runE ⟨o, none⟩ <;> rw [e] at hu' <;> cases hu' <;> rfl
  obtain ⟨d, hd, h⟩ := bind_ok h
  have agr := (reps_iff _ _ _).1 (hU ⟨o, none⟩) u hu a
  have key : (∃ i, d.key.row i = a) ↔ ∃ v, TU a v := by
    rw [keyRowRep]
    exact ⟨fun ⟨_, h⟩ => let ⟨_, v, hv⟩ := (Tab.dom_holds hd _ _).1 h; ⟨v, (agr v ha rfl).1 hv⟩,
      fun ⟨v, h⟩ => ⟨a, (Tab.dom_holds hd a a).2 ⟨rfl, v, (agr v ha rfl).2 h⟩⟩⟩
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
theorem cmp_sound {op : String} {f : {n m : USize} → Vals .long n → Vals .long m → Except String (Tab .long .long)}
    {P : Int64 → Int64 → Prop}
    (hf : ∀ {n m : USize} (k : Vals .long n) (l : Vals .long m) t, f k l = .ok t →
      ∀ a c, t.Holds a c ↔ (∃ i, k.row i = a) ∧ (∃ j, l.row j = c) ∧ P a c)
    {U : Rel .long .long} {TU : Core.Rel Int64 Int64} (hU : ∀ K, U.Reps K TU) :
    ∀ K, (GenK.cmp op f U).Reps K (fun a b => (∃ v, TU a v) ∧ (∃ v, TU b v) ∧ P a b) := fun K => by
  rw [reps_iff]; intro t h
  obtain ⟨k, hk, h⟩ := bind_ok h
  obtain ⟨l, hl, ht⟩ := bind_ok h
  exact fun a c ha hc =>
    (hf _ _ t ht a c).trans (and_congr (cmp_side hU hk ha) (and_congr (cmp_side hU hl hc) Iff.rfl))

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
