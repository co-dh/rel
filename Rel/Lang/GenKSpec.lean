module

public import Rel.Run.Lang.GenK
public import Rel.RepBits
public import Rel.RepTabArith
public import Rel.RepWFOps

-- exposed: every def body is a spec a downstream `rfl`/`decide`/`simp` may unfold (PLAN W.8)
@[expose] public section

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

/-- What a context knows is `WF`: each known side `Vals.WF`, its pairs `Tab.WF`. A `lazy` value is run on no other
    (`Rel.Wf`), so `Reps` is asked only there (PLAN 8.5). -/
def _root_.Rel.Known.WF (K : Known A B) : Prop :=
  K.dom.elim True (fun c => Vals.WF c.2) ∧ K.ran.elim True (fun c => Vals.WF c.2) ∧ K.pairs.elim True Tab.WF

theorem _root_.Rel.Known.wf_empty : ({} : Known A B).WF := ⟨trivial, trivial, trivial⟩

/-- A context that knows only `K`'s domain is `WF` where `K` is. -/
theorem _root_.Rel.Known.WF.dom {K : Known A B} {C : Obj} (h : K.WF) : (⟨K.dom, none, none⟩ : Known A C).WF :=
  ⟨h.1, trivial, trivial⟩

/-- `R°`'s context, `K` with its sides and pairs turned over, is `WF` where `K` is (`GenK.conv`). -/
theorem _root_.Rel.Known.WF.conv {K : Known A B} (h : K.WF) :
    (⟨K.ran, K.dom, K.pairs.map fun p => ⟨p.n, p.val, p.key⟩⟩ : Known B A).WF :=
  ⟨h.2.1, h.1, by obtain ⟨_, _, _ | p⟩ := K; trivial; exact ⟨h.2.2.2, h.2.2.1⟩⟩

/-- Either known side of `K` (`dom`, `ran`, `id` read one value set) is `Vals.WF` where `K` is. -/
theorem _root_.Rel.Known.WF.side {K : Known A A} (h : K.WF) : (K.dom <|> K.ran).elim True fun c => Vals.WF c.2 := by
  obtain ⟨_ | _, _, _⟩ := K; exact h.2.1; exact h.1
open Rel.Ext Ext.Enc in
/-- **A bit matrix as its producers (`compMat`, `compTabMat`) build it**: it reads back as rows (`Tab.ofBits`), `g · w`
    does not wrap, each of its `g · w` words is `0` or `1`, and each side's rows `x[ra[·]]`, `y[rc[·]]` are distinct:
    the hypotheses of `Tab.keepBits_law` and `Tab.compTabMat_law`. -/
def _root_.Rel.BitsWf {n m : USize} (g w : USize) (o : Enc) (x : Vals A n) (ra : Enc) (y : Vals C m) (rc : Enc) : Prop :=
  (∀ e, Tab.ofBits g w o x ra y rc ≠ .error e) ∧ (g * w).toNat = g.toNat * w.toNat ∧
  (∀ a < g.toNat, ∀ j < w.toNat, ((raw .i64 (g * w) o)[a * w.toNat + j]?).any (· < 2) = true) ∧
  (∀ a a' : Fin g.toNat, ∀ i i' : Fin n.toNat, ((raw .i64 g ra)[a.1]?.getD 0).toNat = i.1 →
    ((raw .i64 g ra)[a'.1]?.getD 0).toNat = i'.1 → x.row i = x.row i' → a = a') ∧
  (∀ c c' : Fin w.toNat, ∀ i i' : Fin m.toNat, ((raw .i64 w rc)[c.1]?.getD 0).toNat = i.1 →
    ((raw .i64 w rc)[c'.1]?.getD 0).toNat = i'.1 → y.row i = y.row i' → c = c') ∧
  hasNul ra = false ∧ hasNul rc = false ∧ hasNul o = false

/-- **`r` yields only `Tab.WF` tables**: a table is `WF`, a `lazy` value is on every `WF` context (`force`), and a
    `bits` value is `BitsWf` over `WF` sides, so it reads back `WF` (`Tab.ofBits_wf`). -/
def _root_.Rel.Rel.Wf {A B : Obj} : Rel A B → Prop
  | .tab (.ok t) => t.WF
  | .tab (.error _) => True
  | .lazy f => ∀ K, K.WF → (f K).Wf
  | .bits g w o x ra y rc => BitsWf g w o x ra y rc ∧ Vals.WF x ∧ Vals.WF y

theorem _root_.Rel.Rel.Wf.force {r : Rel A B} (h : r.Wf) {K : Known A B} (hK : K.WF) : (r.force K).Wf := by
  induction r with
  | lazy f ih => simp only [Rel.force]; exact ih K (h K hK)
  | tab => exact h
  | bits => exact h

theorem _root_.Rel.Rel.Wf.retried {r : Rel A B} (h : r.Wf) (e : String) : (r.retried e).Wf := by
  induction r with
  | lazy f ih => exact fun K hK => ih K (h K hK)
  | tab t => cases t <;> first | trivial | exact h
  | bits => exact h

theorem _root_.Rel.Rel.Wf.runE {r : Rel A B} (h : r.Wf) {K : Known A B} (hK : K.WF) {t : Tab A B} (ht : r.runE K = .ok t) :
    t.WF := by
  induction r with
  | lazy f ih => exact ih K (h K hK) ht
  | tab t' => cases ht; exact h
  | bits => exact Tab.ofBits_wf ht h.2.1 h.2.2


/-! ### Reading `Reps` off `runE` -/

/-- `P` and `Q` agree at every pair `K` admits: its two values inside `K`'s sides, the pair one of `K`'s pairs. -/
def Agrees (K : Known A B) (P Q : Core.Rel A.El B.El) : Prop :=
  ∀ x y, K.den.1 x x → K.den.2 y y → K.on x y → (P x y ↔ Q x y)

/-- In the empty context agreeing is being equal. -/
theorem agrees_empty {P Q : Core.Rel A.El B.El} (h : Agrees {} P Q) : Q = P :=
  Core.Rel.ext fun a b => (h a b rfl rfl trivial).symm

/-- `R°` reads `R` on the converse pairs (`GenK.conv`'s context). -/
theorem on_conv {K : Known A B} {x : A.El} {y : B.El} (h : K.on x y) :
    (⟨K.ran, K.dom, K.pairs.map fun p => ⟨p.n, p.val, p.key⟩⟩ : Known B A).on y x := by
  obtain ⟨_, _, _ | p⟩ := K
  · trivial
  · obtain ⟨i, h1, h2⟩ := h; exact ⟨i, h2, h1⟩

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
  | tab t => cases t <;> simp [Rel.Rel.Reps, Rel.Rel.runE, Agrees]
  | lazy f ih => simp only [Rel.Rel.Reps, Rel.Rel.runE]; exact ih K
  | bits g w o x ra y rc => simp only [Rel.Rel.Reps, Rel.Rel.runE]; split <;> simp_all [Agrees]

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

theorem retryE_ok {α : Type} {e : String} {t : Except String α} {x : α} (h : retryE e t = .ok x) : t = .ok x := by
  cases t with
  | error => nomatch h
  | ok => exact h

/-- A retried value computes what `r` computes, only its message changed. -/
theorem retried_ok {e : String} {r : Rel A B} {K : Known A B} {t : Tab A B} (h : (r.retried e).runE K = .ok t) :
    r.runE K = .ok t := by
  induction r with
  | tab t0 => exact retryE_ok h
  | lazy f ih => exact ih K h
  | bits => exact h

theorem retried_reps {e : String} {r : Rel A B} {K : Known A B} {X : Core.Rel A.El B.El} (h : r.Reps K X) :
    (r.retried e).Reps K X :=
  (reps_iff _ _ _).2 fun t ht => (reps_iff _ _ _).1 h t (retried_ok ht)

/-! ### The lifting: an op on tables (`lift1`, `lift2`, `ofVals`) is sound where its table step is -/

theorem lift1_runE (f : Tab A B → Except String (Tab C D)) (k : Known C D → Known A B) (R : Rel A B)
    (K : Known C D) : (lift1 f k R).runE K = R.runE (k K) >>= f := by cases R <;> rfl

theorem lift2_runE {E F : Obj} (f : Tab A B → Tab C D → Except String (Tab E F)) (kl : Known E F → Known A B)
    (kr : Known E F → Known C D) (R : Rel A B) (S : Rel C D) (K : Known E F) :
    (lift2 f kl kr R S).runE K = (R.runE (kl K) >>= fun r => S.runE (kr K) >>= f r) := by
  cases R <;> cases S <;> rfl

theorem lift1_sound {f : Tab A B → Except String (Tab C D)} {k : Known C D → Known A B} {R : Rel A B}
    {X : Core.Rel A.El B.El} {Y : Core.Rel C.El D.El} (hk : ∀ K, K.WF → (k K).WF) (hR : ∀ K, K.WF → R.Reps K X)
    (wR : R.Wf) (hf : ∀ K r t, f r = .ok t → r.WF → Agrees (k K) (rep r) X → Agrees K (rep t) Y) (K : Known C D)
    (hK : K.WF) : (lift1 f k R).Reps K Y := by
  rw [reps_iff, lift1_runE]; intro t h
  obtain ⟨r, hr, ht⟩ := bind_ok h
  exact hf K r t ht (wR.runE (hk K hK) hr) ((reps_iff _ _ _).1 (hR _ (hk K hK)) r hr)

theorem lift2_sound {E F : Obj} {f : Tab A B → Tab C D → Except String (Tab E F)} {kl : Known E F → Known A B}
    {kr : Known E F → Known C D} {R : Rel A B} {S : Rel C D} {X : Core.Rel A.El B.El} {Y : Core.Rel C.El D.El}
    {Z : Core.Rel E.El F.El} (hkl : ∀ K, K.WF → (kl K).WF) (hkr : ∀ K, K.WF → (kr K).WF)
    (hR : ∀ K, K.WF → R.Reps K X) (hS : ∀ K, K.WF → S.Reps K Y) (wR : R.Wf) (wS : S.Wf)
    (hf : ∀ K r s t, f r s = .ok t → r.WF → s.WF → Agrees (kl K) (rep r) X → Agrees (kr K) (rep s) Y →
      Agrees K (rep t) Z)
    (K : Known E F) (hK : K.WF) : (lift2 f kl kr R S).Reps K Z := by
  rw [reps_iff, lift2_runE]; intro t h
  obtain ⟨r, hr, h⟩ := bind_ok h
  obtain ⟨s, hs, ht⟩ := bind_ok h
  exact hf K r s t ht (wR.runE (hkl K hK) hr) (wS.runE (hkr K hK) hs) ((reps_iff _ _ _).1 (hR _ (hkl K hK)) r hr)
    ((reps_iff _ _ _).1 (hS _ (hkr K hK)) s hs)

theorem ofVals_sound {f : {n : USize} → Vals A n → Except String (Tab A B)} {Y : Core.Rel A.El B.El}
    (hf : ∀ K n (X : Vals A n) t, K.dom = some ⟨n, X⟩ → Vals.WF X → f X = .ok t → Agrees K (rep t) Y) (K : Known A B)
    (hW : K.WF) : (ofVals A B f).Reps K Y := by
  rw [reps_iff]; intro t h
  cases hK : K.dom with
  | none => simp [ofVals, Rel.Rel.runE, hK] at h
  | some c => obtain ⟨n, X⟩ := c; simp only [ofVals, Rel.Rel.runE, hK, Option.elim] at h; exact hf K n X t hK (by have h1 := hW.1; rw [hK] at h1; exact h1) h

/-- A leaf on demand whose `Tab` law is "a key in demand, related by `P`": `id outl outr nil`, and the rows
    `∋ inl inr` (`τ`, `setify` given their `Obj.lt` hypothesis) run under `ofVals`. -/
theorem ofVals_row_sound {f : {n : USize} → Vals A n → Except String (Tab A B)} {P : Core.Rel A.El B.El}
    (hf : ∀ n (X : Vals A n) t, Vals.WF X → f X = .ok t → ∀ a b, t.Holds a b ↔ (∃ i, X.row i = a) ∧ P a b) :
    ∀ K, K.WF → (ofVals A B f).Reps K P :=
  ofVals_sound fun _ _ _ _ hK hX h a b ha _ _ => (hf _ _ _ hX h a b).trans (and_iff_right ((side_some hK a).1 ha))

/-! ### Structural ops: `id comp conv meet join zero top dom ran` -/

theorem zero_sound : ∀ K, K.WF → (GenK.zero A B).Reps K 𝟘 :=
  fun _ _ => (reps_iff _ _ _).2 fun _ h x y _ _ _ => Tab.zero_holds h x y

theorem val_sound (R : Tab A B × Bool) (hR : R.2 = true → R.1.WF) : ∀ K, K.WF → (GenK.val A B R).Reps K (rep R.1) := fun K hW => by
  rw [reps_iff]; intro t h; unfold GenK.val const at h
  split at h
  · exact fun x y _ _ _ => Tab.canon_holds h (hR ‹_›) x y
  · nomatch h

theorem uni_sound {m : USize} (U : Vals A m × Bool) (hU : U.2 = true → Vals.WF U.1) :
    ∀ K, K.WF → (GenK.uni A m U).Reps K ((graph U.1.row)° ≫ graph U.1.row) := fun K hW => by
  rw [reps_iff]; intro t h; unfold GenK.uni const at h
  split at h
  · refine fun x y _ _ _ => (Tab.idU_holds h (hU ‹_›) x y).trans ⟨?_, ?_⟩
    · rintro ⟨rfl, i, rfl⟩; exact ⟨i, rfl, rfl⟩
    · rintro ⟨i, rfl, rfl⟩; exact ⟨rfl, i, rfl⟩
  · nomatch h

theorem id_sound : ∀ K, K.WF → (GenK.id A).Reps K (𝟙 _) := fun K hW => by
  rw [reps_iff]; intro t h
  have hs := @side_or A K
  -- the side `id` reads is `K.dom`, else `K.ran`: `WF` by `hW`
  have hwo : (K.dom <|> K.ran).elim True (fun c => Vals.WF c.2) := by
    have h1 := hW.1; have h2 := hW.2.1; revert h1 h2; cases K.dom <;> intro h1 h2 <;> assumption
  simp only [GenK.id, Rel.Rel.runE] at h
  generalize (K.dom <|> K.ran) = o at h hs hwo
  cases o with
  | none => simp [Option.elim, Rel.Rel.runE] at h
  | some c =>
    obtain ⟨n, X⟩ := c
    simp only [Option.elim, Rel.Rel.runE] at h
    intro a b ha hb _
    refine (Tab.idU_holds h hwo a b).trans ⟨fun ⟨e, _⟩ => e, fun e => ⟨e, ?_⟩⟩
    subst e; exact (side_some rfl a).1 (hs ha hb)

theorem conv_sound {R : Rel A B} {X : Core.Rel A.El B.El} (hR : ∀ K, K.WF → R.Reps K X) (wR : R.Wf) :
    ∀ K, K.WF → (GenK.conv A B R).Reps K X° :=
  lift1_sound (fun _ h => h.conv) hR wR fun _ _ _ ht wr hr x y hx hy ho =>
    (Tab.conv_holds ht wr x y).trans (hr y x hy hx (on_conv ho))

theorem join_sound {R S : Rel A B} {X Y : Core.Rel A.El B.El} (hR : ∀ K, K.WF → R.Reps K X)
    (hS : ∀ K, K.WF → S.Reps K Y) (wR : R.Wf) (wS : S.Wf) : ∀ K, K.WF → (GenK.join A B R S).Reps K (X ∪ Y) :=
  lift2_sound (fun _ h => h) (fun _ h => h) hR hS wR wS fun _ _ _ _ ht wr ws hr hs x y hx hy ho =>
    (Tab.union_holds ht wr ws x y).trans (or_congr (hr x y hx hy ho) (hs x y hx hy ho))

theorem dom_sound {R : Rel A B} {X : Core.Rel A.El B.El} (hR : ∀ K, K.WF → R.Reps K X) (wR : R.Wf) :
    ∀ K, K.WF → (GenK.dom A B R).Reps K (𝟙 _ ∩ X ≫ X°) :=
  lift1_sound (fun _ h => ⟨h.side, trivial, trivial⟩) hR wR fun _ r _ ht wr hr x x' hx hx' _ => by
    refine (Tab.dom_holds ht wr.1 x x').trans ⟨?_, ?_⟩
    · rintro ⟨rfl, y, h⟩; have e := hr _ y (side_or hx hx') rfl trivial; exact ⟨rfl, y, e.1 h, e.1 h⟩
    · rintro ⟨rfl, y, h, -⟩; exact ⟨rfl, y, (hr _ y (side_or hx hx') rfl trivial).2 h⟩

theorem ran_sound {R : Rel A B} {X : Core.Rel A.El B.El} (hR : ∀ K, K.WF → R.Reps K X) (wR : R.Wf) :
    ∀ K, K.WF → (GenK.ran A B R).Reps K (𝟙 _ ∩ X° ≫ X°°) :=
  lift1_sound (fun _ h => ⟨trivial, h.side, trivial⟩) hR wR fun _ r _ ht wr hr y y' hy hy' _ => by
    refine (Tab.ran_holds ht wr.2 y y').trans (Iff.trans ⟨?_, ?_⟩ (ran_iff X y y').symm)
    · rintro ⟨rfl, x, h⟩; have e := hr x _ rfl (side_or hy hy') trivial; exact ⟨rfl, x, e.1 h, e.1 h⟩
    · rintro ⟨rfl, x, h, -⟩; exact ⟨rfl, x, (hr x _ rfl (side_or hy hy') trivial).2 h⟩

theorem idU_comp_holds {n : USize} {X : Vals A n} {d : Tab A A} {r l : Tab A B} (hd : Tab.idU X = .ok d)
    (hl : d.comp r = .ok l) (hX : Vals.WF X) (hr : r.WF) (x : A.El) (y : B.El) :
    l.Holds x y ↔ (∃ i, X.row i = x) ∧ r.Holds x y := by
  rw [Tab.comp_holds hl (Tab.idU_wf hd hX) hr]
  exact ⟨fun ⟨b, h, hr⟩ => by obtain ⟨rfl, hx⟩ := (Tab.idU_holds hd hX x b).1 h; exact ⟨hx, hr⟩,
    fun ⟨hx, hr⟩ => ⟨x, (Tab.idU_holds hd hX x x).2 ⟨rfl, hx⟩, hr⟩⟩

theorem comp_idU_holds {m : USize} {L : Vals B m} {d : Tab B B} {l w : Tab A B} (hd : Tab.idU L = .ok d)
    (hw : l.comp d = .ok w) (hL : Vals.WF L) (hl : l.WF) (x : A.El) (y : B.El) :
    w.Holds x y ↔ l.Holds x y ∧ ∃ j, L.row j = y := by
  rw [Tab.comp_holds hw hl (Tab.idU_wf hd hL)]
  exact ⟨fun ⟨b, h, h'⟩ => by obtain ⟨rfl, hy⟩ := (Tab.idU_holds hd hL b y).1 h'; exact ⟨h, hy⟩,
    fun ⟨h, hy⟩ => ⟨y, h, (Tab.idU_holds hd hL y y).2 ⟨rfl, hy⟩⟩⟩

/-- `cut K r` is `r` on `K`'s sides. -/
theorem cut_agrees {K : Known A B} {r w : Tab A B} (hK : K.WF) (hr : r.WF) (h : cut K r = .ok w) :
    Agrees K (rep w) (rep r) := by
  obtain ⟨_ | ⟨n, X⟩, _ | ⟨m, L⟩, _⟩ := K <;> obtain ⟨wX, wL, -⟩ := hK <;> intro x y hx hy _
  · obtain rfl := Except.ok.inj (show Except.ok r = .ok w from h); exact Iff.rfl
  · obtain ⟨d, hd, h⟩ := bind_ok (show (Tab.idU L >>= fun d => r.comp d) = .ok w from h)
    exact (comp_idU_holds hd h wL hr x y).trans (and_iff_left ((side_some rfl y).1 hy))
  · obtain ⟨d, hd, h⟩ := bind_ok h
    obtain ⟨l, hl, h⟩ := bind_ok h; obtain rfl := Except.ok.inj h
    exact (idU_comp_holds hd hl wX hr x y).trans (and_iff_right ((side_some rfl x).1 hx))
  · obtain ⟨d, hd, h⟩ := bind_ok h
    obtain ⟨l, hl, h⟩ := bind_ok h; obtain ⟨d', hd', h⟩ := bind_ok h
    exact (comp_idU_holds hd' h wL (Tab.comp_wf hl (Tab.idU_wf hd wX) hr) x y).trans
      ((and_iff_left ((side_some rfl y).1 hy)).trans
      ((idU_comp_holds hd hl wX hr x y).trans (and_iff_right ((side_some rfl x).1 hx))))

/-- `cut` to two known sides: the pairs of `r` whose values lie in `X` and `L`. -/
theorem cut_holds {k : (n : USize) × Vals A n} {l : (m : USize) × Vals B m} {r w : Tab A B}
    (h : cut ⟨some k, some l, none⟩ r = .ok w) (hk : Vals.WF k.2) (hl : Vals.WF l.2) (hr : r.WF) (x : A.El)
    (y : B.El) : rep w x y ↔ (∃ i, k.2.row i = x) ∧ rep r x y ∧ ∃ j, l.2.row j = y := by
  obtain ⟨d, hd, h⟩ := bind_ok h
  obtain ⟨u, hu, h⟩ := bind_ok h; obtain ⟨d', hd', h⟩ := bind_ok h
  exact (comp_idU_holds hd' h hl (Tab.comp_wf hu (Tab.idU_wf hd hk) hr) x y).trans
    ((and_congr_left' (idU_comp_holds hd hu hk hr x y)).trans and_assoc)

/-- **`cut` keeps `Tab.WF`** in a `WF` context: `idU` of a known side composed on (`Tab.idU_wf`, `Tab.comp_wf`). -/
theorem cut_wf {K : Known A B} {r t : Tab A B} (hK : K.WF) (hr : r.WF) (h : cut K r = .ok t) : t.WF := by
  obtain ⟨hd, hn, -⟩ := hK
  -- the `do` block's continuation sits in each branch of `K.dom`'s match, so split on `K.dom` first
  have tail : ∀ l : Tab A B, l.WF → (match K.ran with | some c => do l.comp (← Tab.idU c.2) | none => pure l) = .ok t →
      t.WF := fun l wl h => by
    cases hran : K.ran with
    | none => simp only [hran] at h; cases h; exact wl
    | some c => simp only [hran] at h hn; obtain ⟨u, hu, h⟩ := bind_ok h; exact Tab.comp_wf h wl (Tab.idU_wf hu hn)
  simp only [cut] at h
  cases hdom : K.dom with
  | none => simp only [hdom] at h; exact tail r hr h
  | some c =>
    simp only [hdom] at h hd
    obtain ⟨u, hu, h⟩ := bind_ok h
    obtain ⟨l, hl, h⟩ := bind_ok h
    exact tail l (Tab.comp_wf hl (Tab.idU_wf hu hd) hr) h

/-- `bound K r` is `r` on `K`'s sides, and every pair of it is a pair the context it hands the other operand admits. -/
theorem bound_spec {K : Known A B} {r : Tab A B} {p : Tab A B × Known A B} (hK : K.WF) (hr : r.WF)
    (h : bound K r = .ok p) :
    Agrees K (rep p.1) (rep r) ∧ ∀ x y, rep p.1 x y → p.2.den.1 x x ∧ p.2.den.2 y y ∧ p.2.on x y := by
  obtain ⟨t, ht, h⟩ := bind_ok h
  obtain ⟨d, hd, h⟩ := bind_ok h
  obtain ⟨l, hl, h⟩ := bind_ok h
  obtain rfl := Except.ok.inj h
  have wt := cut_wf hK hr ht
  exact ⟨cut_agrees hK hr ht, fun x y hxy => ⟨(side_some rfl x).2 ((keyRowRep d x).2 ⟨x, (Tab.dom_holds hd wt.1 x x).2 ⟨rfl, y, hxy⟩⟩),
    (side_some rfl y).2 ((keyRowRep l y).2 ⟨y, (Tab.ran_holds hl wt.2 y y).2 ⟨rfl, x, hxy⟩⟩), hxy⟩⟩

theorem top_sound {V : Rel B B} {Y : Core.Rel B.El B.El} (hV : ∀ K, K.WF → V.Reps K Y) (wV : V.Wf) :
    ∀ K, K.WF → (GenK.top A B V).Reps K (Core.Rel.top ≫ Y) := fun K hW => by
  rw [reps_iff]; intro t h
  cases hK : K.dom with
  | none => simp [GenK.top, Rel.Rel.runE, hK] at h
  | some c =>
    obtain ⟨n, X⟩ := c
    simp only [GenK.top, Rel.Rel.runE, hK] at h
    obtain ⟨v, hv, h⟩ := bind_ok h
    obtain ⟨w, hw, ht⟩ := bind_ok h
    have hR : (⟨none, K.ran, none⟩ : Known B B).WF := ⟨trivial, hW.2.1, trivial⟩
    have ev := (reps_iff _ _ _).1 (hV _ hR) v hv
    have ew := cut_agrees hR (wV.runE hR hv) hw
    have wW := cut_wf hR (wV.runE hR hv) hw
    have hX : Vals.WF X := by have h1 := hW.1; rw [hK] at h1; exact h1
    intro a b ha hb hon
    -- `Y` holds beside `b` iff `b` is a value of `w`
    have hY : (∃ j, w.val.row j = b) ↔ ∃ c, Y c b := by
      refine ⟨fun ⟨j, hj⟩ => ⟨w.key.row j, (ev (w.key.row j) b rfl hb trivial).1
        ((ew (w.key.row j) b rfl hb trivial).1 ?_)⟩, fun ⟨c, h⟩ => ?_⟩
      · exact ⟨j, rfl, hj⟩
      · obtain ⟨j, -, hj⟩ := (ew c b rfl hb trivial).2 ((ev c b rfl hb trivial).2 h)
        exact ⟨j, hj⟩
    cases hP : K.pairs with
    | none =>
      simp only [hP] at ht
      refine (Tab.top_val_holds ht hX wW a b).trans
        ⟨fun ⟨_, c, _, h⟩ => ⟨c, trivial, ?_⟩, fun ⟨c, _, h⟩ => ⟨(side_some hK a).1 ha, c, trivial, ?_⟩⟩
      · exact (ev c b rfl hb trivial).1 ((ew c b rfl hb trivial).1 h)
      · exact (ew c b rfl hb trivial).2 ((ev c b rfl hb trivial).2 h)
    | some p =>
      simp only [hP] at ht
      have hp : rep p a b := by unfold Known.on at hon; rw [hP] at hon; exact hon
      have wp : p.WF := by have h3 := hW.2.2; rw [hP] at h3; exact h3
      exact (cut_holds ht hX wW.2 wp a b).trans
        ⟨fun ⟨_, _, h⟩ => let ⟨c, h⟩ := hY.1 h; ⟨c, trivial, h⟩,
         fun ⟨c, _, h⟩ => ⟨(side_some hK a).1 ha, hp, hY.2 ⟨c, h⟩⟩⟩

/-- **`bound` keeps `Tab.WF`**: its table is `cut_wf`'s, its context that table's sides and the table. -/
theorem bound_wf {K : Known A B} {r : Tab A B} {p : Tab A B × Known A B} (hK : K.WF) (hr : r.WF)
    (h : bound K r = .ok p) : p.1.WF ∧ p.2.WF := by
  unfold bound at h
  obtain ⟨t, ht, h⟩ := bind_ok h
  obtain ⟨d, hd, h⟩ := bind_ok h
  obtain ⟨l, hl, h⟩ := bind_ok h
  cases h
  have wt := cut_wf hK hr ht
  exact ⟨wt, (Tab.dom_wf hd wt).1, (Tab.ran_wf hl wt).1, wt⟩

/-! ### Products and sums: `pair outl outr` (`outl outr` by `ofVals_row_sound`) -/

/-- `pairOn`'s two tables are `WF`: the first `bound`'s (`bound_wf`), the second run on its domain. -/
theorem pairOn_wf {D : Option ((n : USize) × Vals A n)} {T : Rel A B} {S : Rel A C} (wT : T.Wf) (wS : S.Wf)
    (hD : D.elim True fun c => Vals.WF c.2) {p : Tab A B × Tab A C} (h : pairOn D T S = .ok p) : p.1.WF ∧ p.2.WF := by
  obtain ⟨r, hr, h⟩ := bind_ok h
  obtain ⟨q, hq, h⟩ := bind_ok h
  obtain ⟨s, hs, h⟩ := bind_ok h
  obtain rfl := Except.ok.inj h
  have hK : (⟨D, none, none⟩ : Known A B).WF := ⟨hD, trivial, trivial⟩
  have wq := bound_wf hK (wT.runE hK hr) hq
  exact ⟨wq.1, wS.runE wq.2.dom hs⟩

/-- `pairOn D T S`'s two tables relate a value of `D` as `X` and `Y` do: `S` agrees with `Y` on the domain of `T`'s
    table (`bound_spec`), and off it both sides are false. -/
theorem pairOn_sound {D : Option ((n : USize) × Vals A n)} {T : Rel A B} {S : Rel A C} {X : Core.Rel A.El B.El}
    {Y : Core.Rel A.El C.El} (hT : ∀ K, K.WF → T.Reps K X) (hS : ∀ K, K.WF → S.Reps K Y)
    (wT : T.Wf) (hD : (⟨D, none, none⟩ : Known A B).WF) {p : Tab A B × Tab A C}
    (h : pairOn D T S = .ok p) (a : A.El) (ha : (⟨D, none, none⟩ : Known A B).den.1 a a) (b : B.El) (c : C.El) :
    rep p.1 a b ∧ rep p.2 a c ↔ X a b ∧ Y a c := by
  obtain ⟨r, hr, h⟩ := bind_ok h
  obtain ⟨q, hq, h⟩ := bind_ok h
  obtain ⟨s, hs, h⟩ := bind_ok h
  obtain rfl := Except.ok.inj h
  obtain ⟨hu, hK⟩ := bound_spec hD (wT.runE hD hr) hq
  have wq := bound_wf hD (wT.runE hD hr) hq
  have er := (reps_iff _ _ _).1 (hT _ hD) r hr a b ha rfl trivial
  have es := (reps_iff _ _ _).1 (hS _ wq.2.dom) s hs
  have eu := hu a b ha rfl trivial
  refine ⟨fun ⟨u, v⟩ => ⟨er.1 (eu.1 u), (es a c (hK a b u).1 rfl trivial).1 v⟩, fun ⟨u, v⟩ => ?_⟩
  have u' := eu.2 (er.2 u)
  exact ⟨u', (es a c (hK a b u').1 rfl trivial).2 v⟩

theorem pairK_sound {R : Rel A B} {S : Rel A C} {X : Core.Rel A.El B.El} {Y : Core.Rel A.El C.El}
    (hR : ∀ K, K.WF → R.Reps K X) (hS : ∀ K, K.WF → S.Reps K Y) (wR : R.Wf) (wS : S.Wf)
    (K : Known A (.prod B C)) (hK : K.WF) {t : Tab A (.prod B C)}
    (h : pairK K.dom R S = .ok t) : Agrees K (rep t) (rpair X Y) := by
  have L : ∀ p, pairOn K.dom R S = .ok p → p.1.pair p.2 = .ok t → Agrees K (rep t) (rpair X Y) :=
    fun _ hp ht a q ha _ _ => let w := pairOn_wf wR wS hK.1 hp
      (Tab.pair_holds ht w.1 w.2 a q).trans (pairOn_sound hR hS wR hK.dom hp a ha q.1 q.2)
  have M : ∀ p, pairOn K.dom S R = .ok p → p.2.pair p.1 = .ok t → Agrees K (rep t) (rpair X Y) :=
    fun _ hp ht a q ha _ _ => let w := pairOn_wf wS wR hK.1 hp
      (Tab.pair_holds ht w.2 w.1 a q).trans
      (and_comm.trans ((pairOn_sound hS hR wS hK.dom hp a ha q.2 q.1).trans and_comm))
  unfold pairK at h; split at h
  · split at h
    · exact L _ ‹_› h
    · obtain ⟨p, hp, ht⟩ := bind_ok (retryE_ok h); exact M p hp ht
  all_goals obtain ⟨p, hp, ht⟩ := bind_ok h
  · exact M p hp ht
  · exact L p hp ht

theorem pair_sound {R : Rel A B} {S : Rel A C} {X : Core.Rel A.El B.El} {Y : Core.Rel A.El C.El}
    (hR : ∀ K, K.WF → R.Reps K X) (hS : ∀ K, K.WF → S.Reps K Y) (wR : R.Wf) (wS : S.Wf) :
    ∀ K, K.WF → (GenK.pair A B C R S).Reps K (rpair X Y) := by
  have hL : ∀ K, K.WF → (Rel.lazy fun K => .tab (pairK K.dom R S) : Rel A (.prod B C)).Reps K (rpair X Y) := fun K hK =>
    (reps_iff _ _ _).2 fun _ h => pairK_sound hR hS wR wS K hK h
  have hT : ∀ K, K.WF → (lift2 Tab.pair (fun K : Known A (.prod B C) => (⟨K.dom, none, none⟩ : Known A B))
      (fun K => ⟨K.dom, none, none⟩) R S).Reps K (rpair X Y) :=
    lift2_sound (fun _ h => h.dom) (fun _ h => h.dom) hR hS wR wS fun _ _ _ _ ht wr ws hr hs a q ha _ _ =>
    (Tab.pair_holds ht wr ws a q).trans (and_congr (hr a q.1 ha rfl trivial) (hs a q.2 ha rfl trivial))
  cases R <;> cases S <;> first | exact hL | exact hT

example : ∀ K, K.WF → (GenK.outl A B).Reps K (graph Prod.fst) := ofVals_row_sound fun _ _ _ hX h => Tab.outl_holds h hX
example : ∀ K, K.WF → (GenK.outr A B).Reps K (graph Prod.snd) := ofVals_row_sound fun _ _ _ hX h => Tab.outr_holds h hX

/-! ### `diff rdiv lam nil succ leq lt` (`nil` by `ofVals_row_sound`, `leq lt` by `cmp_sound`) -/

theorem diff_sound {R S : Rel A B} {X Y : Core.Rel A.El B.El} (hR : ∀ K, K.WF → R.Reps K X)
    (hS : ∀ K, K.WF → S.Reps K Y) (wR : R.Wf) (wS : S.Wf) :
    ∀ K, K.WF → (GenK.diff A B R S).Reps K (diffDen X Y) := by
  unfold GenK.diff; split
  · intro K hW; rw [reps_iff]; intro t h
    obtain ⟨r, hr, h⟩ := bind_ok h
    obtain ⟨p, hp, h⟩ := bind_ok h
    obtain ⟨s, hs, ht⟩ := bind_ok h
    obtain ⟨hu, hK⟩ := bound_spec hW (wR.runE hW hr) hp
    have wp := bound_wf hW (wR.runE hW hr) hp
    have er := (reps_iff _ _ _).1 (hR K hW) r hr
    have es := (reps_iff _ _ _).1 (hS p.2 wp.2) s hs
    intro x y hx hy ho
    refine (Tab.diff_holds ht wp.1 (wS.runE wp.2 hs) x y).trans ⟨fun ⟨a, b⟩ => ⟨(er x y hx hy ho).1 ((hu x y hx hy ho).1 a),
      fun q => b ((es x y (hK x y a).1 (hK x y a).2.1 (hK x y a).2.2).2 q)⟩, fun ⟨a, b⟩ => ?_⟩
    have a' := (hu x y hx hy ho).2 ((er x y hx hy ho).2 a)
    exact ⟨a', fun q => b ((es x y (hK x y a').1 (hK x y a').2.1 (hK x y a').2.2).1 q)⟩
  · exact lift2_sound (fun _ h => h) (fun _ h => h) hR hS wR wS fun _ _ _ _ ht wr ws hr hs x y hx hy ho =>
      (Tab.diff_holds ht wr ws x y).trans (and_congr (hr x y hx hy ho) (not_congr (hs x y hx hy ho)))

theorem rdiv_sound {R : Rel A C} {S : Rel B C} {UA : Rel A A} {UB : Rel B B} {X : Core.Rel A.El C.El}
    {Y : Core.Rel B.El C.El} {TA : Core.Rel A.El A.El} {TB : Core.Rel B.El B.El} (hR : ∀ K, K.WF → R.Reps K X)
    (hS : ∀ K, K.WF → S.Reps K Y) (hA : ∀ K, K.WF → UA.Reps K TA) (hB : ∀ K, K.WF → UB.Reps K TB) (wR : R.Wf)
    (wS : S.Wf) (wA : UA.Wf) (wB : UB.Wf) : ∀ K, K.WF → (GenK.rdiv A B C R S UA UB).Reps K (rdivDen X Y TA TB) :=
  lift2_sound (fun _ _ => Known.wf_empty) (fun _ _ => Known.wf_empty) hR hS wR wS fun _ r s _ ht wr ws hr hs => by
    obtain ⟨sc, hsc, ht⟩ := bind_ok ht
    obtain ⟨rc, hrc, ht⟩ := bind_ok ht
    obtain ⟨ub, hub, ht⟩ := bind_ok ht
    obtain ⟨ua, hua, ht⟩ := bind_ok ht
    obtain ⟨q, hq, ht⟩ := bind_ok ht
    have w1 := Tab.conv_wf hsc ws
    have w2 := Tab.conv_wf hrc wr
    have wu := wB.runE Known.wf_empty hub
    have wa := wA.runE Known.wf_empty hua
    rw [agrees_empty hr, agrees_empty hs, agrees_empty ((reps_iff _ _ _).1 (hA {} Known.wf_empty) ua hua),
      agrees_empty ((reps_iff _ _ _).1 (hB {} Known.wf_empty) ub hub)]
    have wq := Tab.ldivSel_wf (fun h => Tab.ldivOf_wf h w1 w2 wu wa) hq w1 w2 wu wa
    intro x y _ _ _
    refine (Tab.conv_holds ht wq x y).trans ((Tab.ldivSel_holdsBy
      (fun h => Tab.ldivOf_holds ⟨_, hsc, ws.2, ws.1⟩ ⟨_, hrc, wr.2, wr.1⟩ h w1 w2 wu wa) hq w1 w2 wu wa y x).trans ?_)
    simp only [ldivDen_iff, rdivDen_iff, rep_apply, Tab.conv_holds hsc ws, Tab.conv_holds hrc wr]
    exact and_congr Iff.rfl (or_congr Iff.rfl and_comm)

theorem lam_sound {R : Rel A B} {X : Core.Rel A.El B.El} (hR : ∀ K, K.WF → R.Reps K X) (wR : R.Wf) :
    ∀ K, K.WF → (GenK.lam A B R).Reps K (lamDen X) :=
  ofVals_sound fun _ _ _ _ hK hX h a ys ha _ _ => by
    obtain ⟨r, hr, ht⟩ := bind_ok h
    have hW : (⟨some ⟨_, _⟩, none, none⟩ : Known A B).WF := ⟨hX, trivial, trivial⟩
    have er := (reps_iff _ _ _).1 (hR _ hW) r hr
    have ha' := (side_some hK a).1 ha
    exact (Tab.lam_den ht hX (wR.runE hW hr) a ys).trans ((and_iff_right ha').trans ((lamDen_iff _ _ _).trans ((and_congr Iff.rfl
      (forall_congr' fun b => iff_congr Iff.rfl (er a b ((side_some rfl a).2 ha') rfl trivial))).trans (lamDen_iff _ _ _).symm)))

example : ∀ K, K.WF → (GenK.nil A B).Reps K nilDen := ofVals_row_sound fun _ _ _ hX h => Tab.nil_holds h hX

theorem cmp_side {op w : String} {t : QAtomicType} {U : Rel (.atom t) (.atom t)}
    {TU : Core.Rel (Obj.atom t).El (Obj.atom t).El} (hU : ∀ K, K.WF → U.Reps K TU) (wU : U.Wf)
    {o : Option ((n : USize) × Vals (.atom t) n)} {k : (n : USize) × Vals (.atom t) n}
    (hoW : o.elim True fun c => Vals.WF c.2) (h : GenK.cmpSide op w U o = .ok k) {a : (Obj.atom t).El} (ha : o.elim (𝟙 _) (fun c => (graph c.2.row)° ≫ graph c.2.row) a a) :
    (∃ i, k.2.row i = a) ↔ ∃ v, TU a v := by
  obtain ⟨u, hu', h⟩ := bind_ok h
  have hu : U.runE ⟨o, none, none⟩ = .ok u := by
    cases e : U.runE ⟨o, none, none⟩ <;> rw [e] at hu' <;> cases hu' <;> rfl
  obtain ⟨d, hd, h⟩ := bind_ok h
  have wu := wU.runE (show (⟨o, none, none⟩ : Known (.atom t) (.atom t)).WF from ⟨hoW, trivial, trivial⟩) hu
  have agr := (reps_iff _ _ _).1 (hU ⟨o, none, none⟩ ⟨hoW, trivial, trivial⟩) u hu a
  have key : (∃ i, d.key.row i = a) ↔ ∃ v, TU a v := by
    rw [keyRowRep]
    exact ⟨fun ⟨_, h⟩ => let ⟨_, v, hv⟩ := (Tab.dom_holds hd wu.1 _ _).1 h; ⟨v, (agr v ha rfl trivial).1 hv⟩,
      fun ⟨v, h⟩ => ⟨a, (Tab.dom_holds hd wu.1 a a).2 ⟨rfl, v, (agr v ha rfl trivial).2 h⟩⟩⟩
  cases o with
  | none => obtain rfl := Except.ok.inj h; exact key
  | some c =>
    obtain ⟨n, X⟩ := c
    obtain ⟨e, he, h⟩ := bind_ok h
    obtain ⟨T, ht, h⟩ := bind_ok h
    obtain rfl := Except.ok.inj h
    -- atom sides: `Vals.WF` holds with no cell to check
    exact (keyRowRep T a).trans ((exists_congr fun b => (idU_comp_holds he ht trivial ⟨trivial, trivial⟩ a b).trans
      (and_iff_right ((side_some (C := .atom t) rfl a).1 ha))).trans ((keyRowRep d a).symm.trans key))

/-- `cmp (ordOp s t) U` is the order `ordAt s t` of the atom `t` on `U`'s domain: on the pairs `p` a meet hands it,
    `p` cut to the two sides then tested (`Tab.cmpPairs_holds`), agreeing with the order on exactly `p`; else on the
    cross of the sides (`Tab.cmpOn_holds`). `GenK.cmpRel` at an atom is it (`rowOK_cmpRel`). -/
theorem cmp_sound {op : String} {s : Bool} {t : QAtomicType} {U : Rel (.atom t) (.atom t)}
    {TU : Core.Rel (Obj.atom t).El (Obj.atom t).El} (hU : ∀ K, K.WF → U.Reps K TU) (wU : U.Wf) :
    ∀ K, K.WF → (GenK.cmp op (Tab.ordOp s t) U).Reps K
      (fun a b => (∃ v, TU a v) ∧ (∃ v, TU b v) ∧ Tab.ordAt s t a b) := fun K hW => by
  rw [reps_iff]; intro T h
  obtain ⟨o, hop, h⟩ := bind_ok h
  obtain ⟨k, hk, h⟩ := bind_ok h
  obtain ⟨l, hl, h⟩ := bind_ok h
  intro a c ha hc ho
  have sk := cmp_side hU wU hW.1 hk ha; have sl := cmp_side hU wU hW.2.1 hl hc
  cases hP : K.pairs with
  | none =>
    simp only [hP] at h
    exact (Tab.cmpOn_holds hop h trivial trivial a c).trans (and_congr sk (and_congr sl Iff.rfl))
  | some p =>
    simp only [hP] at h
    obtain ⟨q, hq, h⟩ := bind_ok h
    have hp : rep p a c := by unfold Known.on at ho; rw [hP] at ho; exact ho
    refine ((Tab.cmpPairs_holds hop h a c).trans (and_congr ((cut_holds hq trivial trivial ⟨trivial, trivial⟩ a c).trans ?_)
      Iff.rfl)).trans and_assoc
    rw [← sk, ← sl]; exact ⟨fun ⟨x, _, z⟩ => ⟨x, z⟩, fun ⟨x, z⟩ => ⟨x, hp, z⟩⟩

/-! ### The rows with a law, under `ofVals` (the wrapper `Expand.primE` fits a row on values alone to) -/

example : ∀ K, K.WF → (ofVals (.arr A) A fun X => Tab.mem X).Reps K (fun xs b => b ∈ xs) :=
  ofVals_row_sound fun _ _ _ hX h => Tab.mem_holds h hX
example : ∀ K, K.WF → (ofVals A (.sum A B) fun X => Tab.inl X).Reps K Core.Rel.inl :=
  ofVals_row_sound fun _ _ _ hX h => Tab.inl_holds h hX
example : ∀ K, K.WF → (ofVals B (.sum A B) fun X => Tab.inr X).Reps K Core.Rel.inr :=
  ofVals_row_sound fun _ _ _ hX h => Tab.inr_holds h hX
example : ∀ K, K.WF → (ofVals A (.arr A) fun X => Tab.tau X).Reps K (fun a ys => ys = [a]) :=
  ofVals_row_sound fun _ _ _ hX h => Tab.tau_den h hX
example : ∀ K, K.WF → (ofVals (.arr B) (.arr B) fun X => Tab.setify X).Reps K (lamDen fun xs b => b ∈ xs) :=
  ofVals_row_sound fun _ _ _ hX h => Tab.setify_den h hX

end GenK

end Rel.Lang
