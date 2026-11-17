import Rel.Lang.Rows

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

/-- `νX : S ∩ φ` by rounds from `S` down, each met with `S`: the greatest fixed point of `X ↦ ⟦S⟧ ∩ Φ X` for a
    monotone `Φ`. Every round is below `⟦S⟧`, so the chain of distinct-row tables below `S` is fixed within `S`'s
    row count plus one (`CRel.rep_fixOn`'s last clause). -/
theorem nu_sound {A B : Obj} {S : Fn false A B} {TS : Den A B} {φ : CRel A B → Fn false A B}
    {Φ : Den A B → Den A B} (hS : Sound S TS) (hΦ : Monotonic Φ)
    (h : ∀ X : CRel A B, X.ok = true → Sound (φ X) (Φ (rep X.rel))) :
    Sound (Gen.nu A B S φ) (Core.Rel.nu fun X => TS ∩ Φ X) := fun ⟨⟩ _ hb x y _ => by
  simp only [Gen.nu] at hb ⊢
  have hs : (S ()).ok = true := by
    cases e : (S ()).ok
    · rw [CRel.fixOn, CRel.guard, e] at hb; exact absurd hb Bool.false_ne_true
    · rfl
  have hX : rep (S ()).rel = TS := hS.eq hs
  have hΨ : Monotonic fun X => TS ∩ Φ X := fun X Y hXY => inter_le' (Core.Rel.le_refl _) (hΦ X Y hXY)
  have hle : ∀ X, TS ∩ Φ X ⊑ TS := fun X => Core.Rel.inter_le_left _ _
  have hit : ∀ i, Nat.repeat (fun X => TS ∩ Φ X) i (rep (S ()).rel) ⊑ rep (S ()).rel := fun i => by
    cases i with
    | zero => exact Core.Rel.le_refl _
    | succ i => show TS ∩ Φ _ ⊑ _; rw [hX]; exact hle _
  have hφ : ∀ D, (CRel.inter (S ()) (φ ⟨D, true⟩ ())).ok = true →
      rep (CRel.inter (S ()) (φ ⟨D, true⟩ ())).rel = TS ∩ Φ (rep D) := fun D hD => by
    have h2 := ok_and hD; rw [Bool.and_eq_true] at h2
    rw [CRel.rep_inter _ _ hD, hX, (h ⟨D, true⟩ rfl).eq h2.2]
  obtain ⟨j, -, hj, hr, hfix, -, hcnt⟩ := CRel.rep_fixOn _ (fun X => CRel.inter (S ()) (φ X ())) (S ())
    (fun X => TS ∩ Φ X) hb hφ hΨ (Or.inr (hX ▸ hle _))
  have hfx := hfix (hcnt _ hit (by omega))
  have hdown : ∀ i, Core.Rel.nu (fun X => TS ∩ Φ X) ⊑ Nat.repeat (fun X => TS ∩ Φ X) i (rep (S ()).rel) :=
    fun i => by
    induction i with
    | zero => show _ ⊑ rep (S ()).rel; rw [hX, ← nu_fix hΨ]; exact hle _
    | succ i ih => show _ ⊑ TS ∩ Φ _; rw [← nu_fix hΨ]; exact hΨ _ _ ih
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

/-! ### The rows of `prims` -/

/-- Every row of `rowDens` not in `rowGaps` has its `Row`. -/
theorem rows_cover : ∀ i : Fin rowDens.length, rowGaps.contains rowDens[i].1.sym = false → ∃ w ∈ rows, w.i = i := by
  decide

theorem none'_sound {A B : Obj} {d : Bool} {T : Den A B} : Sound (none' A B d) T :=
  fun _ _ hb => absurd hb Bool.false_ne_true

/-- The row `r` run on sound arguments: `Prim.run` finds the code of the `rowDens` entry `Prim.den` reads
    (`rowDens_codes`), and that entry's `Row` is in `rows`. -/
theorem Prim.run_sound {r : Prim} {A B : Obj} {cs : List Code} {ss : List Sem} (hr : rowGaps.contains r.sym = false)
    (hs : Code.Sounds cs ss) {f : Fn true A B} (hf : r.run A B cs = some f) : Sound f (r.den A B ss) := by
  have hc : rowCodes.find? (·.sym == r.sym) = (rowDens.find? (·.1.sym == r.sym)).map (·.1) := by
    rw [← rowDens_codes, List.find?_map]; rfl
  unfold Prim.run at hf; unfold Prim.den
  rw [hc] at hf
  cases hx : rowDens.find? (·.1.sym == r.sym) with
  | none => simp [hx] at hf
  | some x =>
    obtain ⟨c, D⟩ := x
    cases ho : r.objs A B with
    | none => simp [hx, ho] at hf
    | some σ =>
      simp only [hx, ho, Option.map_some, Option.bind_eq_bind, Option.bind_some] at hf ⊢
      cases hg : c.run σ cs with
      | none => simp [hg] at hf
      | some g =>
        simp only [hg, Option.bind_some] at hf
        split at hf
        · rename_i h; obtain ⟨rfl, rfl⟩ := h; cases hf
          obtain ⟨i, hi, ei⟩ := List.getElem_of_mem (List.mem_of_find?_eq_some hx)
          have hsym : c.sym = r.sym := by simpa using List.find?_some hx
          obtain ⟨w, -, hw⟩ := rows_cover ⟨i, hi⟩ (by simpa [ei, hsym] using hr)
          have := w.sound
          rw [hw] at this
          simp only [Fin.getElem_fin] at this
          rw [ei] at this
          simpa using this σ cs ss hs g hg
        · cases hf

/-- A row's code at either demand bit, sound wherever every code `Prim.run` finds is. -/
theorem Prim.fn_sound {r : Prim} {A B : Obj} {cs : List Code} {T : Den A B}
    (h : ∀ f, r.run A B cs = some f → Sound f T) : ∀ d, Sound (r.fn A B d cs) T
  | true => by
    cases e : r.run A B cs with
    | none => simp only [Prim.fn, e, Option.getD_none]; exact none'_sound
    | some f => simp only [Prim.fn, e, Option.getD_some]; exact h f e
  | false => none'_sound

/-! ### `compile_sound` -/

/-- What `compile_sound` proves of a node's output `o`: its code and its plan compute `T` on their keys, and where `o`
    is a row's spine `(r, cs)`, the row run on `cs` and then on any further sound arguments computes `Ta` of their
    meanings. `compile` appends an argument's code to `cs` and `Tm.argDen` prepends its meaning to `ss`, so `cs` is
    the prefix already applied and `cs'` the rest. -/
def Out.Sound {A B : Obj} {d : Bool} (o : Out d A B) (T : Den A B) (Ta : List Sem → Den A B) : Prop :=
  Gen.Sound o.fn T ∧ PSound o.pl T ∧ ∀ r cs, o.row = some (r, cs) → ∀ cs' ss, Code.Sounds cs' ss →
    ∀ f, r.run A B (cs ++ cs') = some f → Gen.Sound f (Ta ss)

/-- `Out.memo` is the identity: a closed node's code is a function of `()` alone. -/
theorem Out.memo_eq {A B : Obj} : ∀ {d : Bool} (o : Out d A B), o.memo = o
  | false, _ => rfl
  | true, _ => rfl

theorem Out.Sound.memo {A B : Obj} {d : Bool} {o : Out d A B} {T : Den A B} {Ta : List Sem → Den A B}
    (h : o.Sound T Ta) : o.memo.Sound T Ta := by rw [Out.memo_eq]; exact h

/-- A node that is no row's spine. -/
theorem Out.Sound.node {A B : Obj} {d : Bool} {o : Out d A B} {T : Den A B} {Ta : List Sem → Den A B}
    (h : Gen.Sound o.fn T) (hp : PSound o.pl T) (hr : o.row = none) : o.Sound T Ta :=
  ⟨h, hp, fun _ _ e => by rw [hr] at e; cases e⟩

/-- A node with no bit rule: its plan is its table. -/
theorem Out.Sound.leaf {A B : Obj} {d : Bool} {f : Fn d A B} {T : Den A B} {Ta : List Sem → Den A B}
    (h : Gen.Sound f T) : (Tm.gen.leaf f).Sound T Ta := .node h (pleaf_sound h) rfl

theorem gap_or {a b : Option String} (h : (a <|> b) = none) : a = none ∧ b = none := by
  cases a <;> simp_all

/-- **`compile` is sound**: on a term with no gap, under an environment whose plans compute their variables'
    meanings, the code and the plan of every node compute its meaning `⟦t⟧ρ` on their keys. -/
theorem compile_sound {A B : Obj} {d : Bool} (t : Tm A B d) (hg : t.gap = none) (η : CodeEnv) (ρ : Val)
    (hη : η.Sound ρ) : (t.gen η).Sound (t.den ρ) (t.argDen ρ) := by
  induction t generalizing η ρ with
  | val R => exact Out.Sound.memo (Out.Sound.leaf (val_sound (R, true)))
  | uni U => exact Out.Sound.memo (Out.Sound.leaf (uni_sound (U, true)))
  | zero => exact Out.Sound.memo (Out.Sound.leaf zero_sound)
  | id => exact Out.Sound.memo (Out.Sound.leaf id_sound)
  | outl => exact Out.Sound.memo (Out.Sound.leaf outl_sound)
  | outr => exact Out.Sound.memo (Out.Sound.leaf outr_sound)
  | nil => exact Out.Sound.memo (Out.Sound.leaf nil_sound)
  | atPos k => exact Out.Sound.memo (Out.Sound.leaf (atPos_sound k))
  | top V ih => exact Out.Sound.memo (Out.Sound.leaf (top_sound (ih hg η ρ hη).1))
  | conv R ih =>
    have i := ih hg η ρ hη
    exact Out.Sound.memo (.node (conv_sound i.1) (pconv_sound i.2.1) rfl)
  | dom R ih => exact Out.Sound.memo (Out.Sound.leaf (dom_sound (ih hg η ρ hη).1))
  | ran R ih => exact Out.Sound.memo (Out.Sound.leaf (ran_sound (ih hg η ρ hη).1))
  | est Q ih => exact Out.Sound.memo (Out.Sound.leaf (est_sound (ih hg η ρ hη).1))
  | succ U ih => exact Out.Sound.memo (Out.Sound.leaf (succ_sound (ih hg η ρ hη).1))
  | arith k U ih => exact Out.Sound.memo (Out.Sound.leaf (arith_sound k (ih hg η ρ hη).1))
  | leq U ih => exact Out.Sound.memo (Out.Sound.leaf (leq_sound (ih hg η ρ hη).1))
  | lt U ih => exact Out.Sound.memo (Out.Sound.leaf (lt_sound (ih hg η ρ hη).1))
  | flat R ih => exact Out.Sound.memo (Out.Sound.leaf (flat_sound (ih hg η ρ hη).1))
  | @comp A' B' C' d e R S ihR ihS =>
    obtain ⟨hR, hS⟩ := gap_or hg
    have iR := ihR hR η ρ hη; have iS := ihS hS η ρ hη
    cases d
    · exact Out.Sound.memo (.node (compB_sound iR.2.1 iS.2.1) (pcomp_sound iR.2.1 iS.2.1) rfl)
    · exact Out.Sound.memo (.node (comp_sound iR.1 iS.1) (pcomp_sound iR.2.1 iS.2.1) rfl)
  | @meet A' B' d e R S ihR ihS =>
    obtain ⟨hR, hS⟩ := gap_or hg
    have iR := ihR hR η ρ hη; have iS := ihS hS η ρ hη
    cases d <;> cases e <;> first
      | exact Out.Sound.memo (.node (meetB_sound iR.2.1 iS.2.1) (pmeet_sound iR.2.1 iS.2.1) rfl)
      | exact Out.Sound.memo (.node (meet_sound iR.1 iS.1) (pmeet_sound iR.2.1 iS.2.1) rfl)
  | join R S ihR ihS =>
    obtain ⟨hR, hS⟩ := gap_or hg
    have iR := ihR hR η ρ hη; have iS := ihS hS η ρ hη
    exact Out.Sound.memo (.node (join_sound iR.1 iS.1) (pjoin_sound iR.2.1 iS.2.1) rfl)
  | @diff A' B' d e R S ihR ihS =>
    obtain ⟨hR, hS⟩ := gap_or hg
    have iR := ihR hR η ρ hη; have iS := ihS hS η ρ hη
    cases d <;> cases e <;> first
      | exact Out.Sound.memo (.node (diffB_sound iR.2.1 iS.2.1) (pdiff_sound iR.2.1 iS.2.1) rfl)
      | exact Out.Sound.memo (.node (diff_sound iR.1 iS.1) (pdiff_sound iR.2.1 iS.2.1) rfl)
  | pair R S ihR ihS =>
    obtain ⟨hR, hS⟩ := gap_or hg
    exact Out.Sound.memo (Out.Sound.leaf (pair_sound (ihR hR η ρ hη).1 (ihS hS η ρ hη).1))
  | prod R S ihR ihS =>
    obtain ⟨hR, hS⟩ := gap_or hg
    exact Out.Sound.memo (Out.Sound.leaf (prod_sound (ihR hR η ρ hη).1 (ihS hS η ρ hη).1))
  | junc R S ihR ihS =>
    obtain ⟨hR, hS⟩ := gap_or hg
    exact Out.Sound.memo (Out.Sound.leaf (junc_sound (ihR hR η ρ hη).1 (ihS hS η ρ hη).1))
  | fold e S ihe ihS =>
    obtain ⟨he, hS⟩ := gap_or hg
    exact Out.Sound.memo (Out.Sound.leaf (fold_sound (ihe he η ρ hη).1 (ihS hS η ρ hη).1))
  | ldiv R S U V ihR ihS ihU ihV =>
    obtain ⟨hR, h⟩ := gap_or hg; obtain ⟨hS, h⟩ := gap_or h; obtain ⟨hU, hV⟩ := gap_or h
    have iR := ihR hR η ρ hη; have iS := ihS hS η ρ hη; have iU := ihU hU η ρ hη; have iV := ihV hV η ρ hη
    exact Out.Sound.memo (.node (ldivB_sound iR.2.1 iS.2.1 iU.1 iV.1) (pldiv_sound iR.2.1 iS.2.1 iU.1 iV.1) rfl)
  | rdiv R S U V ihR ihS ihU ihV =>
    obtain ⟨hR, h⟩ := gap_or hg; obtain ⟨hS, h⟩ := gap_or h; obtain ⟨hU, hV⟩ := gap_or h
    exact Out.Sound.memo (Out.Sound.leaf
      (rdiv_sound (ihR hR η ρ hη).1 (ihS hS η ρ hη).1 (ihU hU η ρ hη).1 (ihV hV η ρ hη).1))
  | var k => exact Out.Sound.memo (.node (ofPl_sound (hη k _ _ _)) (hη k _ _ _) rfl)
  | own R ih => exact Out.Sound.memo (ih hg η ρ hη)
  | share k R ih =>
    simp only [Tm.gap] at hg
    split at hg
    · rename_i hc
      have e := R.den_congr ρ Val.empty fun i hi => by simp [List.isEmpty_iff.1 hc] at hi
      have i := ih hg η ρ hη
      rw [e.1, funext e.2] at i
      exact Out.Sound.memo i
    · cases hg
  | mu k w cap b ih =>
    simp only [Tm.gap] at hg
    split at hg
    · rename_i hp
      exact Out.Sound.memo (Out.Sound.leaf (mu_sound (fun X Y h => Tm.den_mono hp h)
        fun X _ => (ih hg _ _ (hη.bind k X)).1))
    · cases hg
  | prim r =>
    have hr : rowGaps.contains r.sym = false := by simpa [Tm.gap] using hg
    refine Out.Sound.memo ⟨Prim.fn_sound (fun f hf => Prim.run_sound (cs := []) (ss := []) hr trivial hf) true,
      pleaf_sound (Prim.fn_sound (fun f hf => Prim.run_sound (cs := []) (ss := []) hr trivial hf) true), ?_⟩
    intro r' cs e; cases e
    exact fun cs' ss hs f hf => Prim.run_sound hr hs hf
  | @arg A' B' C D d e f x ihf ihx =>
    obtain ⟨hf, hx⟩ := gap_or hg
    have i := ihf hf η ρ hη; have ix := ihx hx η ρ hη
    refine Out.Sound.memo ?_
    dsimp only
    cases hrow : (f.gen η).row with
    | none => exact Out.Sound.leaf none'_sound
    | some p =>
      obtain ⟨r, cs⟩ := p
      have hcx : Code.Sound ⟨C, D, e, (x.gen η).fn⟩ ⟨C, D, x.den ρ⟩ := fun X Y e' g h => by
        cases h; exact ⟨_, rfl, ix.1⟩
      have inv : ∀ cs' ss, Code.Sounds cs' ss → ∀ g, r.run A' B' ((cs ++ [⟨C, D, e, (x.gen η).fn⟩]) ++ cs') = some g →
          Sound g (f.argDen ρ (⟨C, D, x.den ρ⟩ :: ss)) := fun cs' ss hs g hg => by
        rw [List.append_assoc] at hg; exact i.2.2 r cs hrow (⟨C, D, e, (x.gen η).fn⟩ :: cs') (⟨C, D, x.den ρ⟩ :: ss) ⟨hcx, hs⟩ g hg
      refine ⟨Prim.fn_sound (fun g hg => inv [] [] trivial g (by simpa using hg)) d,
        pleaf_sound (Prim.fn_sound (fun g hg => inv [] [] trivial g (by simpa using hg)) d), ?_⟩
      intro r' cs' e'; cases e'; exact inv
  | nu k S b ihS ih =>
    simp only [Tm.gap] at hg
    split at hg
    · rename_i hp
      obtain ⟨hS, hb⟩ := gap_or hg
      exact Out.Sound.memo (Out.Sound.leaf (nu_sound (ihS hS η ρ hη).1 (fun X Y h => Tm.den_mono hp h)
        fun X _ => (ih hb _ _ (hη.bind k X)).1))
    · cases hg
  | lam | E | thin | juncD | foldI | call | refold => simp [Tm.gap] at hg
end Rel.Lang
