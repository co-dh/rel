import Rel.Lang.Rows
import Rel.HyloSpec

/-! The cases of `compile_sound` that `GenSpec` has no lemma for (`doc/rel-denotation-design.md` §7.2, §7.5): the
    binders `μ`, `ν`, their environment, and `flat`. Each is stated for every body, so the induction hypothesis
    of a body is already parametric in its variable. -/

namespace Rel.Lang

open Tab Rel.Alg Rel.Rep Rel.Kernel Gen
open scoped Rel.Core.Rel
open Rel.Core.Rel hiding id comp recip inter union zero le inl inr junc

/-- Every variable's plan computes its meaning under `ρ`. -/
def CodeEnv.Sound (η : CodeEnv) (ρ : Val) : Prop := ∀ k A B, PSound (η k A B) (ρ k A B)

/-- `μX : φ` by rounds from `𝟘`: where fewer than `cap` rounds ran, the least fixed point of a monotone `Φ`, each
    round sound at an ok table (`CRel.rep_fixOn`). -/
theorem mu_sound {A B : Obj} {cap : Nat} {φ : CRel A B → Fn false A B} {Φ : Den A B → Den A B}
    (hΦ : Monotonic Φ) (h : ∀ X : CRel A B, X.ok = true → Sound (φ X) (Φ (rep X.rel))) :
    Sound (Gen.mu A B cap φ) (Core.Rel.mu Φ) := const_sound fun hb => by
  obtain ⟨⟨hlt, hok⟩, e⟩ := also_ok_rel hb
  rw [e]
  obtain ⟨j, -, hj, -, hfix, hleast, -⟩ := CRel.rep_fixOn cap (fun X => (φ X).run {}) (some Alg.zero) Φ hok
    (fun D hD => (h (some D) rfl).run_eq hD) hΦ
    (Or.inl (le_iff.2 fun a b h => by rw [CRel.some_rel, rep_zero] at h; exact h.elim))
  have hfx := hfix (hj ▸ of_decide_eq_true hlt)
  exact Core.Rel.le_antisymm
    (hleast _ (le_iff.2 fun a b h => by rw [CRel.some_rel, rep_zero] at h; exact h.elim) (mu_prefixed hΦ))
    (mu_le (by rw [hfx]; exact Core.Rel.le_refl _))

/-- `νX : S ∩ φ` by rounds from `S` down, each met with `S`: the greatest fixed point of `X ↦ ⟦S⟧ ∩ Φ X` for a
    monotone `Φ`. Every round is below `⟦S⟧`, so the chain of distinct-row tables below `S` is fixed within `S`'s
    row count plus one (`CRel.rep_fixOn`'s last clause). -/
theorem nu_sound {A B : Obj} {S : Fn false A B} {TS : Den A B} {φ : CRel A B → Fn false A B}
    {Φ : Den A B → Den A B} (hS : Sound S TS) (hΦ : Monotonic Φ)
    (h : ∀ X : CRel A B, X.ok = true → Sound (φ X) (Φ (rep X.rel))) :
    Sound (Gen.nu A B S φ) (Core.Rel.nu fun X => TS ∩ Φ X) := const_sound fun hb => by
  have hs : CRel.ok (S.run {}) = true := by
    cases e : CRel.ok (S.run {})
    · rw [CRel.fixOn, CRel.guard, e] at hb; exact absurd hb Bool.false_ne_true
    · rfl
  have hX : rep (CRel.rel (S.run {})) = TS := hS.run_eq hs
  have hΨ : Monotonic fun X => TS ∩ Φ X := fun X Y hXY => inter_le' (Core.Rel.le_refl _) (hΦ X Y hXY)
  have hle : ∀ X, TS ∩ Φ X ⊑ TS := fun X => Core.Rel.inter_le_left _ _
  have hit : ∀ i, Nat.repeat (fun X => TS ∩ Φ X) i (rep (CRel.rel (S.run {}))) ⊑ rep (CRel.rel (S.run {})) :=
    fun i => by
    cases i with
    | zero => exact Core.Rel.le_refl _
    | succ i => show TS ∩ Φ _ ⊑ _; rw [hX]; exact hle _
  have hφ : ∀ D, (CRel.inter (S.run {}) ((φ (some D)).run {})).ok = true →
      rep (CRel.inter (S.run {}) ((φ (some D)).run {})).rel = TS ∩ Φ (rep D) := fun D hD => by
    have h2 := CRel.guard_ok_left hD; rw [Bool.and_eq_true] at h2
    rw [CRel.rep_inter _ _ hD, hX, (h (some D) rfl).run_eq h2.2, CRel.some_rel]
  obtain ⟨j, -, hj, hr, hfix, -, hcnt⟩ := CRel.rep_fixOn _ (fun X => CRel.inter (S.run {}) ((φ X).run {}))
    (S.run {}) (fun X => TS ∩ Φ X) hb hφ hΨ (Or.inr (hX ▸ hle _))
  have hfx := hfix (hcnt _ hit (by omega))
  have hdown : ∀ i, Core.Rel.nu (fun X => TS ∩ Φ X) ⊑
      Nat.repeat (fun X => TS ∩ Φ X) i (rep (CRel.rel (S.run {}))) := fun i => by
    induction i with
    | zero => show _ ⊑ rep (CRel.rel (S.run {})); rw [hX, ← nu_fix hΨ]; exact hle _
    | succ i ih => show _ ⊑ TS ∩ Φ _; rw [← nu_fix hΨ]; exact hΨ _ _ ih
  exact Core.Rel.le_antisymm (le_nu (by rw [hfx]; exact Core.Rel.le_refl _)) (hr ▸ hdown j)

/-- `flat(R)`: `(i, a)` to `b` where `R` relates `i` to `(a, b)`, `R` run on the `i` in demand. -/
theorem flat_sound {I A B : Obj} {d : Bool} {R : Fn d I (.prod A B)} {TR : Den I (.prod A B)} (hR : Sound R TR) :
    Sound (flat I A B d R) (flatDen TR) := ofVals_keys fun X hb x b hx => by
  dsimp only at hb ⊢
  obtain ⟨⟨hro, hc⟩, e⟩ := also_ok_rel hb
  rw [e]
  have h1 := CRel.guard_ok_left hc; rw [Bool.and_eq_true] at h1
  have h2 := CRel.guard_ok_left h1.2; rw [Bool.and_eq_true] at h2
  obtain ⟨hp, ep⟩ := CRel.mk_ok_rel h2.1
  obtain ⟨hu, eu⟩ := CRel.mk_ok_rel h2.2
  have h3 := CRel.guard_ok_left hp; rw [Bool.and_eq_true] at h3
  obtain ⟨hr, er⟩ := CRel.mk_ok_rel h3.1
  obtain ⟨-, el⟩ := CRel.mk_ok_rel h3.2
  have hK := (CRel.rep_ofC hro).trans (rep_ranC (Alg.outl (idU X)) (CRel.ofC_ok hro).1)
  have hRk : ∀ i v, rep (CRel.ofC (ranC (Alg.outl (idU X)))).rel i i →
      (rep (onKeys R (CRel.ofC (ranC (Alg.outl (idU X))))).rel i v ↔ TR i v) :=
    fun i v h => onKeys_round hR _ i v ⟨i, h⟩ hr
  have hi : rep (CRel.ofC (ranC (Alg.outl (idU X)))).rel x.1 x.1 := by
    have ho : rep (Alg.outl (idU X)) x x.1 := by rw [rep_outl]; exact ⟨x, hx, rfl⟩
    rw [hK]; exact ⟨rfl, x, ho, ho⟩
  rw [CRel.rep_comp _ _ hc, CRel.rep_comp _ _ h1.2, ep, eu, rep_conv, CRel.rep_pair _ _ hp, er, el, rep_conv,
    rep_outl, rep_outr, CRel.rep_ran _ hu]
  constructor
  · rintro ⟨x', hd, q, ⟨hr, z, ⟨e1, -⟩, ez⟩, z', ⟨e2, -⟩, ez'⟩
    obtain rfl := ((idU_holds X x x').1 hd).1
    subst e1 e2
    have e : q = (x.2, b) := Prod.ext (by first | exact ez | exact ez.symm) (by first | exact ez' | exact ez'.symm)
    subst e
    exact (hRk x.1 _ hi).1 hr
  · intro t
    have hr := (hRk x.1 _ hi).2 t
    exact ⟨x, hx, (x.2, b), ⟨hr, (x.2, b), ⟨rfl, x.1, hr, hr⟩, rfl⟩, (x.2, b), ⟨rfl, x.1, hr, hr⟩, rfl⟩

/-- `F` read at the nodes `P` (`onNodes`) is `P ≫ F`, for any `P`: a lazy `F` runs on `P`'s values. -/
theorem onNodes_sound {A B : Obj} {F : Rel A B} {T : Den A B} (hF : Sound F T) (P : CRel A A)
    (hok : (onNodes F P).ok = true) : rep (onNodes F P).rel = rep P.rel ≫ T := by
  cases F with
  | tab f =>
    simp only [onNodes] at hok ⊢
    by_cases h0 : (P.rel.n == 0) = true
    · rw [if_pos h0] at hok ⊢
      rw [(CRel.mk_ok_rel hok).2, rep_zero]
      exact Core.Rel.ext fun a c => ⟨False.elim, fun ⟨w, h, _⟩ => rep_empty h0 a w h⟩
    · rw [if_neg h0] at hok ⊢
      have hf := CRel.guard_ok_left hok; rw [Bool.and_eq_true] at hf
      have ef : rep (CRel.rel f.toOption) = T := hF.run_eq hf.2
      rw [CRel.rep_comp _ _ hok, ef]
  | lazy g =>
    simp only [onNodes] at hok ⊢
    obtain ⟨⟨-, hc⟩, e⟩ := also_ok_rel hok
    have hk := CRel.guard_ok_left hc; rw [Bool.and_eq_true] at hk
    rw [e, CRel.rep_comp _ _ hc]
    exact Core.Rel.ext fun a c => ⟨fun ⟨p, hp, h⟩ => ⟨p, hp, (onKeys_round hF P p c ⟨a, hp⟩ hk.2).1 h⟩,
      fun ⟨p, hp, h⟩ => ⟨p, hp, (onKeys_round hF P p c ⟨a, hp⟩ hk.2).2 h⟩⟩

/-- `hylo(c, S)` (`Gen.hylo`) computes `μX : Φ`: the nodes `N` reached from the keys by `ch` are the least set
    closed under `TCh` (`CRel.rep_fixOn`), and the rounds over them leave `μ Φ` there (`rep_hylo`), for `Φ`
    monotonic and local along `TCh`, each round sound at an ok table as in `mu_sound`. -/
theorem hylo_sound {A B : Obj} {d e : Bool} {ch : Fn d A A} {φ : CRel A B → Fn e A B} {TCh : Den A A}
    {Φ : Den A B → Den A B} (hm : Monotonic Φ) (hl : Hylo.Local (fun _ => True) TCh Φ) (hch : Sound ch TCh)
    (hφ : ∀ X : CRel A B, X.ok = true → Sound (φ X) (Φ (rep X.rel))) :
    Sound (Gen.hylo A B d e ch φ) (Core.Rel.mu Φ) := ofVals_keys fun X hb x y hx => by
  dsimp only at hb ⊢
  obtain ⟨⟨hlt, hc⟩, e⟩ := also_ok_rel hb
  rw [Bool.and_eq_true] at hlt
  have hc' := CRel.guard_ok_left hc; rw [Bool.and_eq_true] at hc'
  rw [e, CRel.rep_comp _ _ hc, CRel.some_rel]
  -- the reach: one round adds the coreflexive on the values of `N ≫ TCh`
  have hst : ∀ D : Tab A A, (CRel.union (some D) (CRel.ran (onNodes ch (some D)))).ok = true →
      rep (CRel.union (some D) (CRel.ran (onNodes ch (some D)))).rel =
        rep D ∪ (𝟙 _ ∩ (rep D ≫ TCh)° ≫ (rep D ≫ TCh)°°) := fun D hD => by
    have h1 := CRel.guard_ok_left hD; rw [Bool.and_eq_true] at h1
    rw [CRel.rep_union _ _ hD, CRel.rep_ran _ h1.2, onNodes_sound hch _ (CRel.guard_ok_left h1.2), CRel.some_rel]
  have hΨ : ∀ Y Z : Den A A, Y ⊑ Z → Y ∪ (𝟙 _ ∩ (Y ≫ TCh)° ≫ (Y ≫ TCh)°°) ⊑ Z ∪ (𝟙 _ ∩ (Z ≫ TCh)° ≫ (Z ≫ TCh)°°) :=
    fun Y Z h => le_iff.2 fun a b k => k.elim (fun k => Or.inl (le_iff.1 h _ _ k))
      fun ⟨e, w, ⟨v, h1, h2⟩, v', h3, h4⟩ => Or.inr ⟨e, w, ⟨v, le_iff.1 h _ _ h1, h2⟩, v', le_iff.1 h _ _ h3, h4⟩
  have hNok := (hyloRounds_ok _ _ _ hlt.2 hc'.2).1
  obtain ⟨j, -, hj, hrep, hfix, hleast, -⟩ := CRel.rep_fixOn _ _ _
    (fun Y => Y ∪ (𝟙 _ ∩ (Y ≫ TCh)° ≫ (Y ≫ TCh)°°)) hNok hst hΨ (Or.inl (le_iff.2 fun a b h => Or.inl h))
  have hfp := hfix (hj ▸ of_decide_eq_true hlt.1)
  have hcor := hleast (𝟙 _) (le_iff.2 fun a b h => ((idU_holds X a b).1 h).1)
    (le_iff.2 fun a b h => h.elim id fun ⟨e, _⟩ => e)
  have hinf : ∀ i, rep (idU X) ⊑ Nat.repeat (fun Y => Y ∪ (𝟙 _ ∩ (Y ≫ TCh)° ≫ (Y ≫ TCh)°°)) i (rep (idU X)) :=
    fun i => by
    induction i with
    | zero => exact Core.Rel.le_refl _
    | succ i ih => exact le_iff.2 fun a b h => Or.inl (le_iff.1 ih a b h)
  have hxN := le_iff.1 (hrep ▸ hinf j) x x hx
  revert hlt hc' hNok hrep hfp hcor hxN
  generalize (CRel.fixOn USize.size (fun N => CRel.union N (CRel.ran (onNodes ch N))) (some (idU X))).1 = N
  intro hlt hc' hNok hrep hfp hcor hxN
  have hcN : ∀ a b, rep N.rel a b → a = b := fun a b h => le_iff.1 hcor a b h
  have key := rep_hylo (chN := onNodes ch N) (φ := fun Y P => onNodes (φ Y) P) (N := N) hm
    (fun hok X Y a hNa h => hl X Y a trivial fun a' t => h a' (by rw [onNodes_sound hch N hok]; exact ⟨a, hNa, t⟩))
    (fun Y P hY hok hP a b => by
      rw [onNodes_sound (hφ Y hY) P hok]
      exact ⟨fun ⟨w, h1, h2⟩ => by cases hP _ _ h1; exact ⟨h1, h2⟩, fun ⟨h1, h2⟩ => ⟨a, h1, h2⟩⟩)
    hcN
    (fun hok a a' hNa h => by
      rw [onNodes_sound hch N hok] at h
      rw [← hfp]; exact Or.inr ⟨rfl, a, h, h⟩)
    _ hlt.2 hc'.2 x hxN y
  exact ⟨fun ⟨w, h1, h2⟩ => by cases ((idU_holds X x w).1 h1).1; exact key.1 h2,
    fun h => ⟨x, hx, key.2 h⟩⟩

/-- `memRow` at `[E] ⟶ E` relates a list to its members. -/
theorem Prim.den_memRow {E : Obj} {xs : (Obj.arr E).El} {x : E.El} (h : x ∈ xs) :
    Prim.den memRow (.arr E) E [] xs x := by
  have ho : memRow.objs (.arr E) E = some [E] := by simp [Prim.objs, memRow, OExp.unify, Prim.vars, OExp.vars]; rfl
  have hf : rowDens.find? (·.1.sym == memRow.sym) =
      some ⟨RowCode.mem, fun σ _ (xs : List (σ₁ σ).El) x => x ∈ xs⟩ := rfl
  unfold Prim.den; rw [hf, ho]; dsimp only; rw [dif_pos ⟨rfl, rfl⟩]; exact h

/-- A row `F(T)` at `xs` reads `T` only at the members of `xs`. -/
theorem Prim.den_map_congr {r : Prim} (hr : (r.sym == mapRow.sym) = true) {A B C D : Obj} {T T' : Den C D}
    {a : A.El} (h : ∀ m, Prim.den memRow A C [] a m → ∀ e, (T m e ↔ T' m e)) (d : B.El) :
    r.den A B [⟨C, D, T⟩] a d ↔ r.den A B [⟨C, D, T'⟩] a d := by
  have hf : rowDens.find? (·.1.sym == mapRow.sym) = some ⟨RowCode.map, fun σ => Sem.one (X := σ₁ σ) (Y := σ₂ σ)
      fun T (xs : List (σ₁ σ).El) (ys : List (σ₂ σ).El) => ys.length = xs.length ∧
        ∀ t (ht : t < xs.length) (ht' : t < ys.length), T (xs[t]'ht) (ys[t]'ht')⟩ := rfl
  unfold Prim.den; rw [eq_of_beq hr, hf]
  cases r.objs A B with
  | none => exact Iff.rfl
  | some σ =>
    dsimp only
    by_cases hh : (RowCode.map.ty σ).1 = A ∧ (RowCode.map.ty σ).2 = B
    · obtain ⟨rfl, rfl⟩ := hh
      rw [dif_pos ⟨rfl, rfl⟩, dif_pos ⟨rfl, rfl⟩]
      simp only [Sem.one]
      by_cases hc : C = σ₁ σ ∧ D = σ₂ σ
      · obtain ⟨rfl, rfl⟩ := hc
        rw [dif_pos ⟨rfl, rfl⟩, dif_pos ⟨rfl, rfl⟩]
        exact and_congr_right fun _ => forall_congr' fun t => forall_congr' fun ht => forall_congr' fun ht' =>
          h _ (Prim.den_memRow (List.getElem_mem ht)) _
      · rw [dif_neg hc, dif_neg hc]
    · rw [dif_neg hh, dif_neg hh]

/-- **`hylo`'s body is local along its children** (`Hylo.Local`): where `X` and `Y` agree at the children
    `t.kids k A` reaches from `a`, `t` reads the same at `a` under either bound to `k`. -/
theorem Tm.den_local (k : Nat) {A B : Obj} (ρ : Val) (X Y : Den A B) : ∀ {C D : Obj} (t : Tm C D) (c : Tm C A),
    t.kids k A = some c → ∀ a, (∀ a', c.den ρ a a' → ∀ b, (X a' b ↔ Y a' b)) →
      ∀ d, t.den (ρ.bind k X) a d ↔ t.den (ρ.bind k Y) a d := by
  have free : ∀ {C D : Obj} (t : Tm C D), t.fv.contains k = false → ∀ a d,
      t.den (ρ.bind k X) a d ↔ t.den (ρ.bind k Y) a d := fun t h a d => by
    rw [(t.den_congr _ (ρ.bind k Y) fun i hi => by
      rw [Val.bind_ne (by rintro rfl; simp [hi] at h), Val.bind_ne (by rintro rfl; simp [hi] at h)]).1]
  intro C D t
  induction t with
  | @var C' D' _ j =>
    intro c hc a hX d
    unfold Tm.kids at hc; split at hc
    · rename_i hk
      simp only [Tm.fv, List.contains_cons, List.contains_nil, Bool.or_false, beq_iff_eq] at hk
      subst hk
      dsimp only at hc
      simp only [Tm.den, Val.bind, if_true]
      by_cases h : A = C' ∧ B = D'
      · obtain ⟨rfl, rfl⟩ := h
        rw [dif_pos rfl] at hc; cases hc
        rw [dif_pos ⟨rfl, rfl⟩, dif_pos ⟨rfl, rfl⟩]
        exact hX a rfl d
      · simp only [dif_neg h]
    · exact free _ (Bool.eq_false_iff.mpr ‹_›) a d
  | comp R S ihR ihS =>
    intro c hc a hX d
    unfold Tm.kids at hc; split at hc
    · dsimp only at hc
      cases hS : S.fv.contains k
      · simp only [hS, Bool.not_false, if_true] at hc
        simp only [Tm.den]
        exact exists_congr fun m => and_congr (ihR c hc a hX m) (free S hS m d)
      · cases hR : R.fv.contains k
        rotate_left
        · simp only [hS, hR, Bool.not_true, Bool.false_eq_true, ↓reduceIte, reduceCtorEq] at hc
        simp only [hS, hR, Bool.not_true, Bool.false_eq_true, if_false] at hc
        cases hs : S.kids k A <;> simp only [hs, reduceCtorEq, Option.some.injEq] at hc
        subst hc
        rename_i s
        have eX := (R.den_congr (ρ.bind k X) ρ fun i hi => Val.bind_ne (by rintro rfl; simp [hi] at hR)).1
        have eY := (R.den_congr (ρ.bind k Y) ρ fun i hi => Val.bind_ne (by rintro rfl; simp [hi] at hR)).1
        simp only [Tm.den, eX, eY]
        exact exists_congr fun m => and_congr_right fun hm => ihS s hs m (fun a' h' => hX a' ⟨m, hm, h'⟩) d
    · exact free _ (Bool.eq_false_iff.mpr ‹_›) a d
  | meet R S ihR ihS =>
    intro c hc a hX d
    unfold Tm.kids at hc; split at hc
    · dsimp only at hc
      cases hr : R.kids k A <;> cases hs : S.kids k A <;> simp only [hr, hs, reduceCtorEq, Option.some.injEq] at hc
      subst hc
      exact and_congr (ihR _ hr a (fun a' h => hX a' (Or.inl h)) d) (ihS _ hs a (fun a' h => hX a' (Or.inr h)) d)
    · exact free _ (Bool.eq_false_iff.mpr ‹_›) a d
  | join R S ihR ihS =>
    intro c hc a hX d
    unfold Tm.kids at hc; split at hc
    · dsimp only at hc
      cases hr : R.kids k A <;> cases hs : S.kids k A <;> simp only [hr, hs, reduceCtorEq, Option.some.injEq] at hc
      subst hc
      exact or_congr (ihR _ hr a (fun a' h => hX a' (Or.inl h)) d) (ihS _ hs a (fun a' h => hX a' (Or.inr h)) d)
    · exact free _ (Bool.eq_false_iff.mpr ‹_›) a d
  | pair R S ihR ihS =>
    intro c hc a hX d
    unfold Tm.kids at hc; split at hc
    · dsimp only at hc
      cases hr : R.kids k A <;> cases hs : S.kids k A <;> simp only [hr, hs, reduceCtorEq, Option.some.injEq] at hc
      subst hc
      exact and_congr (ihR _ hr a (fun a' h => hX a' (Or.inl h)) d.1)
        (ihS _ hs a (fun a' h => hX a' (Or.inr h)) d.2)
    · exact free _ (Bool.eq_false_iff.mpr ‹_›) a d
  | junc R S ihR ihS =>
    intro c hc a hX d
    unfold Tm.kids at hc; split at hc
    · dsimp only at hc
      cases hr : R.kids k A <;> cases hs : S.kids k A <;> simp only [hr, hs, reduceCtorEq, Option.some.injEq] at hc
      subst hc
      rename_i r s
      exact or_congr (exists_congr fun m => and_congr_right fun e =>
          ihR _ hr m (fun a' h => hX a' (Or.inl ⟨m, e, h⟩)) d)
        (exists_congr fun m => and_congr_right fun e => ihS _ hs m (fun a' h => hX a' (Or.inr ⟨m, e, h⟩)) d)
    · exact free _ (Bool.eq_false_iff.mpr ‹_›) a d
  | juncD R S ihR ihS =>
    intro c hc a hX d
    unfold Tm.kids at hc; split at hc
    · dsimp only at hc
      cases hr : R.kids k A <;> cases hs : S.kids k A <;> simp only [hr, hs, reduceCtorEq, Option.some.injEq] at hc
      subst hc
      exact or_congr (exists_congr fun m => and_congr_right fun e =>
          ihR _ hr m (fun a' h => hX a' (Or.inl ⟨m, e, h⟩)) d)
        (exists_congr fun m => and_congr_right fun e => ihS _ hs m (fun a' h => hX a' (Or.inr ⟨m, e, h⟩)) d)
    · exact free _ (Bool.eq_false_iff.mpr ‹_›) a d
  | dom R ih =>
    intro c hc a hX d
    unfold Tm.kids at hc; split at hc
    · dsimp only at hc
      refine and_congr_right fun e => ?_
      subst e
      exact exists_congr fun m => and_congr (ih c hc a hX m) (ih c hc a hX m)
    · exact free _ (Bool.eq_false_iff.mpr ‹_›) a d
  | own R ih =>
    intro c hc a hX d
    unfold Tm.kids at hc; split at hc
    · dsimp only at hc; exact ih c hc a hX d
    · exact free _ (Bool.eq_false_iff.mpr ‹_›) a d
  | arg f x _ ihx =>
    intro c hc a hX d
    unfold Tm.kids at hc; split at hc
    · cases f with
      | prim r =>
        dsimp only at hc
        split at hc
        · rename_i hr
          cases hs : x.kids k A <;> simp only [hs, reduceCtorEq, Option.some.injEq] at hc
          subst hc
          rename_i s
          simp only [Tm.den, Tm.argDen]
          refine Prim.den_map_congr hr (fun m hm e => ?_) d
          exact ihx s hs m (fun a' h' => hX a' ⟨m, hm, h'⟩) e
        · cases hc
      | _ => dsimp only at hc; cases hc
    · exact free _ (Bool.eq_false_iff.mpr ‹_›) a d
  | _ =>
    intro c hc a hX d
    unfold Tm.kids at hc; split at hc
    · dsimp only at hc; cases hc
    · exact free _ (Bool.eq_false_iff.mpr ‹_›) a d

/-- `[R,S]` on the sum values in demand (`juncD`): each side's part run on that side's values; the scan's bit
    excludes a demand row that names a side with no values (D7 = P). -/
theorem juncD_sound {A B C : Obj} {d e : Bool} {R : Fn d A C} {S : Fn e B C} {TR : Den A C} {TS : Den B C}
    (hR : Sound R TR) (hS : Sound S TS) : Sound (juncD A B C d e R S) (Core.Rel.junc TR TS) := by
  refine ofVals_keys fun {n} X hb x z hx => ?_
  obtain ⟨l, r, tag, idx, xv, yv⟩ := X
  dsimp only at hb ⊢
  obtain ⟨⟨hscan, hc⟩, e⟩ := also_ok_rel hb
  rw [e]
  have h1 := CRel.guard_ok_left hc; rw [Bool.and_eq_true] at h1
  have h2 := CRel.guard_ok_left h1.2; rw [Bool.and_eq_true] at h2
  rw [CRel.rep_comp _ _ hc, CRel.rep_junc _ _ h1.2]
  have hN : ∀ {D : Obj} {F : Rel D C} {T : Den D C} {m : USize} (U : Vals D m), Sound F T →
      (onNodes F (some (idU U))).ok = true → ∀ i z, (rep (onNodes F (some (idU U))).rel (U.row i) z ↔ T (U.row i) z) :=
    fun U hF hok i z => by
      rw [onNodes_sound hF _ hok, CRel.some_rel]
      exact ⟨fun ⟨w, h, t⟩ => by obtain rfl := ((idU_holds U _ w).1 h).1; exact t,
        fun t => ⟨_, (idU_holds U _ _).2 ⟨rfl, i, rfl⟩, t⟩⟩
  have hx' : rep _ x x := hx
  refine (show (∃ w, _ ∧ _) ↔ _ from
    ⟨fun ⟨w, h, j⟩ => ((idU_holds _ x w).1 h).1 ▸ j, fun j => ⟨x, hx', j⟩⟩).trans ?_
  obtain ⟨p, hp⟩ := ((idU_holds _ x x).1 hx).2
  have hrow := List.all_eq_true.1 hscan p (List.mem_finRange p)
  simp only [Vals.row] at hp
  split at hp <;> rename_i ht
  · simp only [ht, if_true, if_false, Bool.false_eq_true, decide_eq_true_eq] at hrow
    rw [dif_pos hrow] at hp; subst hp
    simp only [Core.Rel.junc, Core.Rel.inl, Core.Rel.inr, graph, union_apply, comp_apply, recip_apply,
      reduceCtorEq, false_and, exists_false, false_or, Sum.inr.injEq, exists_eq_left', exists_eq_left]
    first
      | exact hN yv hS h2.2 _ z
      | exact ⟨fun ⟨_, e, h⟩ => e ▸ (hN yv hS h2.2 _ z).1 h,
          fun h => ⟨_, rfl, (hN yv hS h2.2 _ z).2 h⟩⟩
  · simp only [ht, if_true, if_false, Bool.false_eq_true, decide_eq_true_eq] at hrow
    rw [dif_pos hrow] at hp; subst hp
    simp only [Core.Rel.junc, Core.Rel.inl, Core.Rel.inr, graph, union_apply, comp_apply, recip_apply,
      reduceCtorEq, false_and, exists_false, or_false, Sum.inl.injEq, exists_eq_left', exists_eq_left]
    first
      | exact hN xv hR h2.1 _ z
      | exact ⟨fun ⟨_, e, h⟩ => e ▸ (hN xv hR h2.1 _ z).1 h,
          fun h => ⟨_, rfl, (hN xv hR h2.1 _ z).2 h⟩⟩

/-- Binding `k` to a code keeps `CodeEnv.Sound`, the code's meaning bound in `ρ`. -/
theorem CodeEnv.Sound.bindCode {η : CodeEnv} {ρ : Val} (hη : η.Sound ρ) (k : Nat) {c : Code} {s : Sem}
    (hc : Code.Sound c s) : (η.bindCode k c).Sound (ρ.bind k s.2.2) := by
  obtain ⟨X, Y, e, f⟩ := c
  obtain ⟨T, rfl, hf⟩ := hc X Y e f rfl
  intro j A' B'
  by_cases ej : j = k
  · subst ej
    by_cases h : X = A' ∧ Y = B'
    · obtain ⟨rfl, rfl⟩ := h
      simp only [CodeEnv.bindCode, Code.at, Val.bind, and_self, dite_true, if_true]
      exact pleaf_sound hf
    · simp [CodeEnv.bindCode, Code.at, Val.bind, h, PSound, PlOK]; exact fun _ _ _ _ => Iff.rfl
  · simp only [CodeEnv.bindCode, Val.bind, ej, if_false]; exact hη j A' B'

/-- A call's arguments bound in order keep `CodeEnv.Sound`: `bindCode`'s lemma along `Code.Sounds`. -/
theorem CodeEnv.Sound.args {cs : List Code} {ss : List Sem} (h : Code.Sounds cs ss) :
    (CodeEnv.args cs).Sound (Val.args ss) := go 0 h where
  go (k : Nat) : ∀ {cs ss}, Code.Sounds cs ss → (CodeEnv.args.go k cs).Sound (Val.args.go k ss)
    | [], [], _ => fun _ _ _ => by
      simp [CodeEnv.args.go, Val.args.go, Val.empty, PSound, PlOK]; exact fun _ _ _ _ => Iff.rfl
    | _ :: _, ⟨_, _, _⟩ :: _, ⟨hc, hs⟩ => CodeEnv.Sound.bindCode (go (k + 1) hs) k hc
    | [], _ :: _, h | _ :: _, [], h => h.elim

/-! ### The rows of `prims` -/

/-- Every row of `rowDens` has its `Row`: the obligations are the indices of `rowDens`, not `rows`. -/
theorem rows_cover : ∀ i : Fin rowDens.length, ∃ w ∈ rows, w.i = i := by
  decide

theorem none'_sound {A B : Obj} {d : Bool} {T : Den A B} : Sound (none' A B d) T :=
  fun _ => trivial

/-- The row `r` run on sound arguments: `Prim.run` finds the code of the `rowDens` entry `Prim.den` reads
    (`rowDens_codes`), and that entry's `Row` is in `rows`. -/
theorem Prim.run_sound {r : Prim} {A B : Obj} {cs : List Code} {ss : List Sem} (hr : r.ok A B = true)
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
          obtain ⟨w, hw', hw⟩ := rows_cover ⟨i, hi⟩
          have hok : w.ok σ = true := by
            simp only [Prim.ok, ho, Option.all_some, List.all_eq_true, Bool.or_eq_true, bne_iff_ne, ne_eq] at hr
            exact (hr w hw').resolve_left (by simp [hw, ei, hsym])
          have := w.sound σ hok
          rw [hw] at this
          simp only [Fin.getElem_fin] at this
          rw [ei] at this
          simpa using this cs ss hs g hg
        · cases hf

/-- A row's code at either demand bit, sound wherever every code `Prim.run` finds is. -/
theorem Prim.fn_sound {r : Prim} {A B : Obj} {cs : List Code} {T : Den A B}
    (h : ∀ f, r.run A B cs = some f → Sound f T) : ∀ d, Sound (r.fn A B d cs) T
  | true => by
    cases e : r.run A B cs with
    | none => simp only [Prim.fn, e, Option.getD_none]; exact none'_sound
    | some f => simp only [Prim.fn, e, Option.getD_some]; exact h f e
  | false => none'_sound (d := false)

/-! ### `compile_sound` -/

/-- What `compile_sound` proves of a node's output `o`: its code and its plan compute `T` on their keys, and where `o`
    is a row's spine `(r, cs)`, the row run on `cs` and then on any further sound arguments computes `Ta` of their
    meanings. `compile` appends an argument's code to `cs` and `Tm.argDen` prepends its meaning to `ss`, so `cs` is
    the prefix already applied and `cs'` the rest. -/
def Out.Sound {A B : Obj} {d : Bool} (o : Out d A B) (T : Den A B) (Ta : List Sem → Den A B) : Prop :=
  Gen.Sound o.fn T ∧ PSound o.pl T ∧ ∀ r cs, o.row = some (r, cs) → ∀ cs' ss, Code.Sounds cs' ss →
    ∀ f, r.run A B (cs ++ cs') = some f → Gen.Sound f (Ta ss)


/-- A node that is no row's spine. -/
theorem Out.Sound.node {A B : Obj} {d : Bool} {o : Out d A B} {T : Den A B} {Ta : List Sem → Den A B}
    (h : Gen.Sound o.fn T) (hp : PSound o.pl T) (hr : o.row = none) : o.Sound T Ta :=
  ⟨h, hp, fun _ _ e => by rw [hr] at e; cases e⟩

/-- A node with no bit rule: its plan is its table. -/
theorem Out.Sound.leaf {A B : Obj} {d : Bool} {f : Fn d A B} {T : Den A B} {Ta : List Sem → Den A B}
    (h : Gen.Sound f T) : (Tm.gen.leaf f).Sound T Ta := .node h (pleaf_sound h) rfl

theorem gap_or {a b : Option String} (h : (a <|> b) = none) : a = none ∧ b = none := by
  cases a <;> simp_all

/-- `∋` has a lemma at every object, so a `kids` that reads `F(x)` through it adds no gap. -/
theorem memRow_ok (A B : Obj) : memRow.ok A B = true := by
  unfold Prim.ok; cases memRow.objs A B <;> rfl

/-- The children `Tm.kids` builds compile where their term does: they are its parts joined by `∪`, `[ , ]`, `;`
    and `∋`. -/
theorem Tm.gap_kids (k : Nat) (A : Obj) : ∀ {C D : Obj} (t : Tm C D) (c : Tm C A),
    t.gap = none → t.kids k A = some c → c.gap = none := by
  intro C D t
  induction t with
  | var =>
    intro c _ hc; unfold Tm.kids at hc; split at hc
    · dsimp only at hc; split at hc <;> (cases hc; rename_i h; try subst h) <;> rfl
    · cases hc; rfl
  | comp R S ihR ihS =>
    intro c hg hc; obtain ⟨hR, hS⟩ := gap_or (by simpa only [Tm.gap] using hg)
    unfold Tm.kids at hc; split at hc
    · dsimp only at hc
      split at hc
      · exact ihR c hR hc
      · split at hc
        · cases hc
        · cases hs : S.kids k A <;> simp only [hs, reduceCtorEq, Option.some.injEq] at hc
          subst hc; simp only [Tm.gap, hR, ihS _ hS hs]; rfl
    · cases hc; rfl
  | meet R S ihR ihS | join R S ihR ihS | pair R S ihR ihS | junc R S ihR ihS | juncD R S ihR ihS =>
    intro c hg hc; obtain ⟨hR, hS⟩ := gap_or (by simpa only [Tm.gap] using hg)
    unfold Tm.kids at hc; split at hc
    · dsimp only at hc
      cases hr : R.kids k A <;> cases hs : S.kids k A <;> simp only [hr, hs, reduceCtorEq, Option.some.injEq] at hc
      subst hc; simp only [Tm.gap, ihR _ hR hr, ihS _ hS hs]; rfl
    · cases hc; rfl
  | dom R ih | own R ih =>
    intro c hg hc; unfold Tm.kids at hc; split at hc
    · exact ih c (by simpa only [Tm.gap] using hg) hc
    · cases hc; rfl
  | arg f x _ ihx =>
    intro c hg hc; obtain ⟨-, hx⟩ := gap_or (by simpa only [Tm.gap] using hg)
    unfold Tm.kids at hc; split at hc
    · cases f with
      | prim r =>
        dsimp only at hc
        split at hc
        · cases hs : x.kids k A <;> simp only [hs, reduceCtorEq, Option.some.injEq] at hc
          subst hc; simp only [Tm.gap, memRow_ok, ihx _ hx hs]; rfl
        · cases hc
      | _ => dsimp only at hc; cases hc
    · cases hc; rfl
  | _ =>
    intro c _ hc; unfold Tm.kids at hc; split at hc
    · dsimp only at hc; cases hc
    · cases hc; rfl


/-- **`compile` is sound**: on a term with no gap, under an environment whose plans compute their variables'
    meanings, the code and the plan of every node compute its meaning `⟦t⟧ρ` on their keys. -/
theorem compile_sound {A B : Obj} (t : Tm A B) (hg : t.gap = none) (η : CodeEnv) (ρ : Val)
    (hη : η.Sound ρ) : (t.gen η).Sound (t.den ρ) (t.argDen ρ) := by
  -- a `μ`/`ν` round's table, bound as the closed code `Tm.gen` binds it to
  have htab {A B : Obj} (X : CRel A B) : Code.Sound ⟨A, B, false, .tab X⟩ ⟨A, B, rep X.rel⟩ :=
    fun _ _ _ _ h => by cases h; exact ⟨_, rfl, const_sound fun _ => rfl⟩
  match A, B, t, hg with
  | _, _, .val R, hg => rw [Tm.gen]; exact (Out.Sound.leaf (val_sound (R, true)))
  | _, _, .uni U, hg => rw [Tm.gen]; exact (Out.Sound.leaf (uni_sound (U, true)))
  | _, _, .zero, hg => rw [Tm.gen]; exact (Out.Sound.leaf zero_sound)
  | _, _, .id, hg => rw [Tm.gen]; exact (Out.Sound.leaf id_sound)
  | _, _, .outl, hg => rw [Tm.gen]; exact (Out.Sound.leaf outl_sound)
  | _, _, .outr, hg => rw [Tm.gen]; exact (Out.Sound.leaf outr_sound)
  | _, _, .nil, hg => rw [Tm.gen]; exact (Out.Sound.leaf nil_sound)
  | _, _, .atPos k, hg => rw [Tm.gen]; exact (Out.Sound.leaf (atPos_sound k))
  | _, _, .top V, hg => rw [Tm.gen]; exact (Out.Sound.leaf (top_sound (compile_sound V hg η ρ hη).1))
  | _, _, .conv R, hg =>
    have i := compile_sound R hg η ρ hη
    rw [Tm.gen]; exact (.node (conv_sound i.1) (pconv_sound i.2.1) rfl)
  | _, _, .dom R, hg => rw [Tm.gen]; exact (Out.Sound.leaf (dom_sound (compile_sound R hg η ρ hη).1))
  | _, _, .ran R, hg => rw [Tm.gen]; exact (Out.Sound.leaf (ran_sound (compile_sound R hg η ρ hη).1))
  | _, _, .est Q, hg => rw [Tm.gen]; exact (Out.Sound.leaf (est_sound (compile_sound Q hg η ρ hη).1))
  | _, _, .succ U, hg => rw [Tm.gen]; exact (Out.Sound.leaf (succ_sound (compile_sound U hg η ρ hη).1))
  | _, _, .arith k U, hg => rw [Tm.gen]; exact (Out.Sound.leaf (arith_sound k (compile_sound U hg η ρ hη).1))
  | _, _, .leq U, hg => rw [Tm.gen]; exact (Out.Sound.leaf (leq_sound (compile_sound U hg η ρ hη).1))
  | _, _, .lt U, hg => rw [Tm.gen]; exact (Out.Sound.leaf (lt_sound (compile_sound U hg η ρ hη).1))
  | _, _, .flat R, hg => rw [Tm.gen]; exact (Out.Sound.leaf (flat_sound (compile_sound R hg η ρ hη).1))
  | _, _, .comp R S, hg =>
    obtain ⟨hR, hS⟩ := gap_or hg
    have iR := compile_sound R hR η ρ hη; have iS := compile_sound S hS η ρ hη
    rw [Tm.gen]; dsimp only [Tm.dem]; revert iR; generalize R.gen η = r; generalize R.dem = d at r ⊢
    cases d <;> intro iR
    · exact (.node (compB_sound iR.2.1 iS.2.1) (pcomp_sound iR.2.1 iS.2.1) rfl)
    · exact (.node (comp_sound iR.1 iS.1) (pcomp_sound iR.2.1 iS.2.1) rfl)
  | _, _, .meet R S, hg =>
    obtain ⟨hR, hS⟩ := gap_or hg
    have iR := compile_sound R hR η ρ hη; have iS := compile_sound S hS η ρ hη
    rw [Tm.gen]; dsimp only [Tm.dem]; revert iR iS; generalize R.gen η = r; generalize S.gen η = s
    generalize R.dem = d at r ⊢; generalize S.dem = e at s ⊢
    cases d <;> cases e <;> intro iR iS <;> first
      | exact (.node (meetB_sound iR.2.1 iS.2.1) (pmeet_sound iR.2.1 iS.2.1) rfl)
      | exact (.node (meet_sound iR.1 iS.1) (pmeet_sound iR.2.1 iS.2.1) rfl)
  | _, _, .join R S, hg =>
    obtain ⟨hR, hS⟩ := gap_or hg
    have iR := compile_sound R hR η ρ hη; have iS := compile_sound S hS η ρ hη
    rw [Tm.gen]; exact (.node (join_sound iR.1 iS.1) (pjoin_sound iR.2.1 iS.2.1) rfl)
  | _, _, .diff R S, hg =>
    obtain ⟨hR, hS⟩ := gap_or hg
    have iR := compile_sound R hR η ρ hη; have iS := compile_sound S hS η ρ hη
    rw [Tm.gen]; dsimp only [Tm.dem]; revert iR iS; generalize R.gen η = r; generalize S.gen η = s
    generalize R.dem = d at r ⊢; generalize S.dem = e at s ⊢
    cases d <;> cases e <;> intro iR iS <;> first
      | exact (.node (diffB_sound iR.2.1 iS.2.1) (pdiff_sound iR.2.1 iS.2.1) rfl)
      | exact (.node (diff_sound iR.1 iS.1) (pdiff_sound iR.2.1 iS.2.1) rfl)
  | _, _, .pair R S, hg =>
    obtain ⟨hR, hS⟩ := gap_or hg
    rw [Tm.gen]; exact (Out.Sound.leaf (pair_sound (compile_sound R hR η ρ hη).1 (compile_sound S hS η ρ hη).1))
  | _, _, .prod R S, hg =>
    obtain ⟨hR, hS⟩ := gap_or hg
    rw [Tm.gen]; exact (Out.Sound.leaf (prod_sound (compile_sound R hR η ρ hη).1 (compile_sound S hS η ρ hη).1))
  | _, _, .junc R S, hg =>
    obtain ⟨hR, hS⟩ := gap_or hg
    rw [Tm.gen]; exact (Out.Sound.leaf (junc_sound (compile_sound R hR η ρ hη).1 (compile_sound S hS η ρ hη).1))
  | _, _, .foldr e S, hg =>
    obtain ⟨he, hS⟩ := gap_or hg
    rw [Tm.gen]; exact (Out.Sound.leaf (foldr_sound (compile_sound e he η ρ hη).1 (compile_sound S hS η ρ hη).1))
  | _, _, .fold e S, hg =>
    obtain ⟨he, hS⟩ := gap_or hg
    rw [Tm.gen]; exact (Out.Sound.leaf (fold_sound (compile_sound e he η ρ hη).1 (compile_sound S hS η ρ hη).1))
  | _, _, .foldI e S, hg =>
    obtain ⟨he, hS⟩ := gap_or hg
    rw [Tm.gen]; exact (Out.Sound.leaf (foldI_sound (compile_sound e he η ρ hη).1 (compile_sound S hS η ρ hη).1))
  | _, _, .ldiv R S U V, hg =>
    obtain ⟨hR, h⟩ := gap_or hg; obtain ⟨hS, h⟩ := gap_or h; obtain ⟨hU, hV⟩ := gap_or h
    have iR := compile_sound R hR η ρ hη; have iS := compile_sound S hS η ρ hη; have iU := compile_sound U hU η ρ hη; have iV := compile_sound V hV η ρ hη
    rw [Tm.gen]; exact (.node (ldivB_sound iR.2.1 iS.2.1 iU.1 iV.1) (pldiv_sound iR.2.1 iS.2.1 iU.1 iV.1) rfl)
  | _, _, .rdiv R S U V, hg =>
    obtain ⟨hR, h⟩ := gap_or hg; obtain ⟨hS, h⟩ := gap_or h; obtain ⟨hU, hV⟩ := gap_or h
    rw [Tm.gen]; exact (Out.Sound.leaf
      (rdiv_sound (compile_sound R hR η ρ hη).1 (compile_sound S hS η ρ hη).1 (compile_sound U hU η ρ hη).1 (compile_sound V hV η ρ hη).1))
  | _, _, .var _ k, hg => rw [Tm.gen]; exact (.node (ofPl_sound (hη k _ _)) (hη k _ _) rfl)
  | _, _, .own R, hg => rw [Tm.gen]; exact (compile_sound R hg η ρ hη)
  | _, _, .share k R, hg =>
    simp only [Tm.gap] at hg
    split at hg
    · rename_i hc
      have e := R.den_congr ρ Val.empty fun i hi => by simp [List.isEmpty_iff.1 hc] at hi
      have i := compile_sound R hg η ρ hη
      rw [e.1, funext e.2] at i
      rw [Tm.gen]; exact i
    · cases hg
  | _, _, .mu k w cap b, hg =>
    simp only [Tm.gap] at hg
    split at hg
    · rename_i hp
      rw [Tm.gen]; exact (Out.Sound.leaf (mu_sound (fun X Y h => Tm.den_mono hp h)
        fun X _ => (compile_sound b hg _ _ (hη.bindCode k (htab X))).1))
    · cases hg
  | _, _, .prim (A := A') (B := B') r, hg =>
    have hr : r.ok A' B' = true := by simpa [Tm.gap] using hg
    rw [Tm.gen]; refine ⟨Prim.fn_sound (fun f hf => Prim.run_sound (cs := []) (ss := []) hr trivial hf) true,
      pleaf_sound (Prim.fn_sound (fun f hf => Prim.run_sound (cs := []) (ss := []) hr trivial hf) true), ?_⟩
    intro r' cs e; cases e
    exact fun cs' ss hs f hf => Prim.run_sound hr hs hf
  | _, _, .arg (A := A') (B := B') (C := C) (D := D) f x, hg =>
    obtain ⟨hf, hx⟩ := gap_or hg
    have i := compile_sound f hf η ρ hη; have ix := compile_sound x hx η ρ hη
    rw [Tm.gen]
    dsimp only
    cases hrow : (f.gen η).row with
    | none => exact Out.Sound.leaf none'_sound
    | some p =>
      obtain ⟨r, cs⟩ := p
      have hcx : Code.Sound ⟨C, D, x.dem, (x.gen η).fn⟩ ⟨C, D, x.den ρ⟩ := fun X Y e' g h => by
        cases h; exact ⟨_, rfl, ix.1⟩
      have inv : ∀ cs' ss, Code.Sounds cs' ss →
          ∀ g, r.run A' B' ((cs ++ [⟨C, D, x.dem, (x.gen η).fn⟩]) ++ cs') = some g →
          Sound g (f.argDen ρ (⟨C, D, x.den ρ⟩ :: ss)) := fun cs' ss hs g hg => by
        rw [List.append_assoc] at hg
        exact i.2.2 r cs hrow (⟨C, D, x.dem, (x.gen η).fn⟩ :: cs') (⟨C, D, x.den ρ⟩ :: ss) ⟨hcx, hs⟩ g hg
      refine ⟨Prim.fn_sound (fun g hg => inv [] [] trivial g (by simpa using hg)) f.dem,
        pleaf_sound (Prim.fn_sound (fun g hg => inv [] [] trivial g (by simpa using hg)) f.dem), ?_⟩
      intro r' cs' e'; cases e'; exact inv
  | _, _, .nu k S b, hg =>
    simp only [Tm.gap] at hg
    split at hg
    · rename_i hp
      obtain ⟨hS, hb⟩ := gap_or hg
      rw [Tm.gen]; exact (Out.Sound.leaf (nu_sound (compile_sound S hS η ρ hη).1 (fun X Y h => Tm.den_mono hp h)
        fun X _ => (compile_sound b hb _ _ (hη.bindCode k (htab X))).1))
    · cases hg
  | _, _, .juncD R S, hg =>
    obtain ⟨hR, hS⟩ := gap_or hg
    rw [Tm.gen]; exact (Out.Sound.leaf (juncD_sound (compile_sound R hR η ρ hη).1 (compile_sound S hS η ρ hη).1))
  | _, _, .lam (A := A') (B := B') R, hg =>
    simp only [Tm.gap] at hg
    split at hg
    · rename_i hc
      obtain ⟨ho, hi⟩ := Rep.canonical_spec B' hc
      rw [Tm.gen]; exact (Out.Sound.leaf (lam_sound (compile_sound R hg η ρ hη).1 ho hi))
    · cases hg
  | _, _, .E (A := A') (B := B') R, hg =>
    simp only [Tm.gap] at hg
    split at hg
    · rename_i hc
      obtain ⟨ho, hi⟩ := Rep.canonical_spec B' hc
      rw [Tm.gen]; exact (Out.Sound.leaf (E_sound (compile_sound R hg η ρ hη).1 ho hi))
    · cases hg
  | _, _, .thin (B := B') Q, hg =>
    simp only [Tm.gap] at hg
    split at hg
    · rename_i hc
      simp only [Bool.and_eq_true] at hc
      obtain ⟨ho, hi⟩ := Rep.canonical_spec B' hc.1
      rw [Tm.gen]; exact (Out.Sound.leaf (thin_sound (compile_sound Q hg η ρ hη).1
        (fun p p' h => eq_of_heq (Q.cor_den hc.2 ρ p p' h)) ho hi))
    · cases hg
  | A', _, .hylo k w b, hg =>
    simp only [Tm.gap] at hg
    split at hg
    · rename_i c hc
      split at hg
      · rename_i hp
        -- the child is named as `Tm.gen` names it, `getD` of `kids`, which `hc` reads as `c`
        have := Tm.size_kids k A' b
        have e : (b.kids k A').getD .zero = c := by rw [hc]; rfl
        rw [Tm.gen]
        exact Out.Sound.leaf (hylo_sound (fun X Y h => Tm.den_mono hp h)
          (fun X Y a _ h => Tm.den_local k ρ X Y b c hc a (e ▸ h))
          (compile_sound _ (e ▸ Tm.gap_kids k _ b c hg hc) η ρ hη).1
          fun X _ => (compile_sound b hg _ _ (hη.bindCode k (htab X))).1)
      · cases hg
    · cases hg
  | _, _, .call .., hg => simp [Tm.gap] at hg
termination_by t.size
decreasing_by all_goals simp only [Tm.size] at *; omega

/-- The typed entry: `compile` with its soundness as the subtype's proof, on a term with no gap under an
    environment whose plans compute their variables' meanings. -/
def compileS (η : CodeEnv) (ρ : Val) (hη : η.Sound ρ) {A B : Obj} (t : Tm A B) (hw : t.gap = none) :
    {r : Rel A B // Gen.Sound r (t.den ρ)} :=
  ⟨compile η t, (compile_sound t hw η ρ hη).1⟩

end Rel.Lang
