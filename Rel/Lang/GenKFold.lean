import Rel.Lang.GenKBits

/-! The `GenK` ops of the value verbs and the folds (`arith`, `fold`), each representing its constructor's case of
    `Tm.den` from the op's `Tab` law, in `GenKSpec`'s style (`reps_iff`, `ofVals_sound`). -/

namespace Rel.Lang

open Rel Rel.Rep Rel.Kernel Rel.Verify Gen
open scoped Rel.Core.Rel
open Rel.Core.Rel hiding id comp recip inter union zero le inl inr junc

/-- **The round invariant of `Tab.foldRounds`**, for any peel and step given by their laws: `Pe r x r'` splits what is
left `r` of a key's array into the element `x` read now and the rest `r'` (`cons°` for `peelL`, `snoc°` for `peelR`),
`St k v x v'` is a round's step at the key `k`, and `W k r v w` says the rounds at `k` from value `v` on what is left
`r` end at `w` (`hW`, `hnil`). Then the answer holds `out` and, for each key, `W` from its value in `P` along its rest.
The rest is one per key (`hf`) and `P` keyed inside it (`hsub`); a `pack` keeps the rows (`hpack`). So a round
reads one element per key, and `hstep` is asked only there (`filter`'s keep-or-append step needs it). -/
theorem Tab.foldRounds_holds {K E V : Obj} {peel : Tab K (.arr E) → Except String (Tab K E × Tab K (.arr E))}
    {step : Tab K V → Tab K E → Except String (Tab K V)}
    (Pe : (Obj.arr E).El → E.El → (Obj.arr E).El → Prop) (St : K.El → V.El → E.El → V.El → Prop)
    (W : K.El → (Obj.arr E).El → V.El → V.El → Prop)
    (hPe : ∀ r x r' y r'', Pe r x r' → Pe r y r'' → x = y ∧ r' = r'')
    (hnil : ∀ k r, (¬∃ x r', Pe r x r') → ∀ v w, W k r v w ↔ w = v)
    (hW : ∀ k r x r' v w, Pe r x r' → (W k r v w ↔ ∃ v', St k v x v' ∧ W k r' v' w))
    (hpeel : ∀ rest el rest', peel rest = .ok (el, rest') →
      (∀ k x, el.Holds k x ↔ ∃ r r', rest.Holds k r ∧ Pe r x r') ∧
      ∀ k r', rest'.Holds k r' ↔ ∃ r x, rest.Holds k r ∧ Pe r x r')
    (hstep : ∀ P el T, step P el = .ok T → (∀ k x x', el.Holds k x → el.Holds k x' → x = x') →
      ∀ k v', T.Holds k v' ↔ ∃ v x, P.Holds k v ∧ el.Holds k x ∧ St k v x v')
    (hpack : ∀ R R' : Tab K V, R.pack = .ok R' → ∀ a b, R'.Holds a b ↔ R.Holds a b) :
    ∀ f rest P out res, Tab.foldRounds peel step f rest P out = .ok res →
      (∀ k r r', rest.Holds k r → rest.Holds k r' → r = r') → (∀ k v, P.Holds k v → ∃ r, rest.Holds k r) →
      ∀ k w, res.Holds k w ↔ out.Holds k w ∨ ∃ r v, rest.Holds k r ∧ P.Holds k v ∧ W k r v w := by
  intro f
  induction f with
  | zero => intro rest P out res h; simp [Tab.foldRounds] at h
  | succ f ih =>
    intro rest P out res h hf hsub k w
    simp only [Tab.foldRounds] at h
    by_cases h0 : P.n = 0
    · rw [if_pos (by simp [h0])] at h
      cases h
      have np : ∀ k v, ¬ P.Holds k v := fun _ _ ⟨i, _⟩ => by have := i.2; simp [h0] at this
      exact ⟨Or.inl, fun h => h.elim id fun ⟨_, v, _, hv, _⟩ => (np _ _ hv).elim⟩
    rw [if_neg (by simpa using h0)] at h
    simp only [bind, Except.bind_eq_ok'] at h
    obtain ⟨_, -, ⟨el, rest'⟩, hp, h⟩ := h
    simp only [bind, Except.bind_eq_ok'] at h
    obtain ⟨s, hs, P', hP', d, hd, c, hc, df, hdf, u, hu, o', ho', h⟩ := h
    obtain ⟨hel, hrest'⟩ := hpeel _ _ _ hp
    have hel1 : ∀ k x x', el.Holds k x → el.Holds k x' → x = x' := fun k x x' hx hx' => by
      obtain ⟨r₁, _, hr₁, hp₁⟩ := (hel k x).1 hx
      obtain ⟨r₂, _, hr₂, hp₂⟩ := (hel k x').1 hx'
      rw [hf k _ _ hr₁ hr₂] at hp₁
      exact (hPe _ _ _ _ _ hp₁ hp₂).1
    have hP'h : ∀ k v', P'.Holds k v' ↔ ∃ v x, P.Holds k v ∧ el.Holds k x ∧ St k v x v' :=
      fun k v' => (hpack _ _ hP' k v').trans (hstep _ _ _ hs hel1 k v')
    have ho : ∀ k w, o'.Holds k w ↔ out.Holds k w ∨ (P.Holds k w ∧ ¬ ∃ x, el.Holds k x) := by
      intro k w
      rw [hpack _ _ ho', Tab.union_holds hu, Tab.diff_holds hdf, Tab.comp_holds hc]
      simp only [Tab.dom_holds hd]
      exact or_congr Iff.rfl (and_congr_right fun hw => not_congr
        ⟨fun ⟨_, ⟨rfl, x, hx⟩, _⟩ => ⟨x, hx⟩, fun ⟨x, hx⟩ => ⟨k, ⟨rfl, x, hx⟩, hw⟩⟩)
    have hf' : ∀ k r r', rest'.Holds k r → rest'.Holds k r' → r = r' := by
      intro k a b ha hb
      obtain ⟨r₁, x₁, h₁, p₁⟩ := (hrest' k a).1 ha
      obtain ⟨r₂, x₂, h₂, p₂⟩ := (hrest' k b).1 hb
      rw [hf k _ _ h₁ h₂] at p₁
      exact (hPe _ _ _ _ _ p₁ p₂).2
    have hsub' : ∀ k v, P'.Holds k v → ∃ r, rest'.Holds k r := by
      intro k v hv
      obtain ⟨_, x, _, hx, _⟩ := (hP'h k v).1 hv
      obtain ⟨r, r', hr, hp⟩ := (hel k x).1 hx
      exact ⟨r', (hrest' k r').2 ⟨r, x, hr, hp⟩⟩
    rw [ih _ _ _ _ h hf' hsub' k w, ho, or_assoc]
    refine or_congr Iff.rfl ⟨?_, ?_⟩
    · rintro (⟨hw, hn⟩ | ⟨r', v', hr', hv', hW'⟩)
      · obtain ⟨r, hr⟩ := hsub k w hw
        have hnp : ¬∃ x r', Pe r x r' := fun ⟨x, r', hp⟩ => hn ⟨x, (hel k x).2 ⟨r, r', hr, hp⟩⟩
        exact ⟨r, w, hr, hw, (hnil k r hnp w w).2 rfl⟩
      · obtain ⟨v, x, hv, hx, hs⟩ := (hP'h k v').1 hv'
        obtain ⟨r₁, x₁, hr₁, hp₁⟩ := (hrest' k r').1 hr'
        obtain ⟨r, r'', hr, hp⟩ := (hel k x).1 hx
        rw [hf k _ _ hr₁ hr] at hp₁
        obtain ⟨rfl, rfl⟩ := hPe _ _ _ _ _ hp hp₁
        exact ⟨r, v, hr, hv, (hW k _ _ _ _ _ hp).2 ⟨v', hs, hW'⟩⟩
    · rintro ⟨r, v, hr, hv, hWr⟩
      by_cases hp : ∃ x r', Pe r x r'
      · obtain ⟨x, r', hp⟩ := hp
        obtain ⟨v', hs, hW'⟩ := (hW k _ _ _ _ _ hp).1 hWr
        exact Or.inr ⟨r', v', (hrest' k r').2 ⟨r, x, hr, hp⟩,
          (hP'h k v').2 ⟨v, x, hv, (hel k x).2 ⟨r, r', hr, hp⟩, hs⟩, hW'⟩
      · obtain rfl := (hnil k r hp v w).1 hWr
        refine Or.inl ⟨hv, fun ⟨x, hx⟩ => ?_⟩
        obtain ⟨r₁, r', hr₁, hp₁⟩ := (hel k x).1 hx
        rw [hf k _ _ hr₁ hr] at hp₁
        exact hp ⟨x, r', hp₁⟩

/-- **The left fold peeled at its head** (`cons°`): a chain from `Te` on `x :: xs` is a first value `v` from `Te`, one
step to `v'`, and a chain from `v'` on `xs`. It is `foldRounds_holds`'s `hW` for `peelL`, with `W r v = foldDen (= v) TS r`. -/
theorem foldDen_cons {E V : Obj} (Te : Den V V) (TS : Den (.prod V E) V) (x : E.El) (xs : List E.El) (w : V.El) :
    foldDen Te TS (x :: xs) w ↔ ∃ v v', (∃ a, Te a v) ∧ TS (v, x) v' ∧ foldDen (fun _ b => b = v') TS xs w := by
  constructor
  · rintro ⟨_ | ⟨v, ys⟩, hy, ⟨a, ha⟩, hS, rfl⟩
    · simp at hy
    · simp only [List.length_cons, Nat.add_right_cancel_iff] at hy
      exact ⟨v, ys[0]'(by omega), ⟨a, ha⟩, hS 0 (by simp), ys, hy, ⟨v, rfl⟩,
        fun t ht => hS (t + 1) (by simp; omega), rfl⟩
  · rintro ⟨v, v', ⟨a, ha⟩, hs, ys, hy, ⟨_, h0⟩, hS, rfl⟩
    refine ⟨v :: ys, by simp [hy], ⟨a, ha⟩, fun t ht => ?_, rfl⟩
    cases t with
    | zero => simpa [h0] using hs
    | succ t => exact hS t (by simpa using ht)

/-- The left fold of no elements from the value `v` is `v`. -/
theorem foldDen_nil {E V : Obj} (TS : Den (.prod V E) V) (v w : V.El) :
    foldDen (fun _ b => b = v) TS [] w ↔ w = v :=
  ⟨fun ⟨_, _, ⟨_, h0⟩, _, hw⟩ => hw.trans h0,
    fun hw => ⟨[v], rfl, ⟨v, rfl⟩, fun _ ht => absurd ht (Nat.not_lt_zero _), hw⟩⟩

/-- The right fold of no elements from the value `v` is `v`. -/
theorem foldrDen_nil {E V : Obj} (TS : Den (.prod E V) V) (v w : V.El) :
    foldrDen (fun _ b => b = v) TS [] w ↔ w = v :=
  ⟨fun ⟨_, _, ⟨_, h0⟩, _, hw⟩ => hw.trans h0,
    fun hw => ⟨[v], rfl, ⟨v, rfl⟩, fun _ ht => absurd ht (Nat.not_lt_zero _), hw⟩⟩

/-- A left fold from `Te` is one from a value `v` of `Te`'s range. -/
theorem foldDen_start {E V : Obj} (Te : Den V V) (TS : Den (.prod V E) V) (xs : List E.El) (w : V.El) :
    foldDen Te TS xs w ↔ ∃ v, (∃ a, Te a v) ∧ foldDen (fun _ b => b = v) TS xs w :=
  ⟨fun ⟨ys, hy, h0, hS, hw⟩ => ⟨_, h0, ys, hy, ⟨w, rfl⟩, hS, hw⟩,
    fun ⟨_, ⟨a, ha⟩, ys, hy, ⟨_, h0⟩, hS, hw⟩ => ⟨ys, hy, ⟨a, h0 ▸ ha⟩, hS, hw⟩⟩

/-- A right fold from `Te` is one from a value `v` of `Te`'s range. -/
theorem foldrDen_start {E V : Obj} (Te : Den V V) (TS : Den (.prod E V) V) (xs : List E.El) (w : V.El) :
    foldrDen Te TS xs w ↔ ∃ v, (∃ a, Te a v) ∧ foldrDen (fun _ b => b = v) TS xs w :=
  ⟨fun ⟨ys, hy, h0, hS, hw⟩ => ⟨_, h0, ys, hy, ⟨w, rfl⟩, hS, hw⟩,
    fun ⟨_, ⟨a, ha⟩, ys, hy, ⟨_, h0⟩, hS, hw⟩ => ⟨ys, hy, ⟨a, h0 ▸ ha⟩, hS, hw⟩⟩

/-- **The right fold peeled at its last element** (`snoc°`): a chain from `Te` on `xs ++ [x]` is a first value `v`
from `Te`, one step `TS (x, v)` to `v'`, and a chain from `v'` on `xs` (the mirror of `foldDen_cons`). -/
theorem foldrDen_snoc {E V : Obj} (Te : Den V V) (TS : Den (.prod E V) V) (x : E.El) (xs : List E.El) (w : V.El) :
    foldrDen Te TS (xs ++ [x]) w ↔
      ∃ v v', (∃ a, Te a v) ∧ TS (x, v) v' ∧ foldrDen (fun _ b => b = v') TS xs w := by
  have hl : (xs ++ [x]).length = xs.length + 1 := by simp
  constructor
  · rintro ⟨ys, hy, ⟨a, ha⟩, hS, rfl⟩
    have g : ∀ i j (hi : i < ys.length) (hj : j < ys.length), i = j → ys[i] = ys[j] := by
      intro i j _ _ h; subst h; rfl
    have hT := hS xs.length (by omega)
    simp only [List.getElem_concat_length] at hT
    refine ⟨ys[xs.length + 1]'(by omega), ys[xs.length]'(by omega),
      ⟨a, (g _ _ (by omega) (by omega) hl) ▸ ha⟩, hT, ys.take (xs.length + 1),
      by simp only [List.length_take]; omega, ⟨a, by simp⟩, fun t ht => ?_, by simp⟩
    have h := hS t (by omega)
    simp only [List.getElem_take]
    rwa [List.getElem_append_left ht] at h
  · rintro ⟨v, v', ⟨a, ha⟩, hs, ys, hy, ⟨_, h0⟩, hS, rfl⟩
    refine ⟨ys ++ [v], by simp [hy], ⟨a, by simpa [hy] using ha⟩, fun t ht => ?_,
      (List.getElem_append_left (by omega)).symm⟩
    have ht' : t < xs.length + 1 := by simpa using ht
    rcases Nat.lt_or_ge t xs.length with h | h
    · have e := hS t h
      simp only [List.getElem_append_left h, List.getElem_append_left (show t + 1 < ys.length by omega),
        List.getElem_append_left (show t < ys.length by omega)]
      exact e
    · obtain rfl : t = xs.length := by omega
      simp only [List.getElem_concat_length, List.getElem_append_left (show xs.length < ys.length by omega), h0]
      simpa [hy] using hs

/-- **A left fold whose step keeps the index `c`** (`foldI`'s round, the step met with the key's index `Q`): from
`(c, v)` it ends at `(c, w)` where the left fold at `c` from `v` ends at `w`. -/
theorem foldDen_fibre {I E V : Obj} (TS : Den (.prod (.prod I V) E) (.prod I V)) (Q : I.El → Prop) (c : I.El)
    (hQ : ∀ a, Q a ↔ a = c) (r : List E.El) : ∀ (v : V.El) (w : (Obj.prod I V).El),
    foldDen (fun _ b => b = (c, v)) (fun q q' => TS (q.1, q.2) q' ∧ Q q'.1) r w ↔
      w.1 = c ∧ foldDen (fun _ b => b = v) (fun q v' => TS ((c, q.1), q.2) (c, v')) r w.2 := by
  induction r with
  | nil =>
    intro v w
    rw [foldDen_nil, foldDen_nil]
    exact ⟨fun h => by subst h; exact ⟨rfl, rfl⟩, fun ⟨h1, h2⟩ => Prod.ext h1 h2⟩
  | cons x r ih =>
    intro v w
    rw [foldDen_cons, foldDen_cons]
    constructor
    · rintro ⟨_, ⟨c', v'⟩, ⟨_, rfl⟩, ⟨hs, hq⟩, hr⟩
      obtain rfl : c' = c := (hQ c').1 hq
      obtain ⟨h1, h2⟩ := (ih v' w).1 hr
      exact ⟨h1, v, v', ⟨v, rfl⟩, hs, h2⟩
    · rintro ⟨h1, _, v', ⟨_, rfl⟩, hs, hr⟩
      exact ⟨(c, _), (c, v'), ⟨w, rfl⟩, ⟨hs, (hQ c).2 rfl⟩, (ih v' w).2 ⟨h1, hr⟩⟩

/-- **`foldRounds` by `peelL` is the left fold of the step**: `foldRounds_holds` at `Pe = cons°`, `W` the left fold
(`foldDen`) of `St k` from the value it is given. -/
theorem Tab.foldRoundsL_holds {K E V : Obj} {step : Tab K V → Tab K E → Except String (Tab K V)}
    (St : K.El → V.El → E.El → V.El → Prop)
    (hstep : ∀ P el T, step P el = .ok T → (∀ k x x', el.Holds k x → el.Holds k x' → x = x') →
      ∀ k v', T.Holds k v' ↔ ∃ v x, P.Holds k v ∧ el.Holds k x ∧ St k v x v') :
    ∀ f rest P out res, Tab.foldRounds Tab.peelL step f rest P out = .ok res →
      (∀ k r r', rest.Holds k r → rest.Holds k r' → r = r') → (∀ k v, P.Holds k v → ∃ r, rest.Holds k r) →
      ∀ k w, res.Holds k w ↔ out.Holds k w ∨
        ∃ r v, rest.Holds k r ∧ P.Holds k v ∧ foldDen (fun _ b => b = v) (fun q v' => St k q.1 q.2 v') r w :=
  Tab.foldRounds_holds (fun r x r' => r = x :: r') St
    (fun k r v w => foldDen (fun _ b => b = v) (fun q v' => St k q.1 q.2 v') r w)
    (fun _ _ _ _ _ h₁ h₂ => List.cons.inj (h₁.symm.trans h₂))
    (fun _ r hr v w => match r, hr with
      | [], _ => foldDen_nil _ v w
      | x :: r', hr => (hr ⟨x, r', rfl⟩).elim)
    (fun _ _ x r' v w (hp : _ = x :: r') => by
      subst hp
      exact (foldDen_cons _ _ x r' w).trans ⟨fun ⟨_, v', ⟨_, h0⟩, hs, h⟩ => ⟨v', h0 ▸ hs, h⟩,
        fun ⟨v', hs, h⟩ => ⟨v, v', ⟨v, rfl⟩, hs, h⟩⟩)
    (fun _ _ _ hp => Tab.peelL_holds hp) hstep (fun _ _ hp => Tab.pack_holds hp)

/-- **`foldRounds` by `peelR` is the right fold of the step**: `foldRounds_holds` at `Pe = snoc°`, `W` the right fold
(`foldrDen`) of `St k` from the value it is given. -/
theorem Tab.foldRoundsR_holds {K E V : Obj} {step : Tab K V → Tab K E → Except String (Tab K V)}
    (St : K.El → V.El → E.El → V.El → Prop)
    (hstep : ∀ P el T, step P el = .ok T → (∀ k x x', el.Holds k x → el.Holds k x' → x = x') →
      ∀ k v', T.Holds k v' ↔ ∃ v x, P.Holds k v ∧ el.Holds k x ∧ St k v x v') :
    ∀ f rest P out res, Tab.foldRounds Tab.peelR step f rest P out = .ok res →
      (∀ k r r', rest.Holds k r → rest.Holds k r' → r = r') → (∀ k v, P.Holds k v → ∃ r, rest.Holds k r) →
      ∀ k w, res.Holds k w ↔ out.Holds k w ∨
        ∃ r v, rest.Holds k r ∧ P.Holds k v ∧ foldrDen (fun _ b => b = v) (fun q v' => St k q.2 q.1 v') r w :=
  Tab.foldRounds_holds (fun r x r' => r = r' ++ [x]) St
    (fun k r v w => foldrDen (fun _ b => b = v) (fun q v' => St k q.2 q.1 v') r w)
    (fun _ _ _ _ _ h₁ h₂ => by
      obtain ⟨h, h'⟩ := List.append_inj' (h₁.symm.trans h₂) rfl
      exact ⟨(List.cons.inj h').1, h⟩)
    (fun _ r hr v w => by
      by_cases h0 : r = []
      · subst h0; exact foldrDen_nil _ v w
      · exact (hr ⟨r.getLast h0, r.dropLast, (List.dropLast_concat_getLast h0).symm⟩).elim)
    (fun _ _ x r' v w (hp : _ = r' ++ [x]) => by
      subst hp
      exact (foldrDen_snoc _ _ x r' w).trans ⟨fun ⟨_, v', ⟨_, h0⟩, hs, h⟩ => ⟨v', h0 ▸ hs, h⟩,
        fun ⟨v', hs, h⟩ => ⟨v, v', ⟨v, rfl⟩, hs, h⟩⟩)
    (fun _ _ _ hp => Tab.peelR_holds hp) hstep (fun _ _ hp => Tab.pack_holds hp)

namespace GenK

/-- `arith(k)` on `U`'s universe: the keys' coreflexive `D`, then `D ≫ arithDen k U` (`Tab.arith_holds`). -/
theorem arith_sound {k : UInt8} {U : Rel .long .long} {TU : Core.Rel Int64 Int64} (hU : ∀ K, U.Reps K TU) :
    ∀ K, (GenK.arith k U).Reps K (arithDen k TU) := by
  unfold GenK.arith after
  exact ofVals_sound fun _ _ _ _ hK h x w hx _ => by
    obtain ⟨D, hD, h⟩ := bind_ok h
    obtain ⟨u, hu, ht⟩ := bind_ok h
    rw [agrees_empty ((reps_iff _ _ _).1 (hU {}) u hu)]
    refine (Tab.arith_holds ht x w).trans
      ⟨fun ⟨v, hv, h⟩ => ?_, fun h => ⟨x, (Tab.idU_holds hD x x).2 ⟨rfl, (side_some hK x).1 hx⟩, h⟩⟩
    obtain ⟨rfl, -⟩ := (Tab.idU_holds hD x v).1 hv; exact h

/-- A round's step `compT (r ≫ S)` on the pairs `r` of `P` and `el` (`⟨P, el⟩` or `⟨el, P⟩`): the pairs related by
`S`'s meaning `TS`. -/
theorem pairStep_holds {K C D B : Obj} {S : Rel (.prod C D) B} {TS : Den (.prod C D) B} (hS : ∀ K, S.Reps K TS)
    (wS : S.Wf) {L : Tab K C} {M : Tab K D} {T : Tab K B} (hT : (compT (L.pair M) S).runE {} = .ok T) (k : K.El)
    (b : B.El) : T.Holds k b ↔ ∃ c d, L.Holds k c ∧ M.Holds k d ∧ TS (c, d) b :=
  ((reps_iff _ _ _).1 (compT_sound (r' := L.pair M) (K := {}) (X := rpair L.Holds M.Holds)
      (fun _ hp a q _ _ => Tab.pair_holds hp a q) hS wS) T hT k b rfl rfl).trans
    ⟨fun ⟨q, ⟨h1, h2⟩, h3⟩ => ⟨q.1, q.2, h1, h2, h3⟩, fun ⟨c, d, h1, h2, h3⟩ => ⟨(c, d), ⟨h1, h2⟩, h3⟩⟩

/-- `⦇e,S⦈` on the arrays in demand: `foldRoundsL_holds` from `idU X` (each array whole) and `top X e` (each value
of `e`), the step `TS (v, x)`. -/
theorem fold_sound {E V : Obj} {d : Bool} {e : Rel V V} {S : Rel (.prod V E) V} {Te : Den V V}
    {TS : Den (.prod V E) V} (he : ∀ K, e.Reps K Te) (hS : ∀ K, S.Reps K TS) (wS : S.Wf) :
    ∀ K, (GenK.fold E V d e S).Reps K (foldDen Te TS) :=
  ofVals_sound fun _ _ X t hK h xs w hx _ => by
    obtain ⟨r, hr, h⟩ := bind_ok h
    obtain ⟨te, hte, h⟩ := bind_ok h
    obtain ⟨P, hP, h⟩ := bind_ok h
    obtain ⟨z, hz, h⟩ := bind_ok h
    have ee := (reps_iff _ _ _).1 (he {}) te hte
    have hX := (side_some hK xs).1 hx
    refine (Tab.foldRoundsL_holds (fun _ v x v' => TS (v, x) v')
      (fun P el T hT _ k v' => (pairStep_holds hS wS hT k v')) _ _ _ _ _ h
      (fun k a b ha hb => ((Tab.idU_holds hr k a).1 ha).1.symm.trans ((Tab.idU_holds hr k b).1 hb).1)
      (fun k v hv => ⟨k, (Tab.idU_holds hr k k).2 ⟨rfl, ((Tab.top_holds hP k v).1 hv).1⟩⟩) xs w).trans ?_
    rw [Tab.zero_holds hz, false_or, foldDen_start]
    constructor
    · rintro ⟨r', v, hr', hv, hW⟩
      obtain ⟨rfl, -⟩ := (Tab.idU_holds hr xs r').1 hr'
      obtain ⟨-, j, hj⟩ := (Tab.top_holds hP xs v).1 hv
      exact ⟨v, ⟨_, (ee _ _ rfl rfl).1 ⟨j, rfl, hj⟩⟩, hW⟩
    · rintro ⟨v, ⟨a, ha⟩, hW⟩
      obtain ⟨j, -, hj⟩ := (ee a v rfl rfl).2 ha
      exact ⟨xs, v, (Tab.idU_holds hr xs xs).2 ⟨rfl, hX⟩, (Tab.top_holds hP xs v).2 ⟨hX, j, hj⟩, hW⟩

/-- `⦇e,S⦈ʳ` on the arrays in demand: `foldRoundsR_holds` from `idU X` and `top X e`, the step `TS (x, v)`. -/
theorem foldr_sound {E V : Obj} {d : Bool} {e : Rel V V} {S : Rel (.prod E V) V} {Te : Den V V}
    {TS : Den (.prod E V) V} (he : ∀ K, e.Reps K Te) (hS : ∀ K, S.Reps K TS) (wS : S.Wf) :
    ∀ K, (GenK.foldr E V d e S).Reps K (foldrDen Te TS) :=
  ofVals_sound fun _ _ X t hK h xs w hx _ => by
    obtain ⟨r, hr, h⟩ := bind_ok h
    obtain ⟨te, hte, h⟩ := bind_ok h
    obtain ⟨P, hP, h⟩ := bind_ok h
    obtain ⟨z, hz, h⟩ := bind_ok h
    have ee := (reps_iff _ _ _).1 (he {}) te hte
    have hX := (side_some hK xs).1 hx
    refine (Tab.foldRoundsR_holds (fun _ v x v' => TS (x, v) v')
      (fun P el T hT _ k v' => (pairStep_holds hS wS hT k v').trans
        ⟨fun ⟨x, v, h1, h2, h3⟩ => ⟨v, x, h2, h1, h3⟩, fun ⟨v, x, h1, h2, h3⟩ => ⟨x, v, h2, h1, h3⟩⟩)
      _ _ _ _ _ h
      (fun k a b ha hb => ((Tab.idU_holds hr k a).1 ha).1.symm.trans ((Tab.idU_holds hr k b).1 hb).1)
      (fun k v hv => ⟨k, (Tab.idU_holds hr k k).2 ⟨rfl, ((Tab.top_holds hP k v).1 hv).1⟩⟩) xs w).trans ?_
    rw [Tab.zero_holds hz, false_or, foldrDen_start]
    constructor
    · rintro ⟨r', v, hr', hv, hW⟩
      obtain ⟨rfl, -⟩ := (Tab.idU_holds hr xs r').1 hr'
      obtain ⟨-, j, hj⟩ := (Tab.top_holds hP xs v).1 hv
      exact ⟨v, ⟨_, (ee _ _ rfl rfl).1 ⟨j, rfl, hj⟩⟩, hW⟩
    · rintro ⟨v, ⟨a, ha⟩, hW⟩
      obtain ⟨j, -, hj⟩ := (ee a v rfl rfl).2 ha
      exact ⟨xs, v, (Tab.idU_holds hr xs xs).2 ⟨rfl, hX⟩, (Tab.top_holds hP xs v).2 ⟨hX, j, hj⟩, hW⟩

/-- `⦇e,S⦈` given a family on the pairs `p = (i, xs)` in demand: `foldRoundsL_holds` on the carrier `I×V`, the step
`TS` met with the key's index (`St p q x q' = TS (q, x) q' ∧ q'.1 = p.1`), from `(p.1, b)` with `b` from `e` at `p.1`;
`foldDen_fibre` reads it as the fold at `p.1`. -/
theorem foldI_sound {I E V : Obj} {d d' : Bool} {e : Rel I (.prod V V)} {S : Rel (.prod (.prod I V) E) (.prod I V)}
    {Te : Den I (.prod V V)} {TS : Den (.prod (.prod I V) E) (.prod I V)} (he : ∀ K, e.Reps K Te) (we : e.Wf)
    (hS : ∀ K, S.Reps K TS) (wS : S.Wf) : ∀ K, (GenK.foldI I E V d d' e S).Reps K (foldIDen Te TS) :=
  ofVals_sound fun _ _ X t hK h p v hp _ => by
    obtain ⟨i, hi, h⟩ := bind_ok h
    obtain ⟨es, hes, h⟩ := bind_ok h
    dsimp only at h
    obtain ⟨rest, hrest, h⟩ := bind_ok h
    obtain ⟨o1, ho1, h⟩ := bind_ok h
    obtain ⟨c1, hc1, h⟩ := bind_ok h
    obtain ⟨P, hP, h⟩ := bind_ok h
    obtain ⟨z, hz, h⟩ := bind_ok h
    obtain ⟨out, hout, h⟩ := bind_ok h
    obtain ⟨o2, ho2, h⟩ := bind_ok h
    have hX := (side_some hK p).1 hp
    have ees := (reps_iff _ _ _).1 (compT_sound (r' := .ok i) (K := {}) (X := i.Holds)
      (fun _ h' _ _ _ _ => by cases h'; exact Iff.rfl) he we) es hes
    have hip : ∀ k a, i.Holds k a ↔ (∃ j, X.row j = k) ∧ a = k.1 := fun k a => Tab.outl_holds hi k a
    have hout' := Tab.foldRoundsL_holds (fun k q x q' => TS (q, x) q' ∧ i.Holds k q'.1)
      (fun P el T hT _ k q' => by
        obtain ⟨s, hs, hT⟩ := bind_ok hT
        obtain ⟨o, ho, hT⟩ := bind_ok hT
        obtain ⟨c, hc, hT⟩ := bind_ok hT
        obtain ⟨pr, hpr, hT⟩ := bind_ok hT
        have hsq := pairStep_holds hS wS hs k
        rw [Tab.inter_holds hT, Tab.pair_holds hpr, hsq]
        constructor
        · rintro ⟨⟨a, x, h1, h2, h3⟩, hi1, -⟩; exact ⟨a, x, h1, h2, h3, hi1⟩
        · rintro ⟨a, x, h1, h2, h3, hi1⟩
          have hs' : s.Holds k q' := (hsq q').2 ⟨a, x, h1, h2, h3⟩
          obtain ⟨j, -, hj⟩ := _root_.id hs'
          exact ⟨⟨a, x, h1, h2, h3⟩, hi1,
            (Tab.comp_holds hc k q'.2).2 ⟨q', hs', (Tab.outr_holds ho q' q'.2).2 ⟨⟨j, hj⟩, rfl⟩⟩⟩)
      _ _ _ _ _ hout
      (fun k a b ha hb => ((Tab.outr_holds hrest k a).1 ha).2.trans ((Tab.outr_holds hrest k b).1 hb).2.symm)
      (fun k q hq => ⟨k.2, (Tab.outr_holds hrest k k.2).2
        ⟨((hip k q.1).1 ((Tab.pair_holds hP k q).1 hq).1).1, rfl⟩⟩) p
    have hQ : ∀ a, i.Holds p a ↔ a = p.1 := fun a => (hip p a).trans (and_iff_right hX)
    refine (Tab.comp_holds h p v).trans (Iff.trans ?_ (foldDen_start _ _ p.2 v).symm)
    constructor
    · rintro ⟨w, hw, ho⟩
      obtain ⟨-, rfl⟩ := (Tab.outr_holds ho2 w v).1 ho
      rcases (hout' w).1 hw with hz' | ⟨r, ⟨q1, q2⟩, hr', hq, hW⟩
      · exact ((Tab.zero_holds hz p w).1 hz').elim
      obtain ⟨-, rfl⟩ := (Tab.outr_holds hrest p r).1 hr'
      obtain ⟨hq1, hq2⟩ := (Tab.pair_holds hP p (q1, q2)).1 hq
      obtain rfl : q1 = p.1 := (hQ q1).1 hq1
      obtain ⟨⟨a0, b0⟩, hq0, ho'⟩ := (Tab.comp_holds hc1 p q2).1 hq2
      obtain ⟨-, rfl⟩ := (Tab.outr_holds ho1 _ q2).1 ho'
      obtain ⟨a, ha, hTe⟩ := (ees p _ rfl rfl).1 hq0
      obtain rfl := (hQ a).1 ha
      exact ⟨_, ⟨a0, hTe⟩, ((foldDen_fibre TS (i.Holds p) p.1 hQ p.2 _ w).1 hW).2⟩
    · rintro ⟨b0, ⟨a0, ha0⟩, hW⟩
      have hes' : es.Holds p (a0, b0) := (ees p _ rfl rfl).2 ⟨p.1, (hQ _).2 rfl, ha0⟩
      obtain ⟨j, -, hj⟩ := _root_.id hes'
      have hw : out.Holds p (p.1, v) := (hout' _).2 (Or.inr ⟨p.2, (p.1, b0),
        (Tab.outr_holds hrest p p.2).2 ⟨hX, rfl⟩,
        (Tab.pair_holds hP p _).2 ⟨(hQ _).2 rfl,
          (Tab.comp_holds hc1 p b0).2 ⟨(a0, b0), hes', (Tab.outr_holds ho1 _ b0).2 ⟨⟨j, hj⟩, rfl⟩⟩⟩,
        (foldDen_fibre TS (i.Holds p) p.1 hQ p.2 b0 (p.1, v)).2 ⟨rfl, hW⟩⟩)
      obtain ⟨jo, -, hjo⟩ := _root_.id hw
      exact ⟨(p.1, v), hw, (Tab.outr_holds ho2 _ v).2 ⟨⟨jo, hjo⟩, rfl⟩⟩

end GenK

/-- The left fold from `c` along `ys` is the iteration `rowDens` states for `loop`: states `g 0 = c`, each step
`TF (g t, ys[t]) (g (t+1))`, ending at `g |ys|`. -/
theorem foldDen_iter {X Y : Obj} (TF : Den (.prod X Y) X) :
    ∀ (ys : List Y.El) (c w : X.El), foldDen (fun _ b => b = c) TF ys w ↔
      ∃ g : Nat → X.El, g 0 = c ∧ (∀ t (ht : t < ys.length), TF (g t, ys[t]'ht) (g (t + 1))) ∧ w = g ys.length
  | [], c, w => by
    rw [foldDen_nil]
    exact ⟨fun h => ⟨fun _ => c, rfl, fun _ ht => absurd ht (Nat.not_lt_zero _), h⟩,
      fun ⟨_, h0, _, hw⟩ => hw.trans h0⟩
  | y :: ys, c, w => by
    rw [foldDen_cons]
    constructor
    · rintro ⟨v, v', ⟨_, hv⟩, hs, h⟩
      obtain ⟨g, h0, hg, hw⟩ := (foldDen_iter TF ys v' w).1 h
      refine ⟨fun | 0 => c | t + 1 => g t, rfl, fun t ht => ?_, hw⟩
      cases t with
      | zero => obtain rfl : v = c := hv; show TF (v, y) (g 0); rw [h0]; exact hs
      | succ t => exact hg t (Nat.lt_of_succ_lt_succ ht)
    · rintro ⟨g, h0, hg, hw⟩
      refine ⟨c, g 1, ⟨c, rfl⟩, h0 ▸ hg 0 (Nat.zero_lt_succ _), (foldDen_iter TF ys (g 1) w).2
        ⟨fun t => g (t + 1), rfl, fun t ht => hg (t + 1) (Nat.succ_lt_succ ht), hw⟩⟩

/-- **`P ≫ loop(F)`** (`Tab.loop`), its step `F` given the pairs `D` a round meets acting as `D ≫ TF`: each `(c, ys)`
of `P` to the left fold of `TF` along `ys` from `c` (`foldRoundsL_holds`, keyed by `ran P`). -/
theorem Tab.loop_holds {K X Y : Obj} {F : Tab (.prod X Y) (.prod X Y) → Except String (Tab (.prod X Y) X)}
    {TF : Den (.prod X Y) X} (hF : ∀ D T, F D = .ok T → ∀ q x, T.Holds q x ↔ ∃ q', D.Holds q q' ∧ TF q' x)
    {P : Tab K (.prod X (.arr Y))} {res : Tab K X} (h : Tab.loop F P = .ok res) (k : K.El) (c : X.El) :
    res.Holds k c ↔ ∃ p : (Obj.prod X (.arr Y)).El, P.Holds k p ∧ foldDen (fun _ b => b = p.1) TF p.2 c := by
  unfold Tab.loop at h
  obtain ⟨D, hD, h⟩ := GenK.bind_ok h
  obtain ⟨o1, ho1, h⟩ := GenK.bind_ok h
  obtain ⟨rest, hrest, h⟩ := GenK.bind_ok h
  obtain ⟨o2, ho2, h⟩ := GenK.bind_ok h
  obtain ⟨P0, hP0, h⟩ := GenK.bind_ok h
  obtain ⟨z, hz, h⟩ := GenK.bind_ok h
  obtain ⟨fr, hfr, h⟩ := GenK.bind_ok h
  have hrest' : ∀ p r, rest.Holds p r ↔ (∃ x, P.Holds x p) ∧ r = p.2 := fun p r => by
    rw [Tab.comp_holds hrest]
    constructor
    · rintro ⟨b, hb, ho⟩
      obtain ⟨rfl, hx⟩ := (Tab.ran_holds hD p b).1 hb
      exact ⟨hx, ((Tab.outr_holds ho1 p r).1 ho).2⟩
    · rintro ⟨hx, rfl⟩
      have hb := (Tab.ran_holds hD p p).2 ⟨rfl, hx⟩
      obtain ⟨i, -, hi⟩ := hb
      exact ⟨p, (Tab.ran_holds hD p p).2 ⟨rfl, hx⟩, (Tab.outr_holds ho1 p p.2).2 ⟨⟨i, hi⟩, rfl⟩⟩
  have hP0' : ∀ p v, P0.Holds p v ↔ (∃ x, P.Holds x p) ∧ v = p.1 := fun p v => by
    rw [Tab.comp_holds hP0]
    constructor
    · rintro ⟨b, hb, ho⟩
      obtain ⟨rfl, hx⟩ := (Tab.ran_holds hD p b).1 hb
      exact ⟨hx, ((Tab.outl_holds ho2 p v).1 ho).2⟩
    · rintro ⟨hx, rfl⟩
      have hb := (Tab.ran_holds hD p p).2 ⟨rfl, hx⟩
      obtain ⟨i, -, hi⟩ := hb
      exact ⟨p, (Tab.ran_holds hD p p).2 ⟨rfl, hx⟩, (Tab.outl_holds ho2 p p.1).2 ⟨⟨i, hi⟩, rfl⟩⟩
  have hfr' := Tab.foldRoundsL_holds (fun _ v x v' => TF (v, x) v') (fun S el T hT _ k v' => by
      obtain ⟨p, hp, hT⟩ := GenK.bind_ok hT
      obtain ⟨Dp, hDp, hT⟩ := GenK.bind_ok hT
      obtain ⟨T', hT', hT⟩ := GenK.bind_ok hT
      rw [Tab.comp_holds hT]
      constructor
      · rintro ⟨q, hq, hTq⟩
        obtain ⟨q', hd, hq'⟩ := (hF _ _ hT' q v').1 hTq
        obtain ⟨rfl, -⟩ := (Tab.ran_holds hDp q q').1 hd
        obtain ⟨h1, h2⟩ := (Tab.pair_holds hp k q).1 hq
        exact ⟨q.1, q.2, h1, h2, hq'⟩
      · rintro ⟨v, x, h1, h2, h3⟩
        have hq := (Tab.pair_holds hp k (v, x)).2 ⟨h1, h2⟩
        exact ⟨(v, x), hq, (hF _ _ hT' _ v').2 ⟨(v, x), (Tab.ran_holds hDp _ _).2 ⟨rfl, k, hq⟩, h3⟩⟩)
    _ _ _ _ _ hfr (fun p a b ha hb => ((hrest' p a).1 ha).2.trans ((hrest' p b).1 hb).2.symm)
    (fun p v hv => ⟨p.2, (hrest' p p.2).2 ⟨((hP0' p v).1 hv).1, rfl⟩⟩)
  rw [Tab.comp_holds h]
  refine exists_congr fun p => and_congr_right fun hp => ?_
  rw [hfr', Tab.zero_holds hz, false_or]
  constructor
  · rintro ⟨r, v, hr, hv, hW⟩
    obtain ⟨-, rfl⟩ := (hrest' p r).1 hr
    obtain ⟨-, rfl⟩ := (hP0' p v).1 hv
    exact hW
  · exact fun hW => ⟨p.2, p.1, (hrest' p p.2).2 ⟨⟨k, hp⟩, rfl⟩, (hP0' p p.1).2 ⟨⟨k, hp⟩, rfl⟩, hW⟩

open Classical in
/-- **`filter(p)` on the cells `X`** (`Tab.filter`): each array of `X` to its elements that are keys of `P`, in
order; a round appends `x` where `x ∈ dom P` and keeps `acc` otherwise (`foldRoundsL_holds`, one `x` per key). -/
theorem Tab.filter_holds {B : Obj} {n : USize} {P : Tab B B} {X : Vals (.arr B) n} {res : Tab (.arr B) (.arr B)}
    (h : Tab.filter P X = .ok res) (xs ys : List B.El) :
    res.Holds xs ys ↔ (∃ i, X.row i = xs) ∧ ys = xs.filter fun x => decide (∃ y, P.Holds x y) := by
  unfold Tab.filter at h
  obtain ⟨D, hD, h⟩ := GenK.bind_ok h
  obtain ⟨rest, hrest, h⟩ := GenK.bind_ok h
  obtain ⟨P0, hP0, h⟩ := GenK.bind_ok h
  obtain ⟨z, hz, h⟩ := GenK.bind_ok h
  have hfold : ∀ (ws v w : List B.El), foldDen (E := B) (V := .arr B) (fun _ b => b = v)
      (fun q v' => ((∃ y, P.Holds q.2 y) ∧ v' = q.1 ++ [q.2]) ∨ ((¬∃ y, P.Holds q.2 y) ∧ v' = q.1)) ws w ↔
      w = v ++ ws.filter fun x => decide (∃ y, P.Holds x y) := by
    intro ws
    induction ws with
    | nil => intro v w; rw [foldDen_nil]; simp
    | cons x ws ih =>
      intro v w
      rw [foldDen_cons]
      constructor
      · rintro ⟨_, v', ⟨_, rfl⟩, hs, hw⟩
        rw [ih] at hw; subst hw
        rcases hs with ⟨hy, rfl⟩ | ⟨hn, rfl⟩
        · simp [List.filter_cons, hy]
        · simp [List.filter_cons, hn]
      · intro hw; subst hw
        by_cases hx : ∃ y, P.Holds x y
        · exact ⟨v, v ++ [x], ⟨v, rfl⟩, Or.inl ⟨hx, rfl⟩, (ih _ _).2 (by simp [List.filter_cons, hx])⟩
        · exact ⟨v, v, ⟨v, rfl⟩, Or.inr ⟨hx, rfl⟩, (ih _ _).2 (by simp [List.filter_cons, hx])⟩
  have hfr := Tab.foldRoundsL_holds
    (fun _ v x v' => ((∃ y, P.Holds x y) ∧ v' = v ++ [x]) ∨ ((¬∃ y, P.Holds x y) ∧ v' = v))
    (fun S el T hT hu k v' => by
      obtain ⟨kk, hk, hT⟩ := GenK.bind_ok hT
      obtain ⟨pk, hpk, hT⟩ := GenK.bind_ok hT
      obtain ⟨s, hs, hT⟩ := GenK.bind_ok hT
      obtain ⟨ed, hed, hT⟩ := GenK.bind_ok hT
      obtain ⟨kd, hkd, hT⟩ := GenK.bind_ok hT
      obtain ⟨df, hdf, hT⟩ := GenK.bind_ok hT
      obtain ⟨c, hc, hT⟩ := GenK.bind_ok hT
      have hkk : ∀ b, kk.Holds k b ↔ el.Holds k b ∧ ∃ y, P.Holds b y := fun b => by
        rw [Tab.comp_holds hk]
        exact ⟨fun ⟨x, hx, hd⟩ => by obtain ⟨rfl, hy⟩ := (Tab.dom_holds hD x b).1 hd; exact ⟨hx, hy⟩,
          fun ⟨hx, hy⟩ => ⟨b, hx, (Tab.dom_holds hD b b).2 ⟨rfl, hy⟩⟩⟩
      have hdf' : ∀ k', df.Holds k k' ↔ k = k' ∧ (∃ x, el.Holds k x) ∧ ¬∃ x, kk.Holds k x := fun k' => by
        rw [Tab.diff_holds hdf, Tab.dom_holds hed, Tab.dom_holds hkd]
        exact ⟨fun ⟨⟨e, hx⟩, hn⟩ => ⟨e, hx, fun hy => hn ⟨e, hy⟩⟩, fun ⟨e, hx, hn⟩ => ⟨⟨e, hx⟩, fun ⟨_, hy⟩ => hn hy⟩⟩
      rw [Tab.union_holds hT, Tab.snoc_holds hs, Tab.comp_holds hc]
      constructor
      · rintro (⟨p, hp, rfl⟩ | ⟨k', hd, hv⟩)
        · obtain ⟨hv, hb⟩ := (Tab.pair_holds hpk k p).1 hp
          obtain ⟨hx, hy⟩ := (hkk _).1 hb
          exact ⟨p.1, p.2, hv, hx, Or.inl ⟨hy, rfl⟩⟩
        · obtain ⟨rfl, ⟨x, hx⟩, hn⟩ := (hdf' k').1 hd
          exact ⟨v', x, hv, hx, Or.inr ⟨fun hy => hn ⟨x, (hkk x).2 ⟨hx, hy⟩⟩, rfl⟩⟩
      · rintro ⟨v, x, hv, hx, ⟨hy, rfl⟩ | ⟨hn, rfl⟩⟩
        · exact Or.inl ⟨(v, x), (Tab.pair_holds hpk k (v, x)).2 ⟨hv, (hkk x).2 ⟨hx, hy⟩⟩, rfl⟩
        · refine Or.inr ⟨k, (hdf' k).2 ⟨rfl, ⟨x, hx⟩, fun ⟨b, hb⟩ => ?_⟩, hv⟩
          obtain ⟨hb', hy⟩ := (hkk b).1 hb
          obtain rfl := hu k x b hx hb'
          exact hn hy)
    _ _ _ _ _ h
    (fun k a b ha hb => ((Tab.idU_holds hrest k a).1 ha).1.symm.trans ((Tab.idU_holds hrest k b).1 hb).1)
    (fun k v hv => ⟨k, (Tab.idU_holds hrest k k).2 ⟨rfl, ((Tab.nil_holds hP0 k v).1 hv).1⟩⟩)
  rw [hfr, Tab.zero_holds hz, false_or]
  constructor
  · rintro ⟨r, v, hr, hv, hW⟩
    obtain ⟨rfl, hi⟩ := (Tab.idU_holds hrest xs r).1 hr
    obtain ⟨-, rfl⟩ := (Tab.nil_holds hP0 xs v).1 hv
    exact ⟨hi, by simpa using (hfold _ _ _).1 hW⟩
  · rintro ⟨hi, rfl⟩
    exact ⟨xs, [], (Tab.idU_holds hrest xs xs).2 ⟨rfl, hi⟩, (Tab.nil_holds hP0 xs []).2 ⟨hi, rfl⟩,
      (hfold _ _ _).2 (by simp)⟩

/-- **`concat` on the cells of cells `X`** (`Tab.flatten`): each array of arrays of `X` to their concatenation, the
left fold of `cat` from `[]` (`foldRoundsL_holds`). -/
theorem Tab.flatten_holds {B : Obj} {n : USize} {X : Vals (.arr (.arr B)) n} {res : Tab (.arr (.arr B)) (.arr B)}
    (h : Tab.flatten X = .ok res) (xss : List (List B.El)) (ys : List B.El) :
    res.Holds xss ys ↔ (∃ i, X.row i = xss) ∧ ys = xss.flatten := by
  unfold Tab.flatten at h
  obtain ⟨rest, hrest, h⟩ := GenK.bind_ok h
  obtain ⟨P0, hP0, h⟩ := GenK.bind_ok h
  obtain ⟨z, hz, h⟩ := GenK.bind_ok h
  have hfold : ∀ (ws : List (List B.El)) (v w : List B.El), foldDen (E := .arr B) (V := .arr B)
      (fun _ b => b = v) (fun q v' => v' = q.1 ++ q.2) ws w ↔ w = v ++ ws.flatten := by
    intro ws
    induction ws with
    | nil => intro v w; rw [foldDen_nil]; simp
    | cons x ws ih =>
      intro v w
      rw [foldDen_cons]
      constructor
      · rintro ⟨_, v', ⟨_, rfl⟩, rfl, hw⟩; rw [ih] at hw; subst hw; simp
      · intro hw; subst hw; exact ⟨v, v ++ x, ⟨v, rfl⟩, rfl, (ih _ _).2 (by simp)⟩
  have hfr := Tab.foldRoundsL_holds (fun _ v x v' => v' = v ++ x)
    (fun S el T hT _ k v' => by
      obtain ⟨p, hp, hT⟩ := GenK.bind_ok hT
      rw [Tab.cat_holds hT]
      constructor
      · rintro ⟨q, hq, rfl⟩; obtain ⟨h1, h2⟩ := (Tab.pair_holds hp k q).1 hq; exact ⟨q.1, q.2, h1, h2, rfl⟩
      · rintro ⟨v, x, h1, h2, rfl⟩; exact ⟨(v, x), (Tab.pair_holds hp k (v, x)).2 ⟨h1, h2⟩, rfl⟩)
    _ _ _ _ _ h
    (fun k a b ha hb => ((Tab.idU_holds hrest k a).1 ha).1.symm.trans ((Tab.idU_holds hrest k b).1 hb).1)
    (fun k v hv => ⟨k, (Tab.idU_holds hrest k k).2 ⟨rfl, ((Tab.nil_holds hP0 k v).1 hv).1⟩⟩)
  rw [hfr, Tab.zero_holds hz, false_or]
  constructor
  · rintro ⟨r, v, hr, hv, hW⟩
    obtain ⟨rfl, hi⟩ := (Tab.idU_holds hrest xss r).1 hr
    obtain ⟨-, rfl⟩ := (Tab.nil_holds hP0 xss v).1 hv
    exact ⟨hi, by simpa using (hfold _ _ _).1 hW⟩
  · rintro ⟨hi, rfl⟩
    exact ⟨xss, [], (Tab.idU_holds hrest xss xss).2 ⟨rfl, hi⟩, (Tab.nil_holds hP0 xss []).2 ⟨hi, rfl⟩,
      (hfold _ _ _).2 (by simp)⟩

namespace GenK

open Classical in
/-- `filter(p)`, `Expand.primE`'s fit of the row (`elems`, `Tab.filter`): each array in demand to its elements in
`dom T`, `p` run knowing its domain is those elements, where it agrees with its meaning `T`. -/
theorem filter_sound {B : Obj} {d : Bool} {R : Rel B B} {T : Den B B} (hR : ∀ K, R.Reps K T) :
    ∀ K, (GenK.elems B B (.arr B) d R fun P X => Tab.filter P X).Reps K
      (fun xs ys => ys = xs.filter fun x => decide (∃ y, T x y)) := by
  unfold GenK.elems
  exact ofVals_sound fun _ _ X t hK h xs ys hx _ => by
    obtain ⟨M, hM, h⟩ := bind_ok h
    obtain ⟨k, hk, h⟩ := bind_ok h
    obtain ⟨P, hP, h⟩ := bind_ok h
    have hi := (side_some hK xs).1 hx
    have ha := (reps_iff _ _ _).1 (hR ⟨some ⟨k.n, k.key⟩, none⟩) P hP
    have hPT : ∀ x ∈ xs, (∃ y, P.Holds x y) ↔ ∃ y, T x y := fun x hm => by
      obtain ⟨j, hj, -⟩ := (Tab.ran_holds hk x x).2 ⟨rfl, xs, (Tab.mem_holds hM xs x).2 ⟨hi, hm⟩⟩
      exact exists_congr fun y => ha x y ((side_some rfl x).2 ⟨j, hj⟩) rfl
    show t.Holds xs ys ↔ _
    rw [Tab.filter_holds h, and_iff_right hi, List.filter_congr fun x hm => decide_eq_decide.2 (hPT x hm)]

/-- `loop(F)`, `Expand.primE`'s fit of the row (`stepAfter`, `Tab.loop`): each `(c, ys)` in demand to the states
of `rowDens`' `loop` iteration of `F`'s meaning `TF`, `F` run on the pairs each round meets (`compT_sound`). -/
theorem loop_sound {X Y : Obj} {d : Bool} {F : Rel (.prod X Y) X} {TF : Den (.prod X Y) X}
    (hF : ∀ K, F.Reps K TF) (wF : F.Wf) :
    ∀ K, (GenK.stepAfter (.prod X Y) X (.prod X (.arr Y)) X d F fun F P => Tab.loop F P).Reps K
      (fun p c => ∃ g : Nat → X.El, g 0 = p.1 ∧
        (∀ t (ht : t < p.2.length), TF (g t, p.2[t]'ht) (g (t + 1))) ∧ c = g p.2.length) := by
  have hF' : ∀ (D : Tab (.prod X Y) (.prod X Y)) T, (compT (.ok D) F).runE {} = .ok T →
      ∀ q x, T.Holds q x ↔ ∃ q', D.Holds q q' ∧ TF q' x := fun D T hT q x =>
    (reps_iff _ _ _).1 (compT_sound (r' := .ok D) (K := {}) (X := rep D)
      (fun _ hr a b _ _ => by cases hr; exact Iff.rfl) hF wF) T hT q x rfl rfl
  unfold GenK.stepAfter GenK.after
  exact ofVals_sound fun _ _ V t hK h p c hx _ => by
    obtain ⟨D, hD, h⟩ := bind_ok h
    refine (Tab.loop_holds hF' h p c).trans ?_
    rw [← foldDen_iter]
    constructor
    · rintro ⟨p', hp', hW⟩; obtain ⟨rfl, -⟩ := (Tab.idU_holds hD p p').1 hp'; exact hW
    · exact fun hW => ⟨p, (Tab.idU_holds hD p p).2 ⟨rfl, (side_some hK p).1 hx⟩, hW⟩

end GenK

end Rel.Lang
