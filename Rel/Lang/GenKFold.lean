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
reads one element per key, and `hstep` is asked only there (`filter`'s keep-or-append step needs it). `I k r v`, kept
by a round (`hI`), holds of every value at `k` with its rest, so `hstep` sees only states `I` admits: `merge`'s and
`thinL`'s steps read all the states of a key together and are right only where `I` makes that state one. -/
theorem Tab.foldRounds_holds {K E V : Obj} {peel : Tab K (.arr E) → Except String (Tab K E × Tab K (.arr E))}
    {step : Tab K V → Tab K E → Except String (Tab K V)}
    (Pe : (Obj.arr E).El → E.El → (Obj.arr E).El → Prop) (St : K.El → V.El → E.El → V.El → Prop)
    (W : K.El → (Obj.arr E).El → V.El → V.El → Prop) (I : K.El → (Obj.arr E).El → V.El → Prop)
    (hPe : ∀ r x r' y r'', Pe r x r' → Pe r y r'' → x = y ∧ r' = r'')
    (hnil : ∀ k r, (¬∃ x r', Pe r x r') → ∀ v w, W k r v w ↔ w = v)
    (hW : ∀ k r x r' v w, Pe r x r' → (W k r v w ↔ ∃ v', St k v x v' ∧ W k r' v' w))
    (hI : ∀ k r x r' v v', I k r v → Pe r x r' → St k v x v' → I k r' v')
    (hpeel : ∀ rest el rest', peel rest = .ok (el, rest') →
      (∀ k x, el.Holds k x ↔ ∃ r r', rest.Holds k r ∧ Pe r x r') ∧
      ∀ k r', rest'.Holds k r' ↔ ∃ r x, rest.Holds k r ∧ Pe r x r')
    (hpeelw : ∀ r p, peel r = .ok p → r.WF → p.1.WF ∧ p.2.WF)
    (hstepw : ∀ P el t, step P el = .ok t → P.WF → el.WF → t.WF)
    (hstep : ∀ P el T, step P el = .ok T → P.WF → el.WF → (∀ k x x', el.Holds k x → el.Holds k x' → x = x') →
      (∀ k v, P.Holds k v → ∃ r, ((∃ x, el.Holds k x) ↔ ∃ x r', Pe r x r') ∧ ∀ v', P.Holds k v' → I k r v') →
      ∀ k v', T.Holds k v' ↔ ∃ v x, P.Holds k v ∧ el.Holds k x ∧ St k v x v')
    (hpack : ∀ R R' : Tab K V, R.pack = .ok R' → ∀ a b, R'.Holds a b ↔ R.Holds a b) :
    ∀ f rest P out res, Tab.foldRounds peel step f rest P out = .ok res → rest.WF → P.WF →
      (∀ k r r', rest.Holds k r → rest.Holds k r' → r = r') → (∀ k v, P.Holds k v → ∃ r, rest.Holds k r ∧ I k r v) →
      ∀ k w, res.Holds k w ↔ out.Holds k w ∨ ∃ r v, rest.Holds k r ∧ P.Holds k v ∧ W k r v w := by
  intro f
  induction f with
  | zero => intro rest P out res h; simp [Tab.foldRounds] at h
  | succ f ih =>
    intro rest P out res h wr wP hf hsub k w
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
    obtain ⟨wel, wr'⟩ := hpeelw _ _ hp wr
    have hel1 : ∀ k x x', el.Holds k x → el.Holds k x' → x = x' := fun k x x' hx hx' => by
      obtain ⟨r₁, _, hr₁, hp₁⟩ := (hel k x).1 hx
      obtain ⟨r₂, _, hr₂, hp₂⟩ := (hel k x').1 hx'
      rw [hf k _ _ hr₁ hr₂] at hp₁
      exact (hPe _ _ _ _ _ hp₁ hp₂).1
    -- every state of a key meets the invariant at that key's one rest, whose head is the key's element
    have hPI : ∀ k v, P.Holds k v → ∃ r, ((∃ x, el.Holds k x) ↔ ∃ x r', Pe r x r') ∧ ∀ v', P.Holds k v' → I k r v' :=
      fun k v hv => by
        obtain ⟨r, hr, -⟩ := hsub k v hv
        refine ⟨r, ⟨fun ⟨x, hx⟩ => ?_, fun ⟨x, r', hp⟩ => ⟨x, (hel k x).2 ⟨r, r', hr, hp⟩⟩⟩, fun v' hv' => ?_⟩
        · obtain ⟨r₁, r', hr₁, hp⟩ := (hel k x).1 hx; rw [hf k _ _ hr₁ hr] at hp; exact ⟨x, r', hp⟩
        · obtain ⟨r₁, hr₁, hi⟩ := hsub k v' hv'; rw [hf k _ _ hr₁ hr] at hi; exact hi
    have hP'h : ∀ k v', P'.Holds k v' ↔ ∃ v x, P.Holds k v ∧ el.Holds k x ∧ St k v x v' :=
      fun k v' => (hpack _ _ hP' k v').trans (hstep _ _ _ hs wP wel hel1 hPI k v')
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
    have hsub' : ∀ k v, P'.Holds k v → ∃ r, rest'.Holds k r ∧ I k r v := by
      intro k v hv
      obtain ⟨v₀, x, hv₀, hx, hs⟩ := (hP'h k v).1 hv
      obtain ⟨r, r', hr, hp⟩ := (hel k x).1 hx
      obtain ⟨r₀, hr₀, hi⟩ := hsub k v₀ hv₀
      rw [hf k _ _ hr₀ hr] at hi
      exact ⟨r', (hrest' k r').2 ⟨r, x, hr, hp⟩, hI k r x r' v₀ v hi hp hs⟩
    rw [ih _ _ _ _ h wr' (Tab.pack_wf hP' (hstepw _ _ _ hs wP wel)) hf' hsub' k w, ho, or_assoc]
    refine or_congr Iff.rfl ⟨?_, ?_⟩
    · rintro (⟨hw, hn⟩ | ⟨r', v', hr', hv', hW'⟩)
      · obtain ⟨r, hr, -⟩ := hsub k w hw
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
    (St : K.El → V.El → E.El → V.El → Prop) (I : K.El → (Obj.arr E).El → V.El → Prop)
    (hI : ∀ k x r v v', I k (x :: r) v → St k v x v' → I k r v')
    (hstepw : ∀ P el t, step P el = .ok t → P.WF → el.WF → t.WF)
    (hstep : ∀ P el T, step P el = .ok T → P.WF → el.WF → (∀ k x x', el.Holds k x → el.Holds k x' → x = x') →
      (∀ k v, P.Holds k v → ∃ r, ((∃ x, el.Holds k x) ↔ r ≠ []) ∧ ∀ v', P.Holds k v' → I k r v') →
      ∀ k v', T.Holds k v' ↔ ∃ v x, P.Holds k v ∧ el.Holds k x ∧ St k v x v') :
    ∀ f rest P out res, Tab.foldRounds Tab.peelL step f rest P out = .ok res → rest.WF → P.WF →
      (∀ k r r', rest.Holds k r → rest.Holds k r' → r = r') → (∀ k v, P.Holds k v → ∃ r, rest.Holds k r ∧ I k r v) →
      ∀ k w, res.Holds k w ↔ out.Holds k w ∨
        ∃ r v, rest.Holds k r ∧ P.Holds k v ∧ foldDen (fun _ b => b = v) (fun q v' => St k q.1 q.2 v') r w :=
  Tab.foldRounds_holds (fun r x r' => r = x :: r') St
    (fun k r v w => foldDen (fun _ b => b = v) (fun q v' => St k q.1 q.2 v') r w) I
    (fun _ _ _ _ _ h₁ h₂ => List.cons.inj (h₁.symm.trans h₂))
    (fun _ r hr v w => match r, hr with
      | [], _ => foldDen_nil _ v w
      | x :: r', hr => (hr ⟨x, r', rfl⟩).elim)
    (fun _ _ x r' v w (hp : _ = x :: r') => by
      subst hp
      exact (foldDen_cons _ _ x r' w).trans ⟨fun ⟨_, v', ⟨_, h0⟩, hs, h⟩ => ⟨v', h0 ▸ hs, h⟩,
        fun ⟨v', hs, h⟩ => ⟨v, v', ⟨v, rfl⟩, hs, h⟩⟩)
    (fun k _ x r' v v' hi (hp : _ = x :: r') hs => hI k x r' v v' (hp ▸ hi) hs)
    (fun _ _ _ hp => Tab.peelL_holds hp) (fun _ _ => Tab.peelL_wf) hstepw
    (fun P el T h wP wel hu hP => hstep P el T h wP wel hu fun k v hv => by
      obtain ⟨r, he, hall⟩ := hP k v hv
      refine ⟨r, he.trans ⟨fun ⟨x, r', hp⟩ => by rw [hp]; exact List.cons_ne_nil _ _, fun hne => ?_⟩, hall⟩
      cases r with
      | nil => exact (hne rfl).elim
      | cons x r' => exact ⟨x, r', rfl⟩)
    (fun _ _ hp => Tab.pack_holds hp)

/-- **`foldRounds` by `peelR` is the right fold of the step**: `foldRounds_holds` at `Pe = snoc°`, `W` the right fold
(`foldrDen`) of `St k` from the value it is given. -/
theorem Tab.foldRoundsR_holds {K E V : Obj} {step : Tab K V → Tab K E → Except String (Tab K V)}
    (St : K.El → V.El → E.El → V.El → Prop) (I : K.El → (Obj.arr E).El → V.El → Prop)
    (hI : ∀ k x r v v', I k (r ++ [x]) v → St k v x v' → I k r v')
    (hstepw : ∀ P el t, step P el = .ok t → P.WF → el.WF → t.WF)
    (hstep : ∀ P el T, step P el = .ok T → P.WF → el.WF → (∀ k x x', el.Holds k x → el.Holds k x' → x = x') →
      (∀ k v, P.Holds k v → ∃ r, ((∃ x, el.Holds k x) ↔ r ≠ []) ∧ ∀ v', P.Holds k v' → I k r v') →
      ∀ k v', T.Holds k v' ↔ ∃ v x, P.Holds k v ∧ el.Holds k x ∧ St k v x v') :
    ∀ f rest P out res, Tab.foldRounds Tab.peelR step f rest P out = .ok res → rest.WF → P.WF →
      (∀ k r r', rest.Holds k r → rest.Holds k r' → r = r') → (∀ k v, P.Holds k v → ∃ r, rest.Holds k r ∧ I k r v) →
      ∀ k w, res.Holds k w ↔ out.Holds k w ∨
        ∃ r v, rest.Holds k r ∧ P.Holds k v ∧ foldrDen (fun _ b => b = v) (fun q v' => St k q.2 q.1 v') r w :=
  Tab.foldRounds_holds (fun r x r' => r = r' ++ [x]) St
    (fun k r v w => foldrDen (fun _ b => b = v) (fun q v' => St k q.2 q.1 v') r w) I
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
    (fun k _ x r' v v' hi (hp : _ = r' ++ [x]) hs => hI k x r' v v' (hp ▸ hi) hs)
    (fun _ _ _ hp => Tab.peelR_holds hp) (fun _ _ => Tab.peelR_wf) hstepw
    (fun P el T h wP wel hu hP => hstep P el T h wP wel hu fun k v hv => by
      obtain ⟨r, he, hall⟩ := hP k v hv
      refine ⟨r, he.trans ⟨fun ⟨x, r', hp⟩ => by rw [hp]; simp, fun hne => ?_⟩, hall⟩
      exact ⟨r.getLast hne, r.dropLast, (List.dropLast_concat_getLast hne).symm⟩)
    (fun _ _ hp => Tab.pack_holds hp)

namespace GenK

/-- `arith t k` on `U`'s universe: the keys' coreflexive `D`, then `D ≫ arithDen t k U` (`Tab.arith_holds`). -/
theorem arith_sound {t : QAtomicType} {k : UInt8} {U : Rel (.atom t) (.atom t)}
    {TU : Core.Rel (Obj.atom t).El (Obj.atom t).El} (hU : ∀ K, K.WF → U.Reps K TU) :
    ∀ K, K.WF → (GenK.arith t k U).Reps K (arithDen t k TU) := by
  unfold GenK.arith after
  exact ofVals_sound fun _ _ _ _ hK _ h x w hx _ _ => by
    obtain ⟨D, hD, ht⟩ := bind_ok h
    have hu : ∀ n (X : Vals (.atom t) n) t, U.runE ⟨some ⟨n, X⟩, none, none⟩ = .ok t → ∀ a v, (∃ i, X.row i = a) →
        (t.Holds a v ↔ TU a v) := fun n X t h a v ha =>
      (reps_iff _ _ _).1 (hU ⟨some ⟨n, X⟩, none, none⟩ ⟨trivial, trivial, trivial⟩) t h a v ((side_some rfl a).2 ha) rfl
        trivial
    refine (Tab.arith_holds hu ht x w).trans
      ⟨fun ⟨v, hv, h⟩ => ?_, fun h => ⟨x, (Tab.idU_holds hD x x).2 ⟨rfl, (side_some hK x).1 hx⟩, h⟩⟩
    obtain ⟨rfl, -⟩ := (Tab.idU_holds hD x v).1 hv; exact h

/-- A round's step `compT (r ≫ S)` on the pairs `r` of `P` and `el` (`⟨P, el⟩` or `⟨el, P⟩`): the pairs related by
`S`'s meaning `TS`. -/
theorem pairStep_holds {K C D B : Obj} {S : Rel (.prod C D) B} {TS : Den (.prod C D) B}
    (hS : ∀ K, K.WF → S.Reps K TS) (wS : S.Wf) {L : Tab K C} {M : Tab K D} {T : Tab K B} (wL : L.WF) (wM : M.WF)
    (hT : (compT (L.pair M) S).runE {} = .ok T) (k : K.El) (b : B.El) :
    T.Holds k b ↔ ∃ c d, L.Holds k c ∧ M.Holds k d ∧ TS (c, d) b :=
  ((reps_iff _ _ _).1 (compT_sound (r' := L.pair M) (K := {}) (X := rpair L.Holds M.Holds)
      (fun _ hp a q _ _ _ => Tab.pair_holds hp a q) hS wS Known.wf_empty (fun _ hp => Tab.pair_wf hp wL wM))
      T hT k b rfl rfl trivial).trans
    ⟨fun ⟨q, ⟨h1, h2⟩, h3⟩ => ⟨q.1, q.2, h1, h2, h3⟩, fun ⟨c, d, h1, h2, h3⟩ => ⟨(c, d), ⟨h1, h2⟩, h3⟩⟩

/-- The table of a round's step `compT (r ≫ S)` on the pairs `r` of `WF` tables is `WF`. -/
theorem pairStep_wf {K C D B : Obj} {S : Rel (.prod C D) B} (wS : S.Wf) {L : Tab K C} {M : Tab K D} {T : Tab K B}
    (wL : L.WF) (wM : M.WF) (hT : (compT (L.pair M) S).runE {} = .ok T) : T.WF :=
  (compT_wf (r' := L.pair M) (fun _ hp => Tab.pair_wf hp wL wM) wS).runE Known.wf_empty hT

/-- `⦇e,S⦈` on the arrays in demand: `foldRoundsL_holds` from `idU X` (each array whole) and `top X e` (each value
of `e`), the step `TS (v, x)`. -/
theorem fold_sound {E V : Obj} {d : Bool} {e : Rel V V} {S : Rel (.prod V E) V} {Te : Den V V}
    {TS : Den (.prod V E) V} (he : ∀ K, K.WF → e.Reps K Te) (we : e.Wf) (hS : ∀ K, K.WF → S.Reps K TS)
    (wS : S.Wf) : ∀ K, K.WF → (GenK.fold E V d e S).Reps K (foldDen Te TS) :=
  ofVals_sound fun _ _ X t hK wX h xs w hx _ _ => by
    obtain ⟨r, hr, h⟩ := bind_ok h
    obtain ⟨te, hte, h⟩ := bind_ok h
    obtain ⟨P, hP, h⟩ := bind_ok h
    obtain ⟨z, hz, h⟩ := bind_ok h
    have ee := (reps_iff _ _ _).1 (he {} Known.wf_empty) te hte
    have hX := (side_some hK xs).1 hx
    refine (Tab.foldRoundsL_holds (fun _ v x v' => TS (v, x) v')
      (fun _ _ _ => True) (fun _ _ _ _ _ _ _ => trivial) (fun _ _ _ hT wP wel => pairStep_wf wS wP wel hT)
      (fun P el T hT wP wel _ _ k v' => (pairStep_holds hS wS wP wel hT k v')) _ _ _ _ _ h
      (Tab.idU_wf hr wX) (Tab.top_wf hP wX (we.runE Known.wf_empty hte).2)
      (fun k a b ha hb => ((Tab.idU_holds hr k a).1 ha).1.symm.trans ((Tab.idU_holds hr k b).1 hb).1)
      (fun k v hv => ⟨k, (Tab.idU_holds hr k k).2 ⟨rfl, ((Tab.top_holds hP k v).1 hv).1⟩, trivial⟩) xs w).trans ?_
    rw [Tab.zero_holds hz, false_or, foldDen_start]
    constructor
    · rintro ⟨r', v, hr', hv, hW⟩
      obtain ⟨rfl, -⟩ := (Tab.idU_holds hr xs r').1 hr'
      obtain ⟨-, j, hj⟩ := (Tab.top_holds hP xs v).1 hv
      exact ⟨v, ⟨_, (ee _ _ rfl rfl trivial).1 ⟨j, rfl, hj⟩⟩, hW⟩
    · rintro ⟨v, ⟨a, ha⟩, hW⟩
      obtain ⟨j, -, hj⟩ := (ee a v rfl rfl trivial).2 ha
      exact ⟨xs, v, (Tab.idU_holds hr xs xs).2 ⟨rfl, hX⟩, (Tab.top_holds hP xs v).2 ⟨hX, j, hj⟩, hW⟩

/-- `⦇e,S⦈ʳ` on the arrays in demand: `foldRoundsR_holds` from `idU X` and `top X e`, the step `TS (x, v)`. -/
theorem foldr_sound {E V : Obj} {d : Bool} {e : Rel V V} {S : Rel (.prod E V) V} {Te : Den V V}
    {TS : Den (.prod E V) V} (he : ∀ K, K.WF → e.Reps K Te) (we : e.Wf) (hS : ∀ K, K.WF → S.Reps K TS)
    (wS : S.Wf) : ∀ K, K.WF → (GenK.foldr E V d e S).Reps K (foldrDen Te TS) :=
  ofVals_sound fun _ _ X t hK wX h xs w hx _ _ => by
    obtain ⟨r, hr, h⟩ := bind_ok h
    obtain ⟨te, hte, h⟩ := bind_ok h
    obtain ⟨P, hP, h⟩ := bind_ok h
    obtain ⟨z, hz, h⟩ := bind_ok h
    have ee := (reps_iff _ _ _).1 (he {} Known.wf_empty) te hte
    have hX := (side_some hK xs).1 hx
    refine (Tab.foldRoundsR_holds (fun _ v x v' => TS (x, v) v')
      (fun _ _ _ => True) (fun _ _ _ _ _ _ _ => trivial) (fun _ _ _ hT wP wel => pairStep_wf wS wel wP hT)
      (fun P el T hT wP wel _ _ k v' => (pairStep_holds hS wS wel wP hT k v').trans
        ⟨fun ⟨x, v, h1, h2, h3⟩ => ⟨v, x, h2, h1, h3⟩, fun ⟨v, x, h1, h2, h3⟩ => ⟨x, v, h2, h1, h3⟩⟩)
      _ _ _ _ _ h (Tab.idU_wf hr wX) (Tab.top_wf hP wX (we.runE Known.wf_empty hte).2)
      (fun k a b ha hb => ((Tab.idU_holds hr k a).1 ha).1.symm.trans ((Tab.idU_holds hr k b).1 hb).1)
      (fun k v hv => ⟨k, (Tab.idU_holds hr k k).2 ⟨rfl, ((Tab.top_holds hP k v).1 hv).1⟩, trivial⟩) xs w).trans ?_
    rw [Tab.zero_holds hz, false_or, foldrDen_start]
    constructor
    · rintro ⟨r', v, hr', hv, hW⟩
      obtain ⟨rfl, -⟩ := (Tab.idU_holds hr xs r').1 hr'
      obtain ⟨-, j, hj⟩ := (Tab.top_holds hP xs v).1 hv
      exact ⟨v, ⟨_, (ee _ _ rfl rfl trivial).1 ⟨j, rfl, hj⟩⟩, hW⟩
    · rintro ⟨v, ⟨a, ha⟩, hW⟩
      obtain ⟨j, -, hj⟩ := (ee a v rfl rfl trivial).2 ha
      exact ⟨xs, v, (Tab.idU_holds hr xs xs).2 ⟨rfl, hX⟩, (Tab.top_holds hP xs v).2 ⟨hX, j, hj⟩, hW⟩

/-- `⦇e,S⦈` given a family on the pairs `p = (i, xs)` in demand: `foldRoundsL_holds` on the carrier `I×V`, the step
`TS` met with the key's index (`St p q x q' = TS (q, x) q' ∧ q'.1 = p.1`), from `(p.1, b)` with `b` from `e` at `p.1`;
`foldDen_fibre` reads it as the fold at `p.1`. -/
theorem foldI_sound {I E V : Obj} {d d' : Bool} {e : Rel I (.prod V V)} {S : Rel (.prod (.prod I V) E) (.prod I V)}
    {Te : Den I (.prod V V)} {TS : Den (.prod (.prod I V) E) (.prod I V)} (he : ∀ K, K.WF → e.Reps K Te)
    (we : e.Wf) (hS : ∀ K, K.WF → S.Reps K TS) (wS : S.Wf) :
    ∀ K, K.WF → (GenK.foldI I E V d d' e S).Reps K (foldIDen Te TS) :=
  ofVals_sound fun _ _ X t hK wX h p v hp _ _ => by
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
    have wi := Tab.outl_wf hi wX
    have ees := (reps_iff _ _ _).1 (compT_sound (r' := .ok i) (K := {}) (X := i.Holds)
      (fun _ h' _ _ _ _ _ => by cases h'; exact Iff.rfl) he we Known.wf_empty (fun _ h' => by cases h'; exact wi)) es hes
    have wes := (compT_wf (r' := .ok i) (fun _ h' => by cases h'; exact wi) we).runE Known.wf_empty hes
    have hip : ∀ k a, i.Holds k a ↔ (∃ j, X.row j = k) ∧ a = k.1 := fun k a => Tab.outl_holds hi k a
    have hout' := Tab.foldRoundsL_holds (fun k q x q' => TS (q, x) q' ∧ i.Holds k q'.1)
      (fun _ _ _ => True) (fun _ _ _ _ _ _ _ => trivial) (fun P el T hT wP wel => by
        obtain ⟨s, hs, hT⟩ := bind_ok hT
        obtain ⟨o, ho, hT⟩ := bind_ok hT
        obtain ⟨c, hc, hT⟩ := bind_ok hT
        obtain ⟨pr, hpr, hT⟩ := bind_ok hT
        have ws := pairStep_wf wS wP wel hs
        exact Tab.inter_wf hT ws (Tab.pair_wf hpr wi (Tab.comp_wf hc ws (Tab.outr_wf ho ws.2))))
      (fun P el T hT wP wel _ _ k q' => by
        obtain ⟨s, hs, hT⟩ := bind_ok hT
        obtain ⟨o, ho, hT⟩ := bind_ok hT
        obtain ⟨c, hc, hT⟩ := bind_ok hT
        obtain ⟨pr, hpr, hT⟩ := bind_ok hT
        have hsq := pairStep_holds hS wS wP wel hs k
        rw [Tab.inter_holds hT, Tab.pair_holds hpr, hsq]
        constructor
        · rintro ⟨⟨a, x, h1, h2, h3⟩, hi1, -⟩; exact ⟨a, x, h1, h2, h3, hi1⟩
        · rintro ⟨a, x, h1, h2, h3, hi1⟩
          have hs' : s.Holds k q' := (hsq q').2 ⟨a, x, h1, h2, h3⟩
          obtain ⟨j, -, hj⟩ := _root_.id hs'
          exact ⟨⟨a, x, h1, h2, h3⟩, hi1,
            (Tab.comp_holds hc k q'.2).2 ⟨q', hs', (Tab.outr_holds ho q' q'.2).2 ⟨⟨j, hj⟩, rfl⟩⟩⟩)
      _ _ _ _ _ hout (Tab.outr_wf hrest wX)
      (Tab.pair_wf hP wi (Tab.comp_wf hc1 wes (Tab.outr_wf ho1 wes.2)))
      (fun k a b ha hb => ((Tab.outr_holds hrest k a).1 ha).2.trans ((Tab.outr_holds hrest k b).1 hb).2.symm)
      (fun k q hq => ⟨k.2, (Tab.outr_holds hrest k k.2).2
        ⟨((hip k q.1).1 ((Tab.pair_holds hP k q).1 hq).1).1, rfl⟩, trivial⟩) p
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
      obtain ⟨a, ha, hTe⟩ := (ees p _ rfl rfl trivial).1 hq0
      obtain rfl := (hQ a).1 ha
      exact ⟨_, ⟨a0, hTe⟩, ((foldDen_fibre TS (i.Holds p) p.1 hQ p.2 _ w).1 hW).2⟩
    · rintro ⟨b0, ⟨a0, ha0⟩, hW⟩
      have hes' : es.Holds p (a0, b0) := (ees p _ rfl rfl trivial).2 ⟨p.1, (hQ _).2 rfl, ha0⟩
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
  have hfr' := Tab.foldRoundsL_holds (fun _ v x v' => TF (v, x) v') (fun _ _ _ => True) (fun _ _ _ _ _ _ _ => trivial) (fun S el T hT _ _ k v' => by
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
    (fun p v hv => ⟨p.2, (hrest' p p.2).2 ⟨((hP0' p v).1 hv).1, rfl⟩, trivial⟩)
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
    (fun _ _ _ => True) (fun _ _ _ _ _ _ _ => trivial) (fun S el T hT hu _ k v' => by
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
    (fun k v hv => ⟨k, (Tab.idU_holds hrest k k).2 ⟨rfl, ((Tab.nil_holds hP0 k v).1 hv).1⟩, trivial⟩)
  rw [hfr, Tab.zero_holds hz, false_or]
  constructor
  · rintro ⟨r, v, hr, hv, hW⟩
    obtain ⟨rfl, hi⟩ := (Tab.idU_holds hrest xs r).1 hr
    obtain ⟨-, rfl⟩ := (Tab.nil_holds hP0 xs v).1 hv
    exact ⟨hi, by simpa using (hfold _ _ _).1 hW⟩
  · rintro ⟨hi, rfl⟩
    exact ⟨xs, [], (Tab.idU_holds hrest xs xs).2 ⟨rfl, hi⟩, (Tab.nil_holds hP0 xs []).2 ⟨hi, rfl⟩,
      (hfold _ _ _).2 (by simp)⟩

open Classical in
/-- **`takewhile(p)` on the cells `X`** (`Tab.takewhile`): each array of `X` to its longest prefix of keys of `P`; a
round puts `x` before `acc` where `x ∈ dom P` and gives `[]` otherwise (`foldRoundsR_holds`, one `x` per key). -/
theorem Tab.takewhile_holds {B : Obj} {n : USize} {P : Tab B B} {X : Vals (.arr B) n} {res : Tab (.arr B) (.arr B)}
    (h : Tab.takewhile P X = .ok res) (xs ys : List B.El) :
    res.Holds xs ys ↔ (∃ i, X.row i = xs) ∧ ys = xs.takeWhile fun x => decide (∃ y, P.Holds x y) := by
  unfold Tab.takewhile at h
  obtain ⟨D, hD, h⟩ := GenK.bind_ok h
  obtain ⟨rest, hrest, h⟩ := GenK.bind_ok h
  obtain ⟨P0, hP0, h⟩ := GenK.bind_ok h
  obtain ⟨z, hz, h⟩ := GenK.bind_ok h
  let g : B.El → List B.El → List B.El := fun x acc => if decide (∃ y, P.Holds x y) then x :: acc else []
  have htw : ∀ ws : List B.El, (ws.takeWhile fun x => decide (∃ y, P.Holds x y)) = ws.foldr g [] := by
    intro ws
    induction ws with
    | nil => rfl
    | cons x ws ih => cases hx : decide (∃ y, P.Holds x y) <;> simp only [List.takeWhile, List.foldr_cons, g, hx, ih] <;> rfl
  -- the right fold peels the last element (`foldrDen_snoc`), so the induction runs on the reversed list
  have hfold' : ∀ (rs v w : List B.El), foldrDen (E := B) (V := .arr B) (fun _ b => b = v)
      (fun q v' => ((∃ y, P.Holds q.1 y) ∧ v' = q.1 :: q.2) ∨ ((¬∃ y, P.Holds q.1 y) ∧ v' = [])) rs.reverse w ↔
      w = rs.reverse.foldr g v := by
    intro rs
    induction rs with
    | nil => intro v w; rw [List.reverse_nil, foldrDen_nil]; rfl
    | cons x ws ih =>
      intro v w
      rw [List.reverse_cons, foldrDen_snoc, List.foldr_append, List.foldr_cons, List.foldr_nil]
      constructor
      · rintro ⟨_, v', ⟨_, rfl⟩, hs, hw⟩
        rw [ih] at hw; subst hw
        rcases hs with ⟨hy, rfl⟩ | ⟨hn, rfl⟩
        · simp [g, hy]
        · simp [g, hn]
      · intro hw; subst hw
        by_cases hx : ∃ y, P.Holds x y
        · exact ⟨v, x :: v, ⟨v, rfl⟩, Or.inl ⟨hx, rfl⟩, (ih _ _).2 (by simp [g, hx])⟩
        · exact ⟨v, [], ⟨v, rfl⟩, Or.inr ⟨hx, rfl⟩, (ih _ _).2 (by simp [g, hx])⟩
  have hfold : ∀ (ws v w : List B.El), foldrDen (E := B) (V := .arr B) (fun _ b => b = v)
      (fun q v' => ((∃ y, P.Holds q.1 y) ∧ v' = q.1 :: q.2) ∨ ((¬∃ y, P.Holds q.1 y) ∧ v' = [])) ws w ↔
      w = ws.foldr g v := fun ws v w => by simpa only [List.reverse_reverse] using hfold' ws.reverse v w
  have hfr := Tab.foldRoundsR_holds
    (fun _ v x v' => ((∃ y, P.Holds x y) ∧ v' = x :: v) ∨ ((¬∃ y, P.Holds x y) ∧ v' = []))
    (fun _ _ _ => True) (fun _ _ _ _ _ _ _ => trivial) (fun S el T hT hu _ k v' => by
      obtain ⟨kk, hk, hT⟩ := GenK.bind_ok hT
      obtain ⟨pk, hpk, hT⟩ := GenK.bind_ok hT
      obtain ⟨c, hc, hT⟩ := GenK.bind_ok hT
      obtain ⟨ed, hed, hT⟩ := GenK.bind_ok hT
      obtain ⟨kd, hkd, hT⟩ := GenK.bind_ok hT
      obtain ⟨df, hdf, hT⟩ := GenK.bind_ok hT
      obtain ⟨ca, hca, hT⟩ := GenK.bind_ok hT
      obtain ⟨nl, hnl, hT⟩ := GenK.bind_ok hT
      obtain ⟨cn, hcn, hT⟩ := GenK.bind_ok hT
      have hkk : ∀ b, kk.Holds k b ↔ el.Holds k b ∧ ∃ y, P.Holds b y := fun b => by
        rw [Tab.comp_holds hk]
        exact ⟨fun ⟨x, hx, hd⟩ => by obtain ⟨rfl, hy⟩ := (Tab.dom_holds hD x b).1 hd; exact ⟨hx, hy⟩,
          fun ⟨hx, hy⟩ => ⟨b, hx, (Tab.dom_holds hD b b).2 ⟨rfl, hy⟩⟩⟩
      have hdf' : ∀ k', df.Holds k k' ↔ k = k' ∧ (∃ x, el.Holds k x) ∧ ¬∃ x, kk.Holds k x := fun k' => by
        rw [Tab.diff_holds hdf, Tab.dom_holds hed, Tab.dom_holds hkd]
        exact ⟨fun ⟨⟨e, hx⟩, hn⟩ => ⟨e, hx, fun hy => hn ⟨e, hy⟩⟩, fun ⟨e, hx, hn⟩ => ⟨⟨e, hx⟩, fun ⟨_, hy⟩ => hn hy⟩⟩
      rw [Tab.union_holds hT, Tab.cons_holds hc, Tab.comp_holds hcn]
      constructor
      · rintro (⟨p, hp, rfl⟩ | ⟨v, hv, hn⟩)
        · obtain ⟨hb, hv⟩ := (Tab.pair_holds hpk k p).1 hp
          obtain ⟨hx, hy⟩ := (hkk _).1 hb
          exact ⟨p.2, p.1, hv, hx, Or.inl ⟨hy, rfl⟩⟩
        · obtain ⟨k', hd, hv⟩ := (Tab.comp_holds hca k v).1 hv
          obtain ⟨rfl, ⟨x, hx⟩, hno⟩ := (hdf' k').1 hd
          obtain ⟨-, rfl⟩ := (Tab.nil_holds hnl v v').1 hn
          exact ⟨v, x, hv, hx, Or.inr ⟨fun hy => hno ⟨x, (hkk x).2 ⟨hx, hy⟩⟩, rfl⟩⟩
      · rintro ⟨v, x, hv, hx, ⟨hy, rfl⟩ | ⟨hn, rfl⟩⟩
        · exact Or.inl ⟨(x, v), (Tab.pair_holds hpk k (x, v)).2 ⟨(hkk x).2 ⟨hx, hy⟩, hv⟩, rfl⟩
        · obtain ⟨i, -, hi⟩ := id hv
          refine Or.inr ⟨v, (Tab.comp_holds hca k v).2 ⟨k, (hdf' k).2 ⟨rfl, ⟨x, hx⟩, fun ⟨b, hb⟩ => ?_⟩, hv⟩,
            (Tab.nil_holds hnl v []).2 ⟨⟨i, hi⟩, rfl⟩⟩
          obtain ⟨hb', hy⟩ := (hkk b).1 hb
          obtain rfl := hu k x b hx hb'
          exact hn hy)
    _ _ _ _ _ h
    (fun k a b ha hb => ((Tab.idU_holds hrest k a).1 ha).1.symm.trans ((Tab.idU_holds hrest k b).1 hb).1)
    (fun k v hv => ⟨k, (Tab.idU_holds hrest k k).2 ⟨rfl, ((Tab.nil_holds hP0 k v).1 hv).1⟩, trivial⟩)
  rw [hfr, Tab.zero_holds hz, false_or]
  constructor
  · rintro ⟨r, v, hr, hv, hW⟩
    obtain ⟨rfl, hi⟩ := (Tab.idU_holds hrest xs r).1 hr
    obtain ⟨-, rfl⟩ := (Tab.nil_holds hP0 xs v).1 hv
    exact ⟨hi, by rw [(hfold _ _ _).1 hW, htw]⟩
  · rintro ⟨hi, rfl⟩
    exact ⟨xs, [], (Tab.idU_holds hrest xs xs).2 ⟨rfl, hi⟩, (Tab.nil_holds hP0 xs []).2 ⟨hi, rfl⟩,
      (hfold _ _ _).2 (htw xs)⟩

section
open Rel.Ext

/-- A strictly ascending map of `[0, T)` into `[0, T)` is the identity. -/
theorem strictMono_id {T : Nat} {f : Nat → Nat} (hs : ∀ i j, i < j → j < T → f i < f j) (hb : ∀ i < T, f i < T) :
    ∀ i < T, f i = i := by
  have up : ∀ i < T, i ≤ f i := fun i => by
    induction i with
    | zero => intro; exact Nat.zero_le _
    | succ i ih => intro hi; have := hs i (i + 1) (by omega) hi; have := ih (by omega); omega
  have gap : ∀ d i, i + d < T → f i + d ≤ f (i + d) := fun d => by
    induction d with
    | zero => intro i _; exact Nat.le_refl _
    | succ d ih =>
      intro i hi; show f i + (d + 1) ≤ f (i + d + 1); rw [← Nat.add_assoc] at hi
      have := ih i (by omega); have := hs (i + d) (i + d + 1) (by omega) hi; omega
  intro i hi
  have := gap (T - 1 - i) i (by omega); rw [show i + (T - 1 - i) = T - 1 by omega] at this
  have := hb (T - 1) (by omega); have := up i hi; omega

/-- **The `i64` order code of a non-negative word** is the word plus `2^63`: the sign bit it flips is clear. -/
theorem ordCode_i64_nonneg {a : Nat} (h : a < 2 ^ 63) : (ordCode 8 false true a.toUInt64).toNat = a + 2 ^ 63 := by
  have ha : a.toUInt64.toNat = a := by simp; omega
  have m64 : (18446744073709551615 : UInt64).toNat = 2 ^ 64 - 1 := rfl
  have e1 : (UInt64.ofNat 9223372036854775808).toNat = 2 ^ 63 := rfl
  have e2 : (9223372036854775808 : Nat) = 2 ^ 63 := rfl
  rw [show a + 2 ^ 63 = 2 ^ 63 + a by omega]
  simp only [ordCode, Nat.reduceMul, Nat.reduceSub, Nat.reducePow, beq_self_eq_true, if_true, Bool.false_eq_true,
    if_false, UInt64.toNat_xor, UInt64.toNat_and, Nat.toUInt64_eq, m64]
  apply Nat.eq_of_testBit_eq; intro i
  rw [ha, e1, e2, show (18446744073709551615 : Nat) = 2 ^ 64 - 1 from rfl, Nat.testBit_xor, Nat.testBit_and, Nat.testBit_two_pow_sub_one]
  rcases Nat.lt_trichotomy i 63 with hi | rfl | hi
  · rw [Nat.testBit_two_pow_add_gt hi, Nat.testBit_two_pow, decide_eq_false (by omega : ¬ 63 = i),
      decide_eq_true (by omega : i < 64)]; simp
  · rw [Nat.testBit_two_pow_add_eq, Nat.testBit_lt_two_pow h, Nat.testBit_two_pow]; simp
  · have h1 : 2 ^ 63 + a < 2 ^ i := Nat.lt_of_lt_of_le (by omega) (Nat.pow_le_pow_right (by omega) hi)
    rw [Nat.testBit_lt_two_pow h1, Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le h (Nat.pow_le_pow_right (by omega)
      (by omega))), Nat.testBit_two_pow, decide_eq_false (by omega : ¬ 63 = i)]; simp

/-- **`lexLe` on a key list led by an `i64` column** orders that column's codes. -/
theorem Arr.lexLe_i64 {n : USize} (x : Arr .i64 n) (rest : List (AscKey × Enc)) {i j : Fin n.toNat}
    (h : lexLe (ascKeys n ((.atom .i64, x.enc) :: rest)) i j = true) :
    (ordCode 8 false true (x.get i).toUInt64).toNat ≤ (ordCode 8 false true (x.get j).toUInt64).toNat := by
  have hs := size_raw (t := .i64) n x.enc x.wf (by decide) (by decide) (by decide)
  have hi : i.1 < (Enc.raw .i64 n x.enc).size := by rw [hs]; exact i.2
  have hj : j.1 < (Enc.raw .i64 n x.enc).size := by rw [hs]; exact j.2
  simp only [ascKeys, ascKey, ascOrd, ascLayout, orderKind, Option.map_some, Option.getD_some, List.cons_append,
    lexLe, Array.getElem?_map, Array.getElem?_eq_getElem hi, Array.getElem?_eq_getElem hj,
    Option.map_some, Option.getD_some, Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true, beq_iff_eq] at h
  rw [Arr.get_i64, Arr.get_i64, Array.getElem?_eq_getElem hi, Array.getElem?_eq_getElem hj,
    Option.getD_some, Option.getD_some, UInt64.toUInt64_toInt64, UInt64.toUInt64_toInt64]
  rcases h with h | ⟨h, -⟩
  · exact Nat.le_of_lt (UInt64.lt_iff_toNat_lt.1 h)
  · exact Nat.le_of_eq (congrArg UInt64.toNat h)

theorem Arr.pos_get {n : USize} {P : Arr .i64 n} (h : Arr.pos n = .ok P) (c : Fin n.toNat) :
    P.get c = c.1.toUInt64.toInt64 := by
  unfold Arr.pos at h
  split at h
  · rename_i o ho
    cases h
    rw [Arr.get_i64]
    show ((Enc.raw .i64 n o)[c.1]?.getD 0).toInt64 = _
    rw [shiftCol_raw ho c.1 c.2, UInt64.add_zero]
  · cases h

/-- **`⟨pos, v⟩ ≫ R` with one image per position is in position order**: where `C`, the composite of the `T`
positions `pos` (`Arr.pos`) keyed to `v` with `R`, has `T` rows and `T` distinct keys (`dom`), row `j` of `C` has key
`j` and is the only row there. Its keys are positions; `dom C`'s ascend strictly (`nub_sorted`, `nub_distinct`) so
they are `0..T-1`; `C`'s ascend (`canon_sorted`), so the row of key `p` is row `p` (`strictMono_id` twice). -/
theorem Tab.comp_pos_rows {A B : Obj} {T : USize} {P : Arr .i64 T} {v : Vals A T} {R : Tab A B} {C : Tab .long B}
    {D : Tab .long .long} (hP : Arr.pos T = .ok P) (hT : T.toNat ≤ 2 ^ 63)
    (hC : (⟨T, P, v⟩ : Tab .long A).comp R = .ok C) (hD : C.dom = .ok D) (hn : C.n = T) (hd : D.n = T) :
    ∀ j : Fin C.n.toNat, C.key.row j = j.1.toUInt64.toInt64 ∧ ∀ y, C.Holds (C.key.row j) y ↔ y = C.val.row j := by
  subst hn
  obtain ⟨a, ha⟩ := Classical.axiomOfChoice fun j : Fin C.n.toNat => show ∃ i : Fin C.n.toNat,
      C.key.row j = i.1.toUInt64.toInt64 by
    obtain ⟨b, ⟨i, hi, -⟩, -⟩ := (Tab.comp_holds hC _ _).1 ⟨j, rfl, rfl⟩
    exact ⟨i, hi ▸ Arr.pos_get hP i⟩
  have hcode : ∀ j, (ordCode 8 false true (C.key.get j).toUInt64).toNat = (a j).1 + 2 ^ 63 := fun j => by
    rw [show C.key.get j = C.key.row j from rfl, ha j, UInt64.toUInt64_toInt64]
    exact ordCode_i64_nonneg (by have := (a j).2; omega)
  have hinj : ∀ j j', C.key.row j = C.key.row j' ↔ a j = a j' := fun j j' => by
    rw [ha, ha]
    refine ⟨fun e => Fin.ext ?_, fun e => by rw [e]⟩
    have k : ∀ i : Fin C.n.toNat, i.1.toUInt64.toNat = i.1 := fun i => by have := i.2; simp; omega
    have := congrArg UInt64.toNat (toInt64_inj e); rwa [k, k] at this
  -- the keys of `dom C` ascend strictly, so they are `0..T-1`: every position is a key of `C`
  unfold Tab.dom at hD
  cases hnb : Vals.nub C.key with
  | error s => simp [hnb, Functor.map, Except.map] at hD
  | ok r =>
  simp only [hnb, Functor.map, Except.map, Except.ok.injEq] at hD
  subst hD
  obtain ⟨sel, hs, hlt⟩ := Vals.nub_sorted (es := [(.atom .i64, C.key.enc)]) hnb rfl
  have hr : r.1.toNat = C.n.toNat := congrArg USize.toNat hd
  let f : Nat → Nat := fun d => if h : d < C.n.toNat then (a (sel ⟨d, hr ▸ h⟩)).1 else 0
  have hf := strictMono_id (f := f) (T := C.n.toNat) (fun d d' hdd hd' => by
      simp only [f, dif_pos hd', dif_pos (Nat.lt_trans hdd hd')]
      have hl := Arr.lexLe_i64 C.key [] (hlt ⟨d, by omega⟩ ⟨d', by omega⟩ hdd).1
      rw [hcode, hcode] at hl
      have hne := Vals.nub_distinct hnb (j := ⟨d, by omega⟩) (j' := ⟨d', by omega⟩) (by simp; omega)
      rw [hs, hs] at hne
      have := mt (hinj _ _).2 hne
      have := Fin.val_ne_of_ne this; omega)
    (fun d hd => by simp only [f, dif_pos hd]; exact (a _).2)
  -- the keys of `C` ascend, so the row of key `p` is row `p`
  obtain ⟨U, hU, -⟩ := Tab.comp_canon hC
  obtain ⟨es, -, hes, -⟩ := Tab.canon_codes hU
  cases h2 : Vals.cols U.val with
  | error s => simp [Vals.cols, h2, bind, Except.bind] at hes
  | ok es₂ =>
  simp only [Vals.cols, h2, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at hes
  subst hes
  obtain ⟨selC, hsC, hltC⟩ := Tab.canon_sorted hU (es := (.atom .i64, U.key.enc) :: es₂) (by
    simp [Vals.cols, h2, bind, Except.bind, pure, Except.pure])
  have hmono : ∀ j j' : Fin C.n.toNat, j.1 < j'.1 → (a j).1 ≤ (a j').1 := fun j j' hjj => by
    have hl := Arr.lexLe_i64 U.key es₂ (hltC j j' hjj).1
    have e1 := (Prod.mk.inj (hsC j)).1; have e2 := (Prod.mk.inj (hsC j')).1
    have c1 := hcode j; have c2 := hcode j'
    rw [show C.key.get j = C.key.row j from rfl, e1] at c1
    rw [show C.key.get j' = C.key.row j' from rfl, e2] at c2
    change (ordCode 8 false true (U.key.get (selC j)).toUInt64).toNat = _ at c1
    change (ordCode 8 false true (U.key.get (selC j')).toUInt64).toNat = _ at c2
    omega
  let g : Nat → Nat := fun p => if h : p < C.n.toNat then (sel ⟨p, by omega⟩).1 else 0
  have hfp : ∀ p (hp : p < C.n.toNat), (a (sel ⟨p, by omega⟩)).1 = p := fun p hp => by
    have := hf p hp; simp only [f, dif_pos hp] at this; exact this
  have hg := strictMono_id (f := g) (T := C.n.toNat) (fun p p' hpp hp' => by
      simp only [g, dif_pos hp', dif_pos (Nat.lt_trans hpp hp')]
      have h1 := hfp p (by omega); have h2 := hfp p' hp'
      rcases Nat.lt_or_ge (sel ⟨p, by omega⟩).1 (sel ⟨p', by omega⟩).1 with h | h
      · exact h
      · rcases Nat.eq_or_lt_of_le h with e | e
        · have := congrArg (fun i => (a i).1) (Fin.ext e); simp only at this; omega
        · have := hmono _ _ e; omega)
    (fun p hp => by simp only [g, dif_pos hp]; exact (sel _).2)
  have hid : ∀ j : Fin C.n.toNat, (a j).1 = j.1 := fun j => by
    have := hg j.1 j.2; simp only [g, dif_pos j.2] at this
    have e : sel ⟨j.1, by omega⟩ = j := Fin.ext this
    have := hfp j.1 j.2; rwa [e] at this
  intro j
  refine ⟨by rw [ha j, hid j], fun y => ⟨fun ⟨i, hi, hy⟩ => ?_, fun hy => ⟨j, rfl, hy.symm⟩⟩⟩
  have := (hinj i j).1 hi
  have e : i = j := Fin.ext (by rw [← hid i, ← hid j, this])
  rw [← hy, e]

end

/-- **`F(R)`'s fold branch on the cells `X`** (`Tab.map` where some element has no image or two): each array `xs` of
`X` to every `ys` of its length with `xs[t] R ys[t]`, the left fold from `[]` of `⟨π₁, π₂ ≫ R⟩ ≫ snoc`
(`foldRoundsL_holds`, the step `v ↦ v ++ [y]` for a `y` with `x R y`). -/
theorem Tab.mapFold_holds {A B : Obj} {n : USize} {R : Tab A B} {X : Vals (.arr A) n} {res : Tab (.arr A) (.arr B)}
    (h : (do Tab.foldRounds Tab.peelL (fun (acc : Tab (.arr A) (.arr B)) (el : Tab (.arr A) A) => do
      Tab.snoc (← acc.pair (← el.comp R))) (X.1.toNat + 2) (← Tab.idU X) (← Tab.nil X) (← Tab.zero)) = .ok res)
    (xs : List A.El) (ys : List B.El) :
    res.Holds xs ys ↔ (∃ i, X.row i = xs) ∧ ys.length = xs.length ∧
      ∀ t (ht : t < xs.length) (ht' : t < ys.length), R.Holds (xs[t]'ht) (ys[t]'ht') := by
  obtain ⟨rest, hrest, h⟩ := GenK.bind_ok h
  obtain ⟨P0, hP0, h⟩ := GenK.bind_ok h
  obtain ⟨z, hz, h⟩ := GenK.bind_ok h
  have hfold : ∀ (ws : List A.El) (v w : List B.El), foldDen (E := A) (V := .arr B) (fun _ b => b = v)
      (fun q v' => ∃ y, R.Holds q.2 y ∧ v' = q.1 ++ [y]) ws w ↔ ∃ zs : List B.El, w = v ++ zs ∧
        zs.length = ws.length ∧ ∀ t (ht : t < ws.length) (ht' : t < zs.length), R.Holds (ws[t]'ht) (zs[t]'ht') := by
    intro ws
    induction ws with
    | nil =>
      intro v w; rw [foldDen_nil]
      exact ⟨fun h => ⟨[], by simp [h], rfl, fun t ht => absurd ht (by simp)⟩,
        fun ⟨zs, hw, hl, _⟩ => by rw [List.length_nil, List.length_eq_zero_iff] at hl; simp [hw, hl]⟩
    | cons x ws ih =>
      intro v w
      rw [foldDen_cons]
      constructor
      · rintro ⟨_, v', ⟨_, rfl⟩, ⟨y, hy, rfl⟩, hw⟩
        obtain ⟨zs, rfl, hl, hz⟩ := (ih _ _).1 hw
        refine ⟨y :: zs, by simp, by simp [hl], fun t ht ht' => ?_⟩
        cases t with
        | zero => exact hy
        | succ t => exact hz t (by simpa using ht) (by simpa using ht')
      · rintro ⟨zs, rfl, hl, hz⟩
        cases zs with
        | nil => simp at hl
        | cons y zs =>
          refine ⟨v, v ++ [y], ⟨v, rfl⟩, ⟨y, hz 0 (by simp) (by simp), rfl⟩, (ih _ _).2 ⟨zs, by simp, by simpa using hl,
            fun t ht ht' => hz (t + 1) (by simpa using ht) (by simpa using ht')⟩⟩
  have hfr := Tab.foldRoundsL_holds (fun _ v x v' => ∃ y, R.Holds x y ∧ v' = v ++ [y])
    (fun _ _ _ => True) (fun _ _ _ _ _ _ _ => trivial) (fun S el T hT _ _ k v' => by
      obtain ⟨c, hc, hT⟩ := GenK.bind_ok hT
      obtain ⟨p, hp, hT⟩ := GenK.bind_ok hT
      rw [Tab.snoc_holds hT]
      constructor
      · rintro ⟨q, hq, rfl⟩
        obtain ⟨h1, h2⟩ := (Tab.pair_holds hp k q).1 hq
        obtain ⟨x, hx, hR⟩ := (Tab.comp_holds hc k q.2).1 h2
        exact ⟨q.1, x, h1, hx, q.2, hR, rfl⟩
      · rintro ⟨v, x, h1, h2, y, hR, rfl⟩
        exact ⟨(v, y), (Tab.pair_holds hp k (v, y)).2 ⟨h1, (Tab.comp_holds hc k y).2 ⟨x, h2, hR⟩⟩, rfl⟩)
    _ _ _ _ _ h
    (fun k a b ha hb => ((Tab.idU_holds hrest k a).1 ha).1.symm.trans ((Tab.idU_holds hrest k b).1 hb).1)
    (fun k v hv => ⟨k, (Tab.idU_holds hrest k k).2 ⟨rfl, ((Tab.nil_holds hP0 k v).1 hv).1⟩, trivial⟩)
  rw [hfr, Tab.zero_holds hz, false_or]
  constructor
  · rintro ⟨r, v, hr, hv, hW⟩
    obtain ⟨rfl, hi⟩ := (Tab.idU_holds hrest xs r).1 hr
    obtain ⟨-, rfl⟩ := (Tab.nil_holds hP0 xs v).1 hv
    obtain ⟨zs, rfl, hl, hz⟩ := (hfold _ _ _).1 hW
    exact ⟨hi, by simpa using hl, by simpa using hz⟩
  · rintro ⟨hi, hl, hz⟩
    exact ⟨xs, [], (Tab.idU_holds hrest xs xs).2 ⟨rfl, hi⟩, (Tab.nil_holds hP0 xs []).2 ⟨hi, rfl⟩,
      (hfold _ _ _).2 ⟨ys, by simp, hl, hz⟩⟩

/-- **`Vals.cells` places any payload under one layout**: its `lo` and `hi` read only the widths `w`. -/
theorem Vals.cells_pay {B : Obj} {T n : USize} {w} {pay : Vals B T} {Y : Vals (.arr B) n}
    (h : Vals.cells n w pay = .ok Y) {C : Obj} (pay' : Vals C T) :
    ∃ lo hi : Arr .i64 n, Y = ⟨T, lo, hi, pay⟩ ∧ Vals.cells n w pay' = .ok ⟨T, lo, hi, pay'⟩ := by
  simp only [Vals.cells, bind] at h ⊢
  rw [Except.bind_eq_ok'] at h; obtain ⟨P, hP, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨lo, hlo, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨c0, hc0, h⟩ := h
  rw [Except.bind_eq_ok'] at h; obtain ⟨hi, hhi, h⟩ := h
  cases h
  exact ⟨lo, hi, rfl, by simp [hP, hlo, hc0, hhi, Except.bind, pure, Except.pure]⟩

/-- **`Tab.map`'s one pass has at most `n * m` rows**: the `T` EXPANDed rows are the summed widths of `n` cells over a
payload of `m` (`cellSpan_spec`, `expand_spec`). -/
theorem expand_cells_le {A : Obj} {n m : USize} {lo up : Arr .i64 n} {f : Vals A m} {s e : Arr .i64 n} {w G u}
    {T : USize} (hb : ¬2 ^ 63 ≤ n.toNat * m.toNat + n.toNat + m.toNat) (hse : cellSpan m lo up = .ok (s, e))
    (hw : colMap .sub n e.enc s.enc = .ok w) (hex : expand n w = .ok (T, G, u)) : T.toNat ≤ n.toNat * m.toNat := by
  have hm63 : m.toNat < 2 ^ 63 := by omega
  have hn63 : n.toNat < 2 ^ 63 := by omega
  obtain ⟨SN, EN, hse', hb1, -⟩ := cellSpan_spec hse hm63 f
  obtain ⟨wN, hwN⟩ : ∃ F : Nat → Nat, ∀ i, F i = EN i - SN i := ⟨_, fun _ => rfl⟩
  have hww : ∀ i < n.toNat, (Ext.Enc.raw .i64 n w)[i]?.getD 0 = (wN i).toUInt64 := by
    intro i hi
    have es := (colMap_raw hw).2.2.2 i hi
    rw [(hse' i hi).2, (hse' i hi).1] at es; simp only [Op.eval, Except.ok.injEq] at es
    rw [← es, hwN, toUInt64_sub (hb1 i).1]
  have hsum : ∀ k, ((List.range k).map wN).sum ≤ k * m.toNat := fun k => by
    induction k with
    | zero => simp
    | succ k ih => rw [sum_range_succ', Nat.succ_mul]; have := hb1 k; rw [hwN]; omega
  rw [(expand_spec hex wN hww (by have := hsum n.toNat; omega) hn63).1]; exact hsum _

/-- **`F(R)` on the cells `X`** (`Tab.map`): each array `xs` of `X` to every `ys` of its length with `xs[t] R ys[t]`.
The fold branch is `mapFold_holds`; in the one-pass branch every element `x` of a cell is a payload row `v[t]`, whose
only image is `C`'s row `t` (`comp_pos_rows`), and the new cells are the old ones mapped by that image
(`cells_expand_row`, once at `R`'s image and once at `id` over `v`). -/
theorem Tab.map_holds {A B : Obj} {n : USize} {R : Tab A B} {X : Vals (.arr A) n} {res : Tab (.arr A) (.arr B)}
    (h : Tab.map R X = .ok res) (xs : List A.El) (ys : List B.El) :
    res.Holds xs ys ↔ (∃ i, X.row i = xs) ∧ ys.length = xs.length ∧
      ∀ t (ht : t < xs.length) (ht' : t < ys.length), R.Holds (xs[t]'ht) (ys[t]'ht') := by
  rcases X with ⟨m, lo, hi, f⟩
  simp only [Tab.map] at h
  split at h
  · simp [bind, Except.bind] at h
  rename_i hb
  obtain ⟨_, -, h⟩ := GenK.bind_ok h
  obtain ⟨⟨s, e⟩, hse, h⟩ := GenK.bind_ok h
  obtain ⟨w, hw, h⟩ := GenK.bind_ok h
  obtain ⟨⟨T, G, u⟩, hex, h⟩ := GenK.bind_ok h
  dsimp only at h
  obtain ⟨sg, hsg, h⟩ := GenK.bind_ok h
  obtain ⟨ix, hix, h⟩ := GenK.bind_ok h
  obtain ⟨v, hv, h⟩ := GenK.bind_ok h
  obtain ⟨P, hP, h⟩ := GenK.bind_ok h
  obtain ⟨C, hC, h⟩ := GenK.bind_ok h
  obtain ⟨D, hD, h⟩ := GenK.bind_ok h
  split at h
  · classical
    rename_i hcd
    simp only [Bool.and_eq_true, beq_iff_eq] at hcd
    obtain ⟨hn, hd⟩ := hcd
    obtain ⟨Y, hY, hc⟩ := GenK.bind_ok h
    have hT : T.toNat ≤ 2 ^ 63 := by have := expand_cells_le (f := f) hb hse hw hex; omega
    have rows := Tab.comp_pos_rows hP hT hC hD hn hd
    subst hn
    -- `R`'s only image of payload row `t` is `C`'s row `t`
    have himg : ∀ (t : Fin C.n.toNat) y, R.Holds (v.row t) y ↔ y = C.val.row t := fun t y => by
      rw [← (rows t).2 y, (rows t).1, Tab.comp_holds hC]
      constructor
      · intro hR; exact ⟨v.row t, ⟨t, Arr.pos_get hP t, rfl⟩, hR⟩
      · rintro ⟨b, ⟨i, hi, rfl⟩, hR⟩
        have k : ∀ i : Fin C.n.toNat, i.1.toUInt64.toNat = i.1 := fun i => by have := i.2; simp; omega
        have e : i = t := Fin.ext (by
          have := congrArg UInt64.toNat (toInt64_inj ((Arr.pos_get hP i).symm.trans hi)); rwa [k, k] at this)
        rwa [← e]
    let g : A.El → B.El := fun a => if h : ∃ y, R.Holds a y then Classical.choose h else B.dflt
    have hg : ∀ t, g (v.row t) = C.val.row t := fun t => by
      have hx : ∃ y, R.Holds (v.row t) y := ⟨_, (himg t _).2 rfl⟩
      simp only [g, dif_pos hx]; exact (himg t _).1 (Classical.choose_spec hx)
    have hrow := Vals.cells_expand_row hb hse hw hex hsg hix g (fun t => by
      obtain ⟨j, hj, hvj⟩ := Vals.gather_row f hv t
      exact ⟨j, hj, by rw [← hvj, hg]⟩) hY
    obtain ⟨lo', hi', -, hY'⟩ := Vals.cells_pay hY v
    have hrow' := Vals.cells_expand_row hb hse hw hex hsg hix id (fun t => by
      obtain ⟨j, hj, hvj⟩ := Vals.gather_row f hv t
      exact ⟨j, hj, hvj⟩) hY'
    -- every element of a cell is a payload row, so `R` maps it to `g` of it and nothing else
    have hfun : ∀ i x, x ∈ Vals.row (A := .arr A) ⟨m, lo, hi, f⟩ i → ∀ y, R.Holds x y ↔ y = g x := fun i x hx y => by
      have e := hrow' i; rw [List.map_id] at e; rw [← e] at hx
      simp only [Vals.row, List.mem_filterMap] at hx
      obtain ⟨j, -, hj⟩ := hx
      split at hj
      · cases hj; rw [hg]; exact himg j y
      · cases hj
    rw [Tab.canon_holds hc]
    constructor
    · rintro ⟨i, rfl, rfl⟩
      rw [hrow i]
      refine ⟨⟨i, rfl⟩, List.length_map .., fun t ht ht' => ?_⟩
      rw [List.getElem_map]; exact (hfun i _ (List.getElem_mem ht) _).2 rfl
    · rintro ⟨⟨i, rfl⟩, hl, hR⟩
      refine ⟨i, rfl, ?_⟩
      rw [hrow i]
      apply List.ext_getElem (by rw [List.length_map, hl])
      intro t h1 h2
      rw [List.getElem_map]
      exact ((hfun i _ (List.getElem_mem (by simpa using h1)) _).1 (hR t (by simpa using h1) h2)).symm
  · exact Tab.mapFold_holds h xs ys

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
    (fun _ _ _ => True) (fun _ _ _ _ _ _ _ => trivial) (fun S el T hT _ _ k v' => by
      obtain ⟨p, hp, hT⟩ := GenK.bind_ok hT
      rw [Tab.cat_holds hT]
      constructor
      · rintro ⟨q, hq, rfl⟩; obtain ⟨h1, h2⟩ := (Tab.pair_holds hp k q).1 hq; exact ⟨q.1, q.2, h1, h2, rfl⟩
      · rintro ⟨v, x, h1, h2, rfl⟩; exact ⟨(v, x), (Tab.pair_holds hp k (v, x)).2 ⟨h1, h2⟩, rfl⟩)
    _ _ _ _ _ h
    (fun k a b ha hb => ((Tab.idU_holds hrest k a).1 ha).1.symm.trans ((Tab.idU_holds hrest k b).1 hb).1)
    (fun k v hv => ⟨k, (Tab.idU_holds hrest k k).2 ⟨rfl, ((Tab.nil_holds hP0 k v).1 hv).1⟩, trivial⟩)
  rw [hfr, Tab.zero_holds hz, false_or]
  constructor
  · rintro ⟨r, v, hr, hv, hW⟩
    obtain ⟨rfl, hi⟩ := (Tab.idU_holds hrest xss r).1 hr
    obtain ⟨-, rfl⟩ := (Tab.nil_holds hP0 xss v).1 hv
    exact ⟨hi, by simpa using (hfold _ _ _).1 hW⟩
  · rintro ⟨hi, rfl⟩
    exact ⟨xss, [], (Tab.idU_holds hrest xss xss).2 ⟨rfl, hi⟩, (Tab.nil_holds hP0 xss []).2 ⟨hi, rfl⟩,
      (hfold _ _ _).2 (by simp)⟩

/-- **`R ≫ outl`, `R ≫ outr`, `R ≫ cons°`** on the values of `R` (`outl R.val`, `outr R.val`, `uncons R.val`). -/
theorem Tab.comp_outl {K A C : Obj} {R : Tab K (.prod A C)} {o : Tab (.prod A C) A} {T : Tab K A}
    (ho : Tab.outl R.val = .ok o) (h : R.comp o = .ok T) (k : K.El) (a : A.El) :
    T.Holds k a ↔ ∃ v, R.Holds k v ∧ a = v.1 := by
  rw [Tab.comp_holds h]
  refine ⟨fun ⟨v, hv, h2⟩ => ⟨v, hv, ((Tab.outl_holds ho v a).1 h2).2⟩, fun ⟨v, hv, e⟩ => ⟨v, hv, ?_⟩⟩
  obtain ⟨i, _, hi⟩ := hv
  exact (Tab.outl_holds ho v a).2 ⟨⟨i, hi⟩, e⟩

theorem Tab.comp_outr {K A C : Obj} {R : Tab K (.prod A C)} {o : Tab (.prod A C) C} {T : Tab K C}
    (ho : Tab.outr R.val = .ok o) (h : R.comp o = .ok T) (k : K.El) (c : C.El) :
    T.Holds k c ↔ ∃ v, R.Holds k v ∧ c = v.2 := by
  rw [Tab.comp_holds h]
  refine ⟨fun ⟨v, hv, h2⟩ => ⟨v, hv, ((Tab.outr_holds ho v c).1 h2).2⟩, fun ⟨v, hv, e⟩ => ⟨v, hv, ?_⟩⟩
  obtain ⟨i, _, hi⟩ := hv
  exact (Tab.outr_holds ho v c).2 ⟨⟨i, hi⟩, e⟩

theorem Tab.comp_uncons {K C : Obj} {R : Tab K (.arr C)} {u : Tab (.arr C) (.prod C (.arr C))}
    {T : Tab K (.prod C (.arr C))} (hu : Tab.uncons R.val = .ok u) (h : R.comp u = .ok T) (k : K.El)
    (p : (Obj.prod C (.arr C)).El) : T.Holds k p ↔ ∃ xs, R.Holds k xs ∧ xs = p.1 :: p.2 := by
  rw [Tab.comp_holds h]
  refine ⟨fun ⟨v, hv, h2⟩ => ⟨v, hv, ((Tab.uncons_holds hu v p).1 h2).2⟩, fun ⟨v, hv, e⟩ => ⟨v, hv, ?_⟩⟩
  obtain ⟨i, _, hi⟩ := hv
  exact (Tab.uncons_holds hu v p).2 ⟨⟨i, hi⟩, e⟩

/-- `merge(Q)`'s round on the state `((x, y), acc)` (`Tab.merge`'s `tx`, `ty`): the head of `x` appended where `le`
takes it before the head of `y` or `y` is empty, else the head of `y`; none where both are empty. -/
def mergeStep {α : Type} (le : α → α → Bool) : (List α × List α) × List α → Option ((List α × List α) × List α)
  | ((a :: x, b :: y), acc) => some (if le a b then ((x, b :: y), acc ++ [a]) else ((a :: x, y), acc ++ [b]))
  | ((a :: x, []), acc) => some ((x, []), acc ++ [a])
  | (([], b :: y), acc) => some (([], y), acc ++ [b])
  | (([], []), _) => none

/-- The state after `n` rounds of `mergeStep` from `(p, [])`, a round with no step keeping it: the one state a key
`p` of `Tab.merge`'s fold has with `n` elements of its clock read. -/
def mergeRun {α : Type} (le : α → α → Bool) (p : List α × List α) : Nat → (List α × List α) × List α
  | 0 => (p, [])
  | n + 1 => (mergeStep le (mergeRun le p n)).getD (mergeRun le p n)

/-- A round shortens `x ++ y` by one and keeps `acc ++ merge x y`. -/
theorem mergeStep_len {α : Type} {le : α → α → Bool} {v v' : (List α × List α) × List α}
    (h : mergeStep le v = some v') : v'.1.1.length + v'.1.2.length + 1 = v.1.1.length + v.1.2.length ∧
      v'.2 ++ List.merge v'.1.1 v'.1.2 le = v.2 ++ List.merge v.1.1 v.1.2 le := by
  rcases v with ⟨⟨_ | ⟨a, x⟩, _ | ⟨b, y⟩⟩, acc⟩ <;> simp only [mergeStep, Option.some.injEq, reduceCtorEq] at h <;>
    subst h
  · simp
  · cases x <;> simp [List.merge]
  · rw [List.cons_merge_cons]; by_cases hab : le a b <;> simp [hab, List.cons_merge_cons] <;> omega

theorem mergeStep_none {α : Type} (le : α → α → Bool) (v : (List α × List α) × List α) :
    mergeStep le v = none ↔ v.1.1 = [] ∧ v.1.2 = [] := by
  rcases v with ⟨⟨_ | ⟨a, x⟩, _ | ⟨b, y⟩⟩, acc⟩ <;> simp [mergeStep]

theorem mergeRun_len {α : Type} (le : α → α → Bool) (p : List α × List α) :
    ∀ n ≤ p.1.length + p.2.length,
      (mergeRun le p n).1.1.length + (mergeRun le p n).1.2.length = p.1.length + p.2.length - n
  | 0, _ => by simp [mergeRun]
  | n + 1, hn => by
    have ih := mergeRun_len le p n (by omega)
    have e : mergeRun le p (n + 1) = (mergeStep le (mergeRun le p n)).getD (mergeRun le p n) := rfl
    cases hs : mergeStep le (mergeRun le p n) with
    | none =>
      obtain ⟨h1, h2⟩ := (mergeStep_none le _).1 hs
      rw [h1, h2] at ih; simp at ih; omega
    | some v' => rw [e, hs, Option.getD_some]; have := (mergeStep_len hs).1; omega

open Classical in
/-- **`P ≫ merge(Q)`** (`Tab.merge`), `Q` given the pairs `D` it is asked about acting as `TQ` on their diagonal: each
`(x, y)` of `P` to `List.merge x y` under `a ≤ b ⟺ (a, b) TQ (a, b)`. The fold keeps one state per key, the `mergeRun`
of its clock read so far (the invariant of `foldRoundsL_holds`), so a round's pairs of heads are of one state. -/
theorem Tab.merge_holds {K B : Obj} {q : Tab (.prod B B) (.prod B B) → Except String (Tab (.prod B B) (.prod B B))}
    {TQ : Den (.prod B B) (.prod B B)} (hq : Tab.QDiag q TQ)
    {P : Tab K (.prod (.arr B) (.arr B))} {res : Tab K (.arr B)} (h : Tab.merge q P = .ok res) (k : K.El)
    (zs : List B.El) : res.Holds k zs ↔
      ∃ p : (Obj.prod (.arr B) (.arr B)).El, P.Holds k p ∧ zs = List.merge p.1 p.2 fun a b => decide (TQ (a, b) (a, b)) := by
  let le : B.El → B.El → Bool := fun a b => decide (TQ (a, b) (a, b))
  unfold Tab.merge at h
  obtain ⟨D, hD, h⟩ := GenK.bind_ok h
  obtain ⟨rest, hrest, h⟩ := GenK.bind_ok h
  obtain ⟨n0, hn0, h⟩ := GenK.bind_ok h
  obtain ⟨P0, hP0, h⟩ := GenK.bind_ok h
  obtain ⟨z, hz, h⟩ := GenK.bind_ok h
  obtain ⟨out, hout, h⟩ := GenK.bind_ok h
  obtain ⟨o, ho, h⟩ := GenK.bind_ok h
  obtain ⟨oc, hoc, h⟩ := GenK.bind_ok h
  have hrest' : ∀ p r, rest.Holds p r ↔ (∃ x, P.Holds x p) ∧ r = p.1 ++ p.2 := fun p r => by
    rw [Tab.cat_holds hrest]
    constructor
    · rintro ⟨p', hp', rfl⟩; obtain ⟨rfl, hx⟩ := (Tab.ran_holds hD p p').1 hp'; exact ⟨hx, rfl⟩
    · rintro ⟨hx, rfl⟩; exact ⟨p, (Tab.ran_holds hD p p).2 ⟨rfl, hx⟩, rfl⟩
  have hP0' : ∀ p v, P0.Holds p v ↔ (∃ x, P.Holds x p) ∧ v = (p, []) := fun p v => by
    rw [Tab.pair_holds hP0]
    constructor
    · rintro ⟨h1, h2⟩
      obtain ⟨e, hx⟩ := (Tab.ran_holds hD p v.1).1 h1
      exact ⟨hx, Prod.ext e.symm ((Tab.nil_holds hn0 p v.2).1 h2).2⟩
    · rintro ⟨hx, rfl⟩
      have h1 := (Tab.ran_holds hD p p).2 ⟨rfl, hx⟩
      obtain ⟨i, hi, -⟩ := id h1
      exact ⟨h1, (Tab.nil_holds hn0 p []).2 ⟨⟨i, hi⟩, rfl⟩⟩
  have hfold : ∀ (c : List B.El) (v : (Obj.prod (.prod (.arr B) (.arr B)) (.arr B)).El) w,
      v.1.1.length + v.1.2.length = c.length →
      (foldDen (E := B) (fun _ b => b = v) (fun q v' => mergeStep le q.1 = some v') c w ↔
        w = (([], []), v.2 ++ List.merge v.1.1 v.1.2 le)) := by
    intro c
    induction c with
    | nil =>
      intro v w hl
      rw [foldDen_nil]
      obtain ⟨⟨x, y⟩, acc⟩ := v
      simp only [List.length_nil] at hl
      obtain ⟨rfl, rfl⟩ : x = [] ∧ y = [] := ⟨List.eq_nil_of_length_eq_zero (by omega),
        List.eq_nil_of_length_eq_zero (by omega)⟩
      simp
    | cons e c ih =>
      intro v w hl
      rw [foldDen_cons]
      cases hs : mergeStep le v with
      | none =>
        obtain ⟨h1, h2⟩ := (mergeStep_none le _).1 hs
        rw [h1, h2] at hl; simp at hl
      | some v' =>
        obtain ⟨hl', hm⟩ := mergeStep_len hs
        rw [← hm]
        constructor
        · rintro ⟨_, v'', ⟨_, rfl⟩, hs', hw⟩
          rw [hs] at hs'; cases hs'
          exact (ih v' w (by simp at hl; omega)).1 hw
        · intro hw; exact ⟨v, v', ⟨v, rfl⟩, hs, (ih v' w (by simp at hl; omega)).2 hw⟩
  have hfr := Tab.foldRoundsL_holds (fun _ v _ v' => mergeStep le v = some v')
    (fun (p : (Obj.prod (.arr B) (.arr B)).El) (r : (Obj.arr B).El)
      (v : (Obj.prod (.prod (.arr B) (.arr B)) (.arr B)).El) =>
      r.length ≤ p.1.length + p.2.length ∧ v = mergeRun le p (p.1.length + p.2.length - r.length))
    (fun p x r v v' ⟨hl, hv⟩ hs => by
      simp only [List.length_cons] at hl hv
      refine ⟨by omega, ?_⟩
      have e : p.1.length + p.2.length - r.length = (p.1.length + p.2.length - (r.length + 1)) + 1 := by omega
      rw [e]
      show v' = (mergeStep le (mergeRun le p _)).getD _
      rw [← hv, hs]; rfl)
    (fun S el T hT _ hPI k s => by
      obtain ⟨o1, ho1, hT⟩ := GenK.bind_ok hT
      obtain ⟨xy, hxy, hT⟩ := GenK.bind_ok hT
      obtain ⟨o2, ho2, hT⟩ := GenK.bind_ok hT
      obtain ⟨ac, hac, hT⟩ := GenK.bind_ok hT
      obtain ⟨o3, ho3, hT⟩ := GenK.bind_ok hT
      obtain ⟨x, hx, hT⟩ := GenK.bind_ok hT
      obtain ⟨o4, ho4, hT⟩ := GenK.bind_ok hT
      obtain ⟨y, hy, hT⟩ := GenK.bind_ok hT
      obtain ⟨u1, hu1, hT⟩ := GenK.bind_ok hT
      obtain ⟨ux, hux, hT⟩ := GenK.bind_ok hT
      obtain ⟨u2, hu2, hT⟩ := GenK.bind_ok hT
      obtain ⟨uy, huy, hT⟩ := GenK.bind_ok hT
      obtain ⟨o5, ho5, hT⟩ := GenK.bind_ok hT
      obtain ⟨a, ha, hT⟩ := GenK.bind_ok hT
      obtain ⟨o6, ho6, hT⟩ := GenK.bind_ok hT
      obtain ⟨b, hb, hT⟩ := GenK.bind_ok hT
      obtain ⟨hp, hhp, hT⟩ := GenK.bind_ok hT
      obtain ⟨hr, hhr, hT⟩ := GenK.bind_ok hT
      obtain ⟨qt, hqt, hT⟩ := GenK.bind_ok hT
      obtain ⟨hc, hhc, hT⟩ := GenK.bind_ok hT
      obtain ⟨l, hl, hT⟩ := GenK.bind_ok hT
      obtain ⟨dy, hdy, hT⟩ := GenK.bind_ok hT
      obtain ⟨dux, hdux, hT⟩ := GenK.bind_ok hT
      obtain ⟨dd, hdd, hT⟩ := GenK.bind_ok hT
      obtain ⟨tx, htx, hT⟩ := GenK.bind_ok hT
      obtain ⟨ty, hty, hT⟩ := GenK.bind_ok hT
      obtain ⟨o7, ho7, hT⟩ := GenK.bind_ok hT
      obtain ⟨xr, hxr, hT⟩ := GenK.bind_ok hT
      obtain ⟨p1, hp1, hT⟩ := GenK.bind_ok hT
      obtain ⟨pa, hpa, hT⟩ := GenK.bind_ok hT
      obtain ⟨sa, hsa, hT⟩ := GenK.bind_ok hT
      obtain ⟨sx, hsx, hT⟩ := GenK.bind_ok hT
      obtain ⟨o8, ho8, hT⟩ := GenK.bind_ok hT
      obtain ⟨yr, hyr, hT⟩ := GenK.bind_ok hT
      obtain ⟨p2, hp2, hT⟩ := GenK.bind_ok hT
      obtain ⟨pb, hpb, hT⟩ := GenK.bind_ok hT
      obtain ⟨sb, hsb, hT⟩ := GenK.bind_ok hT
      obtain ⟨sy, hsy, hT⟩ := GenK.bind_ok hT
      obtain ⟨c1, hc1, hT⟩ := GenK.bind_ok hT
      obtain ⟨c2, hc2, hT⟩ := GenK.bind_ok hT
      -- `l`: the keys whose heads `(a, b)` `Q` takes on the diagonal (`diag_holds`)
      have hl' : ∀ k k', l.Holds k k' ↔ k = k' ∧ ∃ e : (Obj.prod B B).El,
          (a.Holds k e.1 ∧ b.Holds k e.2) ∧ TQ e e := fun k k' => by
        simp only [Tab.dom_holds hl, Tab.comp_holds hhc]
        refine and_congr_right fun _ => ?_
        have hd := Tab.diag_holds hq (fun e e' h => ((Tab.ran_holds hhr e e').1 h).1) hqt
        constructor
        · rintro ⟨c, e, he, hqc⟩
          obtain ⟨-, -, t⟩ := (hd e c).1 hqc
          exact ⟨e, (Tab.pair_holds hhp k e).1 he, t⟩
        · rintro ⟨e, he, t⟩
          have he' := (Tab.pair_holds hhp k e).2 he
          exact ⟨e, e, he', (hd e e).2 ⟨rfl, (Tab.ran_holds hhr e e).2 ⟨rfl, k, he'⟩, t⟩⟩
      -- `tx`, `ty` are coreflexive: a row of `tx ≫ sx` at `k` is a row of `sx` at `k`
      have hc1' : ∀ s, c1.Holds k s ↔ tx.Holds k k ∧ sx.Holds k s := fun s => by
        rw [Tab.comp_holds hc1]
        refine ⟨fun ⟨k', h1, h2⟩ => ?_, fun ⟨h1, h2⟩ => ⟨k, h1, h2⟩⟩
        obtain rfl : k = k' := by
          rcases (Tab.union_holds htx k k').1 h1 with h3 | h3
          · exact ((hl' k k').1 h3).1
          · exact ((Tab.dom_holds hdux k k').1 ((Tab.diff_holds hdd k k').1 h3).1).1
        exact ⟨h1, h2⟩
      have hc2' : ∀ s, c2.Holds k s ↔ ty.Holds k k ∧ sy.Holds k s := fun s => by
        rw [Tab.comp_holds hc2]
        refine ⟨fun ⟨k', h1, h2⟩ => ?_, fun ⟨h1, h2⟩ => ⟨k, h1, h2⟩⟩
        obtain rfl : k = k' := ((Tab.dom_holds hdy k k').1 ((Tab.diff_holds hty k k').1 h1).1).1
        exact ⟨h1, h2⟩
      simp only [Tab.union_holds hT, hc1', hc2', Tab.union_holds htx,
        Tab.diff_holds hdd, Tab.diff_holds hty, Tab.dom_holds hdy, Tab.dom_holds hdux, hl', Tab.pair_holds hsx,
        Tab.pair_holds hp1, Tab.snoc_holds hsa, Tab.pair_holds hpa, Tab.pair_holds hsy, Tab.pair_holds hp2,
        Tab.snoc_holds hsb, Tab.pair_holds hpb, Tab.comp_outr ho7 hxr, Tab.comp_outr ho8 hyr, Tab.comp_outl ho5 ha,
        Tab.comp_outl ho6 hb, Tab.comp_uncons hu1 hux, Tab.comp_uncons hu2 huy, Tab.comp_outl ho3 hx,
        Tab.comp_outr ho4 hy, Tab.comp_outl ho1 hxy, Tab.comp_outr ho2 hac, Core.Rel.rpair]
      by_cases hk : ∃ v, S.Holds k v
      · obtain ⟨⟨⟨x0, y0⟩, c0⟩, hv0⟩ := hk
        obtain ⟨r0, hel0, hall⟩ := hPI k _ hv0
        have hSk : ∀ v, S.Holds k v ↔ v = ((x0, y0), c0) :=
          fun v => ⟨fun hv => (hall v hv).2.trans (hall _ hv0).2.symm, fun e => e ▸ hv0⟩
        have hlen : x0.length + y0.length = r0.length := by
          have h1 := mergeRun_len le k _ (Nat.sub_le _ r0.length)
          rw [← (hall _ hv0).2] at h1
          have h2 := (hall _ hv0).1
          simp only at h1 h2 ⊢; omega
        rcases x0 with _ | ⟨a0, x1⟩ <;> rcases y0 with _ | ⟨b0, y1⟩ <;> rcases r0 with _ | ⟨e0, r1⟩ <;>
          simp at hlen <;> simp [hSk, hel0, mergeStep, le]
        case pos.nil.cons.cons | pos.cons.nil.cons =>
          obtain ⟨⟨_, _⟩, _⟩ := s; dsimp only
          exact ⟨fun ⟨⟨h1, h2⟩, _, _, ⟨rfl, rfl⟩, h3⟩ => by subst h1 h2 h3; rfl,
            fun hh => by cases hh; exact ⟨⟨rfl, rfl⟩, _, _, ⟨rfl, rfl⟩, rfl⟩⟩
        case pos.cons.cons.cons a0 x1 b0 y1 _ _ =>
          obtain ⟨⟨_, _⟩, _⟩ := s; dsimp only
          by_cases hab : TQ (a0, b0) (a0, b0)
          · rw [if_pos hab]
            refine ⟨fun hh => ?_, fun hh => by
              cases hh; exact Or.inl ⟨⟨a0, b0, ⟨rfl, rfl⟩, hab⟩, ⟨rfl, rfl⟩, _, _, ⟨rfl, rfl⟩, rfl⟩⟩
            rcases hh with ⟨-, ⟨h1, h2⟩, _, _, ⟨rfl, rfl⟩, h3⟩ | ⟨hn, -⟩
            · subst h1 h2 h3; rfl
            · exact (hn hab).elim
          · rw [if_neg hab]
            refine ⟨fun hh => ?_, fun hh => by
              cases hh; exact Or.inr ⟨hab, ⟨rfl, rfl⟩, _, _, ⟨rfl, rfl⟩, rfl⟩⟩
            rcases hh with ⟨⟨a, b, ⟨rfl, rfl⟩, h⟩, -⟩ | ⟨-, ⟨h1, h2⟩, _, _, ⟨rfl, rfl⟩, h3⟩
            · exact (hab h).elim
            · subst h1 h2 h3; rfl
      · simp only [not_exists] at hk
        simp [hk])
    _ _ _ _ _ hout
    (fun p a b ha hb => ((hrest' p a).1 ha).2.trans ((hrest' p b).1 hb).2.symm)
    (fun p v hv => by
      obtain ⟨hx, rfl⟩ := (hP0' p v).1 hv
      exact ⟨p.1 ++ p.2, (hrest' p _).2 ⟨hx, rfl⟩, by simp, by simp [mergeRun]⟩)
  rw [Tab.comp_holds h]
  constructor
  · rintro ⟨p, hp, hpo⟩
    obtain ⟨w, hw, rfl⟩ := (Tab.comp_outr ho hoc p zs).1 hpo
    rcases (hfr p w).1 hw with hz' | ⟨r, v, hr, hv, hW⟩
    · exact ((Tab.zero_holds hz p w).1 hz').elim
    obtain ⟨-, rfl⟩ := (hrest' p r).1 hr
    obtain ⟨-, rfl⟩ := (hP0' p v).1 hv
    rw [hfold _ _ _ (by simp)] at hW
    subst hW
    exact ⟨p, hp, by simp [le]⟩
  · rintro ⟨p, hp, rfl⟩
    have hx : ∃ x, P.Holds x p := ⟨k, hp⟩
    refine ⟨p, hp, (Tab.comp_outr ho hoc p _).2 ⟨(([], []), List.merge p.1 p.2 le), ?_, rfl⟩⟩
    exact (hfr p _).2 (Or.inr ⟨p.1 ++ p.2, (p, []), (hrest' p _).2 ⟨hx, rfl⟩, (hP0' p _).2 ⟨hx, rfl⟩,
      (hfold _ _ _ (by simp)).2 (by simp)⟩)

open Classical in
/-- **`thinL(Q)` on the cells `X`** (`Tab.thinL`), `Q` given the pairs `D` it is asked about acting as `TQ` on their
diagonal: each array `xs` of `X` to `thinLDen`, the right fold from `[]` of `bump`, `x` into `ys`
(`foldRoundsR_holds`). A round's step is keyed by the pair `(x, ys)` it meets, so it needs no invariant. -/
theorem Tab.thinL_holds {B : Obj} {n : USize}
    {q : Tab (.prod B B) (.prod B B) → Except String (Tab (.prod B B) (.prod B B))}
    {TQ : Den (.prod B B) (.prod B B)} (hq : Tab.QDiag q TQ)
    {X : Vals (.arr B) n} {res : Tab (.arr B) (.arr B)} (h : Tab.thinL q X = .ok res) (xs w : List B.El) :
    res.Holds xs w ↔ (∃ i, X.row i = xs) ∧ thinLDen (fun a b => decide (TQ (a, b) (a, b))) xs w := by
  let le : B.El → B.El → Bool := fun a b => decide (TQ (a, b) (a, b))
  -- `bump`: `x` into `v` (`thinLDen`'s clause at one index, `v = ys[t+1]`, `v' = ys[t]`)
  let St : (Obj.arr B).El → (Obj.arr B).El → B.El → (Obj.arr B).El → Prop := fun _ v x v' =>
    (v = [] ∧ v' = [x]) ∨ ∃ b bs, v = b :: bs ∧ ((le x b = true ∧ v' = x :: bs) ∨ (le b x = true ∧ v' = v) ∨
      (le x b = false ∧ le b x = false ∧ v' = x :: v))
  unfold Tab.thinL at h
  dsimp only at h
  obtain ⟨rest, hrest, h⟩ := GenK.bind_ok h
  obtain ⟨P0, hP0, h⟩ := GenK.bind_ok h
  obtain ⟨z, hz, h⟩ := GenK.bind_ok h
  have hfr := Tab.foldRoundsR_holds St (fun _ _ _ => True) (fun _ _ _ _ _ _ _ => trivial)
    (fun S el T hT _ _ k v' => by
      obtain ⟨p, hp, hT⟩ := GenK.bind_ok hT
      obtain ⟨E, hE, hT⟩ := GenK.bind_ok hT
      obtain ⟨o1, ho1, hT⟩ := GenK.bind_ok hT
      obtain ⟨x, hx, hT⟩ := GenK.bind_ok hT
      obtain ⟨o2, ho2, hT⟩ := GenK.bind_ok hT
      obtain ⟨ys, hys, hT⟩ := GenK.bind_ok hT
      obtain ⟨o3, ho3, hT⟩ := GenK.bind_ok hT
      obtain ⟨u, hu, hT⟩ := GenK.bind_ok hT
      obtain ⟨o4, ho4, hT⟩ := GenK.bind_ok hT
      obtain ⟨b, hb, hT⟩ := GenK.bind_ok hT
      obtain ⟨ab, hab, hT⟩ := GenK.bind_ok hT
      obtain ⟨ba, hba, hT⟩ := GenK.bind_ok hT
      obtain ⟨abr, habr, hT⟩ := GenK.bind_ok hT
      obtain ⟨qa, hqa, hT⟩ := GenK.bind_ok hT
      obtain ⟨ca, hca, hT⟩ := GenK.bind_ok hT
      obtain ⟨up, hup, hT⟩ := GenK.bind_ok hT
      obtain ⟨bar, hbar, hT⟩ := GenK.bind_ok hT
      obtain ⟨qb, hqb, hT⟩ := GenK.bind_ok hT
      obtain ⟨cb, hcb, hT⟩ := GenK.bind_ok hT
      obtain ⟨down, hdown, hT⟩ := GenK.bind_ok hT
      obtain ⟨du, hdu, hT⟩ := GenK.bind_ok hT
      obtain ⟨ed, hed, hT⟩ := GenK.bind_ok hT
      obtain ⟨d1, hd1, hT⟩ := GenK.bind_ok hT
      obtain ⟨d2, hd2, hT⟩ := GenK.bind_ok hT
      obtain ⟨lone, hlone, hT⟩ := GenK.bind_ok hT
      obtain ⟨o5, ho5, hT⟩ := GenK.bind_ok hT
      obtain ⟨bs, hbs, hT⟩ := GenK.bind_ok hT
      obtain ⟨cl, hcl, hT⟩ := GenK.bind_ok hT
      obtain ⟨xb, hxb, hT⟩ := GenK.bind_ok hT
      obtain ⟨cx, hcx, hT⟩ := GenK.bind_ok hT
      obtain ⟨uc, huc, hT⟩ := GenK.bind_ok hT
      obtain ⟨un1, hun1, hT⟩ := GenK.bind_ok hT
      obtain ⟨dc, hdc, hT⟩ := GenK.bind_ok hT
      obtain ⟨rr, hrr, hT⟩ := GenK.bind_ok hT
      have hx' : ∀ e a, x.Holds e a ↔ (∃ k, p.Holds k e) ∧ a = e.1 := fun e a => by
        rw [Tab.comp_outl ho1 hx]
        exact ⟨fun ⟨v, hv, ha⟩ => by obtain ⟨rfl, hk⟩ := (Tab.ran_holds hE e v).1 hv; exact ⟨hk, ha⟩,
          fun ⟨hk, ha⟩ => ⟨e, (Tab.ran_holds hE e e).2 ⟨rfl, hk⟩, ha⟩⟩
      have hys' : ∀ e l, ys.Holds e l ↔ (∃ k, p.Holds k e) ∧ l = e.2 := fun e l => by
        rw [Tab.comp_outr ho2 hys]
        exact ⟨fun ⟨v, hv, ha⟩ => by obtain ⟨rfl, hk⟩ := (Tab.ran_holds hE e v).1 hv; exact ⟨hk, ha⟩,
          fun ⟨hk, ha⟩ => ⟨e, (Tab.ran_holds hE e e).2 ⟨rfl, hk⟩, ha⟩⟩
      have hu' : ∀ e (c : (Obj.prod B (.arr B)).El), u.Holds e c ↔ (∃ k, p.Holds k e) ∧ e.2 = c.1 :: c.2 :=
        fun e c => by
          rw [Tab.comp_uncons ho3 hu]
          exact ⟨fun ⟨l, hl, he⟩ => by obtain ⟨hk, rfl⟩ := (hys' e l).1 hl; exact ⟨hk, he⟩,
            fun ⟨hk, he⟩ => ⟨e.2, (hys' e _).2 ⟨hk, rfl⟩, he⟩⟩
      have hb' : ∀ e a, b.Holds e a ↔ (∃ k, p.Holds k e) ∧ ∃ l, e.2 = a :: l := fun e a => by
        rw [Tab.comp_outl ho4 hb]
        exact ⟨fun ⟨c, hc, ha⟩ => by obtain ⟨hk, he⟩ := (hu' e c).1 hc; subst ha; exact ⟨hk, c.2, he⟩,
          fun ⟨hk, l, he⟩ => ⟨(a, l), (hu' e _).2 ⟨hk, he⟩, rfl⟩⟩
      have hbs' : ∀ e l, bs.Holds e l ↔ (∃ k, p.Holds k e) ∧ ∃ a, e.2 = a :: l := fun e l => by
        rw [Tab.comp_outr ho5 hbs]
        exact ⟨fun ⟨c, hc, ha⟩ => by obtain ⟨hk, he⟩ := (hu' e c).1 hc; subst ha; exact ⟨hk, c.1, he⟩,
          fun ⟨hk, a, he⟩ => ⟨(a, l), (hu' e _).2 ⟨hk, he⟩, rfl⟩⟩
      have hdu' : ∀ e e', du.Holds e e' ↔ e = e' ∧ (∃ k, p.Holds k e) ∧ e.2 ≠ [] := fun e e' => by
        rw [Tab.dom_holds hdu]
        refine and_congr_right fun _ => ⟨fun ⟨c, hc⟩ => ?_, fun ⟨hk, hne⟩ => ?_⟩
        · obtain ⟨hk, he⟩ := (hu' e c).1 hc; exact ⟨hk, by rw [he]; exact List.cons_ne_nil _ _⟩
        · obtain ⟨a, l, he⟩ := List.exists_cons_of_ne_nil hne; exact ⟨(a, l), (hu' e _).2 ⟨hk, he⟩⟩
      -- `up`, `down`: the pairs whose `(x, b)`, `(b, x)` `Q` takes on the diagonal (`diag_holds`)
      have hup' : ∀ e e', up.Holds e e' ↔ e = e' ∧ ∃ c, b.Holds e c ∧ (∃ k, p.Holds k e) ∧ le e.1 c = true :=
        fun e e' => by
          simp only [Tab.dom_holds hup, Tab.comp_holds hca]
          have hd := Tab.diag_holds hq (fun c c' h => ((Tab.ran_holds habr c c').1 h).1) hqa
          refine and_congr_right fun _ => ⟨fun ⟨y, c, hc, hy⟩ => ?_, fun ⟨c, hc, hk, hl⟩ => ?_⟩
          · obtain ⟨h1, h2⟩ := (Tab.pair_holds hab e c).1 hc
            obtain ⟨hk, he1⟩ := (hx' e _).1 h1
            exact ⟨c.2, h2, hk, decide_eq_true (by rw [← he1]; exact ((hd c y).1 hy).2.2)⟩
          · have hc' := (Tab.pair_holds hab e (e.1, c)).2 ⟨(hx' e _).2 ⟨hk, rfl⟩, hc⟩
            exact ⟨_, _, hc', (hd _ _).2 ⟨rfl, (Tab.ran_holds habr _ _).2 ⟨rfl, e, hc'⟩, of_decide_eq_true hl⟩⟩
      have hdown' : ∀ e e', down.Holds e e' ↔ e = e' ∧ ∃ c, b.Holds e c ∧ (∃ k, p.Holds k e) ∧ le c e.1 = true :=
        fun e e' => by
          simp only [Tab.dom_holds hdown, Tab.comp_holds hcb]
          have hd := Tab.diag_holds hq (fun c c' h => ((Tab.ran_holds hbar c c').1 h).1) hqb
          refine and_congr_right fun _ => ⟨fun ⟨y, c, hc, hy⟩ => ?_, fun ⟨c, hc, hk, hl⟩ => ?_⟩
          · obtain ⟨h1, h2⟩ := (Tab.pair_holds hba e c).1 hc
            obtain ⟨hk, he1⟩ := (hx' e _).1 h2
            exact ⟨c.1, h1, hk, decide_eq_true (by rw [← he1]; exact ((hd c y).1 hy).2.2)⟩
          · have hc' := (Tab.pair_holds hba e (c, e.1)).2 ⟨hc, (hx' e _).2 ⟨hk, rfl⟩⟩
            exact ⟨_, _, hc', (hd _ _).2 ⟨rfl, (Tab.ran_holds hbar _ _).2 ⟨rfl, e, hc'⟩, of_decide_eq_true hl⟩⟩
      -- `lone`, `up`, `down` are coreflexive: a row of `C ≫ S` at `e` is a row of `S` at `e`
      have hco : ∀ {Z : Obj} {C : Tab (Obj.prod B (.arr B)) (Obj.prod B (.arr B))} {S T : Tab (Obj.prod B (.arr B)) Z},
          (∀ e e', C.Holds e e' → e = e') → C.comp S = .ok T → ∀ e v, T.Holds e v ↔ C.Holds e e ∧ S.Holds e v :=
        fun hc h e v => by
          rw [Tab.comp_holds h]
          exact ⟨fun ⟨e', h1, h2⟩ => by obtain rfl := hc _ _ h1; exact ⟨h1, h2⟩, fun ⟨h1, h2⟩ => ⟨e, h1, h2⟩⟩
      have hlc : ∀ e e', lone.Holds e e' → e = e' := fun e e' h => by
        rcases (Tab.union_holds hlone e e').1 h with h | h
        · exact ((Tab.ran_holds hE e e').1 ((Tab.diff_holds hed e e').1 h).1).1
        · exact ((hdu' e e').1 ((Tab.diff_holds hd1 e e').1 ((Tab.diff_holds hd2 e e').1 h).1).1).1
      have hcl' : ∀ e v, cl.Holds e v ↔ lone.Holds e e ∧ v = e.1 :: e.2 := fun e v => by
        rw [Tab.cons_holds hcl]
        exact ⟨fun ⟨c, hc, hv⟩ => by obtain rfl := hlc _ _ hc; exact ⟨hc, hv⟩, fun ⟨hc, hv⟩ => ⟨e, hc, hv⟩⟩
      have hr : ∀ e v', rr.Holds e v' ↔ (∃ k, p.Holds k e) ∧ St k e.2 e.1 v' := by
        intro e v'
        rw [Tab.union_holds hrr, Tab.union_holds hun1, hcl', hco (fun e e' h => ((hup' e e').1 h).1) huc,
          hco (fun e e' h => ((hdown' e e').1 h).1) hdc]
        simp only [Tab.union_holds hlone, Tab.diff_holds hed, Tab.diff_holds hd2, Tab.diff_holds hd1,
          Tab.ran_holds hE, hdu', hup', hdown', Tab.cons_holds hcx, Tab.pair_holds hxb, Core.Rel.rpair, hx', hbs',
          hys', hb', St, true_and]
        obtain ⟨x0, _ | ⟨b0, l⟩⟩ := e
        · simp
        · by_cases hk : ∃ k, p.Holds k (x0, b0 :: l) <;> simp [hk] <;>
            cases h1 : le x0 b0 <;> cases h2 : le b0 x0 <;> simp [h1, h2, and_assoc]
      rw [Tab.comp_holds hT]
      constructor
      · rintro ⟨e, he, hre⟩
        obtain ⟨h1, h2⟩ := (Tab.pair_holds hp k e).1 he
        exact ⟨e.2, e.1, h2, h1, ((hr e v').1 hre).2⟩
      · rintro ⟨v, a, hv, ha, hs⟩
        have he := (Tab.pair_holds hp k (a, v)).2 ⟨ha, hv⟩
        exact ⟨(a, v), he, (hr _ v').2 ⟨⟨k, he⟩, hs⟩⟩)
    _ _ _ _ _ h
    (fun k a b ha hb => ((Tab.idU_holds hrest k a).1 ha).1.symm.trans ((Tab.idU_holds hrest k b).1 hb).1)
    (fun k v hv => ⟨k, (Tab.idU_holds hrest k k).2 ⟨rfl, ((Tab.nil_holds hP0 k v).1 hv).1⟩, trivial⟩)
  rw [hfr, Tab.zero_holds hz, false_or]
  constructor
  · rintro ⟨r, v, hr, hv, ⟨ys, hy, ⟨_, h0⟩, hS, hw⟩⟩
    obtain ⟨rfl, hi⟩ := (Tab.idU_holds hrest xs r).1 hr
    obtain ⟨-, rfl⟩ := (Tab.nil_holds hP0 xs v).1 hv
    exact ⟨hi, ys, hy, h0, hS, hw⟩
  · rintro ⟨hi, ys, hy, h0, hS, hw⟩
    exact ⟨xs, [], (Tab.idU_holds hrest xs xs).2 ⟨rfl, hi⟩, (Tab.nil_holds hP0 xs []).2 ⟨hi, rfl⟩,
      ys, hy, ⟨[], h0⟩, hS, hw⟩

namespace GenK

open Classical in
/-- A row given one test `p`, run on the arrays in demand (`elems`) as `f`, whose law reads `P` only through the test
`∃ y, P x y` on the array's elements, by `F` (which reads its test only on the elements): it represents `F` of the
test of `p`'s meaning `T`, `p` run knowing its domain is those elements, where it agrees with `T`. -/
theorem elemsTest_sound {B C : Obj} {d : Bool} {R : Rel B B} {T : Den B B}
    {f : {n : USize} → Tab B B → Vals (.arr B) n → Except String (Tab (.arr B) C)}
    {F : (B.El → Bool) → List B.El → C.El}
    (hf : ∀ {n : USize} {P : Tab B B} {X : Vals (.arr B) n} {t : Tab (.arr B) C}, f P X = .ok t → ∀ xs ys,
      t.Holds xs ys ↔ (∃ i, X.row i = xs) ∧ ys = F (fun x => decide (∃ y, P.Holds x y)) xs)
    (hF : ∀ p q xs, (∀ x ∈ xs, p x = q x) → F p xs = F q xs) (hR : ∀ K, R.Reps K T) :
    ∀ K, (GenK.elems B B C d R f).Reps K (fun xs ys => ys = F (fun x => decide (∃ y, T x y)) xs) := by
  unfold GenK.elems
  exact ofVals_sound fun _ _ X t hK h xs ys hx _ _ => by
    obtain ⟨M, hM, h⟩ := bind_ok h
    obtain ⟨k, hk, h⟩ := bind_ok h
    obtain ⟨P, hP, h⟩ := bind_ok h
    have hi := (side_some hK xs).1 hx
    have ha := (reps_iff _ _ _).1 (hR ⟨some ⟨k.n, k.key⟩, none, none⟩) P hP
    have hPT : ∀ x ∈ xs, (∃ y, P.Holds x y) ↔ ∃ y, T x y := fun x hm => by
      obtain ⟨j, hj, -⟩ := (Tab.ran_holds hk x x).2 ⟨rfl, xs, (Tab.mem_holds hM xs x).2 ⟨hi, hm⟩⟩
      exact exists_congr fun y => ha x y ((side_some rfl x).2 ⟨j, hj⟩) rfl trivial
    show t.Holds xs ys ↔ _
    rw [hf h, and_iff_right hi, hF _ _ xs fun x hm => decide_eq_decide.2 (hPT x hm)]

open Classical in
/-- `filter(p)`, `Expand.primE`'s fit of the row (`elems`, `Tab.filter`): each array in demand to its elements in
`dom T` (`elemsTest_sound`). -/
theorem filter_sound {B : Obj} {d : Bool} {R : Rel B B} {T : Den B B} (hR : ∀ K, R.Reps K T) :
    ∀ K, (GenK.elems B B (.arr B) d R fun P X => Tab.filter P X).Reps K
      (fun xs ys => ys = xs.filter fun x => decide (∃ y, T x y)) :=
  elemsTest_sound (C := .arr B) (F := fun p (xs : List B.El) => xs.filter p) (fun h xs ys => Tab.filter_holds h xs ys)
    (fun _ _ _ h => List.filter_congr h) hR

open Classical in
/-- `takewhile(p)`, `Expand.primE`'s fit of the row (`elems`, `Tab.takewhile`): each array in demand to its longest
prefix in `dom T` (`elemsTest_sound`). -/
theorem takewhile_sound {B : Obj} {d : Bool} {R : Rel B B} {T : Den B B} (hR : ∀ K, R.Reps K T) :
    ∀ K, (GenK.elems B B (.arr B) d R fun P X => Tab.takewhile P X).Reps K
      (fun xs ys => ys = xs.takeWhile fun x => decide (∃ y, T x y)) :=
  elemsTest_sound (C := .arr B) (F := fun p (xs : List B.El) => xs.takeWhile p)
    (fun h xs ys => Tab.takewhile_holds h xs ys) (fun p q xs h => by
      induction xs with
      | nil => rfl
      | cons x xs ih =>
        simp only [List.takeWhile, h x List.mem_cons_self, ih fun y hy => h y (List.mem_cons_of_mem _ hy)]) hR

/-- `F(R)`, `Expand.primE`'s fit of the row (`elems`, `Tab.map`): each array in demand to every array of its length
related pointwise by `R`'s meaning `T`, `R` run knowing its domain is the elements, where it agrees with `T`. -/
theorem map_sound {A B : Obj} {d : Bool} {R : Rel A B} {T : Den A B} (hR : ∀ K, R.Reps K T) :
    ∀ K, (GenK.elems A B (.arr B) d R fun P X => Tab.map P X).Reps K
      (fun xs ys => ys.length = xs.length ∧ ∀ t (ht : t < xs.length) (ht' : t < ys.length), T (xs[t]'ht) (ys[t]'ht')) := by
  unfold GenK.elems
  exact ofVals_sound fun _ _ X t hK h xs ys hx _ _ => by
    obtain ⟨M, hM, h⟩ := bind_ok h
    obtain ⟨k, hk, h⟩ := bind_ok h
    obtain ⟨P, hP, h⟩ := bind_ok h
    have hi := (side_some hK xs).1 hx
    have ha := (reps_iff _ _ _).1 (hR ⟨some ⟨k.n, k.key⟩, none, none⟩) P hP
    have hPT : ∀ x ∈ xs, ∀ y, P.Holds x y ↔ T x y := fun x hm y => by
      obtain ⟨j, hj, -⟩ := (Tab.ran_holds hk x x).2 ⟨rfl, xs, (Tab.mem_holds hM xs x).2 ⟨hi, hm⟩⟩
      exact ha x y ((side_some rfl x).2 ⟨j, hj⟩) rfl trivial
    show t.Holds xs ys ↔ _
    rw [Tab.map_holds h, and_iff_right hi]
    exact and_congr_right fun _ => forall_congr' fun s => forall_congr' fun hs => forall_congr' fun hs' =>
      hPT _ (List.getElem_mem hs) _

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
      (fun _ hr a b _ _ _ => by cases hr; exact Iff.rfl) hF wF) T hT q x rfl rfl trivial
  unfold GenK.stepAfter GenK.after
  exact ofVals_sound fun _ _ V t hK h p c hx _ _ => by
    obtain ⟨D, hD, h⟩ := bind_ok h
    refine (Tab.loop_holds hF' h p c).trans ?_
    rw [← foldDen_iter]
    constructor
    · rintro ⟨p', hp', hW⟩; obtain ⟨rfl, -⟩ := (Tab.idU_holds hD p p').1 hp'; exact hW
    · exact fun hW => ⟨p, (Tab.idU_holds hD p p).2 ⟨rfl, (side_some hK p).1 hx⟩, hW⟩

end GenK

end Rel.Lang
