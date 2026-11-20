import Rel.Lang.GenKBits

/-! The `GenK` ops of the value verbs and the folds (`arith`, `fold`), each representing its constructor's case of
    `Tm.den` from the op's `Tab` law, in `GenKSpec`'s style (`reps_iff`, `ofVals_sound`). -/

namespace Rel.Lang

open Rel Rel.Rep Rel.Kernel Rel.Verify Gen
open scoped Rel.Core.Rel
open Rel.Core.Rel hiding id comp recip inter union zero le inl inr junc

/-- **The round invariant of `Tab.foldRounds`**, for any peel and step given by their laws: `Pe r x r'` splits what is
left `r` of a key's array into the element `x` read now and the rest `r'` (`cons°` for `peelL`, `snoc°` for `peelR`),
`St v x v'` is a round's step, and `W r v w` says the rounds from value `v` on what is left `r` end at `w` (`hW`, `hnil`).
Then the answer holds `out` and, for each key, `W` from its value in `P` along its rest. The rest is one per key
(`hf`) and `P` keyed inside it (`hsub`); a `pack` keeps the rows (`hpack`). -/
theorem Tab.foldRounds_holds {K E V : Obj} {peel : Tab K (.arr E) → Except String (Tab K E × Tab K (.arr E))}
    {step : Tab K V → Tab K E → Except String (Tab K V)}
    (Pe : (Obj.arr E).El → E.El → (Obj.arr E).El → Prop) (St : V.El → E.El → V.El → Prop)
    (W : (Obj.arr E).El → V.El → V.El → Prop)
    (hPe : ∀ r x r' y r'', Pe r x r' → Pe r y r'' → x = y ∧ r' = r'')
    (hnil : ∀ r, (¬∃ x r', Pe r x r') → ∀ v w, W r v w ↔ w = v)
    (hW : ∀ r x r' v w, Pe r x r' → (W r v w ↔ ∃ v', St v x v' ∧ W r' v' w))
    (hpeel : ∀ rest el rest', peel rest = .ok (el, rest') →
      (∀ k x, el.Holds k x ↔ ∃ r r', rest.Holds k r ∧ Pe r x r') ∧
      ∀ k r', rest'.Holds k r' ↔ ∃ r x, rest.Holds k r ∧ Pe r x r')
    (hstep : ∀ P el T, step P el = .ok T → ∀ k v', T.Holds k v' ↔ ∃ v x, P.Holds k v ∧ el.Holds k x ∧ St v x v')
    (hpack : ∀ R R' : Tab K V, R.pack = .ok R' → ∀ a b, R'.Holds a b ↔ R.Holds a b) :
    ∀ f rest P out res, Tab.foldRounds peel step f rest P out = .ok res →
      (∀ k r r', rest.Holds k r → rest.Holds k r' → r = r') → (∀ k v, P.Holds k v → ∃ r, rest.Holds k r) →
      ∀ k w, res.Holds k w ↔ out.Holds k w ∨ ∃ r v, rest.Holds k r ∧ P.Holds k v ∧ W r v w := by
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
    have hP'h : ∀ k v', P'.Holds k v' ↔ ∃ v x, P.Holds k v ∧ el.Holds k x ∧ St v x v' :=
      fun k v' => (hpack _ _ hP' k v').trans (hstep _ _ _ hs k v')
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
        exact ⟨r, w, hr, hw, (hnil r hnp w w).2 rfl⟩
      · obtain ⟨v, x, hv, hx, hs⟩ := (hP'h k v').1 hv'
        obtain ⟨r₁, x₁, hr₁, hp₁⟩ := (hrest' k r').1 hr'
        obtain ⟨r, r'', hr, hp⟩ := (hel k x).1 hx
        rw [hf k _ _ hr₁ hr] at hp₁
        obtain ⟨rfl, rfl⟩ := hPe _ _ _ _ _ hp hp₁
        exact ⟨r, v, hr, hv, (hW _ _ _ _ _ hp).2 ⟨v', hs, hW'⟩⟩
    · rintro ⟨r, v, hr, hv, hWr⟩
      by_cases hp : ∃ x r', Pe r x r'
      · obtain ⟨x, r', hp⟩ := hp
        obtain ⟨v', hs, hW'⟩ := (hW _ _ _ _ _ hp).1 hWr
        exact Or.inr ⟨r', v', (hrest' k r').2 ⟨r, x, hr, hp⟩,
          (hP'h k v').2 ⟨v, x, hv, (hel k x).2 ⟨r, r', hr, hp⟩, hs⟩, hW'⟩
      · obtain rfl := (hnil r hp v w).1 hWr
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

end GenK

end Rel.Lang
