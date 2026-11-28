import Rel.Lang.Laws.AopA7_3_Party
import Rel.Lang.Laws.AopA6_2
import Rel.Lang.Laws.MssFused
import Rel.Lang.Laws.MssGreedy
import Rel.Lang.Laws.Eunion
import Rel.Lang.PreludeConcat
import Rel.Lang.PreludeRows

/-! # `c(B, r) max = best(B, r) cost(r)` (B&dM §7.3, the company party), on the concrete core

`Rel/Programs/Party.lean` computes the best party's cost two ways: `best(B, r) cost(r)` folds every party and keeps one
of greatest cost, `c(B, r) max` carries the pair (best cost with the employee, best cost without) up the forest. Both are
`hylo(⟨𝟙, kids(B)⟩, −)`, the least fixed point `Tm.hylo` means, so both are empty at an employee below a cycle and no
acyclicity is assumed. -/

namespace Rel.Lang
open Tab Rel.Rep
open scoped Rel.Core.Rel
open Rel.Core.Rel hiding id comp recip inter union zero le inl inr junc

/-! ### The forest hylomorphism `hylo(⟨𝟙, K⟩, S)` read pointwise -/

section Forest
variable {A V : Obj}

/-- One step of `hylo(⟨𝟙, K⟩, S)`: `e` to `v` through the children `ks` of `e` and their values `vs`. -/
def forestStep (K : Core.Rel A.El (Obj.El (.arr A))) (S : Core.Rel (Obj.El (.prod A (.arr V))) V.El)
    (X : Core.Rel A.El V.El) : Core.Rel A.El V.El :=
  fun e v => ∃ ks vs, K e ks ∧ mapDen X ks vs ∧ S (e, vs) v

theorem forestStep_mono (K : Core.Rel A.El (Obj.El (.arr A))) (S : Core.Rel (Obj.El (.prod A (.arr V))) V.El) :
    Monotonic (forestStep K S) := fun _ _ h => Core.Rel.le_iff.2 fun _ _ ⟨ks, vs, hk, hm, hs⟩ =>
  ⟨ks, vs, hk, Core.Rel.le_iff.1 (mapDen_mono h) _ _ hm, hs⟩

theorem forest_unfold (K : Core.Rel A.El (Obj.El (.arr A))) (S : Core.Rel (Obj.El (.prod A (.arr V))) V.El)
    (e : A.El) (v : V.El) : mu (forestStep K S) e v ↔ forestStep K S (mu (forestStep K S)) e v := by
  rw [mu_fix (forestStep_mono K S)]

/-- Induction over the derivation of a least fixed point value: `P` holds at `e` once it holds at its children. -/
theorem forest_ind (K : Core.Rel A.El (Obj.El (.arr A))) (S : Core.Rel (Obj.El (.prod A (.arr V))) V.El)
    (P : A.El → V.El → Prop)
    (h : ∀ e ks vs v, K e ks → mapDen (fun a b => mu (forestStep K S) a b ∧ P a b) ks vs → S (e, vs) v → P e v)
    (e : A.El) (v : V.El) (hv : mu (forestStep K S) e v) : P e v := by
  have hY : forestStep K S (fun a b => mu (forestStep K S) a b ∧ P a b) ⊑ fun a b => mu (forestStep K S) a b ∧ P a b :=
    Core.Rel.le_iff.2 fun e v ⟨ks, vs, hk, hm, hs⟩ =>
      ⟨(forest_unfold K S e v).2 ⟨ks, vs, hk, Core.Rel.le_iff.1 (mapDen_mono (Core.Rel.le_iff.2 fun _ _ h => h.1)) _ _ hm, hs⟩,
        h e ks vs v hk hm hs⟩
  exact (Core.Rel.le_iff.1 (mu_le hY) e v hv).2

end Forest

theorem mapDen_nil_nil {A B : Obj} (T : Core.Rel A.El B.El) : mapDen T [] [] := (mapDen_iff _ _ _).2 ⟨rfl, nofun⟩

theorem mapDen_nil_iff {A B : Obj} (T : Core.Rel A.El B.El) (ys : List B.El) : mapDen T [] ys ↔ ys = [] :=
  ⟨fun h => List.length_eq_zero_iff.1 ((mapDen_iff _ _ _).1 h).1, fun h => h ▸ mapDen_nil_nil T⟩

/-- `F(T)` at a cons: the heads related by `T`, the tails by `F(T)`. -/
theorem mapDen_cons_iff {A B : Obj} (T : Core.Rel A.El B.El) (x : A.El) (xs : List A.El) (zs : List B.El) :
    mapDen T (x :: xs) zs ↔ ∃ y ys, zs = y :: ys ∧ T x y ∧ mapDen T xs ys := by
  constructor
  · intro h
    obtain ⟨hl, h⟩ := (mapDen_iff _ _ _).1 h
    match zs, hl, h with
    | y :: ys, hl, h =>
      refine ⟨y, ys, rfl, h 0 (by simp) (by simp), (mapDen_iff _ _ _).2 ⟨by simpa using hl, fun t h1 h2 => ?_⟩⟩
      exact h (t + 1) (by simp; omega) (by simp; omega)
  · rintro ⟨y, ys, rfl, h0, h⟩
    obtain ⟨hl, h⟩ := (mapDen_iff _ _ _).1 h
    refine (mapDen_iff _ _ _).2 ⟨by simp [hl], fun t h1 h2 => ?_⟩
    cases t with
    | zero => exact h0
    | succ t => exact h t (by simp at h1; omega) (by simp at h2; omega)

theorem mapDen_choice {A B : Obj} {T : Core.Rel A.El B.El} : ∀ {xs : List A.El}, (∀ x ∈ xs, ∃ y, T x y) →
    ∃ ys, mapDen T xs ys
  | [], _ => ⟨[], mapDen_nil_nil T⟩
  | x :: xs, h => by
    obtain ⟨y, hy⟩ := h x (by simp)
    obtain ⟨ys, hys⟩ := mapDen_choice (xs := xs) fun z hz => h z (by simp [hz])
    exact ⟨y :: ys, (mapDen_cons_iff _ _ _ _).2 ⟨y, ys, rfl, hy, hys⟩⟩

theorem mapDen_mem {A B : Obj} {T : Core.Rel A.El B.El} : ∀ {xs : List A.El} {ys : List B.El}, mapDen T xs ys →
    ∀ y ∈ ys, ∃ x ∈ xs, T x y
  | [], ys, h => by rw [(mapDen_nil_iff _ _).1 h]; simp
  | x :: xs, _, h => by
    obtain ⟨y, ys, rfl, h0, h⟩ := (mapDen_cons_iff _ _ _ _).1 h
    intro z hz
    rcases List.mem_cons.1 hz with rfl | hz
    · exact ⟨x, by simp, h0⟩
    · obtain ⟨w, hw, hw'⟩ := mapDen_mem h z hz; exact ⟨w, by simp [hw], hw'⟩

/-! ### Sums of non-negative words -/

/-- The integer sum of a list of words. -/
def isum (ys : List Int64) : Int := (ys.map Int64.toInt).sum

theorem isum_cons (y : Int64) (ys : List Int64) : isum (y :: ys) = y.toInt + isum ys := by simp [isum]
theorem isum_append (a b : List Int64) : isum (a ++ b) = isum a + isum b := by
  induction a with
  | nil => simp [isum]
  | cons x a ih => rw [List.cons_append, isum_cons, isum_cons, ih]; omega

theorem isum_nonneg {ys : List Int64} (h : ∀ y ∈ ys, 0 ≤ y.toInt) : 0 ≤ isum ys := by
  induction ys with
  | nil => simp [isum]
  | cons y ys ih =>
    rw [isum_cons]
    have := h y (by simp); have := ih fun z hz => h z (by simp [hz]); omega

/-- `sum` at `i64` over non-negative words: defined exactly where the integer sum is a word, and equal to it. -/
theorem sumDen_nn {ys : List Int64} (h : ∀ y ∈ ys, 0 ≤ y.toInt) (s : Int64) :
    sumDen .i64 ys s ↔ isum ys < 2 ^ 63 ∧ s.toInt = isum ys := by
  rw [sumDen_fold (by decide)]
  induction ys using snocInd generalizing s with
  | nil =>
    rw [foldDen_empty]
    constructor
    · rintro ⟨_, rfl⟩; exact ⟨by simp [isum], rfl⟩
    · rintro ⟨-, hs⟩; exact ⟨0, Int64.toInt_inj.1 (by simpa [isum] using hs)⟩
  | snoc ys y ih =>
    have hy : 0 ≤ y.toInt := h y (by simp)
    have hys : ∀ z ∈ ys, 0 ≤ z.toInt := fun z hz => h z (by simp [hz])
    have h0 := isum_nonneg hys
    rw [foldDen_snoc, isum_append]
    have hsy : isum [y] = y.toInt := by simp [isum]
    rw [hsy]
    have hnul : ∀ x : Int64, 0 ≤ x.toInt → x ≠ Alg.nul := fun x hx e => by
      subst e; have : Alg.nul.toInt = -2 ^ 63 := by decide
      omega
    constructor
    · rintro ⟨u, hu, hs⟩
      obtain ⟨h1, h2⟩ := (ih hys u).1 hu
      obtain ⟨-, -, -, h4, rfl⟩ := (stepDen_add_iff _ _ _).1 hs
      refine ⟨by omega, ?_⟩
      rw [Int64.toInt_add, Int.bmod_eq_of_le (by omega) (by omega)]; omega
    · rintro ⟨h1, h2⟩
      have hb : -2 ^ 63 ≤ isum ys ∧ isum ys < 2 ^ 63 := ⟨by omega, by omega⟩
      refine ⟨Int64.ofInt (isum ys), (ih hys _).2 ⟨hb.2, Int64.toInt_ofInt_of_le hb.1 hb.2⟩, ?_⟩
      have e1 := Int64.toInt_ofInt_of_le hb.1 hb.2
      refine (stepDen_add_iff _ _ _).2 ⟨hnul _ (by omega), hnul _ hy, by omega, by omega, ?_⟩
      apply Int64.toInt_inj.1
      rw [Int64.toInt_add, Int.bmod_eq_of_le (by omega) (by omega)]; omega

theorem mapDen_mem_left {A B : Obj} {T : Core.Rel A.El B.El} : ∀ {xs : List A.El} {ys : List B.El}, mapDen T xs ys →
    ∀ x ∈ xs, ∃ y, T x y
  | [], _, _ => by simp
  | x :: xs, _, h => by
    obtain ⟨y, ys, rfl, h0, h⟩ := (mapDen_cons_iff _ _ _ _).1 h
    intro z hz
    rcases List.mem_cons.1 hz with rfl | hz
    · exact ⟨y, h0⟩
    · exact mapDen_mem_left h z hz

/-! ### The party semantics: costs, the fold `⟨include, exclude⟩` and the pair of best costs `tally` -/

section Party
variable (r : Core.Rel (Obj.El .long) (Obj.El .long)) (uN : Int64 → Prop)

/-- `p` costs `z`: its ratings `ys` (`F(r)`), each in `N`, sum to `z`. -/
def CostI (p : List Int64) (z : Int) : Prop :=
  ∃ ys, mapDen (A := .long) (B := .long) r p ys ∧ (∀ y ∈ ys, uN y) ∧ isum ys = z

theorem costI_nil (z : Int) : CostI r uN [] z ↔ z = 0 := by
  constructor
  · rintro ⟨ys, h, -, rfl⟩; rw [(mapDen_nil_iff _ _).1 h]; rfl
  · rintro rfl; exact ⟨[], mapDen_nil_nil _, by simp, rfl⟩

theorem costI_cons (e : Int64) (p : List Int64) (z : Int) :
    CostI r uN (e :: p) z ↔ ∃ y z', r e y ∧ uN y ∧ CostI r uN p z' ∧ z = y.toInt + z' := by
  constructor
  · rintro ⟨_, h, hu, rfl⟩
    obtain ⟨y, ys, rfl, h0, h⟩ := (mapDen_cons_iff _ _ _ _).1 h
    exact ⟨y, isum ys, h0, hu y (by simp), ⟨ys, h, fun x hx => hu x (by simp [hx]), rfl⟩, isum_cons _ _⟩
  · rintro ⟨y, _, h0, hy, ⟨ys, h, hu, rfl⟩, rfl⟩
    exact ⟨y :: ys, (mapDen_cons_iff _ _ _ _).2 ⟨y, ys, rfl, h0, h⟩,
      fun x hx => (List.mem_cons.1 hx).elim (· ▸ hy) (hu x), isum_cons _ _⟩

theorem costI_append (p q : List Int64) (z : Int) :
    CostI r uN (p ++ q) z ↔ ∃ z1 z2, CostI r uN p z1 ∧ CostI r uN q z2 ∧ z = z1 + z2 := by
  induction p generalizing z with
  | nil =>
    simp only [List.nil_append, costI_nil]
    exact ⟨fun h => ⟨0, z, rfl, h, by omega⟩, fun ⟨_, _, h1, h2, h3⟩ => by subst h1; rw [h3]; simpa using h2⟩
  | cons e p ih =>
    rw [List.cons_append, costI_cons]
    constructor
    · rintro ⟨y, z', h0, hy, hp, rfl⟩
      obtain ⟨z1, z2, h1, h2, rfl⟩ := (ih z').1 hp
      exact ⟨y.toInt + z1, z2, (costI_cons r uN e p _).2 ⟨y, z1, h0, hy, h1, rfl⟩, h2, by omega⟩
    · rintro ⟨_, z2, h1, h2, rfl⟩
      obtain ⟨y, z1, h0, hy, h1', rfl⟩ := (costI_cons r uN e p _).1 h1
      exact ⟨y, z1 + z2, h0, hy, (ih _).2 ⟨z1, z2, h1', h2, rfl⟩, by omega⟩

theorem costI_fun (hr : ∀ e y y', r e y → r e y' → y = y') :
    ∀ {p : List Int64} {z z' : Int}, CostI r uN p z → CostI r uN p z' → z = z'
  | [], _, _, h, h' => by rw [(costI_nil r uN _).1 h, (costI_nil r uN _).1 h']
  | e :: p, _, _, h, h' => by
    obtain ⟨y, z, h0, -, hp, rfl⟩ := (costI_cons r uN e p _).1 h
    obtain ⟨y', z', h0', -, hp', rfl⟩ := (costI_cons r uN e p _).1 h'
    rw [hr _ _ _ h0 h0', costI_fun hr hp hp']

theorem costI_nonneg (hnn : ∀ x, uN x → 0 ≤ x.toInt) {p : List Int64} {z : Int} (h : CostI r uN p z) : 0 ≤ z := by
  obtain ⟨ys, -, hu, rfl⟩ := h; exact isum_nonneg fun y hy => hnn y (hu y hy)

/-- `choose = π₁ ∪ π₂` on a pair of parties. -/
def CH : Core.Rel (Obj.El (.prod (.arr .long) (.arr .long))) (Obj.El (.arr .long)) := fun p q => q = p.1 ∨ q = p.2

/-- `S = ⟨include, exclude⟩` read pointwise. -/
def SF : Core.Rel (Obj.El (.prod .long (.arr (.prod (.arr .long) (.arr .long))))) (Obj.El (.prod (.arr .long) (.arr .long))) :=
  fun q w => w.1 = q.1 :: (q.2.map Prod.snd).flatten ∧ ∃ qs, mapDen CH q.2 qs ∧ w.2 = qs.flatten

/-- The binary `max` on `N`, guarded. -/
def MX : Core.Rel (Obj.El (.prod .long .long)) (Obj.El .long) :=
  fun v m => uN v.1 ∧ uN v.2 ∧ m = if v.2 < v.1 then v.1 else v.2

/-- `tally(r)` read pointwise, its sums already integers (`sumDen_nn`). -/
def ST : Core.Rel (Obj.El (.prod .long (.arr (.prod .long .long)))) (Obj.El (.prod .long .long)) :=
  fun q w => (∃ y s, r q.1 y ∧ uN y ∧ (∀ x ∈ q.2, uN x.2) ∧ uN s ∧ s.toInt = isum (q.2.map Prod.snd) ∧ uN w.1 ∧
      w.1.toInt = y.toInt + s.toInt) ∧ ∃ ms, mapDen (MX uN) q.2 ms ∧ uN w.2 ∧ w.2.toInt = isum ms

variable (K : Core.Rel (Obj.El .long) (Obj.El (.arr .long)))

/-- The claim the induction on `c` carries: both components are in `N`, bound the costs of every fold pair, and are
    attained by one fold pair. -/
def PA (e : Int64) (w : Obj.El (.prod .long .long)) : Prop :=
  uN w.1 ∧ uN w.2 ∧ (∀ p, mu (forestStep K SF) e p →
      (∀ z, CostI r uN p.1 z → z ≤ w.1.toInt) ∧ (∀ z, CostI r uN p.2 z → z ≤ w.2.toInt)) ∧
    ∃ p, mu (forestStep K SF) e p ∧ CostI r uN p.1 w.1.toInt ∧ CostI r uN p.2 w.2.toInt

theorem inc_bound : ∀ {ks : List Int64} {vs : List (Obj.El (.prod .long .long))}
    {ps : List (Obj.El (.prod (.arr .long) (.arr .long)))} {z : Int},
    mapDen (A := .long) (B := .prod .long .long) (fun k v => PA r uN K k v) ks vs → mapDen (mu (forestStep K SF)) ks ps →
    CostI r uN (ps.map Prod.snd).flatten z → z ≤ isum (vs.map Prod.snd)
  | [], vs, ps, z, hv, hp, hz => by
    rw [(mapDen_nil_iff _ _).1 hv, (mapDen_nil_iff _ _).1 hp] at *
    simp [(costI_nil r uN _).1 hz, isum]
  | k :: ks, _, _, z, hv, hp, hz => by
    obtain ⟨v, vs, rfl, hv0, hv⟩ := (mapDen_cons_iff _ _ _ _).1 hv
    obtain ⟨p, ps, rfl, hp0, hp⟩ := (mapDen_cons_iff _ _ _ _).1 hp
    simp only [List.map_cons, List.flatten_cons] at hz ⊢
    obtain ⟨z1, z2, h1, h2, rfl⟩ := (costI_append r uN _ _ _).1 hz
    rw [isum_cons]
    have := (hv0.2.2.1 p hp0).2 z1 h1
    have := inc_bound hv hp h2
    omega

theorem exc_bound : ∀ {ks : List Int64} {vs : List (Obj.El (.prod .long .long))}
    {ps : List (Obj.El (.prod (.arr .long) (.arr .long)))} {qs : List (Obj.El (.arr .long))} {ms : List Int64} {z : Int},
    mapDen (A := .long) (B := .prod .long .long) (fun k v => PA r uN K k v) ks vs → mapDen (mu (forestStep K SF)) ks ps → mapDen CH ps qs →
    mapDen (MX uN) vs ms → CostI r uN qs.flatten z → z ≤ isum ms
  | [], vs, ps, qs, ms, z, hv, hp, hq, hm, hz => by
    rw [(mapDen_nil_iff _ _).1 hv] at hm; rw [(mapDen_nil_iff _ _).1 hp] at hq
    rw [(mapDen_nil_iff _ _).1 hq] at hz; rw [(mapDen_nil_iff _ _).1 hm]
    simp [(costI_nil r uN _).1 hz, isum]
  | k :: ks, _, _, _, _, z, hv, hp, hq, hm, hz => by
    obtain ⟨v, vs, rfl, hv0, hv⟩ := (mapDen_cons_iff _ _ _ _).1 hv
    obtain ⟨p, ps, rfl, hp0, hp⟩ := (mapDen_cons_iff _ _ _ _).1 hp
    obtain ⟨q, qs, rfl, hq0, hq⟩ := (mapDen_cons_iff _ _ _ _).1 hq
    obtain ⟨m, ms, rfl, hm0, hm⟩ := (mapDen_cons_iff _ _ _ _).1 hm
    simp only [List.flatten_cons] at hz
    obtain ⟨z1, z2, h1, h2, rfl⟩ := (costI_append r uN _ _ _).1 hz
    rw [isum_cons]
    have := exc_bound hv hp hq hm h2
    obtain ⟨-, -, rfl⟩ := hm0
    have hb := hv0.2.2.1 p hp0
    have hle : z1 ≤ (if v.2 < v.1 then v.1 else v.2).toInt := by
      rcases hq0 with rfl | rfl
      · have := hb.1 z1 h1
        by_cases h : v.2 < v.1
        · rw [if_pos h]; omega
        · rw [if_neg h]; have := Int64.le_iff_toInt_le.1 (Int64.not_lt.1 h); omega
      · have := hb.2 z1 h1
        by_cases h : v.2 < v.1
        · rw [if_pos h]; have := Int64.lt_iff_toInt_lt.1 h; omega
        · rw [if_neg h]; omega
    omega

theorem attain : ∀ {ks : List Int64} {vs : List (Obj.El (.prod .long .long))} {ms : List Int64},
    mapDen (A := .long) (B := .prod .long .long) (fun k v => PA r uN K k v) ks vs → mapDen (MX uN) vs ms →
    ∃ ps qs, mapDen (mu (forestStep K SF)) ks ps ∧ mapDen CH ps qs ∧
      CostI r uN (ps.map Prod.snd).flatten (isum (vs.map Prod.snd)) ∧ CostI r uN qs.flatten (isum ms)
  | [], vs, ms, hv, hm => by
    rw [(mapDen_nil_iff _ _).1 hv] at hm ⊢; rw [(mapDen_nil_iff _ _).1 hm]
    exact ⟨[], [], mapDen_nil_nil _, mapDen_nil_nil _, (costI_nil r uN _).2 rfl, (costI_nil r uN _).2 rfl⟩
  | k :: ks, _, _, hv, hm => by
    obtain ⟨v, vs, rfl, hv0, hv⟩ := (mapDen_cons_iff _ _ _ _).1 hv
    obtain ⟨m, ms, rfl, hm0, hm⟩ := (mapDen_cons_iff _ _ _ _).1 hm
    obtain ⟨ps, qs, hp, hq, h1, h2⟩ := attain hv hm
    obtain ⟨p, hp0, hc1, hc2⟩ := hv0.2.2.2
    obtain ⟨-, -, rfl⟩ := hm0
    refine ⟨p :: ps, (if v.2 < v.1 then p.1 else p.2) :: qs, (mapDen_cons_iff _ _ _ _).2 ⟨p, ps, rfl, hp0, hp⟩,
      (mapDen_cons_iff _ _ _ _).2 ⟨_, qs, rfl, by unfold CH; split <;> simp, hq⟩, ?_, ?_⟩
    · simp only [List.map_cons, List.flatten_cons, isum_cons]
      exact (costI_append r uN _ _ _).2 ⟨_, _, hc2, h1, rfl⟩
    · simp only [List.flatten_cons, isum_cons]
      refine (costI_append r uN _ _ _).2 ⟨_, _, ?_, h2, rfl⟩
      split
      · exact hc1
      · exact hc2

section Laws
variable {r uN K}
variable (hK : ∀ e ks ks', K e ks → K e ks' → ks = ks') (hr : ∀ e y y', r e y → r e y' → y = y')

include hK hr in
/-- Induction on `c`: every value of `c` is the pair of best costs (`PA`). -/
theorem tally_best : ∀ e w, mu (forestStep K (ST r uN)) e w → PA r uN K e w := by
  apply forest_ind
  intro e ks vs w hk hv hS
  have hv' : mapDen (A := .long) (B := .prod .long .long) (fun k v => PA r uN K k v) ks vs :=
    Core.Rel.le_iff.1 (mapDen_mono (Core.Rel.le_iff.2 fun _ _ h => h.2)) _ _ hv
  obtain ⟨⟨y, s, hy, hyu, -, -, hs, hw1u, hw1⟩, ms, hm, hw2u, hw2⟩ := hS
  refine ⟨hw1u, hw2u, fun p hp => ?_, ?_⟩
  · obtain ⟨ks', ps, hk', hps, h1, qs, hq, h2⟩ := (forest_unfold K SF e p).1 hp
    obtain rfl := hK _ _ _ hk hk'
    refine ⟨fun z hz => ?_, fun z hz => ?_⟩
    · rw [h1] at hz
      obtain ⟨y', z', hy', -, hz', rfl⟩ := (costI_cons r uN _ _ _).1 hz
      obtain rfl := hr _ _ _ hy hy'
      have := inc_bound r uN K hv' hps hz'
      simp only at hs; omega
    · rw [h2] at hz
      have := exc_bound r uN K hv' hps hq hm hz
      omega
  · obtain ⟨ps, qs, hps, hq, h1, h2⟩ := attain r uN K hv' hm
    refine ⟨(e :: (ps.map Prod.snd).flatten, qs.flatten),
      (forest_unfold K SF e _).2 ⟨ks, ps, hk, hps, rfl, qs, hq, rfl⟩, ?_, ?_⟩
    · exact (costI_cons r uN _ _ _).2 ⟨y, _, hy, hyu, h1, by simp only at hs; omega⟩
    · rw [hw2]; exact h2

variable {uE : Int64 → Prop} (hKE : ∀ e ks, uE e → K e ks → ∀ k ∈ ks, uE k)
  (hP : ∀ e p q, uE e → mu (forestStep K SF) e p → CH p q → ∃ n, uN n ∧ CostI r uN q n.toInt)

include hK hr hKE hP in
/-- Induction on the fold: where a party is, `c` has a value, every guarded sum of it being some party's cost. -/
theorem tally_total : ∀ e p, mu (forestStep K SF) e p → uE e → ∃ w, mu (forestStep K (ST r uN)) e w := by
  apply forest_ind (P := fun e _ => uE e → ∃ w, mu (forestStep K (ST r uN)) e w)
  intro e ks ps _ hk hps _ he
  obtain ⟨vs, hvs⟩ := mapDen_choice (A := .long) (B := .prod .long .long) (T := mu (forestStep K (ST r uN)))
    (xs := ks) fun k hk' => (mapDen_mem_left hps k hk').elim fun _ h => h.2 (hKE e ks he hk k hk')
  have hv' : mapDen (A := .long) (B := .prod .long .long) (fun k v => PA r uN K k v) ks vs :=
    Core.Rel.le_iff.1 (mapDen_mono (Core.Rel.le_iff.2 fun k v h => tally_best hK hr k v h)) _ _ hvs
  have hvu : ∀ v ∈ vs, uN v.1 ∧ uN v.2 := fun v hv => by
    obtain ⟨k, -, hk⟩ := mapDen_mem hv' v hv; exact ⟨hk.1, hk.2.1⟩
  obtain ⟨ms, hms⟩ := mapDen_choice (A := .prod .long .long) (B := .long) (T := MX uN) (xs := vs)
    fun v hv => ⟨_, (hvu v hv).1, (hvu v hv).2, rfl⟩
  obtain ⟨ps', qs', hps', hq', h1, h2⟩ := attain r uN K hv' hms
  have hf1 : mu (forestStep K SF) e (e :: (ps'.map Prod.snd).flatten, qs'.flatten) :=
    (forest_unfold K SF e _).2 ⟨ks, ps', hk, hps', rfl, qs', hq', rfl⟩
  have hsnd : mapDen CH ps' (ps'.map Prod.snd) :=
    Core.Rel.le_iff.1 (mapDen_mono (T := fun p ys => ys = Prod.snd p) (Core.Rel.le_iff.2 fun _ _ h => .inr h)) _ _
      ((mapDen_graph _ _ _).2 rfl)
  have hf2 : mu (forestStep K SF) e (e :: (ps'.map Prod.snd).flatten, (ps'.map Prod.snd).flatten) :=
    (forest_unfold K SF e _).2 ⟨ks, ps', hk, hps', rfl, _, hsnd, rfl⟩
  obtain ⟨n1, hn1u, hn1⟩ := hP _ _ _ he hf1 (.inl rfl)
  obtain ⟨n0, hn0u, hn0⟩ := hP _ _ _ he hf2 (.inr rfl)
  obtain ⟨n2, hn2u, hn2⟩ := hP _ _ _ he hf1 (.inr rfl)
  obtain ⟨y, z', hy, hyu, hz', hn1e⟩ := (costI_cons r uN _ _ _).1 hn1
  have e0 := costI_fun r uN hr hn0 h1
  have e1 := costI_fun r uN hr hz' h1
  have e2 := costI_fun r uN hr hn2 h2
  exact ⟨(n1, n2), (forest_unfold K (ST r uN) e _).2 ⟨ks, vs, hk, hvs,
    ⟨y, n0, hy, hyu, fun x hx => (hvu x hx).2, hn0u, e0, hn1u, show n1.toInt = y.toInt + n0.toInt by omega⟩, ms, hms, hn2u, e2⟩⟩

/-- `p` costs the word `n` of `N`. -/
def Cost (r : Core.Rel (Obj.El .long) (Obj.El .long)) (uN : Int64 → Prop) (p : List Int64) (n : Int64) : Prop :=
  uN n ∧ CostI r uN p n.toInt

include hK hr hKE hP in
/-- **`c max = best cost`**, pointwise: the best pair's larger component is the cost of a party no other party
    outweighs, given the list `Lp` of `e`'s parties. -/
theorem cMax_sem (e : Int64) (he : uE e) (n : Int64) (Lp : List (List Int64))
    (hL : ∀ q, q ∈ Lp ↔ ∃ p, mu (forestStep K SF) e p ∧ CH p q) :
    (∃ w, mu (forestStep K (ST r uN)) e w ∧ MX uN w n) ↔
      ∃ p, p ∈ Lp ∧ (∀ q ∈ Lp, q = p ∨ ∃ a b, Cost r uN p a ∧ Cost r uN q b ∧ b ≤ a) ∧ Cost r uN p n := by
  constructor
  · rintro ⟨w, hw, hw1u, hw2u, rfl⟩
    obtain ⟨-, -, hb, p, hp, hc1, hc2⟩ := tally_best hK hr e w hw
    have hn : uN (if w.2 < w.1 then w.1 else w.2) := by split <;> assumption
    have hc : CostI r uN (if w.2 < w.1 then p.1 else p.2) (if w.2 < w.1 then w.1 else w.2).toInt := by
      split <;> assumption
    refine ⟨_, (hL _).2 ⟨p, hp, by unfold CH; split <;> simp⟩, fun q hq => .inr ?_, hn, hc⟩
    obtain ⟨p', hp', hch⟩ := (hL q).1 hq
    obtain ⟨b, hbu, hbc⟩ := hP _ _ _ he hp' hch
    refine ⟨_, b, ⟨hn, hc⟩, ⟨hbu, hbc⟩, Int64.le_iff_toInt_le.2 ?_⟩
    have h1 := (hb p' hp').1; have h2 := (hb p' hp').2
    have hlt := @Int64.lt_iff_toInt_lt w.2 w.1
    rcases hch with rfl | rfl
    · have := h1 _ hbc; split <;> rename_i h
      · omega
      · have : ¬ w.2.toInt < w.1.toInt := fun h' => h (hlt.2 h')
        omega
    · have := h2 _ hbc; split <;> rename_i h
      · have := hlt.1 h; omega
      · omega
  · rintro ⟨p, hp, hmax, hnu, hpc⟩
    obtain ⟨p0, hp0, hch0⟩ := (hL p).1 hp
    obtain ⟨w, hw⟩ := tally_total hK hr hKE hP e p0 hp0 he
    obtain ⟨hw1u, hw2u, hb, ps, hps, hc1, hc2⟩ := tally_best hK hr e w hw
    have hle : ∀ (q : List Int64) (v : Int64), uN v → CostI r uN q v.toInt → CH ps q → v.toInt ≤ n.toInt := by
      intro q v hv hq hch
      rcases hmax q ((hL q).2 ⟨ps, hps, hch⟩) with rfl | ⟨a, b, ⟨-, ha⟩, ⟨-, hb'⟩, hab⟩
      · exact Int.le_of_eq (costI_fun r uN hr hq hpc)
      · rw [costI_fun r uN hr hq hb', costI_fun r uN hr hpc ha]; exact Int64.le_iff_toInt_le.1 hab
    have l1 := hle _ _ hw1u hc1 (.inl rfl)
    have l2 := hle _ _ hw2u hc2 (.inr rfl)
    have hlt := @Int64.lt_iff_toInt_lt w.2 w.1
    refine ⟨w, hw, hw1u, hw2u, Int64.toInt_inj.1 ?_⟩
    rcases hch0 with rfl | rfl
    · have := (hb p0 hp0).1 _ hpc; split <;> rename_i h
      · omega
      · have : ¬ w.2.toInt < w.1.toInt := fun h' => h (hlt.2 h')
        omega
    · have := (hb p0 hp0).2 _ hpc; split <;> rename_i h
      · have := hlt.1 h; omega
      · omega

end Laws

end Party

/-! ### The terms of `Party.lean` read as the semantics above -/

/-- `hylo(⟨𝟙, kids(B)⟩, S)`, `B` at variable 0 and the recursive call at `k`, as the elaborator writes it. -/
abbrev Tm.forestHylo {V : Obj} (k : Nat) (w : String) (S : Tm (.prod .long (.arr V)) V) : Tm .long V :=
  Tm.hylo k w (Tm.comp (Tm.comp (Tm.pair Tm.id (Tm.lam (Tm.conv (Tm.var (A := .long) 0)))) (Tm.crossId (Tm.fmapT (Tm.var k)))) S)

theorem Tm.forestHylo_den {V : Obj} {k : Nat} (w : String) (S : Tm (.prod .long (.arr V)) V)
    (SD : Core.Rel (Obj.El (.prod .long (.arr V))) V.El) (ρ : Val) (hk : k ≠ 0)
    (hS : ∀ X : Core.Rel (Obj.El .long) V.El, S.den (ρ.bind k X) = SD) :
    (Tm.forestHylo k w S).den ρ = Core.Rel.mu (forestStep (lamDen (ρ 0 .long .long)°) SD) := by
  show Core.Rel.mu _ = _
  congr 1; funext X e v
  have h0 : ρ.bind k X 0 = ρ 0 := Val.bind_ne (Ne.symm hk)
  have h1 : ρ.bind k X k .long V = X := by simp [Val.bind]
  simp only [Tm.den, Tm.argDen, Prim.den_mapRow, hS, h0, h1, Core.Rel.comp_apply, Core.Rel.rpair, Core.Rel.graph,
    forestStep]
  apply propext; constructor
  · rintro ⟨⟨a, vs⟩, ⟨⟨e', ks⟩, ⟨he, hk⟩, ⟨_, rfl, ha⟩, _, rfl, hm⟩, hs⟩
    obtain rfl : _ = _ := he
    obtain rfl : _ = _ := ha
    exact ⟨_, _, hk, hm, hs⟩
  · rintro ⟨ks, vs, hk, hm, hs⟩
    exact ⟨(e, vs), ⟨(e, ks), ⟨rfl, hk⟩, ⟨e, rfl, rfl⟩, ks, rfl, hm⟩, hs⟩

/-- `S = ⟨(𝟙×(F(π₂)concat))cons, π₂F(choose)concat⟩`. -/
abbrev Tm.partyS : Tm (.prod .long (.arr (.prod (.arr .long) (.arr .long)))) (.prod (.arr .long) (.arr .long)) :=
  Tm.pair (Tm.comp (Tm.crossId (Tm.comp (Tm.fmapT Tm.outr) (Tm.prim (rowOf "concat") : Tm (.arr (.arr .long)) (.arr .long)))) (Tm.prim (rowOf "cons")))
    (Tm.comp (Tm.comp Tm.outr (Tm.fmapT Tm.chooseT)) (Tm.prim (rowOf "concat")))

theorem Tm.partyS_den (ρ : Val) : Tm.partyS.den ρ = SF := by
  funext q w
  simp only [Tm.den, Tm.argDen, Prim.den_mapRow, Prim.den_cons, Prim.den_concat, Core.Rel.comp_apply, Core.Rel.rpair,
    Core.Rel.graph, SF]
  have hc : (graph Prod.fst ∪ graph Prod.snd : Core.Rel (Obj.El (.prod (.arr .long) (.arr .long))) (Obj.El (.arr .long))) = CH :=
    rfl
  have hg : ∀ m w, mapDen (graph Prod.snd : Core.Rel (Obj.El (.prod (.arr .long) (.arr .long))) (Obj.El (.arr .long))) m w ↔
    w = m.map Prod.snd := mapDen_graph (A := .prod (.arr .long) (.arr .long)) (B := .arr .long) Prod.snd
  rw [hc]; apply propext; constructor
  · rintro ⟨⟨⟨a, b⟩, ⟨⟨_, rfl, ha⟩, _, rfl, ys, hys, rfl⟩, h1⟩, qs, ⟨_, rfl, hq⟩, h2⟩
    obtain rfl : _ = _ := ha
    rw [(hg _ _).1 hys] at h1
    exact ⟨h1, qs, hq, h2⟩
  · rintro ⟨h1, qs, hq, h2⟩
    exact ⟨⟨(q.1, (q.2.map Prod.snd).flatten), ⟨⟨_, rfl, rfl⟩, _, rfl, _, (hg _ _).2 rfl, rfl⟩, h1⟩, qs, ⟨_, rfl, hq⟩, h2⟩

/-- `arithRow "max"` at the atom `t` is `stepAt t greater`, as `Prim.den_plusRow`. -/
theorem Prim.den_maxRow {t : QAtomicType} :
    Prim.den (arithRow "max") (.prod (.atom t) (.atom t)) (.atom t) [] = stepAt t Rel.Kernel.Ew.greater := by
  have ho : ∀ ps, (arithRow "max").objs (.prod (.atom t) (.atom t)) (.atom t) ps = some [.atom t] := by
    simp [Prim.objs, Option.orElse, arithRow, OExp.unify, Prim.vars, OExp.vars, List.eraseDups, List.eraseDupsBy,
      List.eraseDupsBy.loop, List.lookup]
  have hf : rowDens.find? (·.1.sym == (arithRow "max").sym) =
      some ⟨⟨"max", fun σ => (.prod (σ₁ σ) (σ₁ σ), σ₁ σ)⟩, fun σ _ => stepOn Rel.Kernel.Ew.greater (σ₁ σ)⟩ := rfl
  unfold Prim.den; rw [hf, ho]; dsimp only; rw [dif_pos ⟨rfl, rfl⟩]; rfl

theorem Tm.cut2_max_den (ρ : Val) {t : QAtomicType} (U : Tm (.atom t) (.atom t)) (hU : ∀ x y, U.den ρ x y → x = y) :
    (Tm.cut2 (arithRow "max") U).den ρ = arithDen t Rel.Kernel.Ew.greater (U.den ρ) := by
  funext p w; obtain ⟨a, b⟩ := p; apply propext; rw [arithDen_iff]
  simp only [Tm.cut2, Tm.prod, Tm.den, Tm.argDen, Prim.den_maxRow, Core.Rel.comp, Core.Rel.rpair, Core.Rel.graph]
  constructor
  · rintro ⟨⟨qa, qb⟩, ⟨⟨a', e1, h1⟩, ⟨b', e2, h2⟩⟩, v, hs, hv⟩
    subst e1 e2
    obtain rfl := hU _ _ h1; obtain rfl := hU _ _ h2
    exact ⟨⟨_, h1⟩, ⟨_, h2⟩, v, hs, hv⟩
  · rintro ⟨⟨c1, h1⟩, ⟨c2, h2⟩, v, hs, hv⟩
    obtain rfl := hU _ _ h1; obtain rfl := hU _ _ h2
    exact ⟨(a, b), ⟨⟨a, rfl, h1⟩, ⟨b, rfl, h2⟩⟩, v, hs, hv⟩

section Bridge
variable {n : USize} (U : Vals .long n)

/-- Membership in the universe `U`. -/
def InU (x : Int64) : Prop := ∃ i, x = U.row i

theorem uni_den' (ρ : Val) : (Tm.uni U).den ρ = fun a b => a = b ∧ InU U a := by
  funext a b; apply propext; rw [Tm.uni_iff]
  exact ⟨fun ⟨i, h1, h2⟩ => ⟨h1.trans h2.symm, i, h1⟩, fun ⟨h, i, h1⟩ => ⟨i, h1, h ▸ h1⟩⟩

theorem uni_graph : ((graph U.row)° ≫ graph U.row : Core.Rel (Obj.El .long) (Obj.El .long)) =
    fun a b => a = b ∧ InU U a := uni_den' U Val.empty

theorem mapDen_corefl (P : Int64 → Prop) : ∀ (xs ys : List Int64),
    mapDen (A := .long) (B := .long) (fun a b => a = b ∧ P a) xs ys ↔ ys = xs ∧ ∀ x ∈ xs, P x
  | [], ys => by rw [mapDen_nil_iff]; simp
  | x :: xs, ys => by
    rw [mapDen_cons_iff, List.forall_mem_cons]
    constructor
    · rintro ⟨y, ys, rfl, ⟨rfl, hp⟩, h⟩; obtain ⟨rfl, h⟩ := (mapDen_corefl P xs ys).1 h; exact ⟨rfl, hp, h⟩
    · rintro ⟨rfl, hp, h⟩; exact ⟨x, xs, rfl, ⟨rfl, hp⟩, (mapDen_corefl P xs xs).2 ⟨rfl, h⟩⟩

variable (hnn : ∀ i, 0 ≤ (U.row i).toInt)

theorem inU_nonneg (hnn : ∀ i, 0 ≤ (U.row i).toInt) {x : Int64} (h : InU U x) : 0 ≤ x.toInt := by
  obtain ⟨i, rfl⟩ := h; exact hnn i

theorem inU_ne_nul (hnn : ∀ i, 0 ≤ (U.row i).toInt) {x : Int64} (h : InU U x) : x ≠ Alg.nul := by
  rintro rfl; have := inU_nonneg U hnn h; have : Alg.nul.toInt = -2 ^ 63 := by decide
  omega

theorem intStep_greater (a b : Int64) :
    Rel.Kernel.Ew.intStep Rel.Kernel.Ew.greater Alg.nul a b = if b < a then a else b := by
  unfold Rel.Kernel.Ew.intStep; rfl

/-- `F(U) sum U`, the sum cut to `U`, as the elaborator writes it; a `def`, so `simp` reads it by `Tm.sumU_den`. -/
def Tm.sumU : Tm (.arr .long) .long :=
  Tm.comp (Tm.comp (Tm.fmapT (Tm.uni U)) (Tm.prim sumRow)) (Tm.uni U)

variable (hnn : ∀ i, 0 ≤ (U.row i).toInt)

include hnn in
theorem Tm.sumU_den (ρ : Val) :
    (Tm.sumU U).den ρ = fun ys s => (∀ y ∈ ys, InU U y) ∧ InU U s ∧ s.toInt = isum ys := by
  funext ys s; apply propext
  unfold Tm.sumU
  simp only [Tm.den, Tm.argDen, Prim.den_mapRow, Prim.den_sumRow]
  rw [uni_graph]; simp only [Core.Rel.comp_apply, mapDen_corefl]
  constructor
  · rintro ⟨b, ⟨b1, hm, hs⟩, rfl, hb⟩
    obtain ⟨rfl, hall⟩ := (mapDen_corefl (InU U) _ _).1 hm
    exact ⟨hall, hb, ((sumDen_nn (fun y hy => inU_nonneg U hnn (hall y hy)) b).1 hs).2⟩
  · rintro ⟨hall, hs, he⟩
    have := Int64.toInt_lt s
    exact ⟨s, ⟨ys, (mapDen_corefl (InU U) _ _).2 ⟨rfl, hall⟩, (sumDen_nn (fun y hy => inU_nonneg U hnn (hall y hy)) s).2 ⟨by omega, he⟩⟩, rfl, hs⟩

theorem Tm.fmapT_den' {A B : Obj} (ρ : Val) (X : Tm A B) : (Tm.fmapT X).den ρ = mapDen (X.den ρ) := by
  simp only [Tm.fmapT, Tm.den, Tm.argDen, Prim.den_mapRow]

include hnn in
/-- `cost(r) = F(r) F(U) sum U`. -/
theorem Tm.costU_den (ρ : Val) (X : Tm .long .long) :
    (Tm.comp (Tm.fmapT X) (Tm.sumU U)).den ρ = Cost (X.den ρ) (InU U) := by
  funext p z; apply propext
  show (∃ ys, (Tm.fmapT X).den ρ p ys ∧ (Tm.sumU U).den ρ ys z) ↔ _
  rw [Tm.fmapT_den', Tm.sumU_den U hnn]; unfold Cost CostI
  constructor
  · rintro ⟨ys, hm, ha, hz, he⟩; exact ⟨hz, ys, hm, ha, he.symm⟩
  · rintro ⟨hz, ys, hm, ha, he⟩; exact ⟨ys, hm, ha, hz, he.symm⟩

include hnn in
theorem Tm.cutMax_den (ρ : Val) : (Tm.cut2 (arithRow "max") (Tm.uni U)).den ρ = MX (InU U) := by
  rw [Tm.cut2_max_den ρ _ (fun x y h => by rw [uni_den'] at h; exact h.1), uni_den']
  funext p m; obtain ⟨a, b⟩ := p; apply propext; rw [arithDen_iff]
  show _ ↔ InU U a ∧ InU U b ∧ m = if b < a then a else b
  constructor
  · rintro ⟨⟨_, -, ha⟩, ⟨_, -, hb⟩, v, hs, rfl, -⟩
    exact ⟨ha, hb, ((stepDen_iff _ _ _).1 hs).1.trans (intStep_greater a b)⟩
  · rintro ⟨ha, hb, rfl⟩
    have hi : InU U (if b < a then a else b) := by split <;> assumption
    refine ⟨⟨a, rfl, ha⟩, ⟨b, rfl, hb⟩, _, (stepDen_iff _ _ _).2 ⟨(intStep_greater a b).symm, inU_ne_nul U hnn hi, ?_⟩,
      rfl, hi⟩
    rw [if_neg (by decide), if_neg (by decide), if_neg (by decide)]; trivial

include hnn in
theorem Tm.cutPlus_den (ρ : Val) : (Tm.cut2 (arithRow "plus") (Tm.uni U)).den ρ =
    fun p w => InU U p.1 ∧ InU U p.2 ∧ InU U w ∧ w.toInt = p.1.toInt + p.2.toInt := by
  rw [Tm.cut2_plus_den ρ _ (fun x y h => by rw [uni_den'] at h; exact h.1), uni_den']
  funext p w; obtain ⟨a, b⟩ := p; apply propext; rw [arithDen_iff]
  show _ ↔ InU U a ∧ InU U b ∧ InU U w ∧ w.toInt = a.toInt + b.toInt
  constructor
  · rintro ⟨⟨_, -, ha⟩, ⟨_, -, hb⟩, v, hs, rfl, hv⟩
    obtain ⟨-, -, h1, h2, rfl⟩ := (stepDen_add_iff _ _ _).1 hs
    exact ⟨ha, hb, hv, by rw [Int64.toInt_add, Int.bmod_eq_of_le (by omega) (by omega)]⟩
  · rintro ⟨ha, hb, hw, he⟩
    have := Int64.toInt_lt w; have := inU_nonneg U hnn ha; have := inU_nonneg U hnn hb
    have hs : a + b = w := by rw [← Int64.toInt_inj, Int64.toInt_add, Int.bmod_eq_of_le (by omega) (by omega), he]
    exact ⟨⟨a, rfl, ha⟩, ⟨b, rfl, hb⟩, w, (stepDen_add_iff _ _ _).2
      ⟨inU_ne_nul U hnn ha, inU_ne_nul U hnn hb, by omega, by omega, hs.symm⟩, rfl, hw⟩

/-- `tally(r) = ⟨(π₁r) + (π₂F(π₂)sum), π₂F(max)sum⟩`, `r` at variable 1, as the elaborator writes it. -/
abbrev Tm.tallyT : Tm (.prod .long (.arr (.prod .long .long))) (.prod .long .long) :=
  Tm.pair (Tm.arg (Tm.arg (Tm.call [4, 5] `«_+_» none []
      (Tm.comp (Tm.pair (Tm.var 4) (Tm.var 5)) (Tm.cut2 (arithRow "plus") (Tm.uni U)))) (Tm.comp Tm.outl (Tm.var 1) : Tm (.prod .long (.arr (.prod .long .long))) .long))
      (Tm.comp (Tm.comp Tm.outr (Tm.fmapT (Tm.outr (A := .long)))) (Tm.sumU U) : Tm (.prod .long (.arr (.prod .long .long))) .long))
    (Tm.comp (Tm.comp Tm.outr (Tm.fmapT (Tm.cut2 (arithRow "max") (Tm.uni U)))) (Tm.sumU U))

include hnn in
theorem Tm.tallyT_den (ρ : Val) : (Tm.tallyT U).den ρ = ST (ρ 1 .long .long) (InU U) := by
  funext q w; obtain ⟨e, vs⟩ := q; obtain ⟨w1, w2⟩ := w; apply propext
  simp (config := {decide := true}) only [Tm.tallyT, Tm.den, Tm.argDen, Val.args, Val.bind, Tm.cutPlus_den U hnn,
    Tm.cutMax_den U hnn, Tm.sumU_den U hnn, Prim.den_mapRow, Core.Rel.comp_apply, Core.Rel.rpair, Core.Rel.graph,
    ite_true, dite_true, and_self, ↓reduceIte]
  have hg : ∀ m w, mapDen (graph Prod.snd : Core.Rel (Obj.El (.prod .long .long)) (Obj.El .long)) m w ↔
    w = m.map Prod.snd := mapDen_graph (A := .prod .long .long) (B := .long) Prod.snd
  unfold ST
  constructor
  · rintro ⟨⟨⟨y, s⟩, ⟨⟨_, rfl, hy⟩, ys, ⟨_, rfl, hm⟩, hall, hs, hse⟩, hyu, hsu, hw1, hwe⟩, ms, ⟨_, rfl, hms⟩, -, hw2,
      hw2e⟩
    obtain rfl := (hg _ _).1 hm
    exact ⟨⟨y, s, hy, hyu, fun x hx => hall _ (List.mem_map_of_mem hx), hsu, hse, hw1, hwe⟩, ms, hms, hw2, hw2e⟩
  · rintro ⟨⟨y, s, hy, hyu, hall, hsu, hse, hw1, hwe⟩, ms, hms, hw2, hw2e⟩
    refine ⟨⟨(y, s), ⟨⟨e, rfl, hy⟩, vs.map Prod.snd, ⟨vs, rfl, (hg _ _).2 rfl⟩, ?_, hsu, hse⟩, hyu, hsu, hw1, hwe⟩,
      ms, ⟨vs, rfl, hms⟩, ?_, hw2, hw2e⟩
    · intro z hz; obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hz; exact hall x hx
    · intro m hm; obtain ⟨x, -, ha, hb, rfl⟩ := mapDen_mem hms m hm; split <;> assumption

theorem uniComp_den {B : Obj} (ρ : Val) (S : Tm .long B) (a : Int64) (b : B.El) :
    (Tm.comp (Tm.uni U) S).den ρ a b ↔ InU U a ∧ S.den ρ a b := by
  show (∃ z, (Tm.uni U).den ρ a z ∧ S.den ρ z b) ↔ _
  rw [uni_den']
  exact ⟨fun ⟨_, ⟨rfl, h⟩, hs⟩ => ⟨h, hs⟩, fun ⟨h, hs⟩ => ⟨a, ⟨rfl, h⟩, hs⟩⟩

theorem conv4 {α β γ δ ε : Type} (R1 : Core.Rel α β) (R2 : Core.Rel β γ) (R3 : Core.Rel γ δ) (R4 : Core.Rel δ ε) :
    ((R4° ≫ (R3° ≫ R2°)) ≫ R1°) = (R1 ≫ ((R2 ≫ R3) ≫ R4))° := by
  funext a b; apply propext; simp only [Core.Rel.comp_apply, Core.Rel.recip_apply]
  constructor
  · rintro ⟨y, ⟨s, h4, z, h3, h2⟩, h1⟩; exact ⟨y, h1, s, ⟨z, h2, h3⟩, h4⟩
  · rintro ⟨y, h1, s, ⟨z, h2, h3⟩, h4⟩; exact ⟨y, ⟨s, h4, z, h3, h2⟩, h1⟩

/-- `cost(r)°`, its converses pushed to the leaves, as the elaborator writes it. -/
abbrev Tm.costC (X : Tm .long .long) : Tm .long (.arr .long) :=
  Tm.comp (Tm.comp (Tm.conv (Tm.uni U)) (Tm.comp (Tm.conv (Tm.prim sumRow)) (Tm.conv (Tm.fmapT (Tm.uni U)))))
    (Tm.conv (Tm.fmapT X))

/-- `R(r)° = cost(r) ≥ cost(r)°`. -/
abbrev Tm.costQ (X : Tm .long .long) : Tm (.arr .long) (.arr .long) :=
  Tm.comp (Tm.conv (Tm.costC U X))
    (Tm.comp (Tm.conv (Tm.arg (Tm.prim (cmpRelRow false)) (Tm.uni U) : Tm .long .long)) (Tm.costC U X))

include hnn in
theorem Tm.costC_den (ρ : Val) (X : Tm .long .long) : (Tm.costC U X).den ρ = (Cost (X.den ρ) (InU U))° := by
  rw [← Tm.costU_den U hnn ρ X]; exact conv4 _ _ _ _

include hnn in
/-- `est(R(r)°)` picks a list member whose cost no other member's exceeds. -/
theorem Tm.estCost_den (ρ : Val) (X : Tm .long .long) (xs : List (List Int64)) (p : List Int64) :
    (Tm.est (pairTest (Tm.costQ U X))).den ρ xs p ↔
      p ∈ xs ∧ ∀ c ∈ xs, c = p ∨ ∃ a b, Cost (X.den ρ) (InU U) p a ∧ Cost (X.den ρ) (InU U) c b ∧ b ≤ a := by
  have hleq : (Tm.arg (Tm.prim (cmpRelRow false)) (Tm.uni U) : Tm .long .long).den ρ = leqDen .i64 ((Tm.uni U).den ρ) := by
    simp only [Tm.den, Tm.argDen, Prim.den_cmpRelRow_le]
  have hQ : ∀ b c, (Tm.costQ U X).den ρ b c ↔ ∃ a b', Cost (X.den ρ) (InU U) b a ∧ Cost (X.den ρ) (InU U) c b' ∧ b' ≤ a := by
    intro b c
    show (∃ m, ((Tm.costC U X).den ρ)° b m ∧ ∃ n', ((Tm.arg (Tm.prim (cmpRelRow false)) (Tm.uni U) : Tm .long .long).den ρ)° m n' ∧
      (Tm.costC U X).den ρ n' c) ↔ _
    rw [Tm.costC_den U hnn, hleq, uni_den']
    simp only [Core.Rel.recip_apply]
    constructor
    · rintro ⟨m, hm, n', hl, hn⟩
      obtain ⟨-, -, hle⟩ := (leqDen_iff _ _ _ _).1 hl
      exact ⟨m, n', hm, hn, hle⟩
    · rintro ⟨m, n', hm, hn, hle⟩
      exact ⟨m, hm, n', (leqDen_iff _ _ _ _).2 ⟨⟨n', rfl, hn.1⟩, ⟨m, rfl, hm.1⟩, hle⟩, hn⟩
  rw [Tm.estPairTest_den]
  simp only [Core.Rel.inter_apply, Core.Rel.ldiv_apply, Core.Rel.recip_apply, Core.Rel.union_apply, memDen]
  refine and_congr_right fun _ => forall_congr' fun c => imp_congr_right fun _ => ?_
  rw [hQ]; constructor
  · rintro (h | h)
    · exact .inr h
    · exact .inl (show p = c from h).symm
  · rintro (h | h)
    · exact .inr (show p = c from h.symm)
    · exact .inl h

end Bridge

/-- **`c(B, r) max = best(B, r) cost(r)`** (`cMax` of `Party.lean`): the larger of the best include/exclude costs is
    the cost of a best party. `B` is variable 0, `r` variable 1, `U` the universe of `E`, `N` of `N` (non-negative
    words). Premises: `r°r ⊑ 𝟙` (`r` simple); `B ⊑ 𝟙B` (every employee of `B` is in `E`, so the recursion stays in
    `E`); `dom(Λ(party(B))) = 𝟙` (each node's parties form a list); `party(B) ⊑ party(B) dom(cost(r))` (every party
    has a cost in `N`, so no sum overflows). The hylo indices `k*` are the elaborator's, one per occurrence. -/
theorem Tm.cMax_den {n12 n41 : USize} {m12 p12 m41 p41 : List String}
    {hw12 hw41 : QAtomicType.i64.width.isSome = true} {k8 k9 k22 k24 k25 : Nat} {w8 w9 w22 w24 w25 : String}
    (hk8 : k8 ≠ 0 := by decide) (hk81 : 1 ≠ k8 := by decide) (hk9 : k9 ≠ 0 := by decide)
    (hk22 : k22 ≠ 0 := by decide) (hk24 : k24 ≠ 0 := by decide) (hk25 : k25 ≠ 0 := by decide)
    (hnn : ∀ U : Vals .long n41, U = (Gen.atom .i64 n41 m41 p41 hw41).1 → ∀ i, 0 ≤ (U.row i).toInt := by
      intro U hU i; subst hU
      exact (Rel.Lang.Gen.atom_get_bound rfl (by bnd_size) (by decide +kernel) (by decide +kernel)
        (by rw [Rel.Lang.Gen.unhex_size]; decide +kernel) 0 (2 ^ 62 - 1) (by decide) (by decide) (by decide +kernel) i).1)
    (ρ : Val) :
    let U := (Gen.atom .i64 n12 m12 p12 hw12).1
    let N := (Gen.atom .i64 n41 m41 p41 hw41).1
    Tm.den ρ (Tm.comp (Tm.conv (Tm.var 1 : Tm .long .long)) (Tm.var 1 : Tm .long .long)) ⊑
      Tm.den ρ (Tm.comp (Tm.uni N) Tm.id) →
    Tm.den ρ (Tm.var 0 : Tm .long .long) ⊑ Tm.den ρ (Tm.comp (Tm.uni U) (Tm.comp Tm.id (Tm.var 0 : Tm .long .long))) →
    Tm.den ρ (Tm.comp (Tm.uni U) (Tm.dom (Tm.lam (Tm.comp (Tm.forestHylo k22 w22 Tm.partyS) Tm.chooseT)))) =
      Tm.den ρ (Tm.comp (Tm.uni U) Tm.id) →
    Tm.den ρ (Tm.comp (Tm.uni U) (Tm.comp (Tm.forestHylo k24 w24 Tm.partyS) Tm.chooseT)) ⊑
      Tm.den ρ (Tm.comp (Tm.uni U) (Tm.comp (Tm.comp (Tm.forestHylo k25 w25 Tm.partyS) Tm.chooseT)
        (Tm.dom (Tm.comp (Tm.fmapT (Tm.var 1 : Tm .long .long)) (Tm.sumU N))))) →
    Tm.den ρ (Tm.comp (Tm.uni U) (Tm.comp (Tm.forestHylo k8 w8 (Tm.tallyT N)) (Tm.cut2 (arithRow "max") (Tm.uni N)))) =
    Tm.den ρ (Tm.comp (Tm.uni U) (Tm.comp (Tm.comp (Tm.lam (Tm.comp (Tm.forestHylo k9 w9 Tm.partyS) Tm.chooseT))
        (Tm.est (pairTest (Tm.costQ N (Tm.var 1))))) (Tm.comp (Tm.fmapT (Tm.var 1 : Tm .long .long)) (Tm.sumU N)))) := by
  intro U N h1 h4 h2 h3
  have hN := hnn N rfl
  have hF : ∀ k w, k ≠ 0 →
      (Tm.forestHylo k w Tm.partyS).den ρ = Core.Rel.mu (forestStep (lamDen (ρ 0 .long .long)°) SF) :=
    fun k w hk => Tm.forestHylo_den w _ SF ρ hk (fun _ => Tm.partyS_den _)
  have hPC : ∀ k w, k ≠ 0 → (Tm.comp (Tm.forestHylo k w Tm.partyS) Tm.chooseT).den ρ =
      Core.Rel.comp (Core.Rel.mu (forestStep (lamDen (ρ 0 .long .long)°) SF)) CH :=
    fun k w hk => by show Core.Rel.comp _ _ = _; rw [hF k w hk]; rfl
  have hT : (Tm.forestHylo k8 w8 (Tm.tallyT N)).den ρ =
      Core.Rel.mu (forestStep (lamDen (ρ 0 .long .long)°) (ST (ρ 1 .long .long) (InU N))) :=
    Tm.forestHylo_den w8 _ _ ρ hk8 (fun X => by rw [Tm.tallyT_den N hN, Val.bind_ne hk81])
  have hcost : (Tm.comp (Tm.fmapT (Tm.var 1 : Tm .long .long)) (Tm.sumU N)).den ρ = Cost (ρ 1 .long .long) (InU N) :=
    Tm.costU_den N hN ρ _
  have hD : ∀ {A B : Obj} (R : Tm A B), (Tm.dom R).den ρ = 𝟙 _ ∩ R.den ρ ≫ (R.den ρ)° :=
    fun R => Prim.den_domRow _
  have hr : ∀ e y y', ρ 1 .long .long e y → ρ 1 .long .long e y' → y = y' := fun e y y' h h' =>
    ((uniComp_den N ρ _ y y').1 (Core.Rel.le_iff.1 h1 y y'
      (show Core.Rel.comp ((ρ 1 .long .long)°) (ρ 1 .long .long) y y' from ⟨e, h, h'⟩))).2
  have hK : ∀ e ks ks', lamDen ((ρ 0 .long .long)°) e ks → lamDen ((ρ 0 .long .long)°) e ks' → ks = ks' :=
    fun _ _ _ h h' => lamDen_unique _ h h'
  have hKE : ∀ e ks, InU U e → lamDen ((ρ 0 .long .long)°) e ks → ∀ k ∈ ks, InU U k := fun e ks _ hk k hk' => by
    have h0 : ρ 0 .long .long k e := (((lamDen_iff _ _ _).1 hk).2 k).1 hk'
    exact ((uniComp_den U ρ (Tm.comp Tm.id (Tm.var 0 : Tm .long .long)) k e).1 (Core.Rel.le_iff.1 h4 k e h0)).1
  have hP : ∀ e p q, InU U e → Core.Rel.mu (forestStep (lamDen (ρ 0 .long .long)°) SF) e p → CH p q →
      ∃ n, InU N n ∧ CostI (ρ 1 .long .long) (InU N) q n.toInt := fun e p q he hp hq => by
    have h := Core.Rel.le_iff.1 h3 e q ((uniComp_den U ρ _ e q).2 ⟨he, by rw [hPC k24 w24 hk24]; exact ⟨p, hp, hq⟩⟩)
    obtain ⟨-, h⟩ := (uniComp_den U ρ _ e q).1 h
    obtain ⟨q', -, hd⟩ := h
    rw [hD, hcost] at hd
    obtain ⟨h0, n, hn, -⟩ := hd
    obtain rfl : q' = q := h0
    exact ⟨n, hn.1, hn.2⟩
  funext a n; apply propext
  rw [uniComp_den U ρ, uniComp_den U ρ]
  refine and_congr_right fun he => ?_
  show (∃ w, (Tm.forestHylo k8 w8 (Tm.tallyT N)).den ρ a w ∧ (Tm.cut2 (arithRow "max") (Tm.uni N)).den ρ w n) ↔
    (∃ p, (∃ Lp, lamDen ((Tm.comp (Tm.forestHylo k9 w9 Tm.partyS) Tm.chooseT).den ρ) a Lp ∧
      (Tm.est (pairTest (Tm.costQ N (Tm.var 1)))).den ρ Lp p) ∧
      (Tm.comp (Tm.fmapT (Tm.var 1 : Tm .long .long)) (Tm.sumU N)).den ρ p n)
  rw [hT, Tm.cutMax_den N hN, hPC k9 w9 hk9, hcost]
  simp only [Tm.estCost_den N hN]
  have hL : ∃ Lp, lamDen (Core.Rel.comp (Core.Rel.mu (forestStep (lamDen (ρ 0 .long .long)°) SF)) CH) a Lp := by
    have h := (uniComp_den U ρ Tm.id a a).2 ⟨he, show (Tm.id : Tm .long .long).den ρ a a from rfl⟩
    rw [← h2] at h
    obtain ⟨-, h⟩ := (uniComp_den U ρ _ a a).1 h
    rw [hD] at h
    obtain ⟨-, Lp, hLp, -⟩ := h
    change lamDen ((Tm.comp (Tm.forestHylo k22 w22 Tm.partyS) Tm.chooseT).den ρ) a Lp at hLp
    rw [hPC k22 w22 hk22] at hLp
    exact ⟨Lp, hLp⟩
  obtain ⟨Lp, hLp⟩ := hL
  rw [cMax_sem hK hr hKE hP a he n Lp fun q => ((lamDen_iff _ _ _).1 hLp).2 q]
  constructor
  · rintro ⟨p, hp, hmax, hc⟩; exact ⟨p, ⟨Lp, hLp, hp, hmax⟩, hc⟩
  · rintro ⟨p, ⟨Lp', hLp', hp, hmax⟩, hc⟩
    obtain rfl := lamDen_unique _ hLp hLp'
    exact ⟨p, hp, hmax, hc⟩

end Rel.Lang
