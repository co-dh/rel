module

public import Rel.Lang.Den

@[expose] public section

/-! The Prelude law `Eunion` (`Programs/Prelude.lean`): `E(R) = E((𝟙÷∋)E(R))E(∋)`, `E(R)` is the union of the images of
    `Λ(R)`. On arrays (strictly ascending lists by `Obj.key`, not sets) the premise is that every image has such a
    list: two images that tie on `Obj.key` without being equal have none, and then both sides are empty. -/

namespace Rel.Lang

open scoped Rel.Core.Rel
open Rel.Core.Rel hiding id comp recip inter union zero le inl inr junc

variable {A B : Obj}

theorem EDen_iff (T : Core.Rel (Obj.El A) (Obj.El B)) (xs : Obj.El (.arr A)) (ys : Obj.El (.arr B)) :
    EDen T xs ys ↔ ys.Pairwise B.lt ∧ ∀ c, c ∈ ys ↔ ∃ x, x ∈ xs ∧ T x c := lamDen_iff _ _ _

/-- A strictly ascending list has no two members of one key. -/
theorem pw_tie_free {ws : List B.El} (hp : ws.Pairwise B.lt) {x y : B.El} (hx : x ∈ ws) (hy : y ∈ ws)
    (h : B.key x = B.key y) : x = y := by
  have no : ∀ {u v : B.El}, B.lt u v → B.key u = B.key v → False := fun {u v} h1 e =>
    Obj.lt_irrefl B v (by unfold Obj.lt at *; rwa [e] at h1)
  induction ws with
  | nil => exact nomatch hx
  | cons w t ih =>
    obtain ⟨hw, ht⟩ := List.pairwise_cons.1 hp
    rcases List.mem_cons.1 hx with ex | hx' <;> rcases List.mem_cons.1 hy with ey | hy'
    · exact ex.trans ey.symm
    · exact (no (ex ▸ hw y hy') (ex ▸ h)).elim
    · exact (no (ey ▸ hw x hx') (ey ▸ h.symm)).elim
    · exact ih ht hx' hy'

/-- Two strictly ascending lists with the same members are equal. -/
theorem pw_eq {l1 l2 : List B.El} (p1 : l1.Pairwise B.lt) (p2 : l2.Pairwise B.lt) (h : ∀ c, c ∈ l1 ↔ c ∈ l2) :
    l1 = l2 := by
  induction l1 generalizing l2 with
  | nil => cases l2 with
    | nil => rfl
    | cons b t => exact absurd ((h b).2 (List.mem_cons_self ..)) List.not_mem_nil
  | cons a t1 ih => cases l2 with
    | nil => exact absurd ((h a).1 (List.mem_cons_self ..)) List.not_mem_nil
    | cons b t2 =>
      obtain ⟨h1, q1⟩ := List.pairwise_cons.1 p1
      obtain ⟨h2, q2⟩ := List.pairwise_cons.1 p2
      have ab : a = b := by
        rcases List.mem_cons.1 ((h a).1 (List.mem_cons_self ..)) with e | ha
        · exact e
        · rcases List.mem_cons.1 ((h b).2 (List.mem_cons_self ..)) with e | hb
          · exact e.symm
          · exact (Obj.lt_asymm B (h2 a ha) (h1 b hb)).elim
      subst ab
      congr 1
      refine ih q1 q2 fun c => ⟨fun hc => ?_, fun hc => ?_⟩
      · rcases List.mem_cons.1 ((h c).1 (List.mem_cons_of_mem _ hc)) with e | e
        · exact (Obj.lt_irrefl B _ (e ▸ h1 c hc)).elim
        · exact e
      · rcases List.mem_cons.1 ((h c).2 (List.mem_cons_of_mem _ hc)) with e | e
        · exact (Obj.lt_irrefl B _ (e ▸ h2 c hc)).elim
        · exact e

/-- Arrays whose elements of equal key are equal, and whose keys are equal, are equal. -/
theorem arr_key_inj (B : Obj) : ∀ (xs ys : List B.El), (∀ x ∈ xs, ∀ y ∈ ys, B.key x = B.key y → x = y) →
    (Obj.arr B).key xs = (Obj.arr B).key ys → xs = ys
  | [], [], _, _ => rfl
  | [], _ :: _, _, h => by simp [Obj.key] at h
  | _ :: _, [], _, h => by simp [Obj.key] at h
  | x :: xs, y :: ys, hk, h => by
    simp only [Obj.key, List.foldr_cons, List.cons_append, List.cons.injEq, true_and] at h
    have e := Obj.key_prefix B x y _ _ h
    have hxy := hk x (List.mem_cons_self ..) y (List.mem_cons_self ..) e
    subst hxy
    rw [List.append_cancel_left_eq] at h
    rw [arr_key_inj B xs ys (fun a ha b hb => hk a (List.mem_cons_of_mem _ ha) b (List.mem_cons_of_mem _ hb)) h]

theorem lt_trans' (B : Obj) {x y z : B.El} (h1 : B.lt x y) (h2 : B.lt y z) : B.lt x z := List.lt_trans h1 h2

/-- Insert `e` into a strictly ascending list, unless a member of its key is already there. -/
theorem ins_pw (e : B.El) : ∀ L : List B.El, L.Pairwise B.lt → (∀ y ∈ L, B.key e = B.key y → e = y) →
    ∃ M : List B.El, M.Pairwise B.lt ∧ ∀ z, z ∈ M ↔ z = e ∨ z ∈ L
  | [], _, _ => ⟨[e], by simp, by simp⟩
  | y :: t, hp, hk => by
    obtain ⟨hy, ht⟩ := List.pairwise_cons.1 hp
    rcases Obj.lt_trichotomy B e y with h | h | h
    · refine ⟨e :: y :: t, List.pairwise_cons.2 ⟨fun z hz => ?_, hp⟩, by simp⟩
      rcases List.mem_cons.1 hz with rfl | hz
      · exact h
      · exact lt_trans' B h (hy z hz)
    · have ey := hk y (List.mem_cons_self ..) h
      exact ⟨y :: t, hp, fun z => by simp [ey]⟩
    · obtain ⟨M, hM, hm⟩ := ins_pw e t ht fun z hz => hk z (List.mem_cons_of_mem _ hz)
      refine ⟨y :: M, List.pairwise_cons.2 ⟨fun z hz => ?_, hM⟩, fun z => ?_⟩
      · rcases (hm z).1 hz with rfl | hz
        · exact h
        · exact hy z hz
      · simp only [List.mem_cons, hm]; exact or_left_comm

/-- A list with no two members of one key but equal ones has a strictly ascending list of the same members. -/
theorem sort_pw : ∀ l : List B.El, (∀ x ∈ l, ∀ y ∈ l, B.key x = B.key y → x = y) →
    ∃ L : List B.El, L.Pairwise B.lt ∧ ∀ z, z ∈ L ↔ z ∈ l
  | [], _ => ⟨[], by simp, by simp⟩
  | e :: l, hk => by
    obtain ⟨L, hL, hm⟩ := sort_pw l fun x hx y hy => hk x (List.mem_cons_of_mem _ hx) y (List.mem_cons_of_mem _ hy)
    obtain ⟨M, hM, hmm⟩ := ins_pw e L hL fun y hy ey =>
      hk e (List.mem_cons_self ..) y (List.mem_cons_of_mem _ ((hm y).1 hy)) ey
    exact ⟨M, hM, fun z => by simp only [hmm, hm, List.mem_cons]⟩

/-- The image of `T` is at most one list at each point. -/
theorem lamDen_unique (T : Core.Rel (Obj.El A) (Obj.El B)) {a : Obj.El A} {g g' : Obj.El (.arr B)}
    (h : lamDen T a g) (h' : lamDen T a g') : g = g' := by
  obtain ⟨p, m⟩ := (lamDen_iff T a g).1 h
  obtain ⟨p', m'⟩ := (lamDen_iff T a g').1 h'
  exact pw_eq p p' fun c => (m c).trans (m' c).symm

/-- A list of images, one for each point of `l` and none else. -/
theorem images (T : Core.Rel (Obj.El A) (Obj.El B)) (h : ∀ a, ∃ ys, lamDen T a ys) :
    ∀ l : List (Obj.El A), ∃ gs : List (Obj.El (.arr B)), (∀ g ∈ gs, ∃ x ∈ l, lamDen T x g) ∧
      ∀ x ∈ l, ∃ g ∈ gs, lamDen T x g
  | [] => ⟨[], by simp, by simp⟩
  | a :: l => by
    obtain ⟨gs, h1, h2⟩ := images T h l
    obtain ⟨g, hg⟩ := h a
    refine ⟨g :: gs, fun g' hg' => ?_, fun x hx => ?_⟩
    · rcases List.mem_cons.1 hg' with rfl | hg'
      · exact ⟨a, List.mem_cons_self .., hg⟩
      · obtain ⟨x, hx, hl⟩ := h1 g' hg'
        exact ⟨x, List.mem_cons_of_mem _ hx, hl⟩
    · rcases List.mem_cons.1 hx with rfl | hx
      · exact ⟨g, List.mem_cons_self .., hg⟩
      · obtain ⟨g', hg', hl⟩ := h2 x hx
        exact ⟨g', List.mem_cons_of_mem _ hg', hl⟩

/-- **`Eunion`**: `E(T) = E((𝟙÷∋)E(T)) E(∋)` — `(𝟙÷∋)E(T)` is `Λ(T)` (`lamDen T`), the premise says every image of `T`
    is a strictly ascending list. -/
theorem EDen_union (T : Core.Rel (Obj.El A) (Obj.El B)) (h : ∀ a, ∃ ys, lamDen T a ys) :
    EDen T = EDen (lamDen T) ≫ EDen memDen := by
  funext xs ws
  refine propext ⟨fun hw => ?_, fun ⟨L, h1, h2⟩ => ?_⟩
  · obtain ⟨hws, hwm⟩ := (EDen_iff T xs ws).1 hw
    obtain ⟨gs, hg1, hg2⟩ := images T h xs
    have hsub : ∀ x ∈ xs, ∀ g, lamDen T x g → ∀ c ∈ g, c ∈ ws := fun x hx g hg c hc =>
      (hwm c).2 ⟨x, hx, (((lamDen_iff T x g).1 hg).2 c).1 hc⟩
    obtain ⟨L, hL, hLm⟩ := sort_pw (B := Obj.arr B) gs (by
      intro g hg g' hg' e
      obtain ⟨x, hx, hl⟩ := hg1 g hg
      obtain ⟨x', hx', hl'⟩ := hg1 g' hg'
      exact arr_key_inj B _ _ (fun a ha b hb =>
        pw_tie_free hws (hsub x hx g hl a ha) (hsub x' hx' g' hl' b hb)) e)
    have hLx : ∀ g, g ∈ L ↔ ∃ x, x ∈ xs ∧ lamDen T x g := fun g => (hLm g).trans
      ⟨hg1 g, fun ⟨x, hx, hl⟩ => by
        obtain ⟨g0, hg0, hl0⟩ := hg2 x hx
        exact lamDen_unique T hl hl0 ▸ hg0⟩
    refine ⟨L, (EDen_iff _ xs L).2 ⟨hL, hLx⟩, (EDen_iff _ L ws).2 ⟨hws, fun c => ?_⟩⟩
    rw [hwm]
    refine ⟨fun ⟨x, hx, hT⟩ => ?_, fun ⟨g, hg, hc⟩ => ?_⟩
    · obtain ⟨g, hg, hl⟩ := hg2 x hx
      exact ⟨g, (hLm g).2 hg, (((lamDen_iff T x g).1 hl).2 c).2 hT⟩
    · obtain ⟨x, hx, hl⟩ := (hLx g).1 hg
      exact ⟨x, hx, (((lamDen_iff T x g).1 hl).2 c).1 hc⟩
  · obtain ⟨hL, hLm⟩ := (EDen_iff _ _ _).1 h1
    obtain ⟨hws, hwm⟩ := (EDen_iff _ _ _).1 h2
    refine (EDen_iff T xs ws).2 ⟨hws, fun c => (hwm c).trans ⟨fun ⟨g, hg, hc⟩ => ?_, fun ⟨x, hx, hT⟩ => ?_⟩⟩
    · obtain ⟨x, hx, hl⟩ := (hLm g).1 hg
      exact ⟨x, hx, (((lamDen_iff T x g).1 hl).2 c).1 hc⟩
    · obtain ⟨g, hg⟩ := h x
      exact ⟨g, (hLm g).2 ⟨x, hx, hg⟩, (((lamDen_iff T x g).1 hg).2 c).2 hT⟩

/-- The prelude's image union law, with `Λ(R)` defined at every point. -/
theorem Tm.Eunion_den {R : Tm A B} (ρ : Val)
    (h : (Tm.dom (.lam R)).den ρ = (Tm.id (A := A)).den ρ) :
    (Tm.lam (.comp .mem R)).den ρ =
      (Tm.comp (.lam (.comp .mem (.lam R))) (.lam (.comp .mem .mem))).den ρ :=
  EDen_union (R.den ρ) (Tm.entire_of_dom h)

/-- An image inside a list `l`, with no two members of one key but equal ones, has a strictly ascending list. -/
theorem lamDen_total (T : Core.Rel (Obj.El A) (Obj.El B)) (a : A.El) (l : List B.El) (hl : ∀ b, T a b → b ∈ l)
    (hk : ∀ b c, T a b → T a c → B.key b = B.key c → b = c) : ∃ ys, lamDen T a ys := by
  classical
  obtain ⟨L, hL, hm⟩ := sort_pw (B := B) (l.filter fun b => decide (T a b)) fun x hx y hy e => by
    simp only [List.mem_filter, decide_eq_true_eq] at hx hy
    exact hk x y hx.2 hy.2 e
  exact ⟨L, (lamDen_iff T a L).2 ⟨hL, fun b => by simpa [hm, List.mem_filter] using hl b⟩⟩


end Rel.Lang
