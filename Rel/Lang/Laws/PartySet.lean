import Rel.Lang.Laws.PartyCost
import Rel.Lang.Laws.StarLinear
import Rel.Lang.Laws.AopA5_6_ListCombinators
import Rel.Lang.Laws.LamTotal
import Rel.Lang.Laws.Cylinder
import Rel.Lang.PreludeSetify

/-! # `party(B) setify = Λ(under(B)) subseq (𝟙 − dom(∋ ∩ (∋ B))) setify` (B&dM §7.3, the company party)

`Rel/Programs/Party.lean` claims the parties of `e`, as sets, are exactly the sets of employees under `e` with no one
beside his boss. Premises: `B°B ⊑ 𝟙` (each employee has at most one boss, so two children's subtrees are disjoint) and
`dom(party(B)) = 𝟙` (every employee has a party, so no cycle lies below him; the right side is never empty). -/

namespace Rel.Lang
open Tab Rel.Rep
open scoped Rel.Core.Rel
open Rel.Core.Rel hiding id comp recip inter union zero le inl inr junc

/-! ### `under(B) = B°*` read as the least fixed point the row `star` means -/

section Under
variable {B : Core.Rel Int64 Int64}

/-- `B°*`: `e` to `e` and to everyone below `e`. -/
def UnderR (B : Core.Rel Int64 Int64) : Core.Rel Int64 Int64 := Core.Rel.mu fun X => 𝟙 _ ∪ B° ≫ X

/-- `B°⁺`: `e` to everyone strictly below `e`. -/
def PlusR (B : Core.Rel Int64 Int64) (e x : Int64) : Prop := ∃ k, B k e ∧ UnderR B k x

/-- Each employee has at most one boss. -/
def SimpleR (B : Core.Rel Int64 Int64) : Prop := ∀ y x z, B y x → B y z → x = z

/-- No member of `p` is the boss of another (`𝟙 − dom(∋ ∩ (∋ B))` holds at `p`). -/
def IndepL (B : Core.Rel Int64 Int64) (p : List Int64) : Prop := ∀ x ∈ p, ∀ z ∈ p, ¬ B z x

theorem under_mono (B : Core.Rel Int64 Int64) : Monotonic (fun X : Core.Rel Int64 Int64 => 𝟙 _ ∪ B° ≫ X) :=
  fun _ _ h => Core.Rel.le_iff.2 fun _ _ hab => by
    rcases hab with h0 | ⟨c, hc, hx⟩
    · exact .inl h0
    · exact .inr ⟨c, hc, Core.Rel.le_iff.1 h _ _ hx⟩

theorem under_iff (e x : Int64) : UnderR B e x ↔ e = x ∨ ∃ k, B k e ∧ UnderR B k x :=
  Iff.of_eq (congrFun (congrFun (mu_fix (under_mono B)).symm e) x)

theorem under_refl (e : Int64) : UnderR B e e := (under_iff e e).2 (.inl rfl)

theorem under_step {e k x : Int64} (hk : B k e) (h : UnderR B k x) : UnderR B e x := (under_iff e x).2 (.inr ⟨k, hk, h⟩)

/-- Induction over a path of `B°*`. -/
theorem under_ind (P : Int64 → Int64 → Prop) (h0 : ∀ e, P e e)
    (h1 : ∀ e k x, B k e → UnderR B k x → P k x → P e x) {e x : Int64} (h : UnderR B e x) : P e x := by
  have hY : (𝟙 _ ∪ B° ≫ fun a b => UnderR B a b ∧ P a b) ⊑ fun a b => UnderR B a b ∧ P a b :=
    Core.Rel.le_iff.2 fun a b hab => by
      rcases hab with h | ⟨k, hk, hx⟩
      · obtain rfl : a = b := h
        exact ⟨under_refl a, h0 a⟩
      · exact ⟨under_step hk hx.1, h1 a k b hk hx.1 hx.2⟩
  exact (Core.Rel.le_iff.1 (mu_le hY) e x h).2

theorem under_trans {a b c : Int64} (h1 : UnderR B a b) (h2 : UnderR B b c) : UnderR B a c :=
  under_ind (P := fun a b => UnderR B b c → UnderR B a c) (fun _ h => h) (fun _ _ _ hk _ ih h => under_step hk (ih h))
    h1 h2

/-- The last step of a path: `z` is `k`, or the boss `y` of `z` is under `k`. -/
theorem under_last {k z : Int64} (h : UnderR B k z) : z = k ∨ ∃ y, UnderR B k y ∧ B z y := by
  refine under_ind (P := fun k z => z = k ∨ ∃ y, UnderR B k y ∧ B z y) (fun _ => .inl rfl) (fun e k x hk _ ih => ?_) h
  rcases ih with rfl | ⟨y, hy, hb⟩
  · exact .inr ⟨e, under_refl e, hk⟩
  · exact .inr ⟨y, under_step hk hy, hb⟩

theorem plus_under {e x : Int64} (h : PlusR B e x) : UnderR B e x := let ⟨_, hk, hu⟩ := h; under_step hk hu

variable (hs : SimpleR B)
include hs

/-- Two employees above one are comparable, when each has at most one boss. -/
theorem under_cmp {a b x : Int64} (ha : UnderR B a x) (hb : UnderR B b x) : UnderR B a b ∨ UnderR B b a := by
  refine under_ind (P := fun a x => ∀ b, UnderR B b x → UnderR B a b ∨ UnderR B b a) (fun _ _ h => .inr h)
    (fun a k x hk _ ih b hb => ?_) ha b hb
  rcases ih b hb with h | h
  · exact .inl (under_step hk h)
  · rcases under_last h with rfl | ⟨y, hy, hky⟩
    · exact .inl (under_step hk (under_refl _))
    · obtain rfl := hs _ _ _ hk hky
      exact .inr hy

/-- The subtrees of two children of `e` are disjoint, unless `e` lies on a cycle. -/
theorem under_disj {e k k' x : Int64} (hA : ¬ PlusR B e e) (hk : B k e) (hk' : B k' e) (hne : k ≠ k')
    (h : UnderR B k x) (h' : UnderR B k' x) : False := by
  have one : ∀ {a b}, B a e → B b e → a ≠ b → UnderR B a b → False := fun ha hb hab hu => by
    rcases under_last hu with rfl | ⟨y, hy, hby⟩
    · exact hab rfl
    · obtain rfl := hs _ _ _ hb hby
      exact hA ⟨_, ha, hy⟩
  rcases under_cmp hs h h' with hu | hu
  · exact one hk hk' hne hu
  · exact one hk' hk (Ne.symm hne) hu

/-- No member of `k`'s subtree is the boss of a member of `k'`'s, for two children of `e` off a cycle. -/
theorem under_cross {e k k' x z : Int64} (hA : ¬ PlusR B e e) (hk : B k e) (hk' : B k' e) (hne : k ≠ k')
    (hz : UnderR B k z) (hx : UnderR B k' x) (hb : B z x) : False := by
  rcases under_last hz with rfl | ⟨y, hy, hzy⟩
  · obtain rfl := hs _ _ _ hb hk
    exact hA ⟨k', hk', hx⟩
  · obtain rfl := hs _ _ _ hzy hb
    exact under_disj hs hA hk hk' hne hy hx

/-- The concatenation of independent parts, one under each child of `e`, is independent. -/
theorem indep_flatten {e : Int64} (hA : ¬ PlusR B e e) : ∀ {ks : List Int64} {qs : List (List Int64)},
    ks.Pairwise (· ≠ ·) → (∀ k ∈ ks, B k e) →
    mapDen (A := .long) (B := .arr .long) (fun k q => (∀ x ∈ q, UnderR B k x) ∧ IndepL B q) ks qs →
    IndepL B qs.flatten
  | [], qs, _, _, hm => by rw [(mapDen_nil_iff _ _).1 hm]; simp [IndepL]
  | k :: ks, _, hp, hk, hm => by
    obtain ⟨q, qs, rfl, ⟨hq, hiq⟩, hm⟩ := (mapDen_cons_iff _ _ _ _).1 hm
    have ih := indep_flatten hA (List.pairwise_cons.1 hp).2 (fun k' h => hk k' (by simp [h])) hm
    have hk0 := hk k (by simp)
    have far : ∀ y ∈ qs.flatten, ∃ k' ∈ ks, k ≠ k' ∧ UnderR B k' y := fun y hy => by
      obtain ⟨q', hq', hy'⟩ := List.mem_flatten.1 hy
      obtain ⟨k', hk', h1, -⟩ := mapDen_mem hm q' hq'
      exact ⟨k', hk', (List.pairwise_cons.1 hp).1 k' hk', h1 y hy'⟩
    intro x hx z hz hb
    simp only [List.flatten_cons, List.mem_append] at hx hz
    rcases hx with hx | hx <;> rcases hz with hz | hz
    · exact hiq x hx z hz hb
    · obtain ⟨k', hk', hne, hu⟩ := far z hz
      exact under_cross hs hA (hk k' (by simp [hk'])) hk0 (Ne.symm hne) hu (hq x hx) hb
    · obtain ⟨k', hk', hne, hu⟩ := far x hx
      exact under_cross hs hA hk0 (hk k' (by simp [hk'])) hne (hq z hz) hu hb
    · exact ih x hx z hz hb

end Under

/-! ### The fold `hylo(⟨𝟙, kids(B)⟩, ⟨include, exclude⟩)` and the independent sets under `e` -/

section Forest
variable {B : Core.Rel Int64 Int64}

local notation "FB" => Core.Rel.mu (forestStep (A := Obj.long) (lamDen B°) SF)

theorem kids_iff {e : Int64} {ks : List Int64} (h : lamDen (A := .long) (B := .long) B° e ks) (k : Int64) :
    k ∈ ks ↔ B k e := ((lamDen_iff _ _ _).1 h).2 k

theorem kids_ne {e : Int64} {ks : List Int64} (h : lamDen (A := .long) (B := .long) B° e ks) :
    ks.Pairwise (· ≠ ·) :=
  ((lamDen_iff _ _ _).1 h).1.imp fun hlt he => by subst he; exact Obj.lt_irrefl _ _ hlt

/-- An employee with a fold value lies on no cycle. -/
theorem forest_acyc : ∀ e w, FB e w → ¬ PlusR B e e := by
  refine forest_ind (lamDen (A := Obj.long) (B := Obj.long) B°) SF (fun e _ => ¬ PlusR B e e) ?_
  intro e ks vs _ hk hm _ ⟨c, hc, hu⟩
  have ih : ∀ k, B k e → ¬ PlusR B k k := fun k hb => by
    obtain ⟨_, -, h⟩ := mapDen_mem_left hm k ((kids_iff hk k).2 hb); exact h
  rcases (under_iff c e).1 hu with rfl | ⟨c', hc', hu'⟩
  · exact ih c hc ⟨c, hc, under_refl c⟩
  · exact ih c hc ⟨c', hc', under_trans hu' (under_step hc (under_refl c))⟩

/-- What a fold pair of `e` is: its first party under `e`, its second strictly under `e`, both independent. -/
def ForestInv (B : Core.Rel Int64 Int64) (e : Int64) (w : List Int64 × List Int64) : Prop :=
  (∀ x ∈ w.1, UnderR B e x) ∧ (∀ x ∈ w.2, PlusR B e x) ∧ IndepL B w.1 ∧ IndepL B w.2

theorem forest_inv (hs : SimpleR B) : ∀ e w, FB e w → ForestInv B e w := by
  refine forest_ind (lamDen (A := Obj.long) (B := Obj.long) B°) SF (fun e w => ForestInv B e w) ?_
  intro e ks vs w hk hm hS
  have hA : ¬ PlusR B e e := forest_acyc e w ((forest_unfold _ _ e w).2
    ⟨ks, vs, hk, Core.Rel.le_iff.1 (mapDen_mono (Core.Rel.le_iff.2 fun _ _ h => h.1)) _ _ hm, hS⟩)
  have hkin : ∀ k ∈ ks, B k e := fun k h => (kids_iff hk k).1 h
  obtain ⟨h1, qs, hq, h2⟩ := (SX_iff _ _ _).1 hS
  have m1 : mapDen (A := .long) (B := .arr .long) (fun k q => (∀ x ∈ q, PlusR B k x) ∧ IndepL B q) ks
      (vs.map Prod.snd) := by
    have : (mapDen (fun a b => FB a b ∧ ForestInv B a b) ≫ mapDen (fun p ys => ys = Prod.snd p)) ks (vs.map Prod.snd) :=
      ⟨vs, hm, (mapDen_graph _ _ _).2 rfl⟩
    rw [mapDen_comp] at this
    refine Core.Rel.le_iff.1 (mapDen_mono (Core.Rel.le_iff.2 fun k q ⟨v, ⟨_, hv⟩, he⟩ => ?_)) _ _ this
    obtain rfl : q = v.2 := he
    exact ⟨hv.2.1, hv.2.2.2⟩
  have m2 : mapDen (A := .long) (B := .arr .long) (fun k q => (∀ x ∈ q, UnderR B k x) ∧ IndepL B q) ks qs := by
    have : (mapDen (fun a b => FB a b ∧ ForestInv B a b) ≫ mapDen CH) ks qs := ⟨vs, hm, hq⟩
    rw [mapDen_comp] at this
    refine Core.Rel.le_iff.1 (mapDen_mono (Core.Rel.le_iff.2 fun k q ⟨v, ⟨_, hv⟩, hc⟩ => ?_)) _ _ this
    rcases (hc : q = v.1 ∨ q = v.2) with rfl | rfl
    · exact ⟨hv.1, hv.2.2.1⟩
    · exact ⟨fun x hx => plus_under (hv.2.1 x hx), hv.2.2.2⟩
  have m1' : mapDen (A := .long) (B := .arr .long) (fun k q => (∀ x ∈ q, UnderR B k x) ∧ IndepL B q) ks
      (vs.map Prod.snd) :=
    Core.Rel.le_iff.1 (mapDen_mono (Core.Rel.le_iff.2 fun _ _ h => ⟨fun x hx => plus_under (h.1 x hx), h.2⟩)) _ _ m1
  have i1 := indep_flatten hs hA (kids_ne hk) hkin m1'
  have i2 := indep_flatten hs hA (kids_ne hk) hkin m2
  have inC : ∀ x ∈ (vs.map Prod.snd).flatten, ∃ k, B k e ∧ PlusR B k x := fun x hx => by
    obtain ⟨q, hq', hx'⟩ := List.mem_flatten.1 hx
    obtain ⟨k, hk', h, -⟩ := mapDen_mem m1 q hq'
    exact ⟨k, hkin k hk', h x hx'⟩
  rw [ForestInv, h1, h2]
  refine ⟨?_, ?_, ?_, i2⟩
  · intro x hx
    rcases List.mem_cons.1 hx with rfl | hx
    · exact under_refl _
    · obtain ⟨k, hk', h⟩ := inC x hx; exact under_step hk' (plus_under h)
  · intro x hx
    obtain ⟨q, hq', hx'⟩ := List.mem_flatten.1 hx
    obtain ⟨k, hk', h, -⟩ := mapDen_mem m2 q hq'
    exact ⟨k, hkin k hk', h x hx'⟩
  · intro x hx z hz hb
    rcases List.mem_cons.1 hx with hxe | hx <;> rcases List.mem_cons.1 hz with hze | hz
    · subst hxe hze; exact hA ⟨_, hb, under_refl _⟩
    · subst hxe
      obtain ⟨k, hk', c, hc, hu⟩ := inC z hz
      rcases under_last hu with rfl | ⟨y, hy, hzy⟩
      · obtain rfl := hs _ _ _ hc hb
        exact hA ⟨_, hk', under_refl _⟩
      · obtain rfl := hs _ _ _ hzy hb
        exact hA ⟨k, hk', under_step hc hy⟩
    · subst hze
      obtain ⟨k, hk', h⟩ := inC x hx
      exact hA ⟨k, hk', under_trans (plus_under h) (under_step hb (under_refl _))⟩
    · exact i1 x hx z hz hb

/-- A choice per child of a fold value and a part: the list of values, the list of parts, and their union. -/
theorem mapDen_build {T : Core.Rel (Obj.El .long) (Obj.El (.prod (.arr .long) (.arr .long)))}
    {C : Core.Rel (Obj.El (.prod (.arr .long) (.arr .long))) (Obj.El (.arr .long))} {G : Int64 → Int64 → Prop} :
    ∀ {ks : List Int64}, (∀ k ∈ ks, ∃ v q, T k v ∧ C v q ∧ ∀ x, x ∈ q ↔ G k x) →
      ∃ vs qs, mapDen T ks vs ∧ mapDen C vs qs ∧ ∀ x, x ∈ qs.flatten ↔ ∃ k ∈ ks, G k x
  | [], _ => ⟨[], [], mapDen_nil_nil _, mapDen_nil_nil _, by simp⟩
  | k :: ks, h => by
    obtain ⟨v, q, hv, hc, hq⟩ := h k (by simp)
    obtain ⟨vs, qs, hvs, hqs, hm⟩ := mapDen_build (ks := ks) fun k' hk' => h k' (by simp [hk'])
    refine ⟨v :: vs, q :: qs, (mapDen_cons_iff _ _ _ _).2 ⟨v, vs, rfl, hv, hvs⟩,
      (mapDen_cons_iff _ _ _ _).2 ⟨q, qs, rfl, hc, hqs⟩, fun x => ?_⟩
    simp [hq, hm, or_and_right, exists_or]

/-- Every independent set `S` under `e` is a fold party of `e`: the first if `e ∈ S`, the second if not. -/
theorem forest_ofSet : ∀ e w, FB e w → ∀ S : Int64 → Prop, (∀ x, S x → UnderR B e x) →
    (∀ x z, S x → S z → ¬ B z x) →
    (S e → ∃ w, FB e w ∧ ∀ x, x ∈ w.1 ↔ S x) ∧ (¬ S e → ∃ w, FB e w ∧ ∀ x, x ∈ w.2 ↔ S x) := by
  apply forest_ind (P := fun e _ => ∀ S : Int64 → Prop, (∀ x, S x → UnderR B e x) → (∀ x z, S x → S z → ¬ B z x) →
    (S e → ∃ w, FB e w ∧ ∀ x, x ∈ w.1 ↔ S x) ∧ (¬ S e → ∃ w, FB e w ∧ ∀ x, x ∈ w.2 ↔ S x))
  intro e ks vs _ hk hm _ S hU hI
  have ih : ∀ k ∈ ks, ∀ S' : Int64 → Prop, (∀ x, S' x → UnderR B k x) → (∀ x z, S' x → S' z → ¬ B z x) →
      (S' k → ∃ w, FB k w ∧ ∀ x, x ∈ w.1 ↔ S' x) ∧ (¬ S' k → ∃ w, FB k w ∧ ∀ x, x ∈ w.2 ↔ S' x) := fun k h => by
    obtain ⟨_, -, h⟩ := mapDen_mem_left hm k h; exact h
  have ihk := fun k (hk' : k ∈ ks) => ih k hk' (fun x => S x ∧ UnderR B k x) (fun _ h => h.2)
    (fun x z hx hz => hI x z hx.1 hz.1)
  have cover : ∀ x, S x → x ≠ e → ∃ k ∈ ks, UnderR B k x := fun x hx hne => by
    rcases (under_iff e x).1 (hU x hx) with h | ⟨k, hb, hu⟩
    · exact absurd h.symm hne
    · exact ⟨k, (kids_iff hk k).2 hb, hu⟩
  have hsnd : ∀ vs' : List (Obj.El (.prod (.arr .long) (.arr .long))), mapDen CH vs' (vs'.map Prod.snd) := fun vs' =>
    Core.Rel.le_iff.1 (mapDen_mono (T := fun p ys => ys = Prod.snd p) (Core.Rel.le_iff.2 fun _ _ h => .inr h)) _ _
      ((mapDen_graph _ _ _).2 rfl)
  constructor
  · intro he
    obtain ⟨vs', qs, hvs, hq, hmem⟩ := mapDen_build (C := fun p ys => ys = Prod.snd p)
      (G := fun k x => S x ∧ UnderR B k x) fun k hk' => by
        obtain ⟨v, hv, hvm⟩ := (ihk k hk').2 fun h => hI e k he h.1 ((kids_iff hk k).1 hk')
        exact ⟨v, v.2, hv, rfl, hvm⟩
    obtain rfl := (mapDen_graph _ _ _).1 hq
    refine ⟨(e :: (vs'.map Prod.snd).flatten, (vs'.map Prod.snd).flatten),
      (forest_unfold _ _ e _).2 ⟨ks, vs', hk, hvs, (SX_iff _ _ _).2 ⟨rfl, _, hsnd vs', rfl⟩⟩, fun x => ?_⟩
    show x ∈ e :: (vs'.map Prod.snd).flatten ↔ S x
    rw [List.mem_cons, hmem]
    constructor
    · rintro (rfl | ⟨k, -, h, -⟩)
      · exact he
      · exact h
    · intro hx
      by_cases hxe : x = e
      · exact .inl hxe
      · obtain ⟨k, hk', hu⟩ := cover x hx hxe; exact .inr ⟨k, hk', hx, hu⟩
  · intro he
    obtain ⟨vs', qs, hvs, hq, hmem⟩ := mapDen_build (C := CH) (G := fun k x => S x ∧ UnderR B k x) fun k hk' => by
      by_cases hSk : S k
      · obtain ⟨v, hv, hvm⟩ := (ihk k hk').1 ⟨hSk, under_refl k⟩
        exact ⟨v, v.1, hv, .inl rfl, hvm⟩
      · obtain ⟨v, hv, hvm⟩ := (ihk k hk').2 fun h => hSk h.1
        exact ⟨v, v.2, hv, .inr rfl, hvm⟩
    refine ⟨(e :: (vs'.map Prod.snd).flatten, qs.flatten),
      (forest_unfold _ _ e _).2 ⟨ks, vs', hk, hvs, (SX_iff _ _ _).2 ⟨rfl, qs, hq, rfl⟩⟩, fun x => ?_⟩
    show x ∈ qs.flatten ↔ S x
    rw [hmem]
    constructor
    · rintro ⟨k, -, h, -⟩; exact h
    · intro hx
      obtain ⟨k, hk', hu⟩ := cover x hx fun h => he (h ▸ hx)
      exact ⟨k, hk', hx, hu⟩

/-- **The parties of `e` as sets are the independent sets under `e`**, given a fold value at `e`. -/
theorem partySet_sem (hs : SimpleR B) (e : Int64) (he : ∃ w, FB e w) (ys : List Int64) :
    (∃ p, (FB ≫ CH) e p ∧ lamDen (memDen (A := .long)) p ys) ↔
      ∃ L, lamDen (A := Obj.long) (B := Obj.long) (UnderR B) e L ∧ ∃ c, c.Sublist L ∧ IndepL B c ∧ lamDen (memDen (A := .long)) c ys := by
  have hmem : ∀ {p c : List Int64}, (∀ x, x ∈ p ↔ x ∈ c) →
      (lamDen (memDen (A := .long)) p ys ↔ lamDen (memDen (A := .long)) c ys) := fun h => by
    simp only [lamDen_iff, memDen, h]
  constructor
  · rintro ⟨p, ⟨w, hw, hch⟩, hys⟩
    obtain ⟨hu1, hu2, hi1, hi2⟩ := forest_inv hs e w hw
    have hp : (∀ x ∈ p, UnderR B e x) ∧ IndepL B p := by
      rcases (hch : p = w.1 ∨ p = w.2) with rfl | rfl
      · exact ⟨hu1, hi1⟩
      · exact ⟨fun x hx => plus_under (hu2 x hx), hi2⟩
    obtain ⟨L, hL⟩ := lamDen_of_flat (A := .long) (B := .long) rfl (UnderR B) e
    have hc : ∀ x, x ∈ L.filter (fun x => decide (x ∈ p)) ↔ x ∈ p := fun x => by
      rw [List.mem_filter, decide_eq_true_iff]
      exact ⟨fun h => h.2, fun h => ⟨(((lamDen_iff _ _ _).1 hL).2 x).2 (hp.1 x h), h⟩⟩
    exact ⟨L, hL, _, List.filter_sublist, fun x hx z hz => hp.2 x ((hc x).1 hx) z ((hc z).1 hz), (hmem hc).2 hys⟩
  · rintro ⟨L, hL, c, hsub, hi, hys⟩
    obtain ⟨w0, hw0⟩ := he
    have hU : ∀ x, x ∈ c → UnderR B e x := fun x hx => (((lamDen_iff _ _ _).1 hL).2 x).1 (hsub.subset hx)
    have h := forest_ofSet e w0 hw0 (· ∈ c) hU fun x z hx hz => hi x hx z hz
    by_cases hec : e ∈ c
    · obtain ⟨w, hw, hm⟩ := h.1 hec
      exact ⟨w.1, ⟨w, hw, .inl rfl⟩, (hmem hm).2 hys⟩
    · obtain ⟨w, hw, hm⟩ := h.2 hec
      exact ⟨w.2, ⟨w, hw, .inr rfl⟩, (hmem hm).2 hys⟩

end Forest

/-! ### The terms of `partySet` -/

/-- `party(B) = hylo(⟨𝟙, kids(B)⟩, S) choose`, the hylo at index `k`, as the elaborator writes it. -/
abbrev Tm.partyT (k : Nat) (w : String) : Tm .long (.arr .long) := Tm.comp (Tm.forestHylo k w Tm.partyS) Tm.chooseT

/-- **`party(B) setify = Λ(under(B)) subseq (𝟙 − dom(∋ ∩ (∋ B))) setify`** (`partySet` of `Party.lean`): the parties
    of an employee, as sets, are the sets of employees under him with no one beside his boss. `B` is variable 0, `U` the
    universe of `E`. Premises: `B°B ⊑ 𝟙` (each employee has at most one boss, so the subtrees of two children are
    disjoint and a party built from them stays independent); `dom(party(B)) = 𝟙` (each employee has a party, so no
    cycle lies below him; the right side always holds the empty set, so this is needed). The hylo indices `k*` are the
    elaborator's, one per occurrence. -/
theorem Tm.partySet_den {n12 : USize} {m12 p12 : List String} {hw12 : QAtomicType.i64.width.isSome = true}
    {k1 k17 : Nat} {w1 w17 : String} (hk1 : k1 ≠ 0 := by decide) (hk17 : k17 ≠ 0 := by decide) (ρ : Val) :
    let U := (Gen.atom .i64 n12 m12 p12 hw12).1
    Tm.den ρ (Tm.comp (Tm.conv (Tm.var 0 : Tm .long .long)) (Tm.var 0 : Tm .long .long)) ⊑
      Tm.den ρ (Tm.comp (Tm.uni U) Tm.id) →
    Tm.den ρ (Tm.comp (Tm.uni U) (Tm.dom (Tm.partyT k17 w17))) = Tm.den ρ (Tm.comp (Tm.uni U) Tm.id) →
    Tm.den ρ (Tm.comp (Tm.uni U) (Tm.comp (Tm.partyT k1 w1) (Tm.prim (rowOf "setify") : Tm (.arr .long) (.arr .long)))) =
    Tm.den ρ (Tm.comp (Tm.uni U) (Tm.comp (Tm.comp (Tm.comp
        (Tm.lam (Tm.arg (Tm.prim (rowOf "star") : Tm .long .long) (Tm.conv (Tm.var 0 : Tm .long .long))))
        (Tm.call [] `Rel.Programs.prelude.subseq (some `Rel.Programs.prelude.subseq.conv) [.long] (Tm.subseqSnoc .long)))
        (Tm.diff Tm.id (Tm.dom (Tm.meet Tm.mem (Tm.comp Tm.mem (Tm.var 0 : Tm .long .long))))))
        (Tm.prim (rowOf "setify") : Tm (.arr .long) (.arr .long)))) := by
  intro U h1 h2
  have hF : ∀ k w, k ≠ 0 →
      (Tm.forestHylo k w Tm.partyS).den ρ = Core.Rel.mu (forestStep (lamDen (ρ 0 .long .long)°) SF) :=
    fun k w hk => Tm.forestHylo_den w _ SF ρ hk (fun _ => by rw [Tm.partyX_den, Tm.chooseT_den])
  have hPC : ∀ k w, k ≠ 0 → (Tm.partyT k w).den ρ =
      Core.Rel.comp (Core.Rel.mu (forestStep (lamDen (ρ 0 .long .long)°) SF)) CH :=
    fun k w hk => by show Core.Rel.comp _ _ = _; rw [hF k w hk]; rfl
  have hD : ∀ {A B : Obj} (R : Tm A B), (Tm.dom R).den ρ = 𝟙 _ ∩ R.den ρ ≫ (R.den ρ)° :=
    fun R => Prim.den_domRow _
  have hs : SimpleR (ρ 0 .long .long) := fun y x z hx hz =>
    ((uniComp_den U ρ Tm.id x z).1 (Core.Rel.le_iff.1 h1 x z
      (show Core.Rel.comp ((ρ 0 .long .long)°) (ρ 0 .long .long) x z from ⟨y, hx, hz⟩))).2
  have hP : ∀ e, InU U e → ∃ w, Core.Rel.mu (forestStep (lamDen (ρ 0 .long .long)°) SF) e w := fun e he => by
    have h := (uniComp_den U ρ Tm.id e e).2 ⟨he, show (Tm.id : Tm .long .long).den ρ e e from rfl⟩
    rw [← h2] at h
    obtain ⟨-, h⟩ := (uniComp_den U ρ (Tm.dom (Tm.partyT k17 w17)) e e).1 h
    rw [hD] at h
    obtain ⟨-, p, hp, -⟩ := h
    rw [hPC k17 w17 hk17] at hp
    obtain ⟨w, hw, -⟩ := hp
    exact ⟨w, hw⟩
  have hset : Prim.den (rowOf "setify") (.arr .long) (.arr .long) [] = lamDen (memDen (A := .long)) := by
    funext xs zs; exact propext (Tm.setifyDef_row ρ xs zs).symm
  have hstar : (Tm.arg (Tm.prim (rowOf "star") : Tm .long .long) (Tm.conv (Tm.var 0 : Tm .long .long))).den ρ =
      UnderR (ρ 0 .long .long) := by
    show Prim.den (rowOf "star") .long .long [⟨.long, .long, (ρ 0 .long .long)°⟩] = _
    rw [Prim.den_star]; rfl
  have hdiff : ∀ c b, (Tm.diff Tm.id (Tm.dom (Tm.meet Tm.mem (Tm.comp Tm.mem (Tm.var 0 : Tm .long .long))))).den ρ c b ↔
      c = b ∧ IndepL (ρ 0 .long .long) c := by
    intro c b
    show (c = b ∧ ¬ (Tm.dom (Tm.meet Tm.mem (Tm.comp Tm.mem (Tm.var 0 : Tm .long .long)))).den ρ c b) ↔ _
    rw [hD]
    constructor
    · rintro ⟨rfl, h⟩
      exact ⟨rfl, fun x hx z hz hb => h ⟨rfl, x, ⟨hx, z, hz, hb⟩, hx, z, hz, hb⟩⟩
    · rintro ⟨rfl, h⟩
      exact ⟨rfl, fun ⟨_, x, ⟨hx, z, hz, hb⟩, _⟩ => h x hx z hz hb⟩
  funext a ys; apply propext
  rw [uniComp_den U ρ, uniComp_den U ρ]
  refine and_congr_right fun he => ?_
  show (∃ p, (Tm.partyT k1 w1).den ρ a p ∧ Prim.den (rowOf "setify") (.arr .long) (.arr .long) [] p ys) ↔
    ∃ b, (∃ c, (∃ L, lamDen ((Tm.arg (Tm.prim (rowOf "star") : Tm .long .long)
        (Tm.conv (Tm.var 0 : Tm .long .long))).den ρ) a L ∧ (Tm.subseqSnoc .long).den (Val.args [] []) L c) ∧
      (Tm.diff Tm.id (Tm.dom (Tm.meet Tm.mem (Tm.comp Tm.mem (Tm.var 0 : Tm .long .long))))).den ρ c b) ∧
      Prim.den (rowOf "setify") (.arr .long) (.arr .long) [] b ys
  rw [hPC k1 w1 hk1, hset, hstar]
  simp only [Tm.subseqSnoc_iff, hdiff]
  rw [partySet_sem hs a (hP a he) ys]
  constructor
  · rintro ⟨L, hL, c, hsub, hi, hys⟩; exact ⟨c, ⟨c, ⟨L, hL, hsub⟩, rfl, hi⟩, hys⟩
  · rintro ⟨b, ⟨c, ⟨L, hL, hsub⟩, rfl, hi⟩, hys⟩; exact ⟨L, hL, c, hsub, hi, hys⟩

end Rel.Lang
