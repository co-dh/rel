import Rel.Lang.Laws.PartySet

/-! # `Λ(guests(B, r)) setify ⊑ best(B, r) setify` (B&dM §7.3, law 53 compared as sets)

`Rel/Programs/Party.lean` claims the guests `win` and `guests` recover from the pair of best costs `c` form, as a set,
a best party. The proof builds, by induction on `c`, a fold pair of each employee whose parts hold the guests and cost
`c`'s components; the chosen part is then a party of cost `c max`, which `cMax_sem` shows no party outweighs. -/

namespace Rel.Lang
open Tab Rel.Rep
open scoped Rel.Core.Rel
open Rel.Core.Rel hiding id comp recip inter union zero le inl inr junc

section Guests
variable {B : Core.Rel Int64 Int64} {r : Core.Rel (Obj.El .long) (Obj.El .long)} {uN : Int64 → Prop}
  {W : Int64 → Prop} {G : Int64 → Int64 → Prop}

local notation "FB" => Core.Rel.mu (forestStep (A := Obj.long) (lamDen B°) SF)
local notation "CB" => Core.Rel.mu (forestStep (A := Obj.long) (lamDen B°) (ST r uN))

/-- What the induction on `c` carries at `e`: a fold pair whose parts cost `w` and hold the guests with `e` in (`e`
    and the guests of its grandchildren) and with `e` out (the guests of its children). -/
def GP (B : Core.Rel Int64 Int64) (r : Core.Rel (Obj.El .long) (Obj.El .long)) (uN : Int64 → Prop)
    (G : Int64 → Int64 → Prop) (e : Int64) (w : Obj.El (.prod .long .long)) : Prop :=
  ∃ p, Core.Rel.mu (forestStep (A := Obj.long) (lamDen B°) SF) e p ∧ CostI r uN p.1 w.1.toInt ∧
    CostI r uN p.2 w.2.toInt ∧ (∀ y, y ∈ p.1 ↔ y = e ∨ ∃ k, B k e ∧ ∃ g, B g k ∧ G g y) ∧
    (∀ y, y ∈ p.2 ↔ ∃ k, B k e ∧ G k y)

variable (hG : ∀ x y, G x y ↔ (W x ∧ (y = x ∨ ∃ k, B k x ∧ ∃ g, B g k ∧ G g y)) ∨ (¬ W x ∧ ∃ k, B k x ∧ G k y))
  (hW : ∀ x w, Core.Rel.mu (forestStep (A := Obj.long) (lamDen B°) (ST r uN)) x w → (W x ↔ w.2 ≤ w.1))

include hG hW in
/-- The children's pairs: the parts they contribute to `e` in and to `e` out, their costs and their guests. -/
theorem attainG : ∀ {ks : List Int64} {vs : List (Obj.El (.prod .long .long))} {ms : List Int64},
    mapDen (A := .long) (B := .prod .long .long) (fun k v => CB k v ∧ GP B r uN G k v) ks vs → mapDen (MX uN) vs ms →
    ∃ ps qs, mapDen FB ks ps ∧ mapDen CH ps qs ∧
      CostI r uN (ps.map Prod.snd).flatten (isum (vs.map Prod.snd)) ∧ CostI r uN qs.flatten (isum ms) ∧
      (∀ y, y ∈ (ps.map Prod.snd).flatten ↔ ∃ k ∈ ks, ∃ g, B g k ∧ G g y) ∧ (∀ y, y ∈ qs.flatten ↔ ∃ k ∈ ks, G k y)
  | [], vs, ms, hv, hm => by
    rw [(mapDen_nil_iff _ _).1 hv] at hm ⊢; rw [(mapDen_nil_iff _ _).1 hm]
    exact ⟨[], [], mapDen_nil_nil _, mapDen_nil_nil _, (costI_nil r uN _).2 rfl, (costI_nil r uN _).2 rfl,
      by simp, by simp⟩
  | k :: ks, _, _, hv, hm => by
    obtain ⟨v, vs, rfl, ⟨hcv, hv0⟩, hv⟩ := (mapDen_cons_iff _ _ _ _).1 hv
    obtain ⟨m, ms, rfl, hm0, hm⟩ := (mapDen_cons_iff _ _ _ _).1 hm
    obtain ⟨ps, qs, hp, hq, h1, h2, hm1, hm2⟩ := attainG hv hm
    obtain ⟨p, hp0, hc1, hc2, hs1, hs2⟩ := hv0
    obtain ⟨-, -, rfl⟩ := (MX_iff uN _ _).1 hm0
    have hlt := @Int64.lt_iff_toInt_lt v.2 v.1
    have hle := @Int64.le_iff_toInt_le v.2 v.1
    refine ⟨p :: ps, (if v.2 ≤ v.1 then p.1 else p.2) :: qs, (mapDen_cons_iff _ _ _ _).2 ⟨p, ps, rfl, hp0, hp⟩,
      (mapDen_cons_iff _ _ _ _).2 ⟨_, qs, rfl, by split <;> simp [CH, Core.Rel.graph], hq⟩, ?_, ?_, ?_, ?_⟩
    · simp only [List.map_cons, List.flatten_cons, isum_cons]
      exact (costI_append r uN _ _ _).2 ⟨_, _, hc2, h1, rfl⟩
    · simp only [List.flatten_cons, isum_cons]
      refine (costI_append r uN _ _ _).2 ⟨_, _, ?_, h2, rfl⟩
      by_cases h : v.2 < v.1
      · rw [if_pos h, if_pos (hle.2 (Int.le_of_lt (hlt.1 h)))]; exact hc1
      · rw [if_neg h]
        by_cases h' : v.2 ≤ v.1
        · rw [if_pos h', show v.2.toInt = v.1.toInt by have := hle.1 h'; have : ¬ v.2.toInt < v.1.toInt := fun x => h (hlt.2 x); omega]
          exact hc1
        · rw [if_neg h']; exact hc2
    · intro y
      simp only [List.map_cons, List.flatten_cons, List.mem_append, hs2, hm1, List.mem_cons, or_and_right, exists_or, exists_eq_left]
    · intro y
      simp only [List.flatten_cons, List.mem_append, hm2, List.mem_cons, or_and_right, exists_or, exists_eq_left]
      refine or_congr_left ?_
      rw [hG k y, hW k v hcv]
      by_cases h' : v.2 ≤ v.1 <;> simp [h', hs1, hs2]

include hG hW in
/-- Induction on `c`: each value of `c` is the cost pair of a fold pair holding the guests (`GP`). -/
theorem guests_fold : ∀ e w, CB e w → GP B r uN G e w := by
  refine forest_ind (lamDen (A := Obj.long) (B := Obj.long) B°) (ST r uN) (fun e w => GP B r uN G e w) ?_
  intro e ks vs w hk hv hS
  obtain ⟨⟨y, s, hy, hyu, -, -, hs, -, hw1⟩, ms, hm, -, hw2⟩ := (ST_iff r uN _ _).1 hS
  obtain ⟨ps, qs, hps, hq, h1, h2, hm1, hm2⟩ := attainG hG hW hv hm
  refine ⟨(e :: (ps.map Prod.snd).flatten, qs.flatten),
    (forest_unfold _ SF e _).2 ⟨ks, ps, hk, hps, (SX_iff _ _ _).2 ⟨rfl, qs, hq, rfl⟩⟩, ?_, ?_, ?_, ?_⟩
  · exact (costI_cons r uN _ _ _).2 ⟨y, _, hy, hyu, h1, by simp only at hs hw1; omega⟩
  · rw [hw2]; exact h2
  · intro x; simp only [List.mem_cons, hm1, kids_iff hk]
  · intro x; simp only [hm2, kids_iff hk]

variable (hr : ∀ e y y', r e y → r e y' → y = y')

include hr in
/-- `c` is a function: both components of a value are best costs, so two values agree. -/
theorem tally_fun {e : Int64} {w w' : Obj.El (.prod .long .long)} (h : CB e w) (h' : CB e w') : w = w' := by
  have hK : ∀ e ks ks', lamDen (A := Obj.long) (B := Obj.long) B° e ks → lamDen (A := Obj.long) (B := Obj.long) B° e ks' → ks = ks' :=
    fun _ _ _ h h' => lamDen_unique _ h h'
  obtain ⟨-, -, hb, p, hp, hc1, hc2⟩ := tally_best hK hr e w h
  obtain ⟨-, -, hb', p', hp', hc1', hc2'⟩ := tally_best hK hr e w' h'
  have := (hb p' hp').1 _ hc1'; have := (hb p' hp').2 _ hc2'
  have := (hb' p hp).1 _ hc1; have := (hb' p hp).2 _ hc2
  exact Prod.ext (Int64.toInt_inj.1 (by omega)) (Int64.toInt_inj.1 (by omega))

variable {uE : Int64 → Prop} (hKE : ∀ e ks, uE e → lamDen (A := Obj.long) (B := Obj.long) B° e ks → ∀ k ∈ ks, uE k)
  (hP : ∀ e p q, uE e → Core.Rel.mu (forestStep (A := Obj.long) (lamDen B°) SF) e p → CH p q → ∃ n, uN n ∧ CostI r uN q n.toInt)

include hG hW hr hKE hP in
/-- **The guests of `e` form, as a set, a best party of `e`**, given a fold value at `e` and the list `Lp` of `e`'s
    parties. -/
theorem guestsBest_sem (e : Int64) (he : uE e) (p0 : Obj.El (.prod (.arr .long) (.arr .long))) (hp0 : FB e p0)
    (Lp : List (List Int64)) (hL : ∀ q, q ∈ Lp ↔ ∃ p, FB e p ∧ CH p q) :
    ∃ q, (∀ y, y ∈ q ↔ G e y) ∧ q ∈ Lp ∧ ∀ c ∈ Lp, c = q ∨ ∃ a b, Cost r uN q a ∧ Cost r uN c b ∧ b ≤ a := by
  have hK : ∀ e ks ks', lamDen (A := Obj.long) (B := Obj.long) B° e ks → lamDen (A := Obj.long) (B := Obj.long) B° e ks' → ks = ks' :=
    fun _ _ _ h h' => lamDen_unique _ h h'
  obtain ⟨w, hw⟩ := tally_total hK hr hKE hP e p0 hp0 he
  obtain ⟨p, hp, hc1, hc2, hs1, hs2⟩ := guests_fold hG hW e w hw
  obtain ⟨hw1u, hw2u, -⟩ := tally_best hK hr e w hw
  obtain ⟨ps, hps, hmax, hcs⟩ := (cMax_sem hK hr hKE hP e he _ Lp hL).1 ⟨w, hw, (MX_iff uN _ _).2 ⟨hw1u, hw2u, rfl⟩⟩
  have hlt := @Int64.lt_iff_toInt_lt w.2 w.1
  have hle := @Int64.le_iff_toInt_le w.2 w.1
  have hqc : Cost r uN (if w.2 ≤ w.1 then p.1 else p.2) (if w.2 < w.1 then w.1 else w.2) := by
    by_cases h : w.2 < w.1
    · rw [if_pos h, if_pos (hle.2 (Int.le_of_lt (hlt.1 h)))]; exact ⟨hw1u, hc1⟩
    · rw [if_neg h]
      by_cases h' : w.2 ≤ w.1
      · rw [if_pos h']
        have e : w.2.toInt = w.1.toInt := by have := hle.1 h'; have : ¬ w.2.toInt < w.1.toInt := fun x => h (hlt.2 x); omega
        exact ⟨hw2u, by rw [e]; exact hc1⟩
      · rw [if_neg h']; exact ⟨hw2u, hc2⟩
  refine ⟨if w.2 ≤ w.1 then p.1 else p.2, fun y => ?_, (hL _).2 ⟨p, hp, by split <;> simp [CH, Core.Rel.graph]⟩, fun c hc => .inr ?_⟩
  · rw [hG e y, hW e w hw]
    by_cases h' : w.2 ≤ w.1 <;> simp [h', hs1, hs2]
  · rcases hmax c hc with rfl | ⟨a, b, ha, hb, hab⟩
    · exact ⟨_, _, hqc, hcs, Int64.le_iff_toInt_le.2 (Int.le_refl _)⟩
    · obtain rfl : a = _ := Int64.toInt_inj.1 (costI_fun r uN hr ha.2 hcs.2)
      exact ⟨_, b, hqc, hb, hab⟩

end Guests

/-! ### The greedy fold `hylo(⟨𝟙, kids⟩, ⟨include, exclude₁(r)⟩)` (p. 178, law 43) -/

section Greedy

/-- `R(r)° = cost(r) ≥ cost(r)°` at the costs of `N`. -/
def QC (r : Core.Rel (Obj.El .long) (Obj.El .long)) (uN : Int64 → Prop) : Core.Rel (List Int64) (List Int64) :=
  Cost r uN ≫ (GE.ge : Core.Rel Int64 Int64) ≫ (Cost r uN)°

/-- `est(R(r)°) = ∋° ∩ (∋° ⧹ (R(r)° ∪ 𝟙)°)`: a member of the list no other member outweighs. -/
def estR (r : Core.Rel (Obj.El .long) (Obj.El .long)) (uN : Int64 → Prop) : Core.Rel (List (List Int64)) (List Int64) :=
  memDen (A := .arr .long) ∩ Core.Rel.ldiv (memDen (A := .arr .long))° ((QC r uN ∪ 𝟙 _)°)

/-- `Λ(choose) est(R(r)°)`: the better part of a fold pair. -/
def PK (r : Core.Rel (Obj.El .long) (Obj.El .long)) (uN : Int64 → Prop) :
    Core.Rel (Obj.El (.prod (.arr .long) (.arr .long))) (Obj.El (.arr .long)) :=
  lamDen CH ≫ estR r uN

/-- `⟨include, exclude₁(r)⟩`: exclude keeps the better part of each child's pair. -/
abbrev SG (r : Core.Rel (Obj.El .long) (Obj.El .long)) (uN : Int64 → Prop) := SX (PK r uN)

variable {B : Core.Rel Int64 Int64} {r : Core.Rel (Obj.El .long) (Obj.El .long)} {uN : Int64 → Prop}

local notation "FB" => Core.Rel.mu (forestStep (A := Obj.long) (lamDen B°) SF)
local notation "CB" => Core.Rel.mu (forestStep (A := Obj.long) (lamDen B°) (ST r uN))

theorem estR_iff (L : List (List Int64)) (c : List Int64) :
    estR r uN L c ↔ c ∈ L ∧ ∀ d ∈ L, d = c ∨ ∃ a b, Cost r uN c a ∧ Cost r uN d b ∧ b ≤ a := by
  simp only [estR, QC, Core.Rel.inter_apply, Core.Rel.ldiv_apply, Core.Rel.recip_apply, Core.Rel.union_apply,
    Core.Rel.comp_apply, memDen]
  refine and_congr_right fun _ => forall_congr' fun d => imp_congr_right fun _ => ?_
  constructor
  · rintro (⟨a, ha, b, hab, hb⟩ | h)
    · exact .inr ⟨a, b, ha, hb, hab⟩
    · exact .inl (show c = d from h).symm
  · rintro (h | ⟨a, b, ha, hb, hab⟩)
    · exact .inr (show c = d from h.symm)
    · exact .inl ⟨a, ha, b, hab, hb⟩

/-- The greedy pair at `e` is a fold pair whose parts cost `c`'s components. -/
def GQ (B : Core.Rel Int64 Int64) (r : Core.Rel (Obj.El .long) (Obj.El .long)) (uN : Int64 → Prop) (e : Int64)
    (g : Obj.El (.prod (.arr .long) (.arr .long))) : Prop :=
  Core.Rel.mu (forestStep (A := Obj.long) (lamDen B°) SF) e g ∧
    ∃ w, Core.Rel.mu (forestStep (A := Obj.long) (lamDen B°) (ST r uN)) e w ∧ CostI r uN g.1 w.1.toInt ∧
      CostI r uN g.2 w.2.toInt

theorem mapDen_imp {A B : Obj} {T T' : Core.Rel A.El B.El} : ∀ {xs : List A.El} {ys : List B.El}, mapDen T xs ys →
    (∀ x ∈ xs, ∀ y, T x y → T' x y) → mapDen T' xs ys
  | [], ys, h, _ => by rw [(mapDen_nil_iff _ _).1 h]; exact mapDen_nil_nil _
  | x :: xs, _, h, hT => by
    obtain ⟨y, ys, rfl, h0, h⟩ := (mapDen_cons_iff _ _ _ _).1 h
    exact (mapDen_cons_iff _ _ _ _).2 ⟨y, ys, rfl, hT x (by simp) y h0, mapDen_imp h fun z hz => hT z (by simp [hz])⟩

variable (hr : ∀ e y y', r e y → r e y' → y = y')

include hr in
/-- The better part of a pair costing `v` is a part, and costs the larger component. -/
theorem pick_cost {p : Obj.El (.prod (.arr .long) (.arr .long))} {v : Obj.El (.prod .long .long)} {c : List Int64}
    (h1 : CostI r uN p.1 v.1.toInt) (h2 : CostI r uN p.2 v.2.toInt) (h : PK r uN p c) :
    CH p c ∧ CostI r uN c (if v.2 < v.1 then v.1 else v.2).toInt := by
  obtain ⟨L, hL, hE⟩ := h
  obtain ⟨hc, hmax⟩ := (estR_iff L c).1 hE
  have mem := ((lamDen_iff _ _ _).1 hL).2
  have hlt := @Int64.lt_iff_toInt_lt v.2 v.1
  have hch := (mem c).1 hc
  refine ⟨hch, ?_⟩
  rcases hch with rfl | rfl
  · have hle : v.2.toInt ≤ v.1.toInt := by
      rcases hmax p.2 ((mem _).2 (.inr rfl)) with he | ⟨a, b, ha, hb, hab⟩
      · rw [he] at h2; exact Int.le_of_eq (costI_fun r uN hr h2 h1)
      · rw [costI_fun r uN hr h1 ha.2, costI_fun r uN hr h2 hb.2]; exact Int64.le_iff_toInt_le.1 hab
    split <;> rename_i hs
    · exact h1
    · rw [show v.2.toInt = v.1.toInt by have : ¬ v.2.toInt < v.1.toInt := fun x => hs (hlt.2 x); omega]; exact h1
  · have hle : v.1.toInt ≤ v.2.toInt := by
      rcases hmax p.1 ((mem _).2 (.inl rfl)) with he | ⟨a, b, ha, hb, hab⟩
      · rw [he] at h1; exact Int.le_of_eq (costI_fun r uN hr h1 h2)
      · rw [costI_fun r uN hr h2 ha.2, costI_fun r uN hr h1 hb.2]; exact Int64.le_iff_toInt_le.1 hab
    split <;> rename_i hs
    · rw [show v.1.toInt = v.2.toInt by have := hlt.1 hs; omega]; exact h2
    · exact h2

include hr in
/-- The children's greedy pairs: their parts cost what `c` gives the children. -/
theorem greedy_list : ∀ {ks : List Int64} {gs : List (Obj.El (.prod (.arr .long) (.arr .long)))}
    {cs : List (List Int64)} {vs : List (Obj.El (.prod .long .long))} {ms : List Int64},
    mapDen (A := .long) (B := .prod (.arr .long) (.arr .long)) (fun k g => GQ B r uN k g) ks gs →
    mapDen (PK r uN) gs cs → mapDen (A := .long) (B := .prod .long .long) CB ks vs → mapDen (MX uN) vs ms →
    CostI r uN (gs.map Prod.snd).flatten (isum (vs.map Prod.snd)) ∧ CostI r uN cs.flatten (isum ms)
  | [], gs, cs, vs, ms, hg, hc, hv, hm => by
    rw [(mapDen_nil_iff _ _).1 hg] at hc ⊢; rw [(mapDen_nil_iff _ _).1 hv] at hm ⊢
    rw [(mapDen_nil_iff _ _).1 hc, (mapDen_nil_iff _ _).1 hm]
    exact ⟨(costI_nil r uN _).2 rfl, (costI_nil r uN _).2 rfl⟩
  | k :: ks, _, _, _, _, hg, hc, hv, hm => by
    obtain ⟨g, gs, rfl, ⟨-, w, hw, h1, h2⟩, hg⟩ := (mapDen_cons_iff _ _ _ _).1 hg
    obtain ⟨c, cs, rfl, hc0, hc⟩ := (mapDen_cons_iff _ _ _ _).1 hc
    obtain ⟨v, vs, rfl, hv0, hv⟩ := (mapDen_cons_iff _ _ _ _).1 hv
    obtain ⟨m, ms, rfl, hm0, hm⟩ := (mapDen_cons_iff _ _ _ _).1 hm
    obtain ⟨r3, r4⟩ := greedy_list hg hc hv hm
    obtain rfl := tally_fun hr hv0 hw
    obtain ⟨-, -, rfl⟩ := (MX_iff uN _ _).1 hm0
    obtain ⟨-, hcc⟩ := pick_cost hr h1 h2 hc0
    refine ⟨?_, ?_⟩
    · simp only [List.map_cons, List.flatten_cons, isum_cons]
      exact (costI_append r uN _ _ _).2 ⟨_, _, h2, r3, rfl⟩
    · simp only [List.flatten_cons, isum_cons]
      exact (costI_append r uN _ _ _).2 ⟨_, _, hcc, r4, rfl⟩

variable {uE : Int64 → Prop} (hKE : ∀ e ks, uE e → lamDen (A := Obj.long) (B := Obj.long) B° e ks → ∀ k ∈ ks, uE k)
  (hP : ∀ e p q, uE e → Core.Rel.mu (forestStep (A := Obj.long) (lamDen B°) SF) e p → CH p q →
    ∃ n, uN n ∧ CostI r uN q n.toInt)

include hr hKE hP in
/-- Induction on the greedy fold: each greedy pair is a fold pair costing `c` (`GQ`). -/
theorem greedy_fold : ∀ e g, Core.Rel.mu (forestStep (A := Obj.long) (lamDen B°) (SG r uN)) e g → uE e →
    GQ B r uN e g := by
  have hK : ∀ e ks ks', lamDen (A := Obj.long) (B := Obj.long) B° e ks →
      lamDen (A := Obj.long) (B := Obj.long) B° e ks' → ks = ks' := fun _ _ _ h h' => lamDen_unique _ h h'
  refine forest_ind (lamDen (A := Obj.long) (B := Obj.long) B°) (SG r uN) (fun e g => uE e → GQ B r uN e g) ?_
  intro e ks gs g hk hgs hS he
  have hgs' : mapDen (A := .long) (B := .prod (.arr .long) (.arr .long)) (fun k g => GQ B r uN k g) ks gs :=
    mapDen_imp hgs fun k hk' _ h => h.2 (hKE e ks he hk k hk')
  obtain ⟨hg1, cs, hcs, hg2⟩ := (SX_iff _ _ _).1 hS
  have hfb : mapDen (A := .long) (B := .prod (.arr .long) (.arr .long)) FB ks gs := mapDen_imp hgs' fun _ _ _ h => h.1
  have hch : mapDen CH gs cs := mapDen_imp hcs fun _ _ c ⟨L, hL, hE⟩ =>
    (((lamDen_iff _ _ _).1 hL).2 c).1 ((estR_iff L c).1 hE).1
  have hf : FB e g := (forest_unfold _ _ e g).2 ⟨ks, gs, hk, hfb, (SX_iff _ _ _).2 ⟨hg1, cs, hch, hg2⟩⟩
  obtain ⟨w, hw⟩ := tally_total hK hr hKE hP e g hf he
  obtain ⟨ks', vs, hk', hvs, hST⟩ := (forest_unfold _ _ e w).1 hw
  obtain rfl := hK _ _ _ hk hk'
  obtain ⟨⟨y, s, hy, hyu, -, -, hs, -, hw1⟩, ms, hms, -, hw2⟩ := (ST_iff r uN _ _).1 hST
  obtain ⟨h3, h4⟩ := greedy_list hr hgs' hcs hvs hms
  refine ⟨hf, w, hw, ?_, ?_⟩
  · rw [hg1]; exact (costI_cons r uN _ _ _).2 ⟨y, _, hy, hyu, h3, by rw [hw1, hs]⟩
  · rw [hg2, hw2]; exact h4

include hr hKE hP in
/-- **The greedy pair's better part is a best party** (law 43 pointwise), given the list `Lp` of `e`'s parties. -/
theorem gfoldBest_sem (e : Int64) (he : uE e) (g : Obj.El (.prod (.arr .long) (.arr .long)))
    (hg : Core.Rel.mu (forestStep (A := Obj.long) (lamDen B°) (SG r uN)) e g) (c : List Int64) (hc : PK r uN g c)
    (Lp : List (List Int64)) (hL : ∀ q, q ∈ Lp ↔ ∃ p, FB e p ∧ CH p q) : estR r uN Lp c := by
  have hK : ∀ e ks ks', lamDen (A := Obj.long) (B := Obj.long) B° e ks →
      lamDen (A := Obj.long) (B := Obj.long) B° e ks' → ks = ks' := fun _ _ _ h h' => lamDen_unique _ h h'
  obtain ⟨hf, w, hw, h1, h2⟩ := greedy_fold hr hKE hP e g hg he
  obtain ⟨hw1u, hw2u, hb, -⟩ := tally_best hK hr e w hw
  obtain ⟨hch, hcc⟩ := pick_cost hr h1 h2 hc
  have hn : uN (if w.2 < w.1 then w.1 else w.2) := by split <;> assumption
  refine (estR_iff Lp c).2 ⟨(hL c).2 ⟨g, hf, hch⟩, fun d hd => .inr ?_⟩
  obtain ⟨p', hp', hch'⟩ := (hL d).1 hd
  obtain ⟨b, hbu, hbc⟩ := hP _ _ _ he hp' hch'
  refine ⟨_, b, ⟨hn, hcc⟩, ⟨hbu, hbc⟩, Int64.le_iff_toInt_le.2 ?_⟩
  have hlt := @Int64.lt_iff_toInt_lt w.2 w.1
  rcases hch' with rfl | rfl
  · have := (hb p' hp').1 _ hbc; split <;> rename_i h
    · omega
    · have : ¬ w.2.toInt < w.1.toInt := fun h' => h (hlt.2 h'); omega
  · have := (hb p' hp').2 _ hbc; split <;> rename_i h
    · have := hlt.1 h; omega
    · omega

end Greedy

/-! ### The terms of `guestsBest` -/

/-- `c(B, r)` at hylo index `k`, `N` the universe of `N`. -/
abbrev Tm.cT {n : USize} (N : Vals .long n) (k i j : Nat) (w : String) : Tm .long (.prod .long .long) :=
  Tm.forestHylo k w (Tm.tallyT N i j)

/-- `(c π₁ ≥) ∩ (c π₂)`, its two `c` at indices `k`, `k'`. -/
abbrev Tm.winM {n : USize} (N : Vals .long n) (k i j k' i' j' : Nat) (w w' : String) : Tm .long .long :=
  Tm.meet (Tm.comp (Tm.comp (Tm.cT N k i j w) Tm.outl) (Tm.conv (Tm.arg (Tm.prim (cmpRelRow false)) (Tm.uni N))))
    (Tm.comp (Tm.cT N k' i' j' w') Tm.outr)

theorem Tm.winM_den {n : USize} (N : Vals .long n) (ρ : Val) (k i j k' i' j' : Nat) (w w' : String)
    (C : Core.Rel Int64 (Obj.El (.prod .long .long)))
    (e1 : (Tm.cT N k i j w).den ρ = C) (e2 : (Tm.cT N k' i' j' w').den ρ = C) (x n : Int64) :
    (Tm.winM N k i j k' i' j' w w').den ρ x n ↔ (∃ w1, C x w1 ∧ InU N n ∧ InU N w1.1 ∧ n ≤ w1.1) ∧ ∃ w2, C x w2 ∧ w2.2 = n := by
  have e3 : (Tm.arg (Tm.prim (cmpRelRow false)) (Tm.uni N) : Tm .long .long).den ρ =
      fun a b => InU N a ∧ InU N b ∧ a ≤ b := by
    have hleq : (Tm.arg (Tm.prim (cmpRelRow false)) (Tm.uni N) : Tm .long .long).den ρ = leqDen .i64 ((Tm.uni N).den ρ) := by
      simp only [Tm.den, Tm.argDen, Prim.den_cmpRelRow_le]
    rw [hleq]; funext a b; apply propext; rw [leqDen_iff, uni_den']
    constructor
    · rintro ⟨⟨_, -, ha⟩, ⟨_, -, hb⟩, h⟩; exact ⟨ha, hb, h⟩
    · rintro ⟨ha, hb, h⟩; exact ⟨⟨a, rfl, ha⟩, ⟨b, rfl, hb⟩, h⟩
  unfold Tm.winM; revert e1 e2 e3
  generalize Tm.cT N k i j w = C1; generalize Tm.cT N k' i' j' w' = C2
  generalize (Tm.arg (Tm.prim (cmpRelRow false)) (Tm.uni N) : Tm .long .long) = L; intro e1 e2 e3
  simp only [Tm.den, e1, e2, e3, Core.Rel.inter_apply, Core.Rel.comp_apply, Core.Rel.recip_apply, Core.Rel.graph]
  constructor
  · rintro ⟨⟨_, ⟨w1, h1, rfl⟩, ha, hb, hle⟩, w2, h2, rfl⟩; exact ⟨⟨w1, h1, ha, hb, hle⟩, w2, h2, rfl⟩
  · rintro ⟨⟨w1, h1, ha, hb, hle⟩, w2, h2, rfl⟩; exact ⟨⟨_, ⟨w1, h1, rfl⟩, ha, hb, hle⟩, w2, h2, rfl⟩

/-- `win B° B° ∪ ((𝟙 − win)B°)`, the step of `guests`, its two `win` at indices `k1 … k4`. -/
abbrev Tm.stepT {n : USize} (N : Vals .long n) (k1 i1 j1 k2 i2 j2 k3 i3 j3 k4 i4 j4 : Nat) (w1 w2 w3 w4 : String) : Tm .long .long :=
  Tm.join (Tm.comp (Tm.comp (Tm.dom (Tm.winM N k1 i1 j1 k2 i2 j2 w1 w2)) (Tm.conv (Tm.var 0 : Tm .long .long)))
      (Tm.conv (Tm.var 0 : Tm .long .long)))
    (Tm.comp (Tm.diff Tm.id (Tm.dom (Tm.winM N k3 i3 j3 k4 i4 j4 w3 w4))) (Tm.conv (Tm.var 0 : Tm .long .long)))

/-- `guests(B, r) = (win B° B° ∪ ((𝟙 − win)B°))* win`, as the elaborator writes it. -/
abbrev Tm.guestsT {n : USize} (N : Vals .long n) (k1 i1 j1 k2 i2 j2 k3 i3 j3 k4 i4 j4 k5 i5 j5 k6 i6 j6 : Nat) (w1 w2 w3 w4 w5 w6 : String) :
    Tm .long .long :=
  Tm.comp (Tm.arg (Tm.prim (rowOf "star") : Tm .long .long) (Tm.stepT N k1 i1 j1 k2 i2 j2 k3 i3 j3 k4 i4 j4 w1 w2 w3 w4))
    (Tm.dom (Tm.winM N k5 i5 j5 k6 i6 j6 w5 w6))

/-- **`Λ(guests(B, r)) setify ⊑ best(B, r) setify`** (`guestsBest` of `Party.lean`): the guests of an employee form,
    as a set, a best party. `B` is variable 0, `r` variable 1, `U` the universe of `E`, `N` of `N`. Premises: `r°r ⊑ 𝟙`
    (`r` simple, so `c` is a function and `win` reads its one value); `B ⊑ 𝟙B` (the recursion stays in `E`);
    `dom(party(B)) = 𝟙` (each employee has a fold value, so `c` has one); `dom(Λ(party(B))) = 𝟙` (the parties form the
    list `best` reads); `party(B) ⊑ party(B) dom(cost(r))` (every party has a cost in `N`). The hylo indices `k*` are
    the elaborator's, one per occurrence. -/
theorem Tm.guestsBest_den {n12 n41 : USize} {m12 p12 m41 p41 : List String}
    {hw12 hw41 : QAtomicType.i64.width.isSome = true} {k1 k2 k3 k4 k5 k6 k9 k17 k22 k24 k25 i1 j1 i2 j2 i3 j3 i4 j4 i5 j5 i6 j6 : Nat}
    {w1 w2 w3 w4 w5 w6 w9 w17 w22 w24 w25 : String}
    (hk1 : k1 ≠ 0 := by decide) (hk1' : 1 ≠ k1 := by decide) (hk2 : k2 ≠ 0 := by decide) (hk2' : 1 ≠ k2 := by decide)
    (hk3 : k3 ≠ 0 := by decide) (hk3' : 1 ≠ k3 := by decide) (hk4 : k4 ≠ 0 := by decide) (hk4' : 1 ≠ k4 := by decide)
    (hk5 : k5 ≠ 0 := by decide) (hk5' : 1 ≠ k5 := by decide) (hk6 : k6 ≠ 0 := by decide) (hk6' : 1 ≠ k6 := by decide)
    (hij1 : j1 ≠ i1 := by decide) (hij2 : j2 ≠ i2 := by decide) (hij3 : j3 ≠ i3 := by decide)
    (hij4 : j4 ≠ i4 := by decide) (hij5 : j5 ≠ i5 := by decide) (hij6 : j6 ≠ i6 := by decide)
    (hk9 : k9 ≠ 0 := by decide) (hk17 : k17 ≠ 0 := by decide) (hk22 : k22 ≠ 0 := by decide)
    (hk24 : k24 ≠ 0 := by decide)
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
    Tm.den ρ (Tm.comp (Tm.uni U) (Tm.dom (Tm.partyT k17 w17))) = Tm.den ρ (Tm.comp (Tm.uni U) Tm.id) →
    Tm.den ρ (Tm.comp (Tm.uni U) (Tm.dom (Tm.lam (Tm.partyT k22 w22)))) = Tm.den ρ (Tm.comp (Tm.uni U) Tm.id) →
    Tm.den ρ (Tm.comp (Tm.uni U) (Tm.partyT k24 w24)) ⊑
      Tm.den ρ (Tm.comp (Tm.uni U) (Tm.comp (Tm.partyT k25 w25)
        (Tm.dom (Tm.comp (Tm.fmapT (Tm.var 1 : Tm .long .long)) (Tm.sumU N))))) →
    Tm.den ρ (Tm.comp (Tm.uni U) (Tm.comp (Tm.lam (Tm.guestsT N k1 i1 j1 k2 i2 j2 k3 i3 j3 k4 i4 j4 k5 i5 j5 k6 i6 j6 w1 w2 w3 w4 w5 w6))
        (Tm.prim (rowOf "setify") : Tm (.arr .long) (.arr .long)))) ⊑
    Tm.den ρ (Tm.comp (Tm.uni U) (Tm.comp (Tm.comp (Tm.lam (Tm.partyT k9 w9))
        (Tm.est (pairTest (Tm.costQ N (Tm.var 1))))) (Tm.prim (rowOf "setify") : Tm (.arr .long) (.arr .long)))) := by
  intro U N h1 h4 h2a h2 h3
  have hN := hnn N rfl
  have hPC : ∀ k w, k ≠ 0 → (Tm.partyT k w).den ρ =
      Core.Rel.comp (Core.Rel.mu (forestStep (lamDen (ρ 0 .long .long)°) SF)) CH := fun k w hk => by
    show Core.Rel.comp _ _ = _; rw [Tm.forestHylo_den w _ SF ρ hk (fun _ => by rw [Tm.partyX_den, Tm.chooseT_den])]; rfl
  have hT : ∀ k i j w, k ≠ 0 → 1 ≠ k → j ≠ i → (Tm.cT N k i j w).den ρ =
      Core.Rel.mu (forestStep (lamDen (ρ 0 .long .long)°) (ST (ρ 1 .long .long) (InU N))) := fun k i j w hk hk1 hij =>
    Tm.forestHylo_den w _ _ ρ hk (fun X => by rw [Tm.tallyT_den N hN _ hij, Val.bind_ne hk1])
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
  -- `win` reads the one value of `c`
  let CB := Core.Rel.mu (forestStep (lamDen (ρ 0 .long .long)°) (ST (ρ 1 .long .long) (InU N)))
  let W : Int64 → Prop := fun x => ∃ n, (∃ w1, CB x w1 ∧ InU N n ∧ InU N w1.1 ∧ n ≤ w1.1) ∧ ∃ w2, CB x w2 ∧ w2.2 = n
  have hWd : ∀ k i j k' i' j' w w', k ≠ 0 → 1 ≠ k → j ≠ i → k' ≠ 0 → 1 ≠ k' → j' ≠ i' → ∀ x x',
      (Tm.dom (Tm.winM N k i j k' i' j' w w')).den ρ x x' ↔ x = x' ∧ W x := by
    intro k i j k' i' j' w w' a b e c d f x x'
    rw [hD]
    show (x = x' ∧ ∃ n, (Tm.winM N k i j k' i' j' w w').den ρ x n ∧ (Tm.winM N k i j k' i' j' w w').den ρ x' n) ↔ _
    simp only [Tm.winM_den N ρ k i j k' i' j' w w' CB (hT k i j w a b e) (hT k' i' j' w' c d f)]
    constructor
    · rintro ⟨rfl, n, h, -⟩; exact ⟨rfl, n, h⟩
    · rintro ⟨rfl, n, h⟩; exact ⟨rfl, n, h, h⟩
  have hW : ∀ x w, CB x w → (W x ↔ w.2 ≤ w.1) := fun x w hw => by
    constructor
    · rintro ⟨n, ⟨w1, h1, -, -, hle⟩, w2, h2, rfl⟩
      obtain rfl := tally_fun hr h1 hw; obtain rfl := tally_fun hr h2 hw; exact hle
    · intro hle
      obtain ⟨hu1, hu2, -⟩ := tally_best hK hr x w hw
      exact ⟨w.2, ⟨w, hw, hu2, hu1, hle⟩, w, hw, rfl⟩
  -- `guests` as the least fixed point of its step
  let SR : Core.Rel Int64 Int64 := fun x m =>
    (W x ∧ ∃ k, ρ 0 .long .long k x ∧ ρ 0 .long .long m k) ∨ (¬ W x ∧ ρ 0 .long .long m x)
  have hS : (Tm.stepT N k1 i1 j1 k2 i2 j2 k3 i3 j3 k4 i4 j4 w1 w2 w3 w4).den ρ = SR := by
    funext x m; apply propext
    show ((∃ m1, (∃ m0, (Tm.dom (Tm.winM N k1 i1 j1 k2 i2 j2 w1 w2)).den ρ x m0 ∧ ρ 0 .long .long m1 m0) ∧ ρ 0 .long .long m m1) ∨
      ∃ m0, (x = m0 ∧ ¬ (Tm.dom (Tm.winM N k3 i3 j3 k4 i4 j4 w3 w4)).den ρ x m0) ∧ ρ 0 .long .long m m0) ↔ SR x m
    simp only [hWd k1 i1 j1 k2 i2 j2 w1 w2 hk1 hk1' hij1 hk2 hk2' hij2, hWd k3 i3 j3 k4 i4 j4 w3 w4 hk3 hk3' hij3 hk4 hk4' hij4]
    constructor
    · rintro (⟨m1, ⟨_, ⟨rfl, hw⟩, h0⟩, h1⟩ | ⟨_, ⟨rfl, hw⟩, h0⟩)
      · exact .inl ⟨hw, m1, h0, h1⟩
      · exact .inr ⟨fun h => hw ⟨rfl, h⟩, h0⟩
    · rintro (⟨hw, m1, h0, h1⟩ | ⟨hw, h0⟩)
      · exact .inl ⟨m1, ⟨x, ⟨rfl, hw⟩, h0⟩, h1⟩
      · exact .inr ⟨x, ⟨rfl, fun h => hw h.2⟩, h0⟩
  have hstar : (Tm.arg (Tm.prim (rowOf "star") : Tm .long .long) (Tm.stepT N k1 i1 j1 k2 i2 j2 k3 i3 j3 k4 i4 j4 w1 w2 w3 w4)).den ρ =
      UnderR SR° := by
    show Prim.den (rowOf "star") .long .long [⟨.long, .long, (Tm.stepT N k1 i1 j1 k2 i2 j2 k3 i3 j3 k4 i4 j4 w1 w2 w3 w4).den ρ⟩] = _
    rw [Prim.den_star, hS]; unfold UnderR; rw [Core.Rel.recip_recip]
  let G : Int64 → Int64 → Prop := fun x y => UnderR SR° x y ∧ W y
  have hGd : ∀ x y, (Tm.guestsT N k1 i1 j1 k2 i2 j2 k3 i3 j3 k4 i4 j4 k5 i5 j5 k6 i6 j6 w1 w2 w3 w4 w5 w6).den ρ x y ↔ G x y := fun x y => by
    show (∃ z, (Tm.arg (Tm.prim (rowOf "star") : Tm .long .long) (Tm.stepT N k1 i1 j1 k2 i2 j2 k3 i3 j3 k4 i4 j4 w1 w2 w3 w4)).den ρ x z ∧
      (Tm.dom (Tm.winM N k5 i5 j5 k6 i6 j6 w5 w6)).den ρ z y) ↔ _
    rw [hstar]; simp only [hWd k5 i5 j5 k6 i6 j6 w5 w6 hk5 hk5' hij5 hk6 hk6' hij6]
    exact ⟨fun ⟨_, h, rfl, hw⟩ => ⟨h, hw⟩, fun ⟨h, hw⟩ => ⟨y, h, rfl, hw⟩⟩
  have hG : ∀ x y, G x y ↔ (W x ∧ (y = x ∨ ∃ k, ρ 0 .long .long k x ∧ ∃ g, ρ 0 .long .long g k ∧ G g y)) ∨
      (¬ W x ∧ ∃ k, ρ 0 .long .long k x ∧ G k y) := fun x y => by
    show (UnderR SR° x y ∧ W y) ↔ _
    rw [under_iff]
    by_cases hw : W x
    · constructor
      · rintro ⟨rfl | ⟨m, (⟨-, k, hk, hm⟩ | ⟨hn, -⟩), hu⟩, hwy⟩
        · exact .inl ⟨hw, .inl rfl⟩
        · exact .inl ⟨hw, .inr ⟨k, hk, m, hm, hu, hwy⟩⟩
        · exact absurd hw hn
      · rintro (⟨-, rfl | ⟨k, hk, g, hg, hu, hwy⟩⟩ | ⟨hn, -⟩)
        · exact ⟨.inl rfl, hw⟩
        · exact ⟨.inr ⟨g, .inl ⟨hw, k, hk, hg⟩, hu⟩, hwy⟩
        · exact absurd hw hn
    · constructor
      · rintro ⟨rfl | ⟨m, (⟨hw', -⟩ | ⟨-, hm⟩), hu⟩, hwy⟩
        · exact absurd hwy hw
        · exact absurd hw' hw
        · exact .inr ⟨hw, m, hm, hu, hwy⟩
      · rintro (⟨hw', -⟩ | ⟨-, m, hm, hu, hwy⟩)
        · exact absurd hw' hw
        · exact ⟨.inr ⟨m, .inr ⟨hw, hm⟩, hu⟩, hwy⟩
  -- the guests of `a` and a best party
  have hset : Prim.den (rowOf "setify") (.arr .long) (.arr .long) [] = lamDen (memDen (A := .long)) := by
    funext xs zs; exact propext (Tm.setifyDef_row ρ xs zs).symm
  refine Core.Rel.le_iff.2 fun a ys h => ?_
  obtain ⟨he, L, hLam, hys⟩ := (uniComp_den U ρ _ a ys).1 h
  have hLm : ∀ y, y ∈ L ↔ G a y := fun y => (((lamDen_iff _ _ _).1 hLam).2 y).trans (hGd a y)
  have hp0 : ∃ w, Core.Rel.mu (forestStep (lamDen (ρ 0 .long .long)°) SF) a w := by
    have h := (uniComp_den U ρ Tm.id a a).2 ⟨he, show (Tm.id : Tm .long .long).den ρ a a from rfl⟩
    rw [← h2a] at h
    obtain ⟨-, h⟩ := (uniComp_den U ρ (Tm.dom (Tm.partyT k17 w17)) a a).1 h
    rw [hD] at h
    obtain ⟨-, p, hp, -⟩ := h
    rw [hPC k17 w17 hk17] at hp
    obtain ⟨w, hw, -⟩ := hp
    exact ⟨w, hw⟩
  obtain ⟨p0, hp0⟩ := hp0
  have hL : ∃ Lp, lamDen (Core.Rel.comp (Core.Rel.mu (forestStep (lamDen (ρ 0 .long .long)°) SF)) CH) a Lp := by
    have h := (uniComp_den U ρ Tm.id a a).2 ⟨he, show (Tm.id : Tm .long .long).den ρ a a from rfl⟩
    rw [← h2] at h
    obtain ⟨-, h⟩ := (uniComp_den U ρ _ a a).1 h
    rw [hD] at h
    obtain ⟨-, Lp, hLp, -⟩ := h
    change lamDen ((Tm.partyT k22 w22).den ρ) a Lp at hLp
    rw [hPC k22 w22 hk22] at hLp
    exact ⟨Lp, hLp⟩
  obtain ⟨Lp, hLp⟩ := hL
  obtain ⟨q, hqm, hq, hbest⟩ := guestsBest_sem (B := ρ 0 .long .long) hG hW hr hKE hP a he p0 hp0 Lp
    fun q => ((lamDen_iff _ _ _).1 hLp).2 q
  have hLp9 : lamDen ((Tm.partyT k9 w9).den ρ) a Lp := by rw [hPC k9 w9 hk9]; exact hLp
  have hmem : lamDen (memDen (A := .long)) q ys := by
    change Prim.den (rowOf "setify") (.arr .long) (.arr .long) [] L ys at hys
    rw [hset] at hys
    have h : ∀ x, x ∈ q ↔ x ∈ L := fun x => (hqm x).trans (hLm x).symm
    simp only [lamDen_iff, memDen, h] at hys ⊢; exact hys
  refine (uniComp_den U ρ _ a ys).2 ⟨he, q, ⟨Lp, hLp9, (Tm.estCost_den N hN ρ (Tm.var 1) Lp q).2 ⟨hq, hbest⟩⟩, ?_⟩
  show Prim.den (rowOf "setify") (.arr .long) (.arr .long) [] q ys
  rw [hset]; exact hmem

/-! ### The terms of `gfoldBest` -/

/-- `Λ(choose)est(R(r)°)`, `r` at variable 1, `N` the universe of `N`. -/
abbrev Tm.pickT {n : USize} (N : Vals .long n) : Tm (.prod (.arr .long) (.arr .long)) (.arr .long) :=
  Tm.comp (Tm.lam Tm.chooseT) (Tm.est (pairTest (Tm.costQ N (Tm.var 1))))

theorem Tm.pickT_den {n : USize} (N : Vals .long n) (hnn : ∀ i, 0 ≤ (N.row i).toInt) (ρ : Val) :
    (Tm.pickT N).den ρ = PK (ρ 1 .long .long) (InU N) := by
  have he : (Tm.est (pairTest (Tm.costQ N (Tm.var 1)))).den ρ = estR (ρ 1 .long .long) (InU N) := by
    funext L c; apply propext; rw [Tm.estCost_den N hnn, estR_iff]; rfl
  show Core.Rel.comp _ _ = _; rw [he]; rfl

/-- **`gfold(B, r) Λ(choose)est(R(r)°) ⊑ best(B, r)`** (law 43, `gfoldBest` of `Party.lean`): the better part of the
    greedy pair is a best party. Premises as `Tm.cMax_den`; the hylo indices `k*` are the elaborator's. -/
theorem Tm.gfoldBest_den {n12 n41 : USize} {m12 p12 m41 p41 : List String}
    {hw12 hw41 : QAtomicType.i64.width.isSome = true} {kg kb k22 k24 k25 : Nat} {wg wb w22 w24 w25 : String}
    (hkg : kg ≠ 0 := by decide) (hkg1 : 1 ≠ kg := by decide) (hkb : kb ≠ 0 := by decide)
    (hk22 : k22 ≠ 0 := by decide) (hk24 : k24 ≠ 0 := by decide)
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
    Tm.den ρ (Tm.comp (Tm.uni U) (Tm.dom (Tm.lam (Tm.partyT k22 w22)))) = Tm.den ρ (Tm.comp (Tm.uni U) Tm.id) →
    Tm.den ρ (Tm.comp (Tm.uni U) (Tm.partyT k24 w24)) ⊑
      Tm.den ρ (Tm.comp (Tm.uni U) (Tm.comp (Tm.partyT k25 w25)
        (Tm.dom (Tm.comp (Tm.fmapT (Tm.var 1 : Tm .long .long)) (Tm.sumU N))))) →
    Tm.den ρ (Tm.comp (Tm.uni U) (Tm.comp (Tm.comp (Tm.forestHylo kg wg (Tm.partyX (Tm.pickT N))) (Tm.lam Tm.chooseT))
        (Tm.est (pairTest (Tm.costQ N (Tm.var 1)))))) ⊑
    Tm.den ρ (Tm.comp (Tm.uni U) (Tm.comp (Tm.lam (Tm.partyT kb wb)) (Tm.est (pairTest (Tm.costQ N (Tm.var 1)))))) := by
  intro U N h1 h4 h2 h3
  have hN := hnn N rfl
  have hPC : ∀ k w, k ≠ 0 → (Tm.partyT k w).den ρ =
      Core.Rel.comp (Core.Rel.mu (forestStep (lamDen (ρ 0 .long .long)°) SF)) CH := fun k w hk => by
    show Core.Rel.comp _ _ = _; rw [Tm.forestHylo_den w _ SF ρ hk (fun _ => by rw [Tm.partyX_den, Tm.chooseT_den])]; rfl
  have hG : (Tm.forestHylo kg wg (Tm.partyX (Tm.pickT N))).den ρ =
      Core.Rel.mu (forestStep (lamDen (ρ 0 .long .long)°) (SG (ρ 1 .long .long) (InU N))) :=
    Tm.forestHylo_den wg _ _ ρ hkg (fun X => by rw [Tm.partyX_den, Tm.pickT_den N hN, Val.bind_ne hkg1])
  have hcost : (Tm.comp (Tm.fmapT (Tm.var 1 : Tm .long .long)) (Tm.sumU N)).den ρ = Cost (ρ 1 .long .long) (InU N) :=
    Tm.costU_den N hN ρ _
  have hD : ∀ {A B : Obj} (R : Tm A B), (Tm.dom R).den ρ = 𝟙 _ ∩ R.den ρ ≫ (R.den ρ)° :=
    fun R => Prim.den_domRow _
  have hr : ∀ e y y', ρ 1 .long .long e y → ρ 1 .long .long e y' → y = y' := fun e y y' h h' =>
    ((uniComp_den N ρ _ y y').1 (Core.Rel.le_iff.1 h1 y y'
      (show Core.Rel.comp ((ρ 1 .long .long)°) (ρ 1 .long .long) y y' from ⟨e, h, h'⟩))).2
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
  have he : (Tm.est (pairTest (Tm.costQ N (Tm.var 1)))).den ρ = estR (ρ 1 .long .long) (InU N) := by
    funext L c; apply propext; rw [Tm.estCost_den N hN, estR_iff]; rfl
  refine Core.Rel.le_iff.2 fun a c h => ?_
  obtain ⟨ha, d, ⟨g, hg, hd⟩, hc⟩ := (uniComp_den U ρ _ a c).1 h
  rw [hG] at hg
  have hpk : PK (ρ 1 .long .long) (InU N) g c := by rw [← Tm.pickT_den N hN]; exact ⟨d, hd, hc⟩
  refine (uniComp_den U ρ _ a c).2 ⟨ha, ?_⟩
  have hL : ∃ Lp, lamDen (Core.Rel.comp (Core.Rel.mu (forestStep (lamDen (ρ 0 .long .long)°) SF)) CH) a Lp := by
    have h := (uniComp_den U ρ Tm.id a a).2 ⟨ha, show (Tm.id : Tm .long .long).den ρ a a from rfl⟩
    rw [← h2] at h
    obtain ⟨-, h⟩ := (uniComp_den U ρ _ a a).1 h
    rw [hD] at h
    obtain ⟨-, Lp, hLp, -⟩ := h
    change lamDen ((Tm.partyT k22 w22).den ρ) a Lp at hLp
    rw [hPC k22 w22 hk22] at hLp
    exact ⟨Lp, hLp⟩
  obtain ⟨Lp, hLp⟩ := hL
  refine ⟨Lp, ?_, ?_⟩
  · change lamDen ((Tm.partyT kb wb).den ρ) a Lp; rw [hPC kb wb hkb]; exact hLp
  · rw [he]
    exact gfoldBest_sem hr hKE hP a ha g hg c hpk Lp fun q => ((lamDen_iff _ _ _).1 hLp).2 q

end Rel.Lang
