import Rel.Lang.GenKBits

/-! The `GenK` ops of the fixed points (`nu`, `mu`), each representing its constructor's case of `Tm.den` from the
    rounds of `Tab.fixOn`. A round is met with (`ν`) or joined to (`μ`) the table before it, so the rounds form a
    chain; every round's table is duplicate-free (`inter`, `union` answer sorted, `pack` keeps the rows), so a round
    that keeps the row count keeps the relation (`Tab.holds_of_n`), which is then a fixed point of the body. The
    invariant that `ν` lies below (`μ` above) every round makes that fixed point the greatest (least); both need the
    body monotone. -/

namespace Rel.Lang

open Rel Rel.Rep Rel.Kernel Rel.Verify Gen
open scoped Rel.Core.Rel
open Rel.Core.Rel hiding id comp recip inter union zero le inl inr junc

namespace Tab
variable {k v : Obj}

/-- Rows pairwise distinct as values make `toList` duplicate-free. -/
theorem toList_nodup {R : Tab k v}
    (h : ∀ j j' : Fin R.n.toNat, j ≠ j' → (R.key.row j, R.val.row j) ≠ (R.key.row j', R.val.row j')) :
    R.toList.Nodup := by
  unfold Tab.toList; rw [List.Nodup, List.pairwise_iff_getElem]
  intro i j hi hj hij
  simp only [List.getElem_ofFn]
  exact h _ _ fun e => Nat.ne_of_lt hij (congrArg Fin.val e)

/-- **`pack` keeps the row count and every row**, in order (`Vals.pack_row`). -/
theorem pack_toList {R R' : Tab k v} (h : R.pack = .ok R') : R'.n = R.n ∧ R'.toList = R.toList := by
  unfold Tab.pack at h
  obtain ⟨kk, hk, h⟩ := GenK.bind_ok h
  obtain ⟨vv, hv, h⟩ := GenK.bind_ok h
  simp only [pure, Except.pure, Except.ok.injEq] at h; subst h
  exact ⟨rfl, by simp only [Tab.toList, Vals.pack_row _ hk, Vals.pack_row _ hv]⟩

/-- **`R ∩ S`'s rows are distinct**: two of them are rows of `R.concat S` with unequal codes (`inter_sorted`), and
    `kasc` ran on that table's columns, so equal rows would have equal codes (`Vals.codes_of_row`). -/
theorem inter_distinct {R S U : Tab k v} (h : R.inter S = .ok U) {j j' : Fin U.n.toNat} (hjj : j ≠ j') :
    (U.key.row j, U.val.row j) ≠ (U.key.row j', U.val.row j') := by
  obtain ⟨C, es, hC, hes, sel, hs, hlt⟩ := Tab.inter_sorted h
  obtain ⟨cs, hc⟩ : ∃ cs, es.mapM (ascCol C.n) = .ok cs := by
    unfold Tab.inter Tab.select at h
    obtain ⟨⟨C', tag⟩, hCt, h⟩ := GenK.bind_ok h
    obtain rfl : C' = C := Except.ok.inj ((Tab.tagged_ok hCt).1.symm.trans hC)
    obtain ⟨es', hes', h⟩ := GenK.bind_ok h
    obtain rfl : es' = es := Except.ok.inj (hes'.symm.trans hes)
    obtain ⟨⟨vs, p⟩, hvp, -⟩ := GenK.bind_ok h
    obtain ⟨cs, hc, -⟩ := kasc_ok hvp
    exact ⟨cs, hc⟩
  intro e
  rw [hs, hs] at e
  rcases Nat.lt_or_gt_of_ne (Fin.val_ne_of_ne hjj) with l | l
  · exact (hlt j j' l).2 (Vals.codes_of_row (A := .prod k v) (C.key, C.val) hes hc _ _ e)
  · exact (hlt j' j l).2 (Vals.codes_of_row (A := .prod k v) (C.key, C.val) hes hc _ _ e.symm)

/-- **`R ∪ S`'s rows are distinct**: it is `canon` of the concatenation (`union_sorted`, `canon_distinct`). -/
theorem union_nodup {R S U : Tab k v} (h : R.union S = .ok U) : U.toList.Nodup := by
  obtain ⟨_, -, hc⟩ := Tab.union_sorted h
  exact toList_nodup fun _ _ hjj => Tab.canon_distinct hc hjj

/-- **A chain step that keeps the row count keeps the relation**: `X` inside `Y`, both duplicate-free and of one
    row count, so `Y` inside `X` (`nodup_length_eq_iff` on their rows). -/
theorem holds_of_n {X Y : Tab k v} (dX : X.toList.Nodup) (dY : Y.toList.Nodup)
    (hXY : ∀ a b, X.Holds a b → Y.Holds a b) (hn : X.n = Y.n) : ∀ a b, Y.Holds a b → X.Holds a b := by
  classical
  have e := (nodup_length_eq_iff dX dY fun p hp => (Tab.holds_iff_mem_toList Y p.1 p.2).1
    (hXY _ _ ((Tab.holds_iff_mem_toList X p.1 p.2).2 hp))).1 (by simp [Tab.toList, hn])
  exact fun a b hb => (Tab.holds_iff_mem_toList X a b).2 (e ((Tab.holds_iff_mem_toList Y a b).1 hb))

/-- **The round invariant of `Tab.fixOn`**: an `I` that every round keeps (`hI`: from `X`, `step X` then `pack`)
    holds of the answer's round, whose `pack`ed table is the answer with the row count of the table before it. -/
theorem fixOn_inv {A B : Obj} {out : String} {step : Tab A B → Except String (Tab A B)} (I : Tab A B → Prop)
    (hI : ∀ X Y Y', I X → step X = .ok Y → Y.pack = .ok Y' → I Y') :
    ∀ n X T, I X → Tab.fixOn out step n X = .ok T →
      ∃ X' Y, I X' ∧ step X' = .ok Y ∧ Y.pack = .ok T ∧ T.n = X'.n := by
  intro n
  induction n with
  | zero => intro X T _ h; simp [Tab.fixOn] at h
  | succ n ih =>
    intro X T hX h
    simp only [Tab.fixOn] at h
    obtain ⟨Y', hY', h⟩ := GenK.bind_ok h
    obtain ⟨Y, hY, hp⟩ := GenK.bind_ok hY'
    by_cases e : Y'.n = X.n
    · rw [if_pos (by simp [e])] at h
      simp only [pure, Except.pure, Except.ok.injEq] at h; subst h
      exact ⟨X, Y, hX, hY, hp, e⟩
    · rw [if_neg (by simpa using e)] at h
      exact ih Y' T (hI X Y Y' hX hY hp) h

end Tab

namespace GenK

/-- **`νX : S ∩ φ`** (`Tab.nu`): from `S`'s canonical table, rounds `X ↦ X ∩ φ(X)`. Each round holds `ν` (`Φ`
    monotone, so `ν = TS ∩ Φ(ν) ⊑ X ∩ Φ(X)`) and lies inside `TS`; the last round is its table before it, so
    `X ⊑ TS ∩ Φ(X)` and `X ⊑ ν` (`le_nu`). -/
theorem nu_sound {A B : Obj} {S : Rel A B} {φ : Tab A B → Rel A B} {TS : Den A B} {Φ : Den A B → Den A B}
    (hS : ∀ K, S.Reps K TS) (hφ : ∀ X K, (φ X).Reps K (Φ (rep X))) (hm : Monotonic Φ) :
    ∀ K, (GenK.nu A B S φ).Reps K (Core.Rel.nu fun X => TS ∩ Φ X) := by
  intro K; rw [reps_iff]; intro t h
  obtain ⟨s, hs, h⟩ := bind_ok (show (S.runE {} >>= fun s => Tab.nu (fun X => (φ X).runE {}) s) = .ok t from h)
  obtain rfl : TS = rep s := agrees_empty ((reps_iff _ _ _).1 (hS {}) s hs)
  have eφ : ∀ X g, (φ X).runE {} = .ok g → Φ (rep X) = rep g :=
    fun X g hg => agrees_empty ((reps_iff _ _ _).1 (hφ X {}) g hg)
  have hfix : rep s ∩ Φ (Core.Rel.nu fun X => rep s ∩ Φ X) = Core.Rel.nu fun X => rep s ∩ Φ X :=
    nu_fix (φ := fun X => rep s ∩ Φ X) fun X Y hXY =>
      le_inter (inter_le_left _ _) (Core.Rel.le_trans (inter_le_right _ _) (hm X Y hXY))
  -- a round: `Y = X ∩ g`, `rep g = Φ(rep X)`, then `pack`
  have round : ∀ X Y Y', ((φ X).runE {} >>= X.inter) = .ok Y → Y.pack = .ok Y' →
      Y'.toList.Nodup ∧ ∀ a b, Y'.Holds a b ↔ X.Holds a b ∧ Φ (rep X) a b := by
    intro X Y Y' hY hp
    obtain ⟨g, hg, hi⟩ := bind_ok hY
    refine ⟨(Tab.pack_toList hp).2 ▸ Tab.toList_nodup fun _ _ => Tab.inter_distinct hi, fun a b => ?_⟩
    rw [Tab.pack_holds hp, Tab.inter_holds hi, eφ X g hg]; rfl
  unfold Tab.nu at h
  obtain ⟨T, hT, h⟩ := bind_ok h
  obtain ⟨X, Y, ⟨dX, nX, sX⟩, hY, hp, hn⟩ := Tab.fixOn_inv
    (fun X : Tab A B => X.toList.Nodup ∧ (Core.Rel.nu fun X => rep s ∩ Φ X) ⊑ rep X ∧ rep X ⊑ rep s)
    (fun X Y Y' ⟨_, nX, sX⟩ hY hp => by
      obtain ⟨d, hY'⟩ := round X Y Y' hY hp
      refine ⟨d, le_iff.2 fun a b hab => (hY' a b).2 ⟨le_iff.1 nX a b hab, ?_⟩,
        le_iff.2 fun a b hab => le_iff.1 sX a b ((hY' a b).1 hab).1⟩
      rw [← hfix, inter_apply] at hab
      exact le_iff.1 (hm _ _ nX) a b hab.2)
    _ _ _ ⟨Tab.toList_nodup fun _ _ => Tab.canon_distinct hT,
      le_iff.2 fun a b ⟨Z, hZ, hz⟩ => (Tab.canon_holds hT a b).2 (Eq.mp (inter_apply _ _ _ _) (le_iff.1 hZ a b hz)).1,
      le_iff.2 fun a b hab => (Tab.canon_holds hT a b).1 hab⟩ h
  obtain ⟨dt, ht⟩ := round X Y t hY hp
  have hX := Tab.holds_of_n dt dX (fun a b hab => ((ht a b).1 hab).1) hn
  have hXt : rep X = rep t := Core.Rel.ext fun a b => ⟨hX a b, fun h => ((ht a b).1 h).1⟩
  have e : rep t = Core.Rel.nu fun X => rep s ∩ Φ X := by
    refine Core.Rel.le_antisymm (le_nu (le_iff.2 fun a b hab => ?_))
      (le_iff.2 fun a b hab => hX a b (le_iff.1 nX a b hab))
    obtain ⟨hx, hΦ⟩ := (ht a b).1 hab
    show (rep s ∩ Φ (rep t)) a b
    rw [← hXt, inter_apply]; exact ⟨le_iff.1 sX a b hx, hΦ⟩
  exact fun x y _ _ => by rw [e]

/-- **`μX : φ`** (`Tab.mu`): from `𝟘`, rounds `X ↦ X ∪ φ(X)`. Each round lies inside `μ` (`Φ` monotone, so
    `X ∪ Φ(X) ⊑ μ ∪ Φ(μ) = μ`); the last round is its table before it, so `Φ(X) ⊑ X` and `μ ⊑ X` (`mu_le`). A run
    reaching its cap is an error, which represents anything. -/
theorem mu_sound {A B : Obj} {w : String} {cap : Nat} {φ : Tab A B → Rel A B} {Φ : Den A B → Den A B}
    (hφ : ∀ X K, (φ X).Reps K (Φ (rep X))) (hm : Monotonic Φ) :
    ∀ K, (GenK.mu A B w cap φ).Reps K (Core.Rel.mu Φ) := by
  intro K; rw [reps_iff]; intro t h
  have eφ : ∀ X g, (φ X).runE {} = .ok g → Φ (rep X) = rep g :=
    fun X g hg => agrees_empty ((reps_iff _ _ _).1 (hφ X {}) g hg)
  -- a round: `Y = X ∪ g`, `rep g = Φ(rep X)`, then `pack`
  have round : ∀ X Y Y', ((φ X).runE {} >>= X.union) = .ok Y → Y.pack = .ok Y' →
      Y'.toList.Nodup ∧ ∀ a b, Y'.Holds a b ↔ X.Holds a b ∨ Φ (rep X) a b := by
    intro X Y Y' hY hp
    obtain ⟨g, hg, hu⟩ := bind_ok hY
    refine ⟨(Tab.pack_toList hp).2 ▸ Tab.union_nodup hu, fun a b => ?_⟩
    rw [Tab.pack_holds hp, Tab.union_holds hu, eφ X g hg]; rfl
  obtain ⟨Z, hZ, h⟩ := bind_ok (show (Tab.zero >>= fun Z =>
    Tab.fixOn (Tab.capMsg w cap) (fun X => (φ X).runE {} >>= X.union) (cap - 1) Z) = .ok t from h)
  have nZ : ∀ a b, ¬ Z.Holds a b := fun a b hz => (Tab.zero_holds hZ a b).1 hz
  obtain ⟨X, Y, ⟨dX, mX⟩, hY, hp, hn⟩ := Tab.fixOn_inv
    (fun X : Tab A B => X.toList.Nodup ∧ rep X ⊑ Core.Rel.mu Φ)
    (fun X Y Y' ⟨_, mX⟩ hY hp => by
      obtain ⟨d, hY'⟩ := round X Y Y' hY hp
      refine ⟨d, le_iff.2 fun a b hab => ?_⟩
      rcases (hY' a b).1 hab with hx | hx
      · exact le_iff.1 mX a b hx
      · exact le_iff.1 (mu_prefixed hm) a b (le_iff.1 (hm _ _ mX) a b hx))
    _ _ _ ⟨by
      rw [show Z.toList = [] from List.eq_nil_iff_forall_not_mem.2 fun p hp => nZ p.1 p.2 ((Tab.holds_iff_mem_toList Z p.1 p.2).2 hp)]
      exact List.nodup_nil, le_iff.2 fun a b hz => (nZ a b hz).elim⟩ h
  obtain ⟨dt, ht⟩ := round X Y t hY hp
  have hX := Tab.holds_of_n dX dt (fun a b hab => (ht a b).2 (.inl hab)) hn.symm
  have hXt : rep X = rep t := Core.Rel.ext fun a b => ⟨fun h => (ht a b).2 (.inl h), hX a b⟩
  have e : rep t = Core.Rel.mu Φ := by
    refine Core.Rel.le_antisymm (le_iff.2 fun a b hab => le_iff.1 mX a b (hX a b hab)) (mu_le (le_iff.2 fun a b hab => ?_))
    rw [← hXt] at hab ⊢; exact hX a b ((ht a b).2 (.inr hab))
  exact fun x y _ _ => by rw [e]

end GenK

end Rel.Lang
