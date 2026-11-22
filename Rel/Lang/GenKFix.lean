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

end Tab

namespace GenK

/-- **`νX : S ∩ φ`** (`Tab.nu`): from `S`'s canonical table, rounds `X ↦ X ∩ φ(X)`. Each round holds `ν` (`Φ`
    monotone, so `ν = TS ∩ Φ(ν) ⊑ X ∩ Φ(X)`) and lies inside `TS`; the last round is its table before it, so
    `X ⊑ TS ∩ Φ(X)` and `X ⊑ ν` (`le_nu`). -/
theorem nu_sound {A B : Obj} {S : Rel A B} {φ : Tab A B → Rel A B} {TS : Den A B} {Φ : Den A B → Den A B}
    (hS : ∀ K, K.WF → S.Reps K TS) (wS : S.Wf) (hφ : ∀ X, X.WF → ∀ K, K.WF → (φ X).Reps K (Φ (rep X)))
    (wφ : ∀ X, X.WF → (φ X).Wf) (hm : Monotonic Φ) :
    ∀ K, K.WF → (GenK.nu A B S φ).Reps K (Core.Rel.nu fun X => TS ∩ Φ X) := by
  intro K _; rw [reps_iff]; intro t h
  obtain ⟨s, hs, h⟩ := bind_ok (show (S.runE {} >>= fun s => Tab.nu (fun X => (φ X).runE {}) s) = .ok t from h)
  obtain rfl : TS = rep s := agrees_empty ((reps_iff _ _ _).1 (hS {} Known.wf_empty) s hs)
  have eφ : ∀ X g, X.WF → (φ X).runE {} = .ok g → Φ (rep X) = rep g :=
    fun X g wX hg => agrees_empty ((reps_iff _ _ _).1 (hφ X wX {} Known.wf_empty) g hg)
  have hfix : rep s ∩ Φ (Core.Rel.nu fun X => rep s ∩ Φ X) = Core.Rel.nu fun X => rep s ∩ Φ X :=
    nu_fix (φ := fun X => rep s ∩ Φ X) fun X Y hXY =>
      le_inter (inter_le_left _ _) (Core.Rel.le_trans (inter_le_right _ _) (hm X Y hXY))
  -- a round: `Y = X ∩ g`, `rep g = Φ(rep X)`, then `pack`
  have round : ∀ X Y Y', X.WF → ((φ X).runE {} >>= X.inter) = .ok Y → Y.pack = .ok Y' →
      Y'.toList.Nodup ∧ (∀ a b, Y'.Holds a b ↔ X.Holds a b ∧ Φ (rep X) a b) ∧ Y'.WF := by
    intro X Y Y' wX hY hp
    obtain ⟨g, hg, hi⟩ := bind_ok hY
    refine ⟨(Tab.pack_toList hp).2 ▸ Tab.toList_nodup fun _ _ => Tab.inter_distinct hi, fun a b => ?_,
      Tab.pack_wf hp (Tab.inter_wf hi wX ((wφ X wX).runE Known.wf_empty hg))⟩
    rw [Tab.pack_holds hp, Tab.inter_holds hi, eφ X g wX hg]; rfl
  unfold Tab.nu at h
  obtain ⟨T, hT, h⟩ := bind_ok h
  obtain ⟨X, Y, ⟨dX, nX, sX, wX⟩, hY, hp, hn⟩ := Tab.fixOn_inv
    (fun X : Tab A B => X.toList.Nodup ∧ (Core.Rel.nu fun X => rep s ∩ Φ X) ⊑ rep X ∧ rep X ⊑ rep s ∧ X.WF)
    (fun X Y Y' ⟨_, nX, sX, wX⟩ hY hp => by
      obtain ⟨d, hY', w⟩ := round X Y Y' wX hY hp
      refine ⟨d, le_iff.2 fun a b hab => (hY' a b).2 ⟨le_iff.1 nX a b hab, ?_⟩,
        le_iff.2 fun a b hab => le_iff.1 sX a b ((hY' a b).1 hab).1, w⟩
      rw [← hfix, inter_apply] at hab
      exact le_iff.1 (hm _ _ nX) a b hab.2)
    _ _ _ ⟨Tab.toList_nodup fun _ _ => Tab.canon_distinct hT,
      le_iff.2 fun a b ⟨Z, hZ, hz⟩ => (Tab.canon_holds hT a b).2 (Eq.mp (inter_apply _ _ _ _) (le_iff.1 hZ a b hz)).1,
      le_iff.2 fun a b hab => (Tab.canon_holds hT a b).1 hab, Tab.canon_wf hT (wS.runE Known.wf_empty hs)⟩ h
  obtain ⟨dt, ht, -⟩ := round X Y t wX hY hp
  have hX := Tab.holds_of_n dt dX (fun a b hab => ((ht a b).1 hab).1) hn
  have hXt : rep X = rep t := Core.Rel.ext fun a b => ⟨hX a b, fun h => ((ht a b).1 h).1⟩
  have e : rep t = Core.Rel.nu fun X => rep s ∩ Φ X := by
    refine Core.Rel.le_antisymm (le_nu (le_iff.2 fun a b hab => ?_))
      (le_iff.2 fun a b hab => hX a b (le_iff.1 nX a b hab))
    obtain ⟨hx, hΦ⟩ := (ht a b).1 hab
    show (rep s ∩ Φ (rep t)) a b
    rw [← hXt, inter_apply]; exact ⟨le_iff.1 sX a b hx, hΦ⟩
  exact fun x y _ _ _ => by rw [e]

/-- **`μX : φ`** (`Tab.mu`): from `𝟘`, rounds `X ↦ X ∪ φ(X)` (`Tab.mu_holds`). Each round lies inside `μ` (`Φ`
    monotone, so `X ∪ Φ(X) ⊑ μ ∪ Φ(μ) = μ`); the answer is a prefixed point of `Φ`, so `μ` lies inside it
    (`mu_le`). A run reaching its cap is an error, which represents anything. -/
theorem mu_sound {A B : Obj} {w : String} {cap : Nat} {φ : Tab A B → Rel A B} {Φ : Den A B → Den A B}
    (hφ : ∀ X, X.WF → ∀ K, K.WF → (φ X).Reps K (Φ (rep X))) (wφ : ∀ X, X.WF → (φ X).Wf) (hm : Monotonic Φ) :
    ∀ K, K.WF → (GenK.mu A B w cap φ).Reps K (Core.Rel.mu Φ) := by
  intro K _; rw [reps_iff]; intro t h
  obtain ⟨mt, ft⟩ := Tab.mu_holds (F := Φ)
    (fun X g wX hg a b => by
      show rep g a b ↔ Φ (rep X) a b; rw [agrees_empty ((reps_iff _ _ _).1 (hφ X wX {} Known.wf_empty) g hg)])
    (fun X g hg wX => (wφ X wX).runE Known.wf_empty hg)
    (· ⊑ Core.Rel.mu Φ) (le_iff.2 fun _ _ hz => hz.elim)
    (fun X mX => le_iff.2 fun a b hab => hab.elim (le_iff.1 mX a b)
      fun hx => le_iff.1 (mu_prefixed hm) a b (le_iff.1 (hm _ _ mX) a b hx))
    (show Tab.mu w cap (fun X => (φ X).runE {}) = .ok t from h)
  have e : rep t = Core.Rel.mu Φ := Core.Rel.le_antisymm mt (mu_le (le_iff.2 ft))
  exact fun x y _ _ _ => by rw [e]

end GenK

end Rel.Lang
