/-
  The decision `thinA(Q)` makes on a state `s`, read back from its primitives' read-backs, which `thinAC_rep`
  discharges under its bit: with `fa s` the element and `fy s` the last element pushed, `up` holds where
  `fy s = b :: bs` and `le (fa s) b`, `down` where `le b (fa s)`, `lone` where `fy s` is empty or neither holds.
  The test is `q` at the pairs the round meets, read as `le`.
-/
import Rel.RepMerge

namespace Rel.Rep

open Tab Rel.Kernel Rel.Verify Rel Rel.Alg Rel.KernelWF

open FoldN OpsN Prim

section Body

open scoped Rel.Core.Rel
open Rel.Core.Rel hiding id comp recip inter union zero le inl inr junc

/-- **`thinA(Q)`'s three cases on a coreflexive `D`, read back from its primitives' read-backs**: a state `s` of
    `D`, `ta` reading its element `fa s` and `ty` its array `fy s`, is in `up` when `fy s = b :: bs` and
    `le (fa s) b`, in `down` when `le b (fa s)`, and in `lone` when `fy s` is empty or neither holds. Each
    hypothesis is one primitive's read-back at the decision's values (`rep_uncons`, `rep_comp`, `rep_pair`,
    `rep_ran`, `rep_dom`, `rep_diff`, `rep_union`); `ht1`, `ht2` read the test on the pairs of heads `rab` the
    decision meets, and on their swaps `rs`. -/
theorem thin_cases_set {B S : Obj} (le : B.El → B.El → Bool) (D : Tab S S) (Dm : S.El → Prop)
    (hD : rep D = corefl (α := S.El) Dm) (fa : S.El → B.El) (fy : S.El → List B.El)
    (ta : Tab S B) (eA : ∀ s x, rep ta s x ↔ Dm s ∧ x = fa s)
    (ty : Tab S (.arr B)) (eY : ∀ s x, rep ty s x ↔ Dm s ∧ x = fy s)
    (tu : Tab S (.prod B (.arr B)))
    (hUn : ∀ (xs : List B.El) b bs, rep (uncons (val ty)) xs (b, bs) ↔
      (∃ j, (val ty).row j = xs) ∧ xs = b :: bs)
    (htu : rep tu = rep ty ≫ rep (uncons (val ty)))
    (tab : Tab S (.prod B B)) (htab : rep tab = rpair (rep ta) (rep (outl tu)))
    (rab : Tab (.prod B B) (.prod B B))
    (hrab : rep rab = corefl (α := (Obj.prod B B).El) fun c => ∃ s, rep tab s c)
    (G1 : Tab (.prod B B) (.prod B B)) (ht1 : ∀ a b, rep rab (a, b) (a, b) → ((∃ c, rep G1 (a, b) c) ↔ le a b = true))
    (tq1 : Tab S (.prod B B)) (htq1 : rep tq1 = rep tab ≫ rep G1)
    (tup : Tab S S) (htup : rep tup = corefl (α := S.El) fun s => ∃ c, rep tq1 s c)
    (ss : Tab (.prod B B) (.prod B B)) (hss : rep ss = rpair (rep (outr rab)) (rep (outl rab)))
    (rs : Tab (.prod B B) (.prod B B))
    (hrs : rep rs = corefl (α := (Obj.prod B B).El) fun c => ∃ x, rep ss x c)
    (G2 : Tab (.prod B B) (.prod B B)) (ht2 : ∀ a b, rep rs (b, a) (b, a) → ((∃ c, rep G2 (b, a) c) ↔ le b a = true))
    (tq2 : Tab (.prod B B) (.prod B B)) (htq2 : rep tq2 = rep ss ≫ rep G2)
    (sw : Tab (.prod B B) (.prod B B))
    (hsw : rep sw = corefl (α := (Obj.prod B B).El) fun x => ∃ c, rep tq2 x c)
    (tq3 : Tab S (.prod B B)) (htq3 : rep tq3 = rep tab ≫ rep sw)
    (tdn : Tab S S) (htdn : rep tdn = corefl (α := S.El) fun s => ∃ c, rep tq3 s c)
    (du : Tab S S) (hdu : rep du = corefl (α := S.El) fun s => ∃ c, rep tu s c)
    (l1 : Tab S S) (hl1 : ∀ s s', rep l1 s s' ↔ rep D s s' ∧ ¬ rep du s s')
    (l2 : Tab S S) (hl2 : ∀ s s', rep l2 s s' ↔ rep du s s' ∧ ¬ rep tup s s')
    (l3 : Tab S S) (hl3 : ∀ s s', rep l3 s s' ↔ rep l2 s s' ∧ ¬ rep tdn s s')
    (lone : Tab S S) (hlone : rep lone = rep l1 ∪ rep l3) :
    (∀ s s', rep tup s s' ↔ s = s' ∧ Dm s ∧ ∃ b bs, fy s = b :: bs ∧ le (fa s) b = true) ∧
    (∀ s s', rep tdn s s' ↔ s = s' ∧ Dm s ∧ ∃ b bs, fy s = b :: bs ∧ le b (fa s) = true) ∧
    (∀ s s', rep lone s s' ↔ s = s' ∧ Dm s ∧
      (fy s = [] ∨ ∃ b bs, fy s = b :: bs ∧ le (fa s) b = false ∧ le b (fa s) = false)) := by
  have eD : ∀ s s', rep D s s' ↔ s = s' ∧ Dm s := fun s s' => by rw [hD]; exact Iff.rfl
  -- `uncons` of the array
  have eU : ∀ s b bs, rep tu s (b, bs) ↔ Dm s ∧ fy s = b :: bs := by
    intro s b bs; rw [htu, comp_apply]
    constructor
    · rintro ⟨v, h1, h2⟩; obtain ⟨hm, rfl⟩ := (eY _ _).1 h1; exact ⟨hm, ((hUn _ b bs).1 h2).2⟩
    · rintro ⟨hm, e⟩
      have h1 : rep ty s (fy s) := (eY _ _).2 ⟨hm, rfl⟩
      obtain ⟨i, -, hi⟩ := id h1
      exact ⟨fy s, h1, (hUn _ b bs).2 ⟨⟨i, hi⟩, e⟩⟩
  -- the pair of heads `(a, b)`
  have eAB : ∀ s a' b, rep tab s (a', b) ↔ Dm s ∧ a' = fa s ∧ ∃ bs, fy s = b :: bs := by
    intro s a' b; rw [htab]
    show rep ta s a' ∧ rep (outl tu) s b ↔ _
    constructor
    · rintro ⟨h1, h2⟩
      obtain ⟨hm, rfl⟩ := (eA _ _).1 h1
      obtain ⟨bs, h3⟩ := (outl_holds tu _ b).1 h2
      exact ⟨hm, rfl, bs, ((eU _ _ _).1 h3).2⟩
    · rintro ⟨hm, rfl, bs, e⟩
      exact ⟨(eA _ _).2 ⟨hm, rfl⟩, (outl_holds tu _ b).2 ⟨bs, (eU _ _ _).2 ⟨hm, e⟩⟩⟩
  have eRab : ∀ c c', rep rab c c' ↔ c = c' ∧ ∃ s, rep tab s c := fun c c' => by rw [hrab]; exact Iff.rfl
  -- `up`: the array is `b :: bs` and `le a b`
  have eUp : ∀ s s', rep tup s s' ↔ s = s' ∧ Dm s ∧ ∃ b bs, fy s = b :: bs ∧ le (fa s) b = true := by
    intro s s'; rw [htup]
    show s = s' ∧ (∃ c, rep tq1 s c) ↔ _
    refine and_congr_right fun _ => ⟨?_, ?_⟩
    · rintro ⟨c, hc⟩
      rw [htq1, comp_apply] at hc
      obtain ⟨⟨a', b⟩, h1, h2⟩ := hc
      obtain ⟨hm, rfl, bs, e⟩ := (eAB _ _ _).1 h1
      exact ⟨hm, b, bs, e, (ht1 _ _ ((eRab _ _).2 ⟨rfl, _, h1⟩)).1 ⟨c, h2⟩⟩
    · rintro ⟨hm, b, bs, e, hl⟩
      have h1 : rep tab s (fa s, b) := (eAB _ _ _).2 ⟨hm, rfl, bs, e⟩
      obtain ⟨c, h2⟩ := (ht1 _ _ ((eRab _ _).2 ⟨rfl, _, h1⟩)).2 hl
      exact ⟨c, by rw [htq1, comp_apply]; exact ⟨_, h1, h2⟩⟩
  -- the swap `(b, a)` of a pair of heads, and `down`: the swap passes
  have eOR : ∀ c x, rep (outr rab) c x ↔ (∃ s, rep tab s c) ∧ x = c.2 := by
    intro c x
    refine (outr_holds rab c x).trans ⟨?_, ?_⟩
    · rintro ⟨w, h⟩; obtain ⟨e, hm⟩ := (eRab _ _).1 h; subst e; exact ⟨hm, rfl⟩
    · rintro ⟨hm, rfl⟩; exact ⟨c.1, (eRab _ _).2 ⟨rfl, hm⟩⟩
  have eOL : ∀ c x, rep (outl rab) c x ↔ (∃ s, rep tab s c) ∧ x = c.1 := by
    intro c x
    refine (outl_holds rab c x).trans ⟨?_, ?_⟩
    · rintro ⟨w, h⟩; obtain ⟨e, hm⟩ := (eRab _ _).1 h; subst e; exact ⟨hm, rfl⟩
    · rintro ⟨hm, rfl⟩; exact ⟨c.2, (eRab _ _).2 ⟨rfl, hm⟩⟩
  have eSS : ∀ a' b d, rep ss (a', b) d ↔ (∃ s, rep tab s (a', b)) ∧ d = (b, a') := by
    intro a' b d; rw [hss]
    show rep (outr rab) (a', b) d.1 ∧ rep (outl rab) (a', b) d.2 ↔ _
    constructor
    · rintro ⟨h1, h2⟩
      obtain ⟨hm, e1⟩ := (eOR _ _).1 h1
      obtain ⟨-, e2⟩ := (eOL _ _).1 h2
      exact ⟨hm, Prod.ext e1 e2⟩
    · rintro ⟨hm, rfl⟩; exact ⟨(eOR _ _).2 ⟨hm, rfl⟩, (eOL _ _).2 ⟨hm, rfl⟩⟩
  have eRs : ∀ c c', rep rs c c' ↔ c = c' ∧ ∃ x, rep ss x c := fun c c' => by rw [hrs]; exact Iff.rfl
  have eSw : ∀ a' b c', rep sw (a', b) c' ↔ (a', b) = c' ∧ (∃ s, rep tab s (a', b)) ∧ le b a' = true := by
    intro a' b c'; rw [hsw]
    show (a', b) = c' ∧ (∃ d, rep tq2 (a', b) d) ↔ _
    refine and_congr_right fun _ => ⟨?_, ?_⟩
    · rintro ⟨d, hd⟩
      rw [htq2, comp_apply] at hd
      obtain ⟨x, h1, h2⟩ := hd
      obtain ⟨hm, rfl⟩ := (eSS _ _ _).1 h1
      exact ⟨hm, (ht2 _ _ ((eRs _ _).2 ⟨rfl, _, h1⟩)).1 ⟨d, h2⟩⟩
    · rintro ⟨hm, hl⟩
      have h1 : rep ss (a', b) (b, a') := (eSS _ _ _).2 ⟨hm, rfl⟩
      obtain ⟨d, h2⟩ := (ht2 _ _ ((eRs _ _).2 ⟨rfl, _, h1⟩)).2 hl
      exact ⟨d, by rw [htq2, comp_apply]; exact ⟨_, h1, h2⟩⟩
  have eDn : ∀ s s', rep tdn s s' ↔ s = s' ∧ Dm s ∧ ∃ b bs, fy s = b :: bs ∧ le b (fa s) = true := by
    intro s s'; rw [htdn]
    show s = s' ∧ (∃ c, rep tq3 s c) ↔ _
    refine and_congr_right fun _ => ⟨?_, ?_⟩
    · rintro ⟨c, hc⟩
      rw [htq3, comp_apply] at hc
      obtain ⟨⟨a', b⟩, h1, h2⟩ := hc
      obtain ⟨hm, rfl, bs, e⟩ := (eAB _ _ _).1 h1
      obtain ⟨-, -, hl⟩ := (eSw _ _ _).1 h2
      exact ⟨hm, b, bs, e, hl⟩
    · rintro ⟨hm, b, bs, e, hl⟩
      have h1 : rep tab s (fa s, b) := (eAB _ _ _).2 ⟨hm, rfl, bs, e⟩
      exact ⟨(fa s, b), by rw [htq3, comp_apply]; exact ⟨_, h1, (eSw _ _ _).2 ⟨rfl, ⟨_, h1⟩, hl⟩⟩⟩
  have eDu : ∀ s s', rep du s s' ↔ s = s' ∧ Dm s ∧ ∃ b bs, fy s = b :: bs := by
    intro s s'; rw [hdu]
    show s = s' ∧ (∃ c, rep tu s c) ↔ _
    refine and_congr_right fun _ => ⟨?_, ?_⟩
    · rintro ⟨⟨b, bs⟩, h⟩; obtain ⟨hm, e⟩ := (eU _ _ _).1 h; exact ⟨hm, b, bs, e⟩
    · rintro ⟨hm, b, bs, e⟩; exact ⟨(b, bs), (eU _ _ _).2 ⟨hm, e⟩⟩
  -- `lone`: the array is empty, or neither pair of heads passes
  refine ⟨eUp, eDn, fun s s' => ?_⟩
  rw [hlone]
  show rep l1 s s' ∨ rep l3 s s' ↔ _
  rw [hl1, hl3, hl2, eD, eDu, eUp, eDn]
  constructor
  · rintro (⟨⟨e, hm⟩, hn⟩ | ⟨⟨⟨e, hm, b, bs, hy⟩, hn1⟩, hn2⟩)
    · refine ⟨e, hm, Or.inl ?_⟩
      cases h : fy s with
      | nil => rfl
      | cons b bs => exact absurd ⟨e, hm, b, bs, h⟩ hn
    · refine ⟨e, hm, Or.inr ⟨b, bs, hy, ?_, ?_⟩⟩
      · cases h : le (fa s) b
        · rfl
        · exact absurd ⟨e, hm, b, bs, hy, h⟩ hn1
      · cases h : le b (fa s)
        · rfl
        · exact absurd ⟨e, hm, b, bs, hy, h⟩ hn2
  · rintro ⟨e, hm, hy | ⟨b, bs, hy, h1, h2⟩⟩
    · refine Or.inl ⟨⟨e, hm⟩, ?_⟩
      rintro ⟨-, -, b, bs, hb⟩
      rw [hy] at hb
      exact List.cons_ne_nil _ _ hb.symm
    · refine Or.inr ⟨⟨⟨e, hm, b, bs, hy⟩, ?_⟩, ?_⟩
      · rintro ⟨-, -, b', bs', hb, h⟩
        rw [hy] at hb
        obtain ⟨rfl, rfl⟩ := List.cons.inj hb
        exact Bool.false_ne_true (h1.symm.trans h)
      · rintro ⟨-, -, b', bs', hb, h⟩
        rw [hy] at hb
        obtain ⟨rfl, rfl⟩ := List.cons.inj hb
        exact Bool.false_ne_true (h2.symm.trans h)

end Body

end Rel.Rep

#print axioms Rel.Rep.thin_cases_set
