import Rel.Lang.GenKBits

/-! `GenK.hylo` represents `μX : Φ(X)` (`Tm.den` of `hylo`) on the keys in demand: the nodes `N` it builds are the keys
    closed under the children, and the rounds of `Tab.mu` on `N ≫ φ` reach a table that is below `μ Φ` (each round
    is) and, `Φ` being local along the children, a prefixed point on `N` (`Tab.mu_holds`). The cycle test is not read:
    it only turns an answer into an error, and an error represents anything. -/

namespace Rel.Lang

open Rel Rel.Rep Rel.Kernel Rel.Verify Gen
open scoped Rel.Core.Rel
open Rel.Core.Rel hiding id comp recip inter union zero le inl inr junc

namespace GenK

/-- `M ≫ S` run on the table `M` (`compT`, the empty context): `S` read on `ran M` (`compT_sound`). -/
theorem compT_holds {A B C : Obj} {S : Rel B C} {Y : Core.Rel B.El C.El} (hS : ∀ K, K.WF → S.Reps K Y) (wS : S.Wf)
    (M : Tab A B) (wM : M.WF) (T : Tab A C) (h : (compT (.ok M) S).runE {} = .ok T) (a : A.El) (c : C.El) :
    T.Holds a c ↔ ∃ b, M.Holds a b ∧ Y b c :=
  (reps_iff _ _ _).1 (compT_sound (r' := .ok M) (K := {}) (X := rep M)
    (fun _ hr a b _ _ _ => by cases hr; exact Iff.rfl) hS wS Known.wf_empty (fun _ hr => by cases hr; exact wM))
    T h a c rfl rfl trivial

/-- **`hylo(c, S)` represents `μX : Φ(X)`** (`GenK.hylo`), given the children's code `ch` representing `CH`, the
body `φ Y` representing `Φ (rep Y)` for every table `Y`, `Φ` monotonic and local along `CH` (`Tm.den_local`). The
nodes `N` (`Tab.mu_holds`) are coreflexive, hold the keys in demand and are closed under `CH`; the rounds on `N` stay
below `μ Φ` and end at `Y` with `N ≫ Φ(Y) ⊑ Y`, so `Z = (N ⇒ Y)` is a prefixed point and `μ Φ ⊑ Y` on `N`. No
well-foundedness is read: a cyclic `ch` makes the code an error table, which represents `μ Φ` vacuously. -/
theorem hylo_sound {A B : Obj} {what : String} {ch : Rel A A} {CH : Den A A}
    {φ : Tab A B → Rel A B} {Φ : Den A B → Den A B} (hch : ∀ K, K.WF → ch.Reps K CH) (wch : ch.Wf)
    (hφ : ∀ Y, Y.WF → ∀ K, K.WF → (φ Y).Reps K (Φ (rep Y))) (wφ : ∀ Y, Y.WF → (φ Y).Wf) (hm : Monotonic Φ)
    (hl : ∀ X Y a, (∀ a', CH a a' → ∀ b, (X a' b ↔ Y a' b)) → ∀ b, (Φ X a b ↔ Φ Y a b)) :
    ∀ K, K.WF → (GenK.hylo A B what ch φ).Reps K (Core.Rel.mu Φ) := by
  unfold GenK.hylo
  exact ofVals_sound fun _ _ _ t hK wX h a b ha _ _ => by
    obtain ⟨D, hD, h⟩ := bind_ok h
    obtain ⟨N, hN, h⟩ := bind_ok h
    obtain ⟨C, -, h⟩ := bind_ok h
    obtain ⟨cyc, -, h⟩ := bind_ok h
    split at h
    · nomatch h
    obtain ⟨_, -, h⟩ := bind_ok h
    obtain ⟨Y, hY, h⟩ := bind_ok h
    -- the nodes: coreflexive, holding `D`, closed under `CH`
    have wD := Tab.idU_wf hD wX
    have hNw : ∀ (M T : Tab A A), (do D.union (← (← (compT (.ok M) ch).runE {}).ran) : Except String (Tab A A)) = .ok T →
        M.WF → T.WF := fun M T hT wM => by
      obtain ⟨R, hR, hT⟩ := bind_ok hT
      obtain ⟨P, hP, hT⟩ := bind_ok hT
      exact Tab.union_wf hT wD
        (Tab.ran_wf hP ((compT_wf (r' := .ok M) (fun _ hr => by cases hr; exact wM) wch).runE Known.wf_empty hR))
    have wN : N.WF := Tab.mu_wf hNw hN
    obtain ⟨hNc, hNF⟩ := Tab.mu_holds (F := fun R a a' => D.Holds a a' ∨ (a = a' ∧ ∃ x y, R x y ∧ CH y a))
      (fun M T wM hT a a' => by
        obtain ⟨R, hR, hT⟩ := bind_ok hT
        obtain ⟨P, hP, hT⟩ := bind_ok hT
        rw [Tab.union_holds hT, Tab.ran_holds hP]
        refine or_congr Iff.rfl (and_congr Iff.rfl ?_)
        exact exists_congr fun x => (compT_holds hch wch M wM R hR x a)) hNw
      (fun R => ∀ a a', R a a' → a = a') (fun _ _ h => h.elim)
      (fun R hR a a' h => h.elim (hR a a') fun h => h.elim (fun h => ((Tab.idU_holds hD a a').1 h).1) (·.1)) hN
    have hDN : ∀ a, D.Holds a a → N.Holds a a := fun a h => hNF a a (Or.inl h)
    have hcl : ∀ a a', N.Holds a a → CH a a' → N.Holds a' a' := fun a a' h c => hNF a' a' (Or.inr ⟨rfl, a, a, h, c⟩)
    -- the rounds on `N`: below `μ Φ`, and a prefixed point there
    obtain ⟨hYm, hYF⟩ := Tab.mu_holds (F := fun R a b => N.Holds a a ∧ Φ R a b)
      (fun M T wM hT a b => by
        rw [compT_holds (hφ M wM) (wφ M wM) N wN T hT a b]
        exact ⟨fun ⟨a', hn, hp⟩ => by obtain rfl := hNc a a' hn; exact ⟨hn, hp⟩, fun ⟨hn, hp⟩ => ⟨a, hn, hp⟩⟩)
      (fun M T hT wM => (compT_wf (r' := .ok N) (fun _ hr => by cases hr; exact wN) (wφ M wM)).runE Known.wf_empty hT)
      (fun R => ∀ a b, R a b → Core.Rel.mu Φ a b) (fun _ _ h => h.elim)
      (fun R hR a b h => h.elim (hR a b) fun h => le_iff.1 (mu_prefixed hm) a b
        (le_iff.1 (hm R (Core.Rel.mu Φ) (le_iff.2 hR)) a b h.2)) hY
    have hZ : Core.Rel.mu Φ ⊑ fun a b => N.Holds a a → Y.Holds a b := mu_le <| le_iff.2 fun a b hz hn =>
      hYF a b ⟨hn, (hl (fun a b => N.Holds a a → Y.Holds a b) (rep Y) a (fun a' c b' => ⟨fun hy => hy (hcl a a' hn c), fun hy _ => hy⟩) b).1 hz⟩
    have hDa : D.Holds a a := (Tab.idU_holds hD a a).2 ⟨rfl, (side_some hK a).1 ha⟩
    rw [rep_apply, Tab.comp_holds h]
    exact ⟨fun ⟨a', hd, hy⟩ => by obtain ⟨rfl, -⟩ := (Tab.idU_holds hD a a').1 hd; exact hYm a b hy,
      fun hm' => ⟨a, hDa, le_iff.1 hZ a b hm' (hDN a hDa)⟩⟩

end GenK

end Rel.Lang
