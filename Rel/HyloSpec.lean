import Rel.Core.Fix

/-! `hylo(c, S)` (`Tm.hylo`) means `μX : c G(X) S`, read on relations as predicates: `Φ X = c G(X) S` is monotonic
    (the elaborator's polarity check) and local — its value at `a` reads `X` only at the children `ch = c ∈_G` of
    `a`, as `G(X)` reads `X` only at the members of a `G`-value (`Tm.den_local`). From the nodes `N` closed under
    `ch`, nothing valued, each round values the pending nodes with no pending child by `Φ` and drops them; the
    rounds that empty the pending set leave the least fixed point on `N` (`rounds_lfp`), and rounds stuck with nodes
    pending mean `ch` is not well-founded there (`stuck_not_acc`), the cycle a run reports. The pending set is a
    coreflexive `P`, the round `P' = P − ready ch P`, `X' = X ∪ ready ch P ≫ Φ X`. -/

namespace Rel.Hylo

open scoped Rel.Core.Rel
open Rel.Core.Rel hiding id comp recip inter union zero le inl inr junc

variable {α β : Type}

/-- `Φ X` at a node `a` of `N` reads `X` only at the children of `a`. -/
def Local (N : α → Prop) (ch : Core.Rel α α) (Φ : Core.Rel α β → Core.Rel α β) : Prop :=
  ∀ X Y a, N a → (∀ a', ch a a' → ∀ b, (X a' b ↔ Y a' b)) → ∀ b, (Φ X a b ↔ Φ Y a b)

/-- The pending nodes (the coreflexive `P`) none of whose children is pending: `P − ch ≫ P ≫ ⊤`. -/
def ready (ch P : Core.Rel α α) : Core.Rel α α := diff P (ch ≫ P ≫ top)

/-- `P` is coreflexive: a set of nodes. -/
def Cor (P : Core.Rel α α) : Prop := ∀ a b, P a b → a = b

theorem ready_iff {ch P : Core.Rel α α} (hP : Cor P) {a a' : α} :
    ready ch P a a' ↔ a = a' ∧ P a a ∧ ∀ c, ch a c → ¬ P c c :=
  ⟨fun ⟨h1, h2⟩ => by
    obtain rfl := hP _ _ h1
    exact ⟨rfl, h1, fun c hc hcc => h2 ⟨c, hc, c, hcc, trivial⟩⟩,
   fun ⟨e, h1, h2⟩ => by
    subst e
    exact ⟨h1, fun ⟨b, hb, c, hc, _⟩ => by
      obtain rfl := hP _ _ hc
      exact h2 b hb hc⟩⟩

theorem ready_comp {ch P : Core.Rel α α} (hP : Cor P) {S : Core.Rel α β} {a : α} {b : β} :
    (ready ch P ≫ S) a b ↔ (P a a ∧ ∀ c, ch a c → ¬ P c c) ∧ S a b :=
  ⟨fun ⟨c, hr, hs⟩ => by
    obtain ⟨rfl, h1, h2⟩ := (ready_iff hP).1 hr
    exact ⟨⟨h1, h2⟩, hs⟩,
   fun ⟨⟨h1, h2⟩, hs⟩ => ⟨a, (ready_iff hP).2 ⟨rfl, h1, h2⟩, hs⟩⟩

/-- `n` rounds from the pending coreflexive `P` and the values `X`: the ready nodes valued by `Φ X` and dropped. -/
def rounds (ch : Core.Rel α α) (Φ : Core.Rel α β → Core.Rel α β) :
    Nat → Core.Rel α α → Core.Rel α β → Core.Rel α α × Core.Rel α β
  | 0, P, X => (P, X)
  | n + 1, P, X => rounds ch Φ n (diff P (ready ch P)) (X ∪ ready ch P ≫ Φ X)

theorem rounds_succ (ch : Core.Rel α α) (Φ : Core.Rel α β → Core.Rel α β) (n : Nat) (P : Core.Rel α α)
    (X : Core.Rel α β) :
    rounds ch Φ (n + 1) P X = rounds ch Φ n (diff P (ready ch P)) (X ∪ ready ch P ≫ Φ X) := rfl

/-- What the rounds keep: `P` is coreflexive, pending nodes lie in `N` and have no value, a node of `N` done has
    the least fixed point's value, and its children are done. -/
def Inv (ch : Core.Rel α α) (Φ : Core.Rel α β → Core.Rel α β) (N : α → Prop) (P : Core.Rel α α)
    (X : Core.Rel α β) : Prop :=
  Cor P ∧ (∀ a, P a a → N a) ∧ (∀ a, N a → ¬ P a a → ∀ b, (X a b ↔ mu Φ a b)) ∧ (∀ a, P a a → ∀ b, ¬ X a b) ∧
    (∀ a a', N a → ¬ P a a → ch a a' → ¬ P a' a')

/-- One round keeps `Inv`: a ready node's children are done, so `Φ X` there is `Φ (mu Φ)` (`Local`), the least
    fixed point's value. -/
theorem round_inv {ch : Core.Rel α α} {Φ : Core.Rel α β → Core.Rel α β} {N : α → Prop} {P : Core.Rel α α}
    {X : Core.Rel α β} (hm : Monotonic Φ)
    (hl : Local N ch Φ) (hN : ∀ a a', N a → ch a a' → N a') (h : Inv ch Φ N P X) :
    Inv ch Φ N (diff P (ready ch P)) (X ∪ ready ch P ≫ Φ X) := by
  obtain ⟨hP, hs, hd, he, hk⟩ := h
  have hr : ∀ a, ready ch P a a ↔ P a a ∧ ∀ c, ch a c → ¬ P c c :=
    fun a => ⟨fun h => ((ready_iff hP).1 h).2, fun h => (ready_iff hP).2 ⟨rfl, h⟩⟩
  refine ⟨fun a b h => hP a b h.1, fun a ha => hs a ha.1, fun a hNa hp b => ?_, fun a hp b hx => ?_,
    fun a a' hNa hp hc hp' => ?_⟩
  · by_cases hpa : P a a
    · have hR := (hr a).1 (Classical.byContradiction fun hR => hp ⟨hpa, hR⟩)
      have key : Φ X a b ↔ mu Φ a b :=
        (hl X (mu Φ) a hNa (fun a' hc b' => hd a' (hN a a' hNa hc) (hR.2 a' hc) b') b).trans
          (by rw [mu_fix hm])
      exact ⟨fun hx => hx.elim (fun hx => absurd hx (he a hpa b))
          (fun hx => key.1 ((ready_comp hP).1 hx).2),
        fun hx => Or.inr ((ready_comp hP).2 ⟨hR, key.2 hx⟩)⟩
    · exact ⟨fun hx => hx.elim (hd a hNa hpa b).1 (fun hx => absurd ((ready_comp hP).1 hx).1.1 hpa),
        fun hx => Or.inl ((hd a hNa hpa b).2 hx)⟩
  · exact hx.elim (he a hp.1 b) (fun hx => hp.2 ((hr a).2 ((ready_comp hP).1 hx).1))
  · by_cases hpa : P a a
    · exact ((hr a).1 (Classical.byContradiction fun hR => hp ⟨hpa, hR⟩)).2 a' hc hp'.1
    · exact hk a a' hNa hpa hc hp'.1

theorem rounds_inv {ch : Core.Rel α α} {Φ : Core.Rel α β → Core.Rel α β} {N : α → Prop}
    (hm : Monotonic Φ) (hl : Local N ch Φ)
    (hN : ∀ a a', N a → ch a a' → N a') :
    ∀ n P X, Inv ch Φ N P X → Inv ch Φ N (rounds ch Φ n P X).1 (rounds ch Φ n P X).2
  | 0, _, _, h => h
  | n + 1, _, _, h => by rw [rounds_succ]; exact rounds_inv hm hl hN n _ _ (round_inv hm hl hN h)

/-- **`hylo` computes the least fixed point**: from the nodes `N` closed under `ch`, all pending and none valued,
    rounds that leave nothing pending value every node of `N` as `mu Φ`, `Φ X = c G(X) S`. -/
theorem rounds_lfp {ch : Core.Rel α α} {Φ : Core.Rel α β → Core.Rel α β} {N : α → Prop}
    (hm : Monotonic Φ) (hl : Local N ch Φ)
    (hN : ∀ a a', N a → ch a a' → N a') (n : Nat) (hdone : (rounds ch Φ n (corefl N) Core.Rel.zero).1 = Core.Rel.zero) :
    ∀ a, N a → ∀ b, ((rounds ch Φ n (corefl N) Core.Rel.zero).2 a b ↔ mu Φ a b) := fun a hNa b =>
  (rounds_inv hm hl hN n (corefl N) _ ⟨fun _ _ h => h.1, fun _ h => h.2, fun _ h hn => absurd ⟨rfl, h⟩ hn,
    fun _ _ _ h => h, fun _ _ h hn => absurd ⟨rfl, h⟩ hn⟩).2.2.1 a hNa
    (fun h => (Eq.mp (congrFun (congrFun hdone a) a) h : False)) b

end Rel.Hylo
