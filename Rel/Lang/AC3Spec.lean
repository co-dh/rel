import Rel.AC3
import Rel.Lang.GenSpec

/-! `Gen.nuAC` computes the `νX` that `Gen.nu`'s plain rounds compute (`nu_sound`), for an AC-3 body
    `S ∩ ⋂ₖ Aₖ\(X Cₖ)`: AC-3's delta rounds end on a fixed naive iterate (`AC3.acFix_naive`), and the naive iterates
    from `S` down reach the greatest fixed point once they are fixed. -/

namespace Rel.Lang

open Tab Rel.Alg Rel.Rep Rel.Kernel Gen
open scoped Rel.Core.Rel
open Rel.Core.Rel hiding id comp recip inter union zero le inl inr junc

/-- One arc `A\(X C)` of an AC-3 body: its code (`Gen.Arc`) and the meanings of its four parts `A`, `C`, `𝟙(V)`,
    `𝟙(D)`. -/
abbrev ArcDen (V D : Obj) := Arc V D × (Den V V × Den D D × Den V V × Den D D)

/-- The four codes of the arc `p` compute their meanings, and its universes are coreflexive: `acFixC` reads a
    universe's keys, `ldivDen` its values, and on a coreflexive the two agree. -/
def ArcDen.Sound {V D : Obj} (p : ArcDen V D) : Prop :=
  Gen.Sound p.1.1 p.2.1 ∧ Gen.Sound p.1.2.1 p.2.2.1 ∧ Gen.Sound p.1.2.2.1 p.2.2.2.1 ∧ Gen.Sound p.1.2.2.2 p.2.2.2.2 ∧
    (∀ w v, p.2.2.2.1 w v → w = v) ∧ ∀ e f, p.2.2.2.2 e f → e = f

/-- The arcs `ps` read at `X`: `⋂ₖ Aₖ\(X Cₖ)`, each division within its arc's universes. -/
abbrev arcsDen {V D : Obj} (ps : List (ArcDen V D)) (X : Den V D) : Den V D :=
  ps.foldr (fun p Y => ldivDen p.2.1 (X ≫ p.2.2.1) p.2.2.2.1 p.2.2.2.2 ∩ Y) Core.Rel.top

/-- `νX : S ∩ ⋂ₖ Aₖ\(X Cₖ)` by AC-3's delta rounds (`Gen.nuAC`), its arcs `q :: ps`: the greatest fixed point, as
    `nu_sound` has it for `Gen.nu`. Hypotheses, `acInv_init`'s read in `Rel(Set)`: the first arc's `𝟙(V)` holds every
    arc's `A`-predecessors (the first delta round checks them all), and each pair of `S` lies in every arc's vacuous
    part (`AC3.Vac`), as the first naive round would leave it. -/
theorem nuAC_sound {V D : Obj} {S : Fn false V D} {TS : Den V D} {q : ArcDen V D} {ps : List (ArcDen V D)}
    (hS : Sound S TS) (hps : ∀ p ∈ q :: ps, p.Sound)
    (hUA : ∀ p ∈ q :: ps, ∀ w x, p.2.1 w x → q.2.2.2.1 w w)
    (hsV : ∀ p ∈ q :: ps, ∀ x e, TS x e → (∃ w, p.2.1 w x) ∨ ((∃ v, p.2.2.2.1 v x) ∧ ∃ f, p.2.2.2.2 f e)) :
    Sound (Gen.nuAC V D S q.1 (ps.map Prod.fst)) (Core.Rel.nu fun X => TS ∩ arcsDen (q :: ps) X) := by
  classical
  let G : ArcDen V D → Revise V D := fun p =>
    ⟨CRel.rel (p.1.1.run {}), CRel.rel (p.1.2.1.run {}), CRel.rel (p.1.2.2.1.run {}), CRel.rel (p.1.2.2.2.run {})⟩
  let okp : ArcDen V D → Bool := fun p => CRel.ok (p.1.1.run {}) && CRel.ok (p.1.2.1.run {}) &&
    CRel.ok (p.1.2.2.1.run {}) && CRel.ok (p.1.2.2.2.run {})
  let s : CRel V D := S.run {}
  let U : Tab V V := CRel.rel (q.1.2.2.1.run {})
  have hG : Gen.nuAC V D S q.1 (ps.map Prod.fst) = .tab (CRel.mk (acFixC s.rel ((q :: ps).map G) U).1.1
      (s.ok && (q :: ps).all okp && (acFixC s.rel ((q :: ps).map G) U).2)) := by
    simp only [Gen.nuAC, List.map_cons, List.map_map, List.all_cons, List.all_map]; rfl
  rw [hG]
  refine const_sound fun hb => ?_
  obtain ⟨hok, e⟩ := CRel.mk_ok_rel hb
  rw [e]
  simp only [Bool.and_eq_true, List.all_eq_true] at hok
  obtain ⟨⟨hs, hall⟩, hd⟩ := hok
  have hTS : rep s.rel = TS := hS.run_eq hs
  -- each arc's tables are its meanings
  have hp' : ∀ p ∈ q :: ps, rep (G p).A = p.2.1 ∧ rep (G p).C = p.2.2.1 ∧ rep (G p).UV = p.2.2.2.1 ∧
      rep (G p).UD = p.2.2.2.2 := fun p hp => by
    obtain ⟨hA, hC, hU, hW, -, -⟩ := hps p hp
    have h := hall p hp
    simp only [okp, Bool.and_eq_true] at h
    obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
    exact ⟨hA.run_eq h1, hC.run_eq h2, hU.run_eq h3, hW.run_eq h4⟩
  -- a coreflexive universe's keys are its values
  have hkey : ∀ {X : Obj} (W : Tab X X) (T : Den X X), rep W = T → (∀ a b, T a b → a = b) →
      ∀ x, (∃ p, W.key.row p = x) ↔ ∃ v, T v x := fun W T hW hT x => by
    rw [keyRowRep, hW]
    exact ⟨fun ⟨b, h⟩ => by obtain rfl := hT x b h; exact ⟨x, h⟩, fun ⟨v, h⟩ => by obtain rfl := hT v x h; exact ⟨v, h⟩⟩
  have hNv : ∀ p ∈ q :: ps, ∀ (X : Den V D) x d,
      AC3.Nv (G p) X x d ↔ ldivDen p.2.1 (X ≫ p.2.2.1) p.2.2.2.1 p.2.2.2.2 x d := by
    intro p hp X x d
    obtain ⟨hA, hC, hU, hW⟩ := hp' p hp
    obtain ⟨-, -, -, -, hUc, hWc⟩ := hps p hp
    simp only [AC3.Nv, AC3.Vac, ldivDen, comp_apply, hA, hC, hkey _ _ hU hUc, hkey _ _ hW hWc]
  have hmem : ∀ (l : List (ArcDen V D)) (X : Den V D) x d,
      arcsDen l X x d ↔ ∀ p ∈ l, ldivDen p.2.1 (X ≫ p.2.2.1) p.2.2.2.1 p.2.2.2.2 x d := by
    intro l X x d
    induction l with
    | nil => simp [arcsDen, Core.Rel.top]
    | cons p l ih =>
      simp only [arcsDen, List.foldr_cons, inter_apply, List.forall_mem_cons] at ih ⊢
      exact and_congr_right fun _ => ih
  have hbody : ∀ (X : Den V D) x d,
      AC3.body s.rel ((q :: ps).map G) X x d ↔ (TS ∩ arcsDen (q :: ps) X) x d := by
    intro X x d
    simp only [AC3.body, inter_apply, hmem, List.forall_mem_map, hTS]
    exact and_congr_right fun _ =>
      ⟨fun h p hp => (hNv p hp X x d).1 (h p hp), fun h p hp => (hNv p hp X x d).2 (h p hp)⟩
  have hUq := hp' q List.mem_cons_self
  obtain ⟨-, -, -, -, hUc, -⟩ := hps q List.mem_cons_self
  obtain ⟨c, hcF, hA⟩ := AC3.acFix_naive s.rel ((q :: ps).map G) U
    (fun w v h => hUc w v (hUq.2.2.1 ▸ h))
    (by
      simp only [List.forall_mem_map]
      intro p hp w x h
      rw [(hp' p hp).1] at h
      show rep (G q).UV w w
      rw [hUq.2.2.1]; exact hUA p hp w x h)
    (by
      simp only [List.forall_mem_map]
      intro p hp x d h
      rw [hTS] at h
      obtain ⟨hA', -, hU', hW'⟩ := hp' p hp
      obtain ⟨-, -, -, -, hUc', hWc'⟩ := hps p hp
      simp only [AC3.Vac, hA', hkey _ _ hU' hUc', hkey _ _ hW' hWc']
      exact hsV p hp x d h)
    hd
  -- the fixed naive iterate is the greatest fixed point
  have hΨ : Monotonic fun X => TS ∩ arcsDen (q :: ps) X := fun X Y hXY => Core.Rel.le_iff.2 fun x d h => by
    simp only [inter_apply, hmem] at h ⊢
    exact ⟨h.1, fun p hp => let ⟨h1, h2⟩ := h.2 p hp
      ⟨fun w hw => let ⟨e, hx, hc⟩ := h1 w hw; ⟨e, Core.Rel.le_iff.1 hXY w e hx, hc⟩, h2⟩⟩
  have hfix := Core.Rel.nu_fix hΨ
  have hle : ∀ k x d, Core.Rel.nu (fun X => TS ∩ arcsDen (q :: ps) X) x d →
      AC3.naive s.rel ((q :: ps).map G) k x d := by
    intro k
    induction k with
    | zero => intro x d h; rw [← hfix] at h; show rep s.rel x d; rw [hTS]; exact h.1
    | succ k ih =>
      intro x d h; rw [← hfix] at h
      exact (hbody _ x d).2 (Core.Rel.le_iff.1 (hΨ _ _ (Core.Rel.le_iff.2 ih)) x d h)
  exact Core.Rel.ext fun x d => (hA x d).trans ⟨fun h => Core.Rel.le_iff.1
    (Core.Rel.le_nu (Y := AC3.naive s.rel ((q :: ps).map G) c) (φ := fun X => TS ∩ arcsDen (q :: ps) X)
      (Core.Rel.le_iff.2 fun x d h => (hbody _ x d).1 ((hcF x d).2 h))) x d h, hle c x d⟩

end Rel.Lang
