import Rel.Lang.Laws.Eunion

/-! The Prelude-level law behind Mss `estUnion`: after a relation `Q` whose images are lists of nonempty lists,
    `E(∋) est(R) = E(est(R)) est(R)` — the `R`-extreme of a union is the `R`-extreme of the members' extremes —
    where `R` (the pair test of `est`) is reflexive, total and transitive on the elements of the lists. -/

namespace Rel.Lang
open scoped Rel.Core.Rel
open Rel.Core.Rel hiding id comp recip inter union zero le inl inr junc

variable {A B : Obj}

/-- A nonempty list over which `q` is reflexive, total and transitive has a `q`-largest member. -/
theorem exists_max {α : Type} (q : α → α → Prop) : ∀ xs : List α, xs ≠ [] → (∀ b ∈ xs, q b b) →
    (∀ b ∈ xs, ∀ c ∈ xs, q b c ∨ q c b) → (∀ b ∈ xs, ∀ c ∈ xs, ∀ d ∈ xs, q b c → q c d → q b d) →
    ∃ m ∈ xs, ∀ c ∈ xs, q m c
  | [], h, _, _, _ => (h rfl).elim
  | [x], _, hr, _, _ => ⟨x, by simp, fun c hc => by obtain rfl := List.mem_singleton.1 hc; exact hr c hc⟩
  | x :: y :: t, _, hr, ht, htr => by
    have sub : ∀ b ∈ y :: t, b ∈ x :: y :: t := fun b hb => List.mem_cons_of_mem _ hb
    obtain ⟨m, hm, hmax⟩ := exists_max q (y :: t) (by simp) (fun b hb => hr b (sub b hb))
      (fun b hb c hc => ht b (sub b hb) c (sub c hc))
      (fun b hb c hc d hd => htr b (sub b hb) c (sub c hc) d (sub d hd))
    have hx : x ∈ x :: y :: t := List.mem_cons_self ..
    rcases ht m (sub m hm) x hx with h | h
    · refine ⟨m, sub m hm, fun c hc => ?_⟩
      rcases List.mem_cons.1 hc with rfl | hc
      · exact h
      · exact hmax c hc
    · refine ⟨x, hx, fun c hc => ?_⟩
      rcases List.mem_cons.1 hc with rfl | hc
      · exact hr c hx
      · exact htr x hx m (sub m hm) c (sub c hc) h (hmax c hc)

/-- `est` read as: a member of `xs` that every other member is `TQ`-below. -/
theorem estDen_iff' (TQ : Core.Rel (Obj.El (.prod B B)) (Obj.El (.prod B B))) (xs : Obj.El (.arr B)) (b : Obj.El B) :
    estDen TQ xs b ↔ b ∈ xs ∧ ∀ c ∈ xs, c ≠ b → TQ (b, c) (b, c) :=
  (estDen_iff TQ xs b).trans (and_congr_right fun _ => ⟨fun h c hc hne => Classical.byContradiction fun hq =>
    h ⟨c, hc, hne, hq⟩, fun h ⟨c, hc, hne, hq⟩ => hq (h c hc hne)⟩)

/-- The extreme of the union `ys1` of `xss` is the extreme of the union `ys2` of the members' extremes. -/
theorem est_union_ext (TQ : Core.Rel (Obj.El (.prod B B)) (Obj.El (.prod B B))) {xss : List (List B.El)}
    {ys1 ys2 : List B.El} (hne : ∀ xs ∈ xss, xs ≠ [])
    (hr : ∀ xs ∈ xss, ∀ b ∈ xs, TQ (b, b) (b, b))
    (ht : ∀ xs ∈ xss, ∀ zs ∈ xss, ∀ b ∈ xs, ∀ c ∈ zs, TQ (b, c) (b, c) ∨ TQ (c, b) (c, b))
    (htr : ∀ xs ∈ xss, ∀ ys ∈ xss, ∀ zs ∈ xss, ∀ b ∈ xs, ∀ c ∈ ys, ∀ d ∈ zs,
      TQ (b, c) (b, c) → TQ (c, d) (c, d) → TQ (b, d) (b, d))
    (h1 : ∀ c, c ∈ ys1 ↔ ∃ x ∈ xss, c ∈ x) (h2 : ∀ c, c ∈ ys2 ↔ ∃ x ∈ xss, estDen TQ x c) (b : B.El) :
    estDen TQ ys1 b ↔ estDen TQ ys2 b := by
  rw [estDen_iff', estDen_iff']
  constructor
  · rintro ⟨hb, hmax⟩
    obtain ⟨xs, hxs, hbx⟩ := (h1 b).1 hb
    refine ⟨(h2 b).2 ⟨xs, hxs, (estDen_iff' _ _ _).2 ⟨hbx, fun c hc hcb => hmax c ((h1 c).2 ⟨xs, hxs, hc⟩) hcb⟩⟩,
      fun c hc hcb => ?_⟩
    obtain ⟨zs, hzs, hcz⟩ := (h2 c).1 hc
    exact hmax c ((h1 c).2 ⟨zs, hzs, ((estDen_iff' _ _ _).1 hcz).1⟩) hcb
  · rintro ⟨hb, hmax⟩
    obtain ⟨xs, hxs, hbx⟩ := (h2 b).1 hb
    have hbx' := ((estDen_iff' _ _ _).1 hbx).1
    refine ⟨(h1 b).2 ⟨xs, hxs, hbx'⟩, fun c hc hcb => ?_⟩
    obtain ⟨zs, hzs, hcz⟩ := (h1 c).1 hc
    obtain ⟨m, hm, hmm⟩ := exists_max (fun u v => TQ (u, v) (u, v)) zs (hne zs hzs) (hr zs hzs)
      (ht zs hzs zs hzs) (htr zs hzs zs hzs zs hzs)
    have hmz : estDen TQ zs m := (estDen_iff' _ _ _).2 ⟨hm, fun c' hc' _ => hmm c' hc'⟩
    have hbm : TQ (b, m) (b, m) := by
      by_cases e : m = b
      · exact e ▸ hr xs hxs b hbx'
      · exact hmax m ((h2 m).2 ⟨zs, hzs, hmz⟩) e
    exact htr xs hxs zs hzs zs hzs b hbx' m hm c hcz hbm (hmm c hcz)

/-- **`estUnion`**: after `Q`, whose images are lists `xss` of nonempty lists (the premises `hne`, `hr`, `ht`, `htr`: `TQ`
    reflexive, total and transitive on their elements) with a union list (`hex`), `E(∋) est(TQ)` is
    `E(est(TQ)) est(TQ)`. -/
theorem estUnion_den (Q : Core.Rel (Obj.El A) (Obj.El (.arr (.arr B))))
    (TQ : Core.Rel (Obj.El (.prod B B)) (Obj.El (.prod B B)))
    (hne : ∀ a xss, Q a xss → ∀ xs ∈ xss, xs ≠ [])
    (hr : ∀ a xss, Q a xss → ∀ xs ∈ xss, ∀ b ∈ xs, TQ (b, b) (b, b))
    (ht : ∀ a xss, Q a xss → ∀ xs ∈ xss, ∀ zs ∈ xss, ∀ b ∈ xs, ∀ c ∈ zs, TQ (b, c) (b, c) ∨ TQ (c, b) (c, b))
    (htr : ∀ a xss, Q a xss → ∀ xs ∈ xss, ∀ ys ∈ xss, ∀ zs ∈ xss, ∀ b ∈ xs, ∀ c ∈ ys, ∀ d ∈ zs,
      TQ (b, c) (b, c) → TQ (c, d) (c, d) → TQ (b, d) (b, d))
    (hex : ∀ a xss, Q a xss → ∃ ys, EDen memDen xss ys) :
    Q ≫ EDen memDen ≫ estDen TQ = Q ≫ EDen (estDen TQ) ≫ estDen TQ := by
  classical
  funext a b
  refine propext ⟨fun ⟨xss, hq, ys1, h1, he⟩ => ?_, fun ⟨xss, hq, ys2, h2, he⟩ => ?_⟩
  · obtain ⟨hp, hm⟩ := (EDen_iff _ xss ys1).1 h1
    refine ⟨xss, hq, ys1.filter fun c => decide (∃ x ∈ xss, estDen TQ x c), (EDen_iff _ _ _).2 ⟨hp.filter _, fun c => ?_⟩, ?_⟩
    · simp only [List.mem_filter, decide_eq_true_eq]
      exact ⟨fun h => h.2, fun h => ⟨(hm c).2 (by obtain ⟨x, hx, hc⟩ := h; exact ⟨x, hx,
        ((estDen_iff' _ _ _).1 hc).1⟩), h⟩⟩
    · refine (est_union_ext TQ (hne a xss hq) (hr a xss hq) (ht a xss hq) (htr a xss hq) hm (fun c => ?_) b).1 he
      simp only [List.mem_filter, decide_eq_true_eq]
      exact ⟨fun h => h.2, fun h => ⟨(hm c).2 (by obtain ⟨x, hx, hc⟩ := h; exact ⟨x, hx,
        ((estDen_iff' _ _ _).1 hc).1⟩), h⟩⟩
  · obtain ⟨ys1, h1⟩ := hex a xss hq
    obtain ⟨-, hm⟩ := (EDen_iff _ xss ys1).1 h1
    obtain ⟨-, hm2⟩ := (EDen_iff _ xss ys2).1 h2
    exact ⟨xss, hq, ys1, h1, (est_union_ext TQ (hne a xss hq) (hr a xss hq) (ht a xss hq) (htr a xss hq) hm hm2 b).2 he⟩

/-- `estUnion` as the prelude builds it: `Q ≫ E(∋) ≫ est(W)` with `est(W)` the `est` row applied to the pair test `W`,
    left-nested as the program elaborates; the premises are `estUnion_den`'s at `Q.den ρ` and `W.den ρ`. -/
theorem Tm.estUnionAt_den {Q : Tm A (.arr (.arr B))} {W : Tm (.prod B B) (.prod B B)} (ρ : Val)
    (hne : ∀ a xss, Q.den ρ a xss → ∀ xs ∈ xss, xs ≠ [])
    (hr : ∀ a xss, Q.den ρ a xss → ∀ xs ∈ xss, ∀ b ∈ xs, W.den ρ (b, b) (b, b))
    (ht : ∀ a xss, Q.den ρ a xss → ∀ xs ∈ xss, ∀ zs ∈ xss, ∀ b ∈ xs, ∀ c ∈ zs,
      W.den ρ (b, c) (b, c) ∨ W.den ρ (c, b) (c, b))
    (htr : ∀ a xss, Q.den ρ a xss → ∀ xs ∈ xss, ∀ ys ∈ xss, ∀ zs ∈ xss, ∀ b ∈ xs, ∀ c ∈ ys, ∀ d ∈ zs,
      W.den ρ (b, c) (b, c) → W.den ρ (c, d) (c, d) → W.den ρ (b, d) (b, d))
    (hex : ∀ a xss, Q.den ρ a xss → ∃ ys, EDen memDen xss ys) :
    (Tm.comp (Tm.comp Q (.lam (.comp .mem .mem))) (((Tm.prim estRow).arg W : Tm (.arr B) B))).den ρ =
      (Tm.comp (Tm.comp Q (.lam (.comp .mem (((Tm.prim estRow).arg W : Tm (.arr B) B))))) (((Tm.prim estRow).arg W : Tm (.arr B) B))).den ρ := by
  simp only [Tm.den, Tm.argDen, Prim.den_estRow, Core.Rel.comp_assoc]
  exact Rel.Lang.estUnion_den (Q.den ρ) (W.den ρ) hne hr ht htr hex

end Rel.Lang
