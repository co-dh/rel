import Rel.Lang.Laws.Eunion

/-! `Mss.toScan : greedy = scan` at `Tm.den`, for a generic seed `Te` and step `TO` (the program's `zero`, `oplus`).

The shapes are those the elaborator builds: juxtaposition nests to the left (`Grammar`, `go (.comp e b)`), `R÷∋` is
`Λ(R)` (`.lam`), and `Pre.compFuse` turns `Λ(S)E(T)` into `Λ(S T)` and `(𝟙÷∋)E(X)` into `Λ(X)`:
- `greedy ≜ (𝟙÷∋)E(suffix)E(g)est(≥)`, `g ≜ ⦇[zero, oplus]⦈ʳ`: `lamDen (splitDen false ≫ G) ≫ estDen TQ`.
- `scan ≜ ⦇[zero⟨𝟙,(𝟙÷∋)⟩, ⟨w,(𝟙÷∋)E(w ∪ π₂π₂∋)⟩]⦈ʳπ₂est(≥)`: `(F ≫ graph Prod.snd) ≫ estDen TQ`, `F` the fold
  `foldrDen (Tz ≫ rpair 𝟙 (lamDen 𝟙)) (rpair W (lamDen (W ∪ (graph Prod.snd ≫ graph Prod.snd) ≫ memDen)))`.

`scan_fold_iff`: `F` relates `xs` to `(g, L)` iff `G xs g` and `L` is the canonical list of `{G s | s suffix of xs}`.
It uses only that `G` is simple (`Te`'s range has at most one value, `TO` simple); `toScan_den` adds that `G` is
entire. `TO` need not be total arithmetic: the program's `oplus` is `(𝟙÷∋)E(⊤zero ∪ plus)est(≥)`, entire although
`plus` at i64 is partial. -/

namespace Rel.Lang
open scoped Rel.Core.Rel Classical
open Rel.Core.Rel hiding id comp recip inter union zero le inl inr junc

variable {E V : Obj}

/-- `Λ(𝟙)` sends `a` to `[a]`. -/
theorem lamDen_id_iff {A : Obj} (a : A.El) (ys : Obj.El (.arr A)) : lamDen (𝟙 _) a ys ↔ ys = [a] := by
  refine ⟨fun h => ?_, fun h => h ▸ (lamDen_iff _ _ _).2 ⟨by simp, fun b => by simp [Core.Rel.id, eq_comm]⟩⟩
  obtain ⟨hp, hm⟩ := (lamDen_iff _ _ _).1 h
  exact pw_eq hp (by simp) fun c => (hm c).trans (by simp [Core.Rel.id, eq_comm])

/-- `⦇e, S⦈ʳ` is simple where the range of `e` has at most one value and `S` is simple. -/
theorem foldrDen_simple (Te : Core.Rel (Obj.El V) (Obj.El V)) (TO : Core.Rel (Obj.El (.prod E V)) (Obj.El V))
    (hTe : ∀ a a' v v', Te a v → Te a' v' → v = v') (hTO : ∀ p w w', TO p w → TO p w' → w = w') :
    ∀ xs g g', foldrDen Te TO xs g → foldrDen Te TO xs g' → g = g'
  | [], g, g', h, h' => by
    obtain ⟨a, ha⟩ := (foldrDen_empty _ _ _).1 h
    obtain ⟨a', ha'⟩ := (foldrDen_empty _ _ _).1 h'
    exact hTe _ _ _ _ ha ha'
  | x :: xs, g, g', h, h' => by
    obtain ⟨u, hu, hg⟩ := (foldrDen_cons _ _ _ _ _).1 h
    obtain ⟨u', hu', hg'⟩ := (foldrDen_cons _ _ _ _ _).1 h'
    obtain rfl := foldrDen_simple Te TO hTe hTO xs u u' hu hu'
    exact hTO _ _ _ hg hg'

/-- `⦇e, S⦈ʳ` is entire where `e` has a value and `S` is entire. -/
theorem foldrDen_entire (Te : Core.Rel (Obj.El V) (Obj.El V)) (TO : Core.Rel (Obj.El (.prod E V)) (Obj.El V))
    (hTe : ∃ a v, Te a v) (hTO : ∀ p, ∃ w, TO p w) : ∀ xs, ∃ g, foldrDen Te TO xs g
  | [] => let ⟨a, v, h⟩ := hTe; ⟨v, (foldrDen_empty _ _ _).2 ⟨a, h⟩⟩
  | x :: xs => by
    obtain ⟨u, hu⟩ := foldrDen_entire Te TO hTe hTO xs
    obtain ⟨w, hw⟩ := hTO (x, u)
    exact ⟨w, (foldrDen_cons _ _ _ _ _).2 ⟨u, hu, hw⟩⟩

/-- The scan's step `⟨w, (𝟙÷∋)E(w ∪ π₂π₂∋)⟩` at `(x, (u, s))`: `w` of it, and the list of `w`'s values and `s`'s. -/
theorem scan_step_iff (TO : Core.Rel (Obj.El (.prod E V)) (Obj.El V))
    (W : Core.Rel (Obj.El (.prod E (.prod V (.arr V)))) (Obj.El V)) (hW : ∀ x u s c, W (x, (u, s)) c ↔ TO (x, u) c)
    (x : E.El) (u : V.El) (s : List V.El) (g : V.El) (L : List V.El) :
    rpair W (lamDen (W ∪ (graph Prod.snd ≫ graph Prod.snd) ≫ memDen)) (x, (u, s)) (g, L) ↔
      TO (x, u) g ∧ L.Pairwise V.lt ∧ ∀ c, c ∈ L ↔ TO (x, u) c ∨ c ∈ s := by
  simp [Core.Rel.rpair, lamDen_iff, Core.Rel.union_apply, Core.Rel.comp_apply, Core.Rel.graph, memDen, hW]

/-- **The scan's fold**: `⦇[zero⟨𝟙,(𝟙÷∋)⟩, ⟨w,(𝟙÷∋)E(w ∪ π₂π₂∋)⟩]⦈ʳ` relates `xs` to `(g, L)` iff `g` is `G xs` and `L`
    is the canonical list of `G`'s values on the suffixes of `xs`, `G = ⦇[zero, oplus]⦈ʳ`. `Tz` is `zero` read at the
    scan's carrier: only its range, the range of `Te`, counts. -/
theorem scan_fold_iff (Te : Core.Rel (Obj.El V) (Obj.El V)) (Tz : Core.Rel (Obj.El (.prod V (.arr V))) (Obj.El V))
    (TO : Core.Rel (Obj.El (.prod E V)) (Obj.El V)) (W : Core.Rel (Obj.El (.prod E (.prod V (.arr V)))) (Obj.El V))
    (hz : ∀ v, (∃ a, Tz a v) ↔ ∃ a, Te a v) (hTe : ∀ a a' v v', Te a v → Te a' v' → v = v')
    (hTO : ∀ p w w', TO p w → TO p w' → w = w') (hW : ∀ x u s c, W (x, (u, s)) c ↔ TO (x, u) c) :
    ∀ (xs : List E.El) (p : V.El × List V.El),
      foldrDen (Tz ≫ rpair (𝟙 _) (lamDen (𝟙 _)))
          (rpair W (lamDen (W ∪ (graph Prod.snd ≫ graph Prod.snd) ≫ memDen))) xs p ↔
        foldrDen Te TO xs p.1 ∧ lamDen (A := .arr E) (B := V) (splitDen false E.El ≫ foldrDen Te TO) xs p.2
  | [], (g, L) => by
    -- the one suffix of `[]` is `[]`, so the values on suffixes are the range of `e`
    have hm0 : ∀ c, (splitDen false E.El ≫ foldrDen Te TO) [] c ↔ ∃ a, Te a c := fun c => by
      rw [Core.Rel.comp_apply]
      constructor
      · rintro ⟨t, ht, hc⟩
        simp only [splitDen_iff, Bool.false_eq_true, ite_false, List.suffix_nil] at ht
        subst ht
        exact (foldrDen_empty _ _ _).1 hc
      · exact fun h => ⟨[], (splitDen_iff _ _ _).2 (by simp), (foldrDen_empty _ _ _).2 h⟩
    rw [foldrDen_empty, foldrDen_empty, lamDen_iff]
    simp only [hm0, Core.Rel.comp_apply, Core.Rel.rpair, Core.Rel.id]
    constructor
    · rintro ⟨a, _, hza, rfl, hL⟩
      obtain rfl := (lamDen_id_iff _ _).1 hL
      obtain ⟨b, hb⟩ := (hz _).1 ⟨a, hza⟩
      refine ⟨⟨b, hb⟩, by simp, fun c => ⟨fun hc => ?_, fun ⟨b', hb'⟩ => List.mem_singleton.2 (hTe _ _ _ _ hb' hb)⟩⟩
      obtain rfl := List.mem_singleton.1 hc
      exact ⟨b, hb⟩
    · rintro ⟨⟨b, hb⟩, hp, hm⟩
      obtain ⟨a, ha⟩ := (hz g).2 ⟨b, hb⟩
      refine ⟨a, g, ha, rfl, (lamDen_id_iff _ _).2
        (pw_eq hp (by simp) fun c => (hm c).trans ⟨fun ⟨b', hb'⟩ => ?_, fun hc => ?_⟩)⟩
      · exact List.mem_singleton.2 (hTe _ _ _ _ hb' hb)
      · obtain rfl := List.mem_singleton.1 hc
        exact ⟨b, hb⟩
  | x :: xs, (g, L) => by
    have ih := scan_fold_iff Te Tz TO W hz hTe hTO hW xs
    have hG := foldrDen_simple Te TO hTe hTO
    -- a value on a suffix of `x :: xs` is `G (x :: xs)` or a value on a suffix of `xs`
    have hsuf : ∀ u, foldrDen Te TO xs u → ∀ c,
        (∃ t, splitDen false E.El (x :: xs) t ∧ foldrDen Te TO t c) ↔
          TO (x, u) c ∨ ∃ t, splitDen false E.El xs t ∧ foldrDen Te TO t c := fun u hu c => by
      simp only [splitDen_iff, Bool.false_eq_true, ite_false, List.suffix_cons_iff]
      constructor
      · rintro ⟨t, rfl | ht, hc⟩
        · obtain ⟨u', hu', hc⟩ := (foldrDen_cons _ _ _ _ _).1 hc
          exact .inl (hG xs u u' hu hu' ▸ hc)
        · exact .inr ⟨t, ht, hc⟩
      · rintro (hc | ⟨t, ht, hc⟩)
        · exact ⟨_, .inl rfl, (foldrDen_cons _ _ _ _ _).2 ⟨u, hu, hc⟩⟩
        · exact ⟨t, .inr ht, hc⟩
    rw [foldrDen_cons, foldrDen_cons]
    constructor
    · rintro ⟨⟨u, s⟩, hF, hS⟩
      obtain ⟨hu, hs⟩ := (ih (u, s)).1 hF
      obtain ⟨hg, hp, hm⟩ := (scan_step_iff TO W hW x u s g L).1 hS
      obtain ⟨-, hsm⟩ := (lamDen_iff _ _ _).1 hs
      refine ⟨⟨u, hu, hg⟩, (lamDen_iff _ _ _).2 ⟨hp, fun c => (hm c).trans ?_⟩⟩
      simp only [Core.Rel.comp_apply, hsuf u hu c, hsm c]
    · rintro ⟨⟨u, hu, hg⟩, hL⟩
      obtain ⟨hp, hm⟩ := (lamDen_iff _ _ _).1 hL
      let P : V.El → Prop := fun c => ∃ t, splitDen false E.El xs t ∧ foldrDen Te TO t c
      have hPm : ∀ c, P c → c ∈ L := fun c hc => (hm c).2 ((hsuf u hu c).2 (.inr hc))
      refine ⟨(u, L.filter fun c => decide (P c)), (ih _).2 ⟨hu, (lamDen_iff _ _ _).2
        ⟨hp.filter _, fun c => ?_⟩⟩, (scan_step_iff TO W hW x u _ g L).2 ⟨hg, hp, fun c => ?_⟩⟩
      · simp only [List.mem_filter, decide_eq_true_eq, Core.Rel.comp_apply]
        exact ⟨fun h => h.2, fun h => ⟨hPm c h, h⟩⟩
      · simp only [List.mem_filter, decide_eq_true_eq]
        refine (hm c).trans ((hsuf u hu c).trans ⟨fun h => h.imp_right fun h => ⟨hPm c h, h⟩, fun h => h.imp_right
          fun h => h.2⟩)

/-- **`toScan` at `Tm.den`**: `(𝟙÷∋)E(suffix)E(g)est(≥) = ⦇[zero⟨𝟙,(𝟙÷∋)⟩, ⟨w,(𝟙÷∋)E(w ∪ π₂π₂∋)⟩]⦈ʳ π₂ est(≥)` with
    `g = ⦇[zero, oplus]⦈ʳ` (`G`) entire, `zero`'s range at most one value (`Te` at `g`'s carrier, `Tz` at the scan's),
    `oplus` (`TO`) simple, and `w` (`W`) `oplus` of the head and the carried value; `foldrDen_entire` supplies `hG`. -/
theorem toScan_den (Te : Core.Rel (Obj.El V) (Obj.El V)) (Tz : Core.Rel (Obj.El (.prod V (.arr V))) (Obj.El V))
    (TO : Core.Rel (Obj.El (.prod E V)) (Obj.El V)) (W : Core.Rel (Obj.El (.prod E (.prod V (.arr V)))) (Obj.El V))
    (TQ : Core.Rel (Obj.El (.prod V V)) (Obj.El (.prod V V)))
    (hz : ∀ v, (∃ a, Tz a v) ↔ ∃ a, Te a v) (hTe : ∀ a a' v v', Te a v → Te a' v' → v = v')
    (hTO : ∀ p w w', TO p w → TO p w' → w = w') (hG : ∀ xs, ∃ g, foldrDen Te TO xs g)
    (hW : ∀ x u s c, W (x, (u, s)) c ↔ TO (x, u) c) :
    lamDen (A := .arr E) (B := V) (splitDen false E.El ≫ foldrDen Te TO) ≫ estDen TQ =
      (foldrDen (Tz ≫ rpair (𝟙 _) (lamDen (𝟙 _)))
          (rpair W (lamDen (W ∪ (graph Prod.snd ≫ graph Prod.snd) ≫ memDen))) ≫ graph Prod.snd) ≫ estDen TQ := by
  funext xs c
  refine propext ⟨fun ⟨L, hL, he⟩ => ?_, fun ⟨l, ⟨p, hF, hl⟩, he⟩ => ?_⟩
  · obtain ⟨g, hg⟩ := hG xs
    exact ⟨L, ⟨(g, L), (scan_fold_iff Te Tz TO W hz hTe hTO hW xs _).2 ⟨hg, hL⟩, rfl⟩, he⟩
  · obtain rfl := hl
    exact ⟨p.2, ((scan_fold_iff Te Tz TO W hz hTe hTO hW xs p).1 hF).2, he⟩

#print axioms toScan_den

end Rel.Lang
