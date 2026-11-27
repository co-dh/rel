import Rel.Lang.Laws.Absorb
import Rel.Lang.Laws.GreedyFold
import Rel.Lang.Laws.LamTotal
import Rel.Lang.PreludeSuffix
import Rel.RepSymRank

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
theorem scan_fold_iff (Te : Core.Rel (Obj.El V) (Obj.El V)) (Zs : Core.Rel (Obj.El (.prod V (.arr V))) (Obj.El (.prod V (.arr V))))
    (TO : Core.Rel (Obj.El (.prod E V)) (Obj.El V)) (W : Core.Rel (Obj.El (.prod E (.prod V (.arr V)))) (Obj.El V))
    (hz : ∀ g L, (∃ a, Zs a (g, L)) ↔ (∃ a, Te a g) ∧ L = [g]) (hTe : ∀ a a' v v', Te a v → Te a' v' → v = v')
    (hTO : ∀ p w w', TO p w → TO p w' → w = w') (hW : ∀ x u s c, W (x, (u, s)) c ↔ TO (x, u) c) :
    ∀ (xs : List E.El) (p : V.El × List V.El),
      foldrDen Zs
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
    rw [foldrDen_empty, foldrDen_empty, lamDen_iff, hz]
    simp only [hm0]
    constructor
    · rintro ⟨hg, rfl⟩
      obtain ⟨b, hb⟩ := hg
      exact ⟨⟨b, hb⟩, by simp, fun c => ⟨fun hc => List.mem_singleton.1 hc ▸ ⟨b, hb⟩,
        fun ⟨b', hb'⟩ => List.mem_singleton.2 (hTe _ _ _ _ hb' hb)⟩⟩
    · rintro ⟨⟨b, hb⟩, hp, hm⟩
      refine ⟨⟨b, hb⟩, pw_eq hp (by simp) fun c => (hm c).trans ⟨fun ⟨b', hb'⟩ => ?_, fun hc => ?_⟩⟩
      · exact List.mem_singleton.2 (hTe _ _ _ _ hb' hb)
      · obtain rfl := List.mem_singleton.1 hc
        exact ⟨b, hb⟩
  | x :: xs, (g, L) => by
    have ih := scan_fold_iff Te Zs TO W hz hTe hTO hW xs
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

/-- `⦇e, S⦈ʳ` is entire on the lists of a carrier `P` where `e` has a value in `Q` and `S` is entire on `P × Q` into `Q`:
    a step that is partial outside the carrier still has a value on every list in `P`. -/
theorem foldrDen_entire_on (P : E.El → Prop) (Q : V.El → Prop) (Te : Core.Rel (Obj.El V) (Obj.El V))
    (TO : Core.Rel (Obj.El (.prod E V)) (Obj.El V)) (hTe : ∃ a v, Te a v ∧ Q v)
    (hTO : ∀ x u, P x → Q u → ∃ w, TO (x, u) w ∧ Q w) :
    ∀ xs : List E.El, (∀ x ∈ xs, P x) → ∃ g, foldrDen Te TO xs g ∧ Q g
  | [], _ => let ⟨a, v, h, hq⟩ := hTe; ⟨v, (foldrDen_empty _ _ _).2 ⟨a, h⟩, hq⟩
  | x :: xs, hP => by
    obtain ⟨u, hu, hqu⟩ := foldrDen_entire_on P Q Te TO hTe hTO xs fun y hy => hP y (List.mem_cons_of_mem _ hy)
    obtain ⟨w, hw, hqw⟩ := hTO x u (hP x (List.mem_cons_self ..)) hqu
    exact ⟨w, (foldrDen_cons _ _ _ _ _).2 ⟨u, hu, hw⟩, hqw⟩

/-- **`toScan` at `Tm.den`**, on the lists a coreflexive guard `Gd` (`safe`) admits:
    `Gd (𝟙÷∋)E(suffix)E(g)est(≥) = Gd ⦇[zero⟨𝟙,(𝟙÷∋)⟩, ⟨w,(𝟙÷∋)E(w ∪ π₂π₂∋)⟩]⦈ʳ π₂ est(≥)` with `g = ⦇[zero, oplus]⦈ʳ` (`G`)
    having a value on every guarded list (`hG`: `oplus` is partial outside `N × N`, so on `[100]` the left side is `{0}`
    and the right side is empty), `zero`'s range at most one value (`Te`), the scan's seed `Zs` the `ran` of
    `zero⟨𝟙,Λ𝟙⟩` (`hz`), `oplus` (`TO`) simple, and `w` (`W`) `oplus` of the head and the carried value. -/
theorem toScan_den (Te : Core.Rel (Obj.El V) (Obj.El V)) (Zs : Core.Rel (Obj.El (.prod V (.arr V))) (Obj.El (.prod V (.arr V))))
    (TO : Core.Rel (Obj.El (.prod E V)) (Obj.El V)) (W : Core.Rel (Obj.El (.prod E (.prod V (.arr V)))) (Obj.El V))
    (TQ : Core.Rel (Obj.El (.prod V V)) (Obj.El (.prod V V))) (Gd : Core.Rel (Obj.El (.arr E)) (Obj.El (.arr E)))
    (hz : ∀ g L, (∃ a, Zs a (g, L)) ↔ (∃ a, Te a g) ∧ L = [g]) (hTe : ∀ a a' v v', Te a v → Te a' v' → v = v')
    (hTO : ∀ p w w', TO p w → TO p w' → w = w') (hGd : ∀ a b, Gd a b → a = b)
    (hG : ∀ xs, Gd xs xs → ∃ g, foldrDen Te TO xs g) (hW : ∀ x u s c, W (x, (u, s)) c ↔ TO (x, u) c) :
    Gd ≫ (lamDen (A := .arr E) (B := V) (splitDen false E.El ≫ foldrDen Te TO) ≫ estDen TQ) =
      Gd ≫ ((foldrDen Zs (rpair W (lamDen (W ∪ (graph Prod.snd ≫ graph Prod.snd) ≫ memDen))) ≫ graph Prod.snd) ≫
        estDen TQ) := by
  funext xs c
  refine propext ⟨fun ⟨ys, hy, L, hL, he⟩ => ?_, fun ⟨ys, hy, l, ⟨p, hF, hl⟩, he⟩ => ?_⟩
  · obtain rfl := hGd _ _ hy
    obtain ⟨g, hg⟩ := hG xs hy
    exact ⟨xs, hy, L, ⟨(g, L), (scan_fold_iff Te Zs TO W hz hTe hTO hW xs _).2 ⟨hg, hL⟩, rfl⟩, he⟩
  · obtain rfl := hGd _ _ hy
    obtain rfl := hl
    exact ⟨xs, hy, p.2, ((scan_fold_iff Te Zs TO W hz hTe hTO hW xs p).1 hF).2, he⟩

/-- `Λ(X) est(R)` is simple where `R` is antisymmetric on a carrier `U` holding the values of `X`: two extremes of one
    set are each `R`-above the other. -/
theorem lamEst_simple {A : Obj} (TQ : Core.Rel (Obj.El (.prod V V)) (Obj.El (.prod V V))) (X : Core.Rel (Obj.El A) (Obj.El V))
    (U : V.El → Prop) (has : ∀ b c, U b → U c → qtDen TQ b c → qtDen TQ c b → b = c) (hX : ∀ a c, X a c → U c) :
    ∀ a w w', (lamDen X ≫ estDen TQ) a w → (lamDen X ≫ estDen TQ) a w' → w = w' := by
  rintro a w w' ⟨ys, h1, h2⟩ ⟨ys', h1', h2'⟩
  obtain rfl := lamDen_unique X h1 h1'
  obtain ⟨hw, hn⟩ := (estDen_lam TQ h1 w).1 h2
  obtain ⟨hw', hn'⟩ := (estDen_lam TQ h1 w').1 h2'
  refine Classical.byContradiction fun hne => ?_
  exact hne (has w w' (hX _ _ hw) (hX _ _ hw') (hn w' hw' (Ne.symm hne)) (hn' w hw hne))

/-- `Λ(X) est(R)` is entire where `R` is a total preorder on a carrier `U` holding the values of `X`, every `X a` is an
    array (`hS`) and has a value (`hne`). -/
theorem lamEst_entire {A : Obj} (TQ : Core.Rel (Obj.El (.prod V V)) (Obj.El (.prod V V))) (X : Core.Rel (Obj.El A) (Obj.El V))
    (U : V.El → Prop) (ht : ∀ b c, U b → U c → qtDen TQ b c ∨ qtDen TQ c b)
    (htr : ∀ b c d, U b → U c → U d → qtDen TQ b c → qtDen TQ c d → qtDen TQ b d) (hX : ∀ a c, X a c → U c)
    (hS : ∀ a, ∃ ys, lamDen X a ys) (hne : ∀ a, ∃ c, X a c) : ∀ a, ∃ w, (lamDen X ≫ estDen TQ) a w := by
  intro a
  obtain ⟨ys, hy⟩ := hS a
  obtain ⟨-, hm⟩ := (lamDen_iff _ _ _).1 hy
  obtain ⟨c0, hc0⟩ := hne a
  obtain ⟨u, hu, hmax⟩ := exists_ext U ht htr ys (fun c hc => hX a c ((hm c).1 hc))
    (List.ne_nil_of_mem ((hm c0).2 hc0))
  exact ⟨u, ys, hy, (estDen_lam TQ hy u).2 ⟨(hm u).1 hu, fun c hc hne => hmax c ((hm c).2 hc) hne⟩⟩

/-- The row `suffix` means `<:+`. -/
theorem Prim.den_suffix {B : Obj} : Prim.den (rowOf "suffix") (.arr B) (.arr B) [] = splitDen false B.El := by
  have hs : (rowOf "suffix").sig = ([], .list (.var {} "B"), .list (.var {} "B")) := rfl
  have ho : (rowOf "suffix").objs (.arr B) (.arr B) [] = some [B] := by
    simp [Prim.objs, Prim.vars, hs, Option.orElse, OExp.unify, OExp.vars, List.eraseDups, List.eraseDupsBy,
      List.eraseDupsBy.loop, List.lookup]
  have hf : rowDens.find? (·.1.sym == (rowOf "suffix").sym) =
      some ⟨RowCode.suffix, fun σ _ => splitDen false (σ₁ σ).El⟩ := rfl
  unfold Prim.den; simp only [List.map_nil]
  rw [hf, ho]; dsimp only; rw [dif_pos ⟨rfl, rfl⟩]; rfl


/-- `Λ(suffix)` has an array at every list of a flat object: the suffixes are the `drop`s, told apart by key. -/
theorem lamSuffix_total {B : Obj} (hB : B.flat = true) (xs : List B.El) :
    ∃ ys, lamDen (A := .arr B) (B := .arr B) (splitDen false B.El) xs ys :=
  lamDen_total (A := .arr B) (B := .arr B) _ xs ((List.range (xs.length + 1)).map xs.drop) (fun b hb => by
      have hs : b <:+ xs := by simpa [splitDen_iff] using hb
      have h := List.suffix_iff_eq_drop.1 hs
      exact List.mem_map.2 ⟨_, List.mem_range.2 (by omega), h.symm⟩)
    fun b c _ _ e => arr_key_inj B b c (fun x _ y _ e' => Obj.key_inj_of_flat B hB x y e') e

/-- `Λ(S) ∋ T` is `S T` where every `S a` is an array: the prelude's `Λ(Λ(S) E(∋ T))` is `Λ(S T)`. -/
theorem lamDen_lam_mem {A B C : Obj} (S : Core.Rel (Obj.El A) (Obj.El B)) (F : Core.Rel (Obj.El B) (Obj.El C))
    (hS : ∀ a, ∃ ys, lamDen S a ys) : lamDen (lamDen S ≫ (memDen ≫ F)) = lamDen (S ≫ F) := by
  have : lamDen S ≫ (memDen ≫ F) = S ≫ F := by
    funext a c
    refine propext ⟨fun ⟨ys, hy, y, hm, hf⟩ => ⟨y, ((lamDen_iff _ _ _).1 hy).2 y |>.1 hm, hf⟩,
      fun ⟨y, hy, hf⟩ => ?_⟩
    obtain ⟨ys, hys⟩ := hS a
    exact ⟨ys, hys, y, ((lamDen_iff _ _ _).1 hys).2 y |>.2 hy, hf⟩
  rw [this]

/-- **`toScan` at the terms the elaborator builds**: on the lists the guard `G` (`safe`) admits,
    `G Λ(Λ(suffix) E(∋ ⦇[ran z, S]⦈ʳ)) est(R) = G ⦇[ran(z⟨𝟙,Λ𝟙⟩), ⟨w, Λ(w ∪ π₂π₂∋)⟩]⦈ʳ π₂ est(R)` with `w = ⟨π₁𝟙,π₂π₁⟩S`
    (`S`, the step `OP`, is not looked into). `G` is coreflexive (`hGd`) and `⦇[ran z, S]⦈ʳ` has a value on each guarded
    list (`hG`: `S` is partial outside `N × N`, so on `[100]` the left side is `{0}` and the right side is empty);
    the seed `z` has at most one value (`hz`) and `S` is simple (`hTO`). -/
theorem Tm.toScan_den {N : Obj} (hN : N.flat = true := by decide) {G : Tm (.arr N) (.arr N)} {z : Tm .one N}
    {OP : Tm (.prod N N) N} {R : Tm N N} (ρ : Val) (hGd : ∀ a b, G.den ρ a b → a = b)
    (hG : ∀ xs, G.den ρ xs xs → ∃ g, (Tm.foldr (Tm.ran z) OP).den ρ xs g)
    (hz : ∀ x y, (∃ m, z.den ρ m x) → (∃ m, z.den ρ m y) → x = y)
    (hTO : ∀ p w w', OP.den ρ p w → OP.den ρ p w' → w = w') :
    (Tm.comp (Tm.comp G (Tm.lam (Tm.comp (Tm.lam (Tm.prim (rowOf "suffix"))) (Tm.comp Tm.mem
        (Tm.foldr (Tm.ran z) OP))))) (Tm.est (Tm.dom (.meet .outr (.comp .outl R))))).den ρ =
      (Tm.comp (Tm.comp G (Tm.comp (Tm.foldr (Tm.ran (Tm.comp z (.pair .id (.lam .id))))
        (.pair (.comp (.pair (.comp .outl .id) (.comp .outr .outl)) OP)
          (.lam (.join (.comp (.pair (.comp .outl .id) (.comp .outr .outl)) OP) (.comp (.comp .outr .outr) .mem)))))
        .outr)) (Tm.est (Tm.dom (.meet .outr (.comp .outl R))))).den ρ := by
  have hZ : ∀ g L, (∃ a, (Tm.ran (Tm.comp z (.pair .id (.lam .id)))).den ρ a (g, L)) ↔
      (∃ a, (Tm.ran z).den ρ a g) ∧ L = [g] := fun g L => by
    refine ⟨fun ⟨a, ha⟩ => ?_, fun ⟨⟨a, ha⟩, hL⟩ => ?_⟩
    · obtain ⟨rfl, m, y, hy, hg, hL⟩ := (Tm.ran_den' ρ _ a (g, L)).1 ha
      obtain rfl : y = g := hg
      exact ⟨⟨_, (Tm.ran_den' ρ z _ _).2 ⟨rfl, m, hy⟩⟩, (lamDen_id_iff y L).1 hL⟩
    · obtain ⟨rfl, m, hy⟩ := (Tm.ran_den' ρ z a g).1 ha
      subst hL
      exact ⟨(a, [a]), (Tm.ran_den' ρ _ _ _).2 ⟨rfl, m, a, hy, rfl, (lamDen_id_iff a [a]).2 rfl⟩⟩
  have hW : ∀ (x u : N.El) (s : N.arr.El) c, (Tm.comp (A := .prod N (.prod N N.arr)) (B := .prod N N)
      (.pair (.comp .outl .id) (.comp .outr .outl)) OP).den ρ (x, (u, s)) c ↔ OP.den ρ (x, u) c := fun x u s c => by
    simp [Tm.den, Core.Rel.comp, rpair, Core.Rel.graph, Core.Rel.id]
    constructor
    · rintro ⟨a, b, ⟨rfl, rfl⟩, h⟩; exact h
    · intro h; exact ⟨x, u, ⟨rfl, rfl⟩, h⟩
  have key := Rel.Lang.toScan_den (E := N) (V := N) ((Tm.ran z).den ρ) ((Tm.ran (Tm.comp z (.pair .id (.lam .id)))).den ρ)
    (OP.den ρ) ((Tm.comp (.pair (.comp .outl .id) (.comp .outr .outl)) OP).den ρ)
    ((Tm.dom (.meet .outr (.comp .outl R))).den ρ) (G.den ρ) hZ
    (fun a a' v v' h h' => by
      obtain ⟨rfl, m, hm⟩ := (Tm.ran_den' ρ z a v).1 h
      obtain ⟨rfl, m', hm'⟩ := (Tm.ran_den' ρ z a' v').1 h'
      exact hz _ _ ⟨m, hm⟩ ⟨m', hm'⟩) hTO hGd hG hW
  have hS := lamDen_lam_mem (A := .arr N) (B := .arr N) (C := N) (splitDen false N.El) (foldrDen ((Tm.ran z).den ρ) (OP.den ρ)) (lamSuffix_total hN)
  simp only [Tm.den, Tm.est_den, Prim.den_suffix, Core.Rel.comp_assoc]
  rw [hS]
  simp only [Core.Rel.comp_assoc] at key
  exact key

#print axioms Tm.toScan_den

end Rel.Lang
