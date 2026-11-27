import Rel.Lang.Den
import Rel.Lang.Laws.FoldUP
import Rel.Lang.PrefixFold

/-! # Fusing a fold into `prefix`: B&dM's `prefix ≫ ⦇[e, S]⦈ = ⦇[e, ⊤e ∪ S]⦈ʳ` (the note's `mss-prefix-sum`)

`F = foldDen Te Tp` is the left fold from the seed `Te` (`Tp` on (acc, x)), `G = foldrDen Te Tf` the right fold whose step
`Tf (x, u) = ⊤Te ∪ Tp (x, u)` either restarts at the seed or adds `x` to the fold of the rest. Sums on a bounded object
drop a value whose sum leaves the object, so the fusion holds only where `Tp` associates on the values met and the seed
commutes with it (`hc`, `hassoc`): no overflow. In the book's model (`Int`) they are the laws of `+` and `0`. -/

namespace Rel.Lang

variable {B : Obj}

/-- The left fold from the seed `Te` over `x :: ys` is `Tp` of `x` and the fold over `ys`: the seed commutes with `Tp`
    (`hc`) and `Tp` associates (`ha`). -/
theorem foldDen_cons_assoc (Te : Core.Rel (Obj.El B) (Obj.El B)) (Tp : Core.Rel (Obj.El (.prod B B)) (Obj.El B))
    (hc : ∀ x w, (∃ u, (∃ a, Te a u) ∧ Tp (u, x) w) ↔ ∃ u, (∃ a, Te a u) ∧ Tp (x, u) w)
    (ha : ∀ x v y w, (∃ u, Tp (x, v) u ∧ Tp (u, y) w) ↔ ∃ v', Tp (v, y) v' ∧ Tp (x, v') w)
    (x : B.El) (ys : List B.El) (w : B.El) :
    foldDen Te Tp (x :: ys) w ↔ ∃ u, foldDen Te Tp ys u ∧ Tp (x, u) w := by
  induction h : ys.length generalizing ys w with
  | zero =>
    obtain rfl := List.length_eq_zero_iff.1 h
    exact (foldDen_snoc Te Tp [] x w).trans ((exists_congr fun u => and_congr_left' (foldDen_empty Te Tp u)).trans
      ((hc x w).trans (exists_congr fun u => and_congr_left' (foldDen_empty Te Tp u).symm)))
  | succ n ih =>
    obtain ⟨ys, y, rfl⟩ := List.eq_nil_or_concat ys |>.resolve_left (by rintro rfl; simp at h)
    rw [List.concat_eq_append]
    have ih := fun u => ih ys u (by simpa using h)
    rw [← List.cons_append, foldDen_snoc]
    refine (exists_congr fun u => and_congr_left' (ih u)).trans (Iff.trans ?_
      (exists_congr fun v' => and_congr_left' (foldDen_snoc Te Tp ys y v').symm))
    constructor
    · rintro ⟨u, ⟨v, hv, hxv⟩, huy⟩
      obtain ⟨v', h1, h2⟩ := (ha x v y w).1 ⟨u, hxv, huy⟩
      exact ⟨v', ⟨v, hv, h1⟩, h2⟩
    · rintro ⟨v', ⟨v, hv, h1⟩, h2⟩
      obtain ⟨u, h3, h4⟩ := (ha x v y w).2 ⟨v', h1, h2⟩
      exact ⟨u, ⟨v, hv, h3⟩, h4⟩

/-- **The fusion**: the folds over the prefixes of `xs` are the right fold with the restarting step `Tf`
    (`hT`: `Tf (x, u) = ⊤Te ∪ Tp (x, u)`). -/
theorem prefix_foldDen_fuse (Te : Core.Rel (Obj.El B) (Obj.El B)) (Tp Tf : Core.Rel (Obj.El (.prod B B)) (Obj.El B))
    (hc : ∀ x w, (∃ u, (∃ a, Te a u) ∧ Tp (u, x) w) ↔ ∃ u, (∃ a, Te a u) ∧ Tp (x, u) w)
    (ha : ∀ x v y w, (∃ u, Tp (x, v) u ∧ Tp (u, y) w) ↔ ∃ v', Tp (v, y) v' ∧ Tp (x, v') w)
    (hT : ∀ x u w, Tf (x, u) w ↔ (∃ a, Te a w) ∨ Tp (x, u) w) (xs : List B.El) (w : B.El) :
    (∃ ys zs, ys ++ zs = xs ∧ foldDen Te Tp ys w) ↔ foldrDen Te Tf xs w := by
  have hne : (∃ a w', Te a w') → ∀ xs : List B.El, ∃ u, foldrDen Te Tf xs u := by
    rintro ⟨a, w', h⟩ xs
    induction xs with
    | nil => exact ⟨w', (foldrDen_empty ..).2 ⟨a, h⟩⟩
    | cons x xs ih =>
      obtain ⟨u, hu⟩ := ih
      exact ⟨w', (foldrDen_cons ..).2 ⟨u, hu, (hT ..).2 (Or.inl ⟨a, h⟩)⟩⟩
  induction xs generalizing w with
  | nil =>
    rw [foldrDen_empty]
    constructor
    · rintro ⟨ys, zs, h, hy⟩
      obtain rfl := (List.append_eq_nil_iff.1 h).1
      exact (foldDen_empty ..).1 hy
    · exact fun h => ⟨[], [], rfl, (foldDen_empty ..).2 h⟩
  | cons x xs ih =>
    rw [foldrDen_cons]
    constructor
    · rintro ⟨ys, zs, h, hy⟩
      cases ys with
      | nil =>
        obtain ⟨a, ha'⟩ := (foldDen_empty ..).1 hy
        obtain ⟨u, hu⟩ := hne ⟨a, w, ha'⟩ xs
        exact ⟨u, hu, (hT ..).2 (Or.inl ⟨a, ha'⟩)⟩
      | cons y ys' =>
        obtain ⟨rfl, h'⟩ := List.cons.inj h
        obtain ⟨u, hu, hp⟩ := (foldDen_cons_assoc Te Tp hc ha y ys' w).1 hy
        exact ⟨u, (ih u).1 ⟨ys', zs, h', hu⟩, (hT ..).2 (Or.inr hp)⟩
    · rintro ⟨u, hu, hf⟩
      rcases (hT ..).1 hf with hs | hp
      · exact ⟨[], x :: xs, rfl, (foldDen_empty ..).2 hs⟩
      · obtain ⟨ys, zs, h', hy⟩ := (ih u).2 hu
        exact ⟨x :: ys, zs, by simp [h'], (foldDen_cons_assoc Te Tp hc ha x ys w).2 ⟨u, hy, hp⟩⟩

open Rel.Core.Rel hiding id comp recip inter union zero le inl inr junc

/-- `⊤e`, the one universe `1` of `⊤` composed with the seed `e`, relates every source to each value of `e`. -/
theorem Tm.topSeed_den {A B : Obj} (ρ : Val) (e : Tm .one B) (a : A.El) (u : B.El) :
    (Tm.comp (.top (Tm.uni (Gen.oneV false (USize.ofNat 1)).fst)) e : Tm A B).den ρ a u ↔ ∃ t, e.den ρ t u := by
  simp only [Tm.den, Core.Rel.comp, Core.Rel.top]
  exact ⟨fun ⟨b, _, he⟩ => ⟨b, he⟩, fun ⟨t, he⟩ => ⟨t, ⟨(), trivial, ⟨0, by simp⟩, by trivial, by trivial⟩, he⟩⟩

theorem Tm.topSeed_rel {A B : Obj} (ρ : Val) (e : Tm .one B) :
    (Tm.comp (.top (Tm.uni (Gen.oneV false (USize.ofNat 1)).fst)) e : Tm A B).den ρ = fun _ u => ∃ t, e.den ρ t u :=
  funext fun a => funext fun u => propext (Tm.topSeed_den ρ e a u)

/-- The prelude's `prefix ⦇[e, S]⦈ = ⦇[e, ⊤e ∪ S]⦈ʳ`, at the elaborated terms. The two premises are the no-overflow
    laws, `⟨⊤e,𝟙⟩S = ⟨𝟙,⊤e⟩S` (the seed commutes) and `⟨π₁S,π₂⟩S = ⟨π₁π₁,⟨π₁π₂,π₂⟩S⟩S` (`S` associates): in the book's
    `Int` they are `0 + x = x + 0` and `(x+v)+y = x+(v+y)`; on a bounded object a sum that leaves it is dropped, so they
    fail at the edge and the fusion holds only for lists whose sums stay inside. -/
theorem Tm.prefixFuse_den {B : Obj} (ρ : Val) (e : Tm .one B) (S : Tm (.prod B B) B)
    (h1 : (Tm.comp (.pair (.comp (.top (Tm.uni (Gen.oneV false (USize.ofNat 1)).fst)) e) .id) S).den ρ =
      (Tm.comp (.pair .id (.comp (.top (Tm.uni (Gen.oneV false (USize.ofNat 1)).fst)) e)) S).den ρ)
    (h2 : (Tm.comp (.pair (.comp .outl S) .outr) S).den ρ =
      (Tm.comp (.pair (.comp .outl .outl) (.comp (.pair (.comp .outl .outr) .outr) S)) S).den ρ) :
    (Tm.comp (.prim (rowOf "prefix")) (Tm.fold (Tm.ran e) S)).den ρ =
      (Tm.foldr (Tm.ran e) (.join (.comp (.top (Tm.uni (Gen.oneV false (USize.ofNat 1)).fst)) e) S)).den ρ := by
  have hTe : ∀ u, (∃ a, (Tm.ran e).den ρ a u) ↔ ∃ t, e.den ρ t u := by
    intro u
    simp only [Tm.ran_den, Core.Rel.inter, Core.Rel.id, Core.Rel.comp, Core.Rel.recip]
    constructor
    · rintro ⟨a, rfl, b, -, h⟩
      exact ⟨b, h⟩
    · rintro ⟨t, h⟩
      exact ⟨u, rfl, t, h, h⟩
  have hc : ∀ x w, (∃ u, (∃ a, (Tm.ran e).den ρ a u) ∧ S.den ρ (u, x) w) ↔
      ∃ u, (∃ a, (Tm.ran e).den ρ a u) ∧ S.den ρ (x, u) w := fun x w => by
    have e1 : ∀ T : Tm B B, (Tm.comp (.pair T .id) S).den ρ = rpair (T.den ρ) (𝟙 _) ≫ S.den ρ := fun _ => rfl
    have e2 : ∀ T : Tm B B, (Tm.comp (.pair .id T) S).den ρ = rpair (𝟙 _) (T.den ρ) ≫ S.den ρ := fun _ => rfl
    rw [e1, e2, Tm.topSeed_rel] at h1
    have := Iff.of_eq (congrFun (congrFun h1 x) w)
    simp only [Core.Rel.comp, rpair, Prod.exists, Core.Rel.id] at this
    constructor
    · rintro ⟨u, hu, hs⟩
      obtain ⟨t, ht⟩ := (hTe u).1 hu
      obtain ⟨a, b, ⟨rfl, t', ht'⟩, hs'⟩ := this.1 ⟨u, x, ⟨⟨t, ht⟩, rfl⟩, hs⟩
      exact ⟨b, (hTe b).2 ⟨t', ht'⟩, hs'⟩
    · rintro ⟨u, hu, hs⟩
      obtain ⟨t, ht⟩ := (hTe u).1 hu
      obtain ⟨a, b, ⟨⟨t', ht'⟩, rfl⟩, hs'⟩ := this.2 ⟨x, u, ⟨rfl, t, ht⟩, hs⟩
      exact ⟨a, (hTe a).2 ⟨t', ht'⟩, hs'⟩
  have ha : ∀ x v y w, (∃ u, S.den ρ (x, v) u ∧ S.den ρ (u, y) w) ↔ ∃ v', S.den ρ (v, y) v' ∧ S.den ρ (x, v') w :=
    fun x v y w => by
    have := Iff.of_eq (congrFun (congrFun h2 ((x, v), y)) w)
    simp [Tm.den, Core.Rel.comp, rpair, Core.Rel.graph, Prod.exists] at this
    constructor
    · rintro ⟨u, h1, h2⟩
      obtain ⟨a, b, ⟨rfl, a', b', ⟨rfl, rfl⟩, hs⟩, hs2⟩ := this.1 ⟨u, y, ⟨h1, rfl⟩, h2⟩
      exact ⟨b, hs, hs2⟩
    · rintro ⟨v', h1, h2⟩
      obtain ⟨a, b, ⟨hsa, rfl⟩, hs⟩ := this.2 ⟨x, v', ⟨rfl, v, y, ⟨rfl, rfl⟩, h1⟩, h2⟩
      exact ⟨a, hsa, hs⟩
  have hT : ∀ x u w, (Tm.join (Tm.comp (.top (Tm.uni (Gen.oneV false (USize.ofNat 1)).fst)) e) S).den ρ (x, u) w ↔
      (∃ a, (Tm.ran e).den ρ a w) ∨ S.den ρ (x, u) w := fun x u w => by
    change ((Tm.comp (.top (Tm.uni (Gen.oneV false (USize.ofNat 1)).fst)) e : Tm (B.prod B) B).den ρ (x, u) w ∨
      S.den ρ (x, u) w) ↔ _
    rw [Tm.topSeed_den, hTe]
  have hpre : ∀ xs b, (Tm.prim (rowOf "prefix") : Tm B.arr B.arr).den ρ xs b ↔ b <+: xs := fun xs b =>
    (Iff.of_eq (congrFun (congrFun (Tm.prefixFold_row ρ (Tm.prefixSeed B) (Tm.prefixFold_seed ρ)) xs) b)).symm.trans
      (Tm.prefixFold_iff ρ _ (Tm.prefixFold_seed ρ) xs b)
  funext xs w; apply propext
  refine Iff.trans ?_ (prefix_foldDen_fuse _ _ _ hc ha hT xs w)
  simp only [Tm.den, Core.Rel.comp]
  constructor
  · rintro ⟨b, hb, hf⟩
    obtain ⟨zs, h⟩ := (hpre xs b).1 hb
    exact ⟨b, zs, h, hf⟩
  · rintro ⟨b, zs, h, hf⟩
    exact ⟨b, (hpre xs b).2 ⟨zs, h⟩, hf⟩

/-- `prefixFuse_den` at the parameters `e = var 0`, `S = var 1` of a theorem `prefixFuse(e, S)`. -/
theorem Tm.prefixFuse_var_den {B : Obj} (ρ : Val)
    (h1 : (Tm.comp (.pair (.comp (.top (Tm.uni (Gen.oneV false (USize.ofNat 1)).fst)) (.var 0 : Tm .one B)) .id)
        (.var 1 : Tm (.prod B B) B)).den ρ =
      (Tm.comp (.pair .id (.comp (.top (Tm.uni (Gen.oneV false (USize.ofNat 1)).fst)) (.var 0 : Tm .one B)))
        (.var 1 : Tm (.prod B B) B)).den ρ)
    (h2 : (Tm.comp (A := .prod (.prod B B) B) (.pair (.comp .outl (.var 1 : Tm (.prod B B) B)) .outr) (.var 1)).den ρ =
      (Tm.comp (A := .prod (.prod B B) B) (.pair (.comp .outl .outl) (.comp (.pair (.comp .outl .outr) .outr) (.var 1)))
        (.var 1 : Tm (.prod B B) B)).den ρ) :
    (Tm.comp (.prim (rowOf "prefix")) (Tm.fold (Tm.ran (.var 0 : Tm .one B)) (.var 1 : Tm (.prod B B) B))).den ρ =
      (Tm.foldr (Tm.ran (.var 0 : Tm .one B))
        (.join (.comp (.top (Tm.uni (Gen.oneV false (USize.ofNat 1)).fst)) (.var 0 : Tm .one B)) (.var 1 : Tm (.prod B B) B))).den ρ :=
  Tm.prefixFuse_den ρ _ _ h1 h2

end Rel.Lang
