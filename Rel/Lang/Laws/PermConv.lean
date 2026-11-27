module

public import Rel.Lang.Laws.FoldUP

public section

namespace Rel.Lang
open Rel.Kernel Tab Rel.Rep
open scoped Rel.Core.Rel
open Rel.Core.Rel hiding id comp recip inter union zero le inl inr junc

/-- `perm ≜ ⦇[nil, add]⦈` with `add ≜ (cat°×𝟙)⟨⟨π₁π₁,π₂⟩snoc,π₁π₂⟩cat` (Prelude), as `Tm.den` reads it: `fold` over
    `nilDen`, `×` is `rprodMap`, a pair `rpair`, and the rows `cat`, `snoc` mean `zs = p.1 ++ p.2`, `zs = p.1 ++ [p.2]`. -/
abbrev permDen {B : Obj} : Core.Rel (Obj.El (.arr B)) (Obj.El (.arr B)) :=
  foldDen (E := B) nilDen
    (rprodMap (fun xs p => xs = p.1 ++ p.2 : Core.Rel (Obj.El (.arr B)) (Obj.El (.prod (.arr B) (.arr B)))) (𝟙 _) ≫
      rpair (rpair (graph Prod.fst ≫ graph Prod.fst) (graph Prod.snd) ≫
        (fun p ys => ys = p.1 ++ [p.2] : Core.Rel (Obj.El (.prod (.arr B) B)) (Obj.El (.arr B))))
        (graph Prod.fst ≫ graph Prod.snd) ≫
      (fun p zs => zs = p.1 ++ p.2 : Core.Rel (Obj.El (.prod (.arr B) (.arr B))) (Obj.El (.arr B))))

/-- `perm` relates an array to exactly its permutations: `add` inserts the new element at any position. -/
theorem permDen_iff {B : Obj} (xs ys : List B.El) : permDen xs ys ↔ xs.Perm ys := by
  obtain ⟨n, hn⟩ : ∃ n, xs.length = n := ⟨_, rfl⟩
  induction n generalizing xs ys with
  | zero =>
    obtain rfl := List.length_eq_zero_iff.1 hn
    refine (foldDen_empty _ _ _).trans ?_
    exact ⟨fun ⟨_, h⟩ => (show ys = [] from h) ▸ List.Perm.refl _, fun h => ⟨ys, List.nil_perm.1 h⟩⟩
  | succ n ih =>
    obtain ⟨L, x, rfl⟩ := (List.eq_nil_or_concat xs).resolve_left (by rintro rfl; simp at hn)
    rw [List.concat_eq_append] at *
    refine (foldDen_snoc _ _ _ _ _).trans ?_
    simp only [Core.Rel.comp_apply, Core.Rel.rprodMap, Core.Rel.rpair, Core.Rel.graph, Core.Rel.id]
    constructor
    · rintro ⟨u, hu, ⟨⟨l, r⟩, x'⟩, ⟨hu', hx⟩, b1, ⟨⟨b2, ⟨⟨b3, rfl, h3⟩, h4⟩, h5⟩, ⟨b4, rfl, h6⟩⟩, h7⟩
      have hy : ys = l ++ x :: r := by simp_all
      have hp : L.Perm (l ++ r) := hu' ▸ (ih L u (by simpa using hn)).1 hu
      rw [hy]
      exact ((hp.append_right [x]).trans (List.perm_append_singleton x _)).trans List.perm_middle.symm
    · intro h
      obtain ⟨s, t, rfl⟩ := List.append_of_mem (h.mem_iff.1 (List.mem_append_right _ (List.mem_singleton_self x)))
      refine ⟨s ++ t, (ih L _ (by simpa using hn)).2 ?_, ((s, t), x), ⟨rfl, rfl⟩,
        (s ++ [x], t), ⟨⟨(s, x), ⟨⟨(s, t), rfl, rfl⟩, rfl⟩, rfl⟩, ⟨(s, t), rfl, rfl⟩⟩, by simp⟩
      exact (((List.perm_append_singleton x L).symm.trans h).trans List.perm_middle).cons_inv

/-- `perm° = perm` (Prelude `permConv`): the permutations of `xs` are those `ys` that have `xs` as a permutation. -/
theorem permDen_conv {B : Obj} : (permDen (B := B))° = permDen := by
  funext ys xs
  exact propext ((permDen_iff xs ys).trans ((List.perm_comm).trans (permDen_iff ys xs).symm))

/-- The prelude's insertion step, with `cat°` elaborated as the `uncat` row. -/
abbrev Tm.permStep (B : Obj) : Tm (.prod (.arr B) B) (.arr B) :=
  .comp (.comp ((Tm.prim (B := .prod (.arr B) (.arr B)) (rowOf "uncat")).prod .id)
    (.pair (.comp (.pair (.comp .outl .outl) .outr) (.prim (B := .arr B) (rowOf "snoc"))) (.comp .outl .outr)))
    (.prim (rowOf "cat"))

/-- The converse contains the expanded fold. The forward term binds its insertion step through the local call. -/
theorem Tm.permConv_den {B : Obj} {k : Nat} {c : Lean.Name} {os : List Obj} (ρ : Val) :
    ((Tm.comp .id (Tm.fold (Tm.ran (Tm.closedNil B)) (Tm.permStep B))).conv).den ρ =
      (Tm.arg (.call [k] c none os (.fold (Tm.ran (Tm.closedNil B)) (.var k))) (Tm.permStep B)).den ρ := by
  have hseed (v : List B.El) : (∃ a, (Tm.ran (Tm.closedNil B)).den ρ a v) ↔ v = [] := by
    simp [Tm.ran_den, Tm.closedNil_den, Core.Rel.id, Core.Rel.inter, Core.Rel.comp, Core.Rel.recip, Core.Rel.graph]
  have hfold : foldDen ((Tm.ran (Tm.closedNil B)).den ρ) ((Tm.permStep B).den ρ) = permDen := by
    apply Core.Rel.ext
    intro xs ys
    unfold permDen
    rw [foldDen_iff, foldDen_iff]
    simp only [hseed, Tm.den, Tm.prod_den, Prim.den_uncat, Prim.den_snoc, Prim.den_cat,
      nilDen, Core.Rel.graph, Core.Rel.comp_assoc, exists_const]
  change (𝟙 _ ≫ foldDen ((Tm.ran (Tm.closedNil B)).den ρ) ((Tm.permStep B).den ρ))° = _
  rw [Core.Rel.id_comp]
  change (foldDen ((Tm.ran (Tm.closedNil B)).den ρ) ((Tm.permStep B).den ρ))° =
    foldDen ((Tm.ran (Tm.closedNil B)).den ρ) ((Val.empty.bind k ((Tm.permStep B).den ρ)) k _ _)
  rw [Val.bind_apply _ _ _ rfl rfl, hfold]
  exact permDen_conv

end Rel.Lang
