import Rel.Programs.Prelude
import Rel.Lang.PreludeMerge
import Rel.Lang.PreludeSuffix

/-! # Laws of freyd §9.2 `AOP/A9_2_Edit.lean`, on the concrete core

An edit operation is `α+(α+α)`: `inl` copy, `inr ∘ inl` delete, `inr ∘ inr` insert. `edit` and `dropT` are right
folds whose steps are functions (`editStep`, `dropStep`), so their denotations are `List.foldr` (`foldrDen_foldr`). -/

namespace Rel.Lang
open scoped Rel.Core.Rel

/-- `step (cpy a,(xs,ys)) = (a::xs,a::ys)`, `step (del a,(xs,ys)) = (a::xs,ys)`, `step (ins a,(xs,ys)) = (xs,a::ys)`. -/
def editStep {A : Type} : A ⊕ (A ⊕ A) → List A × List A → List A × List A
  | .inl c, (xs, ys) => (c :: xs, c :: ys)
  | .inr (.inl c), (xs, ys) => (c :: xs, ys)
  | .inr (.inr c), (xs, ys) => (xs, c :: ys)

/-- The pair step of `dropT`: the first component rebuilds the sequence, the second drops the first operation that
    writes to the target (`ins` goes, `cpy` becomes `del`). -/
def dropStep {A : Type} : A ⊕ (A ⊕ A) → List (A ⊕ (A ⊕ A)) × List (A ⊕ (A ⊕ A)) → List (A ⊕ (A ⊕ A)) × List (A ⊕ (A ⊕ A))
  | .inl c, (es, _) => (.inl c :: es, .inr (.inl c) :: es)
  | .inr (.inl c), (es, ds) => (.inr (.inl c) :: es, .inr (.inl c) :: ds)
  | .inr (.inr c), (es, _) => (.inr (.inr c) :: es, es)

theorem dropFold_fst {A : Type} : ∀ es : List (A ⊕ (A ⊕ A)), (es.foldr dropStep ([], [])).1 = es
  | [] => rfl
  | o :: es => by
    have ih := dropFold_fst es
    simp only [List.foldr_cons]
    generalize es.foldr dropStep ([], []) = d at ih
    obtain ⟨d1, d2⟩ := d
    obtain rfl : d1 = es := ih
    rcases o with c | c | c <;> rfl

/-- freyd `editFn_dropTgt`: editing the dropped sequence leaves the source and drops the head of the target. -/
theorem editDrop_core {A : Type} : ∀ es : List (A ⊕ (A ⊕ A)),
    (es.foldr dropStep ([], [])).2.foldr editStep ([], [])
      = ((es.foldr editStep ([], [])).1, (es.foldr editStep ([], [])).2.tail)
  | [] => rfl
  | o :: es => by
    have ih := editDrop_core es
    have h1 := dropFold_fst es
    simp only [List.foldr_cons]
    generalize es.foldr dropStep ([], []) = d at ih h1
    obtain ⟨d1, d2⟩ := d
    obtain rfl : es = d1 := h1.symm
    generalize hE : es.foldr editStep ([], []) = e at ih ⊢
    obtain ⟨e1, e2⟩ := e
    rcases o with c | c | c <;> simp only [dropStep, editStep, List.foldr_cons, ih, hE, List.tail_cons]

/-! ## The program's terms -/

/-- A right fold seeded by `ran(R)` whose step is the function `f` and every value of `R` is `v₀` is `List.foldr f v₀`
    where `R` reaches `v₀`. -/
theorem Tm.foldrRan_fun {E V A : Obj} (ρ : Val) (R : Tm A V) (S : Tm (.prod E V) V) {f : E.El → V.El → V.El}
    {v₀ : V.El} (hR : ∀ m v, R.den ρ m v → v = v₀) (hS : ∀ x a w, S.den ρ (x, a) w ↔ w = f x a)
    (xs : List E.El) (w : V.El) :
    (Tm.foldr (Tm.ran R) S).den ρ xs w ↔ (∃ m, R.den ρ m v₀) ∧ w = xs.foldr f v₀ := by
  have hF := foldrDen_foldr (I := fun _ => True) (fun x a _ w => hS x a w) (fun _ _ _ => trivial)
  have hr : ∀ a v, (Tm.ran R).den ρ a v ↔ a = v ∧ ∃ m, R.den ρ m a := fun a v => by
    rw [Tm.ran_den]; simp only [Core.Rel.inter, Core.Rel.id, Core.Rel.comp, Core.Rel.recip]
    exact ⟨fun ⟨h, m, hm, _⟩ => ⟨h, m, hm⟩, fun ⟨h, m, hm⟩ => ⟨h, m, hm, h ▸ hm⟩⟩
  change foldrDen ((Tm.ran R).den ρ) (S.den ρ) xs w ↔ _
  rw [foldrDen_start]
  constructor
  · rintro ⟨v, ⟨a, ha⟩, h⟩
    obtain ⟨rfl, m, hm⟩ := (hr a v).1 ha
    obtain rfl := hR m a hm
    exact ⟨⟨m, hm⟩, (hF xs a trivial w).1 h⟩
  · rintro ⟨⟨m, hm⟩, hw⟩
    exact ⟨v₀, ⟨v₀, (hr v₀ v₀).2 ⟨rfl, m, hm⟩⟩, (hF xs v₀ trivial w).2 hw⟩

/-- The seed `P ⟨nil,nil⟩` of a pair fold reaches only `([],[])`, wherever `P` is defined. -/
theorem Tm.nilPairSeed_iff {X M C D : Obj} (ρ : Val) (P : Tm X M) (m : X.El) (v : Obj.El (.prod (.arr C) (.arr D))) :
    (P.comp (Tm.nil.pair Tm.nil)).den ρ m v ↔ v = ([], []) ∧ ∃ u, P.den ρ m u := by
  obtain ⟨v1, v2⟩ := v
  simp only [Tm.den, Tm.nil, Prim.den_nilRow, Core.Rel.comp, Core.Rel.rpair, Core.Rel.graph, Prod.mk.injEq]
  exact ⟨fun ⟨u, hu, h1, h2⟩ => ⟨⟨h1, h2⟩, u, hu⟩, fun ⟨⟨h1, h2⟩, u, hu⟩ => ⟨u, hu, h1, h2⟩⟩

/-- `step = ⟨⟨π₁cpy°,π₂π₁⟩cons,⟨π₁cpy°,π₂π₂⟩cons⟩ ∪ ⟨⟨π₁del°,π₂π₁⟩cons,π₂π₂⟩ ∪ ⟨π₂π₁,⟨π₁ins°,π₂π₂⟩cons⟩` as the
    program elaborates it (`cpy = inl`, `del = inl inr`, `ins = inr inr`). -/
def Tm.editStepT (B : Obj) : Tm (.prod (.sum B (.sum B B)) (.prod (.arr B) (.arr B))) (.prod (.arr B) (.arr B)) :=
  .join (.join
    (.pair (.comp (.pair (.comp .outl (.conv .inl)) (.comp .outr .outl)) (.prim (rowOf "cons")))
      (.comp (.pair (.comp .outl (.conv .inl)) (.comp .outr .outr)) (.prim (rowOf "cons"))))
    (.pair (.comp (.pair (.comp .outl (.comp (.conv .inr) (.conv .inl))) (.comp .outr .outl)) (.prim (rowOf "cons")))
      (.comp .outr .outr)))
    (.pair (.comp .outr .outl)
      (.comp (.pair (.comp .outl (.comp (.conv .inr) (.conv .inr))) (.comp .outr .outr)) (.prim (rowOf "cons"))))

/-- `dropStep` of the program: `π₁ (cpy°cpy)`, `π₁ (del°del)`, `π₁ (ins°ins)` test the operation, `π₁cpy°del` turns a
    copy into a delete. -/
def Tm.dropStepT (B : Obj) :
    Tm (.prod (.sum B (.sum B B)) (.prod (.arr (.sum B (.sum B B))) (.arr (.sum B (.sum B B)))))
      (.prod (.arr (.sum B (.sum B B))) (.arr (.sum B (.sum B B)))) :=
  .join (.join
    (.pair (.comp (.pair (.comp .outl (.comp (.conv .inl) .inl)) (.comp .outr .outl)) (.prim (rowOf "cons") : Tm (.prod (.sum B (.sum B B)) (.arr (.sum B (.sum B B)))) (.arr (.sum B (.sum B B)))))
      (.comp (.pair (.comp (.comp .outl (.conv .inl)) (.comp .inl .inr)) (.comp .outr .outl)) (.prim (rowOf "cons") : Tm (.prod (.sum B (.sum B B)) (.arr (.sum B (.sum B B)))) (.arr (.sum B (.sum B B))))))
    (.pair (.comp (.pair (.comp .outl (.comp (.comp (.conv .inr) (.conv .inl)) (.comp .inl .inr))) (.comp .outr .outl))
        (.prim (rowOf "cons") : Tm (.prod (.sum B (.sum B B)) (.arr (.sum B (.sum B B)))) (.arr (.sum B (.sum B B)))))
      (.comp (.pair (.comp .outl (.comp (.comp (.conv .inr) (.conv .inl)) (.comp .inl .inr))) (.comp .outr .outr))
        (.prim (rowOf "cons") : Tm (.prod (.sum B (.sum B B)) (.arr (.sum B (.sum B B)))) (.arr (.sum B (.sum B B)))))))
    (.pair (.comp (.pair (.comp .outl (.comp (.comp (.conv .inr) (.conv .inr)) (.comp .inr .inr))) (.comp .outr .outl))
        (.prim (rowOf "cons") : Tm (.prod (.sum B (.sum B B)) (.arr (.sum B (.sum B B)))) (.arr (.sum B (.sum B B)))))
      (.comp .outr .outl))

theorem Tm.editStepT_iff (ρ : Val) {B : Obj} (o : Obj.El (.sum B (.sum B B))) (p : List B.El × List B.El)
    (w : List B.El × List B.El) : (Tm.editStepT B).den ρ (o, p) w ↔ w = editStep o p := by
  obtain ⟨xs, ys⟩ := p; obtain ⟨w1, w2⟩ := w
  rcases o with c | c | c <;>
    simp [Tm.editStepT, Tm.den, Prim.den_cons, editStep, Core.Rel.union, Core.Rel.comp, Core.Rel.rpair,
      Core.Rel.recip, Core.Rel.inl, Core.Rel.inr, Core.Rel.graph, and_assoc, exists_eq_left, exists_eq_left', eq_comm]

theorem Tm.dropStepT_iff (ρ : Val) {B : Obj} (o : Obj.El (.sum B (.sum B B)))
    (p : List (Obj.El (.sum B (.sum B B))) × List (Obj.El (.sum B (.sum B B))))
    (w : List (Obj.El (.sum B (.sum B B))) × List (Obj.El (.sum B (.sum B B)))) :
    (Tm.dropStepT B).den ρ (o, p) w ↔ w = dropStep o p := by
  obtain ⟨xs, ys⟩ := p; obtain ⟨w1, w2⟩ := w
  rcases o with c | c | c <;>
    simp [Tm.dropStepT, Tm.den, Prim.den_cons, dropStep, Core.Rel.union, Core.Rel.comp, Core.Rel.rpair,
      Core.Rel.recip, Core.Rel.inl, Core.Rel.inr, Core.Rel.graph, and_assoc, exists_eq_left, exists_eq_left', eq_comm]

/-- **edit-tail, the drop**: `edit (𝟙×tail) ⊑ dropTgt edit` (freyd `edit_dropTgt` is `=`; the prelude `tail` is
    partial at `[]`, so only `⊑` holds). `P` is the seed's prefix, `t'` the body of the `tail` call. -/
theorem Tm.editDropTgt_den {B X M : Obj} {P : Tm X M} {os : List Obj} {t' : Tm (.arr B) (.arr B)}
    (ht : Rel.Programs.prelude.tail.body.instObj [.general] [B] = .ok t' := by rfl) (ρ : Val) :
    Tm.den ρ ((Tm.foldr (Tm.ran (P.comp (Tm.nil.pair Tm.nil))) (Tm.editStepT B)).comp
        ((Tm.outl.comp Tm.id).pair
          (Tm.outr.comp (Tm.call [] `Rel.Programs.prelude.tail (some `Rel.Programs.prelude.tail.conv) os t')))) ⊑
      Tm.den ρ (((Tm.foldr (Tm.ran (P.comp (Tm.nil.pair Tm.nil))) (Tm.dropStepT B)).comp Tm.outr).comp
        (Tm.foldr (Tm.ran (P.comp (Tm.nil.pair Tm.nil))) (Tm.editStepT B))) := by
  have hT : ∀ xs ys, t'.den (Val.args [] []) xs ys ↔ ∃ a, xs = a :: ys := fun xs ys =>
    Tm.tailDef_den [.general] [B] (Val.args [] []) ht xs ys
  have hE := Tm.foldrRan_fun ρ _ (Tm.editStepT B) (fun m v h => ((Tm.nilPairSeed_iff ρ P m v).1 h).1)
    (Tm.editStepT_iff ρ)
  have hD := Tm.foldrRan_fun ρ _ (Tm.dropStepT B) (fun m v h => ((Tm.nilPairSeed_iff ρ P m v).1 h).1)
    (Tm.dropStepT_iff ρ)
  refine Core.Rel.le_iff.2 fun es ⟨w1, w2⟩ h => ?_
  obtain ⟨⟨x, y⟩, he, hw⟩ := h
  obtain ⟨⟨m, hm⟩, hxy⟩ := (hE es (x, y)).1 he
  obtain ⟨u, hu⟩ := ((Tm.nilPairSeed_iff ρ P m _).1 hm).2
  simp only [Tm.den, Core.Rel.rpair, Core.Rel.comp, Core.Rel.graph, Core.Rel.id, hT] at hw
  obtain ⟨⟨_, rfl, rfl⟩, _, rfl, a, rfl⟩ := hw
  refine ⟨(es.foldr dropStep ([], [])).2, ⟨_, (hD es _).2 ⟨⟨m, (Tm.nilPairSeed_iff ρ P m _).2 ⟨rfl, u, hu⟩⟩, rfl⟩, rfl⟩,
    (hE _ _).2 ⟨⟨m, hm⟩, ?_⟩⟩
  rw [editDrop_core, ← hxy]; rfl

/-- **edit-tail** at a generic `Q` for `R°` (stronger form of freyd `edit_tail_snd`): `dropTgt ⊑ Q` gives
    `edit (𝟙×tail) ⊑ Q edit` (`Tm.editDropTgt_den`). -/
theorem Tm.editTailSnd_den {B X M : Obj} {P : Tm X M} {os : List Obj} {t' : Tm (.arr B) (.arr B)}
    {Q : Tm (.arr (.sum B (.sum B B))) (.arr (.sum B (.sum B B)))}
    (ht : Rel.Programs.prelude.tail.body.instObj [.general] [B] = .ok t' := by rfl) (ρ : Val)
    (hQ : Tm.den ρ ((Tm.foldr (Tm.ran (P.comp (Tm.nil.pair Tm.nil))) (Tm.dropStepT B)).comp Tm.outr) ⊑ Tm.den ρ Q) :
    Tm.den ρ ((Tm.foldr (Tm.ran (P.comp (Tm.nil.pair Tm.nil))) (Tm.editStepT B)).comp
        ((Tm.outl.comp Tm.id).pair
          (Tm.outr.comp (Tm.call [] `Rel.Programs.prelude.tail (some `Rel.Programs.prelude.tail.conv) os t')))) ⊑
      Tm.den ρ (Q.comp (Tm.foldr (Tm.ran (P.comp (Tm.nil.pair Tm.nil))) (Tm.editStepT B))) := by
  refine Core.Rel.le_iff.2 fun es w h => ?_
  obtain ⟨fs, hd, he⟩ := Core.Rel.le_iff.1 (Tm.editDropTgt_den ht ρ) es w h
  exact ⟨fs, Core.Rel.le_iff.1 hQ es fs hd, he⟩

theorem dropFold_cons {A : Type} (o : A ⊕ (A ⊕ A)) (es : List (A ⊕ (A ⊕ A))) :
    (o :: es).foldr dropStep ([], []) = dropStep o (es, (es.foldr dropStep ([], [])).2) := by
  have h := dropFold_fst es
  simp only [List.foldr_cons]
  generalize es.foldr dropStep ([], []) = d at h ⊢
  obtain ⟨d1, d2⟩ := d
  obtain rfl : es = d1 := h.symm
  rfl

/-- **dropTgt never lengthens**, at a generic `Q` for `R°` (stronger form of freyd `dropTgt_le`): the premises are
    `drop₂`'s arms — `[] Q []`, `Q` kept under `cons`, a copy `Q`-above its delete, an insert `Q`-above its tail. -/
theorem Tm.dropTgtLe_den {B X M : Obj} {P : Tm X M} {Q : Tm (.arr (.sum B (.sum B B))) (.arr (.sum B (.sum B B)))}
    (ρ : Val)
    (h0 : Tm.den ρ ((P.comp Tm.nil).conv.comp Tm.nil) ⊑ Tm.den ρ Q)
    (h1 : Tm.den ρ ((Tm.outl.pair (Tm.outr.comp Q)).comp
        (.prim (rowOf "cons") : Tm (.prod (.sum B (.sum B B)) (.arr (.sum B (.sum B B)))) (.arr (.sum B (.sum B B)))))
      ⊑ Tm.den ρ ((.prim (rowOf "cons") : Tm (.prod (.sum B (.sum B B)) (.arr (.sum B (.sum B B)))) (.arr (.sum B (.sum B B)))).comp Q))
    (h2 : Tm.den ρ (((((Tm.outl : Tm (.prod (.sum B (.sum B B)) (.arr (.sum B (.sum B B)))) (.sum B (.sum B B))).comp Tm.inl.conv).comp (Tm.inl.comp Tm.inr)).pair Tm.outr).comp
        (.prim (rowOf "cons") : Tm (.prod (.sum B (.sum B B)) (.arr (.sum B (.sum B B)))) (.arr (.sum B (.sum B B)))))
      ⊑ Tm.den ρ (((((Tm.outl : Tm (.prod (.sum B (.sum B B)) (.arr (.sum B (.sum B B)))) (.sum B (.sum B B))).comp (Tm.inl.conv.comp Tm.inl)).pair Tm.outr).comp
        (.prim (rowOf "cons") : Tm (.prod (.sum B (.sum B B)) (.arr (.sum B (.sum B B)))) (.arr (.sum B (.sum B B))))).comp Q))
    (h3 : Tm.den ρ ((((Tm.outl : Tm (.prod (.sum B (.sum B B)) (.arr (.sum B (.sum B B)))) (.sum B (.sum B B))).comp ((Tm.inr.conv.comp Tm.inr.conv).comp (Tm.inr.comp Tm.inr))).pair Tm.outr).comp
        (Tm.outr : Tm (.prod (.sum B (.sum B B)) (.arr (.sum B (.sum B B)))) (.arr (.sum B (.sum B B)))))
      ⊑ Tm.den ρ (((((Tm.outl : Tm (.prod (.sum B (.sum B B)) (.arr (.sum B (.sum B B)))) (.sum B (.sum B B))).comp ((Tm.inr.conv.comp Tm.inr.conv).comp (Tm.inr.comp Tm.inr))).pair Tm.outr).comp
        (.prim (rowOf "cons") : Tm (.prod (.sum B (.sum B B)) (.arr (.sum B (.sum B B)))) (.arr (.sum B (.sum B B))))).comp Q)) :
    Tm.den ρ ((Tm.foldr (Tm.ran (P.comp (Tm.nil.pair Tm.nil))) (Tm.dropStepT B)).comp Tm.outr) ⊑ Tm.den ρ Q := by
  have hD := Tm.foldrRan_fun ρ _ (Tm.dropStepT B) (fun m v h => ((Tm.nilPairSeed_iff ρ P m v).1 h).1)
    (Tm.dropStepT_iff ρ)
  refine Core.Rel.le_iff.2 fun es fs h => ?_
  obtain ⟨p, hp, rfl⟩ := h
  obtain ⟨⟨m, hm⟩, rfl⟩ := (hD es p).1 hp
  obtain ⟨u, hu⟩ := ((Tm.nilPairSeed_iff ρ P m _).1 hm).2
  clear hp
  induction es with
  | nil =>
    refine Core.Rel.le_iff.1 h0 [] [] ⟨m, ?_, ?_⟩ <;>
      simp only [Tm.den, Tm.nil, Prim.den_nilRow, Core.Rel.comp, Core.Rel.recip, Core.Rel.graph] <;> first | exact ⟨u, hu, rfl⟩ | exact ⟨u, hu, trivial⟩ | trivial
  | cons o es ih =>
    rw [dropFold_cons]
    rcases o with c | c | c
    · have := Core.Rel.le_iff.1 h2 (Sum.inl c, es) (Sum.inr (Sum.inl c) :: es) (by
        simp [Tm.den, Prim.den_cons, Core.Rel.comp, Core.Rel.rpair, Core.Rel.recip, Core.Rel.inl, Core.Rel.inr,
          Core.Rel.graph])
      simpa [Tm.den, Prim.den_cons, Core.Rel.comp, Core.Rel.rpair, Core.Rel.recip, Core.Rel.inl, Core.Rel.inr,
        Core.Rel.graph, dropStep, and_assoc, exists_eq_left] using this
    · have := Core.Rel.le_iff.1 h1 (Sum.inr (Sum.inl c), es) (Sum.inr (Sum.inl c) :: (es.foldr dropStep ([], [])).2)
        (by simp only [Tm.den, Prim.den_cons, Core.Rel.comp, Core.Rel.rpair, Core.Rel.graph]; exact ⟨(Sum.inr (Sum.inl c), (es.foldr dropStep ([], [])).2), ⟨rfl, _, rfl, ih⟩, rfl⟩)
      simpa [Tm.den, Prim.den_cons, Core.Rel.comp, Core.Rel.graph, dropStep] using this
    · have := Core.Rel.le_iff.1 h3 (Sum.inr (Sum.inr c), es) es (by
        simp [Tm.den, Core.Rel.comp, Core.Rel.rpair, Core.Rel.recip, Core.Rel.inl, Core.Rel.inr, Core.Rel.graph])
      simpa [Tm.den, Prim.den_cons, Core.Rel.comp, Core.Rel.rpair, Core.Rel.recip, Core.Rel.inl, Core.Rel.inr,
        Core.Rel.graph, dropStep, and_assoc, exists_eq_left] using this

/-! ## The `suffix` rows: `suffix = tail*`, so the tail/drop step of `edit` iterates along it -/

/-- The source mirror of `dropStep`: the first operation that reads the source goes (`del` goes, `cpy` becomes `ins`). -/
def dropStepS {A : Type} : A ⊕ (A ⊕ A) → List (A ⊕ (A ⊕ A)) × List (A ⊕ (A ⊕ A)) → List (A ⊕ (A ⊕ A)) × List (A ⊕ (A ⊕ A))
  | .inl c, (es, _) => (.inl c :: es, .inr (.inr c) :: es)
  | .inr (.inl c), (es, _) => (.inr (.inl c) :: es, es)
  | .inr (.inr c), (es, ds) => (.inr (.inr c) :: es, .inr (.inr c) :: ds)

theorem dropFoldS_fst {A : Type} : ∀ es : List (A ⊕ (A ⊕ A)), (es.foldr dropStepS ([], [])).1 = es
  | [] => rfl
  | o :: es => by
    have ih := dropFoldS_fst es
    simp only [List.foldr_cons]
    generalize es.foldr dropStepS ([], []) = d at ih
    obtain ⟨d1, d2⟩ := d
    obtain rfl : d1 = es := ih
    rcases o with c | c | c <;> rfl

/-- The source twin of `editDrop_core`: editing the dropped sequence drops the head of the source. -/
theorem editDropS_core {A : Type} : ∀ es : List (A ⊕ (A ⊕ A)),
    (es.foldr dropStepS ([], [])).2.foldr editStep ([], [])
      = ((es.foldr editStep ([], [])).1.tail, (es.foldr editStep ([], [])).2)
  | [] => rfl
  | o :: es => by
    have ih := editDropS_core es
    have h1 := dropFoldS_fst es
    simp only [List.foldr_cons]
    generalize es.foldr dropStepS ([], []) = d at ih h1
    obtain ⟨d1, d2⟩ := d
    obtain rfl : es = d1 := h1.symm
    generalize hE : es.foldr editStep ([], []) = e at ih ⊢
    obtain ⟨e1, e2⟩ := e
    rcases o with c | c | c <;> simp only [dropStepS, editStep, List.foldr_cons, ih, hE, List.tail_cons]

/-- `dropStepS` of the program: `π₁cpy°ins` turns a copy into an insert. -/
def Tm.dropStepST (B : Obj) :
    Tm (.prod (.sum B (.sum B B)) (.prod (.arr (.sum B (.sum B B))) (.arr (.sum B (.sum B B)))))
      (.prod (.arr (.sum B (.sum B B))) (.arr (.sum B (.sum B B)))) :=
  .join (.join
    (.pair (.comp (.pair (.comp .outl (.comp (.conv .inl) .inl)) (.comp .outr .outl)) (.prim (rowOf "cons") : Tm (.prod (.sum B (.sum B B)) (.arr (.sum B (.sum B B)))) (.arr (.sum B (.sum B B)))))
      (.comp (.pair (.comp (.comp .outl (.conv .inl)) (.comp .inr .inr)) (.comp .outr .outl)) (.prim (rowOf "cons") : Tm (.prod (.sum B (.sum B B)) (.arr (.sum B (.sum B B)))) (.arr (.sum B (.sum B B))))))
    (.pair (.comp (.pair (.comp .outl (.comp (.comp (.conv .inr) (.conv .inl)) (.comp .inl .inr))) (.comp .outr .outl))
        (.prim (rowOf "cons") : Tm (.prod (.sum B (.sum B B)) (.arr (.sum B (.sum B B)))) (.arr (.sum B (.sum B B)))))
      (.comp .outr .outl)))
    (.pair (.comp (.pair (.comp .outl (.comp (.comp (.conv .inr) (.conv .inr)) (.comp .inr .inr))) (.comp .outr .outl))
        (.prim (rowOf "cons") : Tm (.prod (.sum B (.sum B B)) (.arr (.sum B (.sum B B)))) (.arr (.sum B (.sum B B)))))
      (.comp (.pair (.comp .outl (.comp (.comp (.conv .inr) (.conv .inr)) (.comp .inr .inr))) (.comp .outr .outr))
        (.prim (rowOf "cons") : Tm (.prod (.sum B (.sum B B)) (.arr (.sum B (.sum B B)))) (.arr (.sum B (.sum B B))))))

theorem Tm.dropStepST_iff (ρ : Val) {B : Obj} (o : Obj.El (.sum B (.sum B B)))
    (p : List (Obj.El (.sum B (.sum B B))) × List (Obj.El (.sum B (.sum B B))))
    (w : List (Obj.El (.sum B (.sum B B))) × List (Obj.El (.sum B (.sum B B)))) :
    (Tm.dropStepST B).den ρ (o, p) w ↔ w = dropStepS o p := by
  obtain ⟨xs, ys⟩ := p; obtain ⟨w1, w2⟩ := w
  rcases o with c | c | c <;>
    simp [Tm.dropStepST, Tm.den, Prim.den_cons, dropStepS, Core.Rel.union, Core.Rel.comp, Core.Rel.rpair,
      Core.Rel.recip, Core.Rel.inl, Core.Rel.inr, Core.Rel.graph, and_assoc, exists_eq_left, exists_eq_left', eq_comm]

/-- `suffix = tail*`: `Qp` answers one dropped head (`hs`, `mk` puts the shortened list back in its pair), `Qp`
    reflexive and transitive, so `Qp` answers dropping any prefix `t`, i.e. `y' <:+ t ++ y'`. -/
theorem iterSuffix {E C β : Type} (Qp : List E → List E → Prop) (hr : ∀ a, Qp a a)
    (ht : ∀ a b c, Qp a b → Qp b c → Qp a c) (F : List E → β) (mk : List C → β)
    (hs : ∀ es y c, F es = mk (c :: y) → ∃ fs, Qp es fs ∧ F fs = mk y) (y' : List C) :
    ∀ (t : List C) es, F es = mk (t ++ y') → ∃ fs, Qp es fs ∧ F fs = mk y'
  | [], es, h => ⟨es, hr _, h⟩
  | c :: t, es, h => by
    obtain ⟨fs, hq, hf⟩ := hs es (t ++ y') c h
    obtain ⟨gs, hq', hg⟩ := iterSuffix Qp hr ht F mk hs y' t fs hf
    exact ⟨gs, ht _ _ _ hq hq', hg⟩

/-- `edit` of the program, seeded by `P`: its meaning is `List.foldr editStep` (`Tm.foldrRan_fun`). -/
abbrev Tm.editF {X M : Obj} (P : Tm X M) (B : Obj) :=
  Tm.foldr (Tm.ran (P.comp (Tm.nil.pair Tm.nil))) (Tm.editStepT B)

/-- One step of `Q` along `edit`'s target: from `edit es = (x, c::y)` to some `fs` with `Q es fs`, `edit fs = (x, y)`. -/
theorem Tm.editTgtStep {B X M : Obj} {P : Tm X M} {Q : Tm (.arr (.sum B (.sum B B))) (.arr (.sum B (.sum B B)))}
    (ρ : Val) {m : X.El} {u : M.El} (hu : P.den ρ m u)
    (hQ : Tm.den ρ ((Tm.foldr (Tm.ran (P.comp (Tm.nil.pair Tm.nil))) (Tm.dropStepT B)).comp Tm.outr) ⊑ Tm.den ρ Q)
    (es : List (Obj.El (.sum B (.sum B B)))) (x y : List B.El) (c : B.El)
    (h : es.foldr editStep ([], []) = (x, c :: y)) :
    ∃ fs, Tm.den ρ Q es fs ∧ fs.foldr editStep ([], []) = (x, y) := by
  have hD := Tm.foldrRan_fun ρ _ (Tm.dropStepT B) (fun m v h => ((Tm.nilPairSeed_iff ρ P m v).1 h).1)
    (Tm.dropStepT_iff ρ)
  refine ⟨(es.foldr dropStep ([], [])).2, Core.Rel.le_iff.1 hQ es _
    ⟨_, (hD es _).2 ⟨⟨m, (Tm.nilPairSeed_iff ρ P m _).2 ⟨rfl, u, hu⟩⟩, rfl⟩, rfl⟩, ?_⟩
  simp [editDrop_core, h]

/-- The source twin of `Tm.editTgtStep`: from `edit es = (c::x, y)` to some `fs` with `edit fs = (x, y)`. -/
theorem Tm.editSrcStep {B X M : Obj} {P : Tm X M} {Q : Tm (.arr (.sum B (.sum B B))) (.arr (.sum B (.sum B B)))}
    (ρ : Val) {m : X.El} {u : M.El} (hu : P.den ρ m u)
    (hQ : Tm.den ρ ((Tm.foldr (Tm.ran (P.comp (Tm.nil.pair Tm.nil))) (Tm.dropStepST B)).comp Tm.outr) ⊑ Tm.den ρ Q)
    (es : List (Obj.El (.sum B (.sum B B)))) (x y : List B.El) (c : B.El)
    (h : es.foldr editStep ([], []) = (c :: x, y)) :
    ∃ fs, Tm.den ρ Q es fs ∧ fs.foldr editStep ([], []) = (x, y) := by
  have hD := Tm.foldrRan_fun ρ _ (Tm.dropStepST B) (fun m v h => ((Tm.nilPairSeed_iff ρ P m v).1 h).1)
    (Tm.dropStepST_iff ρ)
  refine ⟨(es.foldr dropStepS ([], [])).2, Core.Rel.le_iff.1 hQ es _
    ⟨_, (hD es _).2 ⟨⟨m, (Tm.nilPairSeed_iff ρ P m _).2 ⟨rfl, u, hu⟩⟩, rfl⟩, rfl⟩, ?_⟩
  simp [editDropS_core, h]

/-- **edit-suffix, target side** at a generic `Q` for `R°`: `edit (𝟙×suffix) ⊑ Q edit`, `suffix = tail*` and
    `editTailSnd` iterated; `𝟙 ⊑ Q` and `Q Q ⊑ Q` are `R°`'s reflexivity and transitivity. -/
theorem Tm.editSuffixRight_den {B X M : Obj} {P : Tm X M} {Q : Tm (.arr (.sum B (.sum B B))) (.arr (.sum B (.sum B B)))}
    (ρ : Val)
    (hQ : Tm.den ρ ((Tm.foldr (Tm.ran (P.comp (Tm.nil.pair Tm.nil))) (Tm.dropStepT B)).comp Tm.outr) ⊑ Tm.den ρ Q)
    (h1 : Tm.den ρ Tm.id ⊑ Tm.den ρ Q) (h2 : Tm.den ρ (Q.comp Q) ⊑ Tm.den ρ Q) :
    Tm.den ρ ((Tm.editF P B).comp
        ((Tm.outl.comp Tm.id).pair (Tm.outr.comp (Tm.prim (rowOf "suffix") : Tm (.arr B) (.arr B))))) ⊑
      Tm.den ρ (Q.comp (Tm.editF P B)) := by
  have hE := Tm.foldrRan_fun ρ _ (Tm.editStepT B) (fun m v h => ((Tm.nilPairSeed_iff ρ P m v).1 h).1)
    (Tm.editStepT_iff ρ)
  refine Core.Rel.le_iff.2 fun es w h => ?_
  obtain ⟨⟨x, y⟩, he, hw⟩ := h
  obtain ⟨⟨m, hm⟩, hxy⟩ := (hE es (x, y)).1 he
  obtain ⟨u, hu⟩ := ((Tm.nilPairSeed_iff ρ P m _).1 hm).2
  simp only [Tm.den, Core.Rel.rpair, Core.Rel.comp, Core.Rel.graph, Core.Rel.id, Prim.den_suffix_iff] at hw
  obtain ⟨⟨x, rfl, hw1⟩, y, rfl, t, hw2⟩ := hw
  obtain ⟨w1, w2⟩ := w
  obtain rfl : x = w1 := hw1
  obtain rfl : t ++ w2 = y := hw2
  obtain ⟨fs, hq, hf⟩ := iterSuffix (Tm.den ρ Q) (fun a => Core.Rel.le_iff.1 h1 a a rfl)
    (fun a b c hab hbc => Core.Rel.le_iff.1 h2 a c ⟨b, hab, hbc⟩) (fun es => es.foldr editStep ([], []))
    (fun y => (x, y)) (fun es y c h => Tm.editTgtStep ρ hu hQ es x y c h) w2 t es hxy.symm
  exact ⟨fs, hq, (hE fs _).2 ⟨⟨m, hm⟩, hf.symm⟩⟩

/-- **edit-suffix, source side**: `edit (suffix×𝟙) ⊑ Q edit`, the mirror of `Tm.editSuffixRight_den` along `dropSrc`. -/
theorem Tm.editSuffixLeft_den {B X M : Obj} {P : Tm X M} {Q : Tm (.arr (.sum B (.sum B B))) (.arr (.sum B (.sum B B)))}
    (ρ : Val)
    (hQ : Tm.den ρ ((Tm.foldr (Tm.ran (P.comp (Tm.nil.pair Tm.nil))) (Tm.dropStepST B)).comp Tm.outr) ⊑ Tm.den ρ Q)
    (h1 : Tm.den ρ Tm.id ⊑ Tm.den ρ Q) (h2 : Tm.den ρ (Q.comp Q) ⊑ Tm.den ρ Q) :
    Tm.den ρ ((Tm.editF P B).comp
        ((Tm.outl.comp (Tm.prim (rowOf "suffix") : Tm (.arr B) (.arr B))).pair (Tm.outr.comp Tm.id))) ⊑
      Tm.den ρ (Q.comp (Tm.editF P B)) := by
  have hE := Tm.foldrRan_fun ρ _ (Tm.editStepT B) (fun m v h => ((Tm.nilPairSeed_iff ρ P m v).1 h).1)
    (Tm.editStepT_iff ρ)
  refine Core.Rel.le_iff.2 fun es w h => ?_
  obtain ⟨⟨x, y⟩, he, hw⟩ := h
  obtain ⟨⟨m, hm⟩, hxy⟩ := (hE es (x, y)).1 he
  obtain ⟨u, hu⟩ := ((Tm.nilPairSeed_iff ρ P m _).1 hm).2
  simp only [Tm.den, Core.Rel.rpair, Core.Rel.comp, Core.Rel.graph, Core.Rel.id, Prim.den_suffix_iff] at hw
  obtain ⟨⟨x, rfl, t, hw1⟩, y, rfl, hw2⟩ := hw
  obtain ⟨w1, w2⟩ := w
  obtain rfl : t ++ w1 = x := hw1
  obtain rfl : y = w2 := hw2
  obtain ⟨fs, hq, hf⟩ := iterSuffix (Tm.den ρ Q) (fun a => Core.Rel.le_iff.1 h1 a a rfl)
    (fun a b c hab hbc => Core.Rel.le_iff.1 h2 a c ⟨b, hab, hbc⟩) (fun es => es.foldr editStep ([], []))
    (fun x => (x, y)) (fun es x c h => Tm.editSrcStep ρ hu hQ es x y c h) w1 t es hxy.symm
  exact ⟨fs, hq, (hE fs _).2 ⟨⟨m, hm⟩, hf.symm⟩⟩

/-- **edit-Vrecip**: `edit (suffix×suffix) ⊑ Q edit` (freyd `V°`), the source side and then the target side. -/
theorem Tm.editVrecip_den {B X M : Obj} {P : Tm X M} {Q : Tm (.arr (.sum B (.sum B B))) (.arr (.sum B (.sum B B)))}
    (ρ : Val)
    (hS : Tm.den ρ ((Tm.foldr (Tm.ran (P.comp (Tm.nil.pair Tm.nil))) (Tm.dropStepST B)).comp Tm.outr) ⊑ Tm.den ρ Q)
    (hT : Tm.den ρ ((Tm.foldr (Tm.ran (P.comp (Tm.nil.pair Tm.nil))) (Tm.dropStepT B)).comp Tm.outr) ⊑ Tm.den ρ Q)
    (h1 : Tm.den ρ Tm.id ⊑ Tm.den ρ Q) (h2 : Tm.den ρ (Q.comp Q) ⊑ Tm.den ρ Q) :
    Tm.den ρ ((Tm.editF P B).comp
        ((Tm.outl.comp (Tm.prim (rowOf "suffix") : Tm (.arr B) (.arr B))).pair
          (Tm.outr.comp (Tm.prim (rowOf "suffix") : Tm (.arr B) (.arr B))))) ⊑
      Tm.den ρ (Q.comp (Tm.editF P B)) := by
  have hE := Tm.foldrRan_fun ρ _ (Tm.editStepT B) (fun m v h => ((Tm.nilPairSeed_iff ρ P m v).1 h).1)
    (Tm.editStepT_iff ρ)
  refine Core.Rel.le_iff.2 fun es w h => ?_
  obtain ⟨⟨x, y⟩, he, hw⟩ := h
  obtain ⟨⟨m, hm⟩, hxy⟩ := (hE es (x, y)).1 he
  obtain ⟨u, hu⟩ := ((Tm.nilPairSeed_iff ρ P m _).1 hm).2
  simp only [Tm.den, Core.Rel.rpair, Core.Rel.comp, Core.Rel.graph, Core.Rel.id, Prim.den_suffix_iff] at hw
  obtain ⟨⟨x, rfl, t, hw1⟩, y, rfl, t', hw2⟩ := hw
  obtain ⟨w1, w2⟩ := w
  obtain rfl : t ++ w1 = x := hw1
  obtain rfl : t' ++ w2 = y := hw2
  have hr := fun a => Core.Rel.le_iff.1 h1 a a rfl
  have ht := fun a b c hab hbc => Core.Rel.le_iff.1 h2 a c ⟨b, hab, hbc⟩
  obtain ⟨fs, hq, hf⟩ := iterSuffix (Tm.den ρ Q) hr ht (fun es => es.foldr editStep ([], []))
    (fun x => (x, t' ++ w2)) (fun es x c h => Tm.editSrcStep ρ hu hS es x _ c h) w1 t es hxy.symm
  obtain ⟨gs, hq', hg⟩ := iterSuffix (Tm.den ρ Q) hr ht (fun es => es.foldr editStep ([], []))
    (fun y => (w1, y)) (fun es y c h => Tm.editTgtStep ρ hu hT es w1 y c h) w2 t' fs hf
  exact ⟨gs, ht _ _ _ hq hq', (hE gs _).2 ⟨⟨m, hm⟩, hg.symm⟩⟩

/-- **edit-V** at any `V` with `V° ⊑ suffix×suffix` (freyd's `V = suffix°×suffix°` is one): `V edit° ⊑ edit° Q°`,
    the converse of `Tm.editVrecip_den`. -/
theorem Tm.editV_den {B X M : Obj} {P : Tm X M} {Q : Tm (.arr (.sum B (.sum B B))) (.arr (.sum B (.sum B B)))}
    {V : Tm (.prod (.arr B) (.arr B)) (.prod (.arr B) (.arr B))} (ρ : Val)
    (hV : Tm.den ρ V.conv ⊑ Tm.den ρ ((Tm.outl.comp (Tm.prim (rowOf "suffix") : Tm (.arr B) (.arr B))).pair
          (Tm.outr.comp (Tm.prim (rowOf "suffix") : Tm (.arr B) (.arr B)))))
    (hS : Tm.den ρ ((Tm.foldr (Tm.ran (P.comp (Tm.nil.pair Tm.nil))) (Tm.dropStepST B)).comp Tm.outr) ⊑ Tm.den ρ Q)
    (hT : Tm.den ρ ((Tm.foldr (Tm.ran (P.comp (Tm.nil.pair Tm.nil))) (Tm.dropStepT B)).comp Tm.outr) ⊑ Tm.den ρ Q)
    (h1 : Tm.den ρ Tm.id ⊑ Tm.den ρ Q) (h2 : Tm.den ρ (Q.comp Q) ⊑ Tm.den ρ Q) :
    Tm.den ρ (V.comp (Tm.id.comp (Tm.editF P B)).conv) ⊑ Tm.den ρ ((Tm.id.comp (Tm.editF P B)).conv.comp Q.conv) := by
  refine Core.Rel.le_iff.2 fun p es h => ?_
  obtain ⟨q, hv, b, hb, he⟩ := h
  obtain rfl : es = b := hb
  obtain ⟨fs, hq, hf⟩ := Core.Rel.le_iff.1 (Tm.editVrecip_den ρ hS hT h1 h2) es p ⟨q, he, Core.Rel.le_iff.1 hV q p hv⟩
  exact ⟨fs, ⟨fs, rfl, hf⟩, hq⟩

/-- **edit-thin** (Proposition 9.4 at `F(U,V) = 1+(U×V)`, written as the junction `[𝟙 inl, ⟨π₁U,π₂V⟩ inr]`):
    `F(U,V) F(𝟙,edit°) [nil,cons] ⊑ F(𝟙,edit°) [nil,cons] Q°`, from `Tm.editV_den` and `cons` lifting `Q°` under `U`
    (freyd's `α_pres_R` at `U = ⊤`); the `1` summand needs only `𝟙 ⊑ Q`. -/
theorem Tm.editThinCondition_den {B X M : Obj} {P : Tm X M} {Q : Tm (.arr (.sum B (.sum B B))) (.arr (.sum B (.sum B B)))}
    {U : Tm (.sum B (.sum B B)) (.sum B (.sum B B))} {V : Tm (.prod (.arr B) (.arr B)) (.prod (.arr B) (.arr B))}
    (ρ : Val)
    (hV : Tm.den ρ V.conv ⊑ Tm.den ρ ((Tm.outl.comp (Tm.prim (rowOf "suffix") : Tm (.arr B) (.arr B))).pair
          (Tm.outr.comp (Tm.prim (rowOf "suffix") : Tm (.arr B) (.arr B)))))
    (hS : Tm.den ρ ((Tm.foldr (Tm.ran (P.comp (Tm.nil.pair Tm.nil))) (Tm.dropStepST B)).comp Tm.outr) ⊑ Tm.den ρ Q)
    (hT : Tm.den ρ ((Tm.foldr (Tm.ran (P.comp (Tm.nil.pair Tm.nil))) (Tm.dropStepT B)).comp Tm.outr) ⊑ Tm.den ρ Q)
    (h1 : Tm.den ρ Tm.id ⊑ Tm.den ρ Q) (h2 : Tm.den ρ (Q.comp Q) ⊑ Tm.den ρ Q)
    (hC : Tm.den ρ (((Tm.outl.comp U).pair (Tm.outr.comp Q.conv)).comp
          (Tm.prim (rowOf "cons") : Tm (.prod (.sum B (.sum B B)) (.arr (.sum B (.sum B B)))) (.arr (.sum B (.sum B B))))) ⊑
        Tm.den ρ ((Tm.prim (rowOf "cons") : Tm (.prod (.sum B (.sum B B)) (.arr (.sum B (.sum B B)))) (.arr (.sum B (.sum B B)))).comp
          Q.conv)) :
    Tm.den ρ ((((Tm.inl.conv.comp (Tm.id.comp Tm.inl)).join
          (Tm.inr.conv.comp (((Tm.outl.comp U).pair (Tm.outr.comp V)).comp Tm.inr))).comp
        ((Tm.inl.conv.comp (Tm.id.comp Tm.inl)).join
          (Tm.inr.conv.comp ((Tm.outl.pair (Tm.outr.comp (Tm.id.comp (Tm.editF P B)).conv)).comp Tm.inr)))).comp
        ((Tm.inl.conv.comp (Tm.nil : Tm .one (.arr (.sum B (.sum B B))))).join (Tm.inr.conv.comp
          (Tm.prim (rowOf "cons") : Tm (.prod (.sum B (.sum B B)) (.arr (.sum B (.sum B B)))) (.arr (.sum B (.sum B B))))))) ⊑
      Tm.den ρ ((((Tm.inl.conv.comp (Tm.id.comp Tm.inl)).join
          (Tm.inr.conv.comp ((Tm.outl.pair (Tm.outr.comp (Tm.id.comp (Tm.editF P B)).conv)).comp Tm.inr))).comp
        ((Tm.inl.conv.comp (Tm.nil : Tm .one (.arr (.sum B (.sum B B))))).join (Tm.inr.conv.comp
          (Tm.prim (rowOf "cons") : Tm (.prod (.sum B (.sum B B)) (.arr (.sum B (.sum B B)))) (.arr (.sum B (.sum B B))))))).comp
        Q.conv) := by
  have hEV : ∀ p q es, Tm.den ρ V p q → Tm.den ρ (Tm.editF P B) es q →
      ∃ fs, Tm.den ρ (Tm.editF P B) fs p ∧ Tm.den ρ Q es fs := fun p q es hv he => by
    obtain ⟨fs, ⟨b, hb, hf⟩, hq⟩ := Core.Rel.le_iff.1 (Tm.editV_den ρ hV hS hT h1 h2) p es ⟨q, hv, es, rfl, he⟩
    obtain rfl : fs = b := hb
    exact ⟨fs, hf, hq⟩
  have hCp := Core.Rel.le_iff.1 hC
  have h1p := Core.Rel.le_iff.1 h1
  refine Core.Rel.le_iff.2 fun s l h => ?_
  simp only [Tm.den, Core.Rel.comp, Core.Rel.union, Core.Rel.recip, Core.Rel.inl, Core.Rel.inr, Core.Rel.graph,
    Core.Rel.id, Core.Rel.rpair, Prim.den_cons, Tm.nil, Prim.den_nilRow, nilDen] at h hCp h1p ⊢
  obtain ⟨b, ⟨b1, hb1, hb⟩, hl⟩ := h
  rcases s with u | ⟨o, p⟩
  · rcases hb1 with ⟨_, -, c, -, rfl⟩ | ⟨_, hc, _⟩
    · rcases hb with ⟨_, -, d, -, rfl⟩ | ⟨_, hd, _⟩
      · rcases hl with ⟨_, -, hn⟩ | ⟨_, he, _⟩
        · exact ⟨l, ⟨Sum.inl c, Or.inl ⟨u, rfl, c, trivial, rfl⟩, Or.inl ⟨c, rfl, hn⟩⟩, h1p l l rfl⟩
        · exact nomatch he
      · exact nomatch hd
    · exact nomatch hc
  · rcases hb1 with ⟨_, hc, _⟩ | ⟨r, hr, w, ⟨⟨_, rfl, hu⟩, _, rfl, hv⟩, rfl⟩
    · exact nomatch hc
    obtain rfl := Sum.inr.inj hr
    rcases hb with ⟨_, hd, _⟩ | ⟨w', hw', t, ⟨ht1, _, rfl, es, ht2, hes⟩, rfl⟩
    · exact nomatch hd
    obtain rfl := Sum.inr.inj hw'
    rcases hl with ⟨_, he, _⟩ | ⟨t', he, hcons⟩
    · exact nomatch he
    obtain rfl := Sum.inr.inj he
    obtain ⟨fs, hf, hq⟩ := hEV p w.2 es hv hes
    obtain ⟨l', hl', hql⟩ := hCp (o, fs) l ⟨(w.1, es), ⟨⟨o, rfl, hu⟩, fs, rfl, hq⟩, by rw [hcons, ht1, ht2]⟩
    exact ⟨l', ⟨Sum.inr (o, fs), Or.inr ⟨(o, p), rfl, (o, fs), ⟨rfl, p, rfl, fs, rfl, hf⟩, rfl⟩,
      Or.inr ⟨(o, fs), rfl, hl'⟩⟩, hql⟩

end Rel.Lang
