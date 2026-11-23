module

public import Rel.Lang.PreludeDfn
public import Rel.RepSums

@[expose] public section

/-! The orders `lt`, `le` of the prelude (O2): their texts mean `Obj.lt` and `Obj.lt ∪ 𝟙` at every object
    (`Tm.lt_den`), and the rows `cmpRow` where these are fused, the atoms of its `num` outside its `native`, which are
    the integer-stored ones (`Tm.lt_row_den`, `Tm.le_row_den`). -/

namespace Rel.Lang

/-- `le ≜ lt ∪ dom(π₁ ∩ π₂)`: the pairs in order or equal. -/
def Tm.leDef (B : Obj) : Tm (.prod B B) (.prod B B) := .join (Tm.ltDef B) (.dom (.meet .outl .outr))

/-- **The row `le` is the definition `Tm.leDef`** at every integer-stored atom: there `leAt` is `ltAt ∨ =` and
    `ltAt` is `Obj.lt` (`ordAt_int`). -/
theorem Tm.le_row_den (ρ : Val) {t : QAtomicType} (h : t.intOrd = true) :
    ordDen false (.atom t) = (Tm.leDef (.atom t)).den ρ := by
  funext p q; apply propext
  obtain ⟨x, y⟩ := p
  obtain ⟨x', y'⟩ := q
  simp only [Tm.leDef, Tm.den, Tm.lt_den, Tm.dom_den, ordDen, Bool.false_eq_true, if_false, (ordAt_int h).2,
    (ordAt_int h).1, Core.Rel.union, Core.Rel.inter, Core.Rel.id, Core.Rel.comp, Core.Rel.recip, Core.Rel.graph,
    Prod.mk.injEq]
  constructor
  · rintro ⟨⟨rfl, rfl⟩, hl | rfl⟩
    · exact .inl ⟨⟨rfl, rfl⟩, hl⟩
    · exact .inr ⟨⟨rfl, rfl⟩, x', ⟨rfl, rfl⟩, rfl, rfl⟩
  · rintro (⟨⟨rfl, rfl⟩, hl⟩ | ⟨⟨rfl, rfl⟩, c, ⟨rfl, rfl⟩, -⟩)
    · exact ⟨⟨rfl, rfl⟩, .inl hl⟩
    · exact ⟨⟨rfl, rfl⟩, .inr rfl⟩

/-- The literal `{0}` of a body's `at(0)` (`Gen.atom_zero`) means the universe `{0}` of `Tm.at0`. -/
theorem Tm.zeroLit_den (ρ : Val) : (Tm.val (Gen.relV (.atom .i64) (.atom .i64) (USize.ofNat 1) (zeroCol .i64 rfl, true)
    (zeroCol .i64 rfl, true)).fst).den ρ = (Tm.uni (A := .atom .i64) (zeroCol .i64 rfl)).den ρ := by
  have hz : ∀ i, ValsB.row (o := false) (A := .atom .i64) (zeroCol .i64 rfl) i = (0 : Int64) := fun i => by
    rw [zeroCol_row]; rfl
  funext a b; apply propext
  rw [Tm.relV_den]
  simp only [Tm.den, Core.Rel.comp, Core.Rel.recip, Core.Rel.graph]
  constructor
  · rintro ⟨i, ha, hb⟩; exact ⟨i, ha.symm, hb ▸ (hz i).trans (hz i).symm⟩
  · rintro ⟨i, ha, hb⟩; exact ⟨i, ha.symm, hb ▸ (hz i).trans (hz i).symm⟩

/-- **`lt`'s text means `Obj.lt`, and the row `lt` where it is fused** (Q3 = H, O2): `prelude.lt.body` (placeholder
    `general` of `α`) at any objects `σ` is `Tm.ltDef` (`Tm.lt_den`); where `α` is an atom of `cmpRow`'s `num`
    outside its `native`, it is the row (`Tm.lt_row_den`). -/
theorem Tm.ltDef_den (ph : List QAtomicType) (σ : List Obj) (ρ : Val)
    {t' : Tm ((Obj.prod (.atom .general) (.atom .general)).inst ph σ)
      ((Obj.prod (.atom .general) (.atom .general)).inst ph σ)}
    (ht : Rel.Programs.prelude.lt.body.instObj ph σ = .ok t') :
    t'.den ρ = (Tm.ltDef ((Obj.atom .general).inst ph σ)).den ρ ∧
      ∀ t, (Obj.atom .general).inst ph σ = .atom t → t.ordNum.isSome → t ∉ (cmpRow "lt").native →
        t'.den ρ = (Tm.prim (cmpRow "lt")).den ρ := by
  have h1 : t'.den ρ = (Tm.ltDef ((Obj.atom .general).inst ph σ)).den ρ := by
    obtain rfl := Except.ok.inj ht
    have hz := Tm.zeroLit_den ρ
    simp only [Tm.den] at hz
    simp only [Tm.ltDef, Tm.at0, Tm.den, Tm.argDen, Gen.atom_zero, cast_eq, hz]
    rfl
  refine ⟨h1, fun t hB ho hf => ?_⟩
  have hi : t.intOrd = true := by revert ho hf; cases t <;> decide
  rw [h1]
  show (Tm.ltDef ((Obj.atom .general).inst ph σ)).den ρ = Prim.den (cmpRow "lt") _ _ []
  generalize (Obj.atom .general).inst ph σ = B at hB ⊢
  subst hB
  rw [Prim.den_cmpRow_lt, Tm.lt_row_den ρ hi]

/-- **`le`'s text means `Tm.leDef`, and the row `le` where it is fused** (Q3 = H, O2): `prelude.le.body` is built
    generic over `α` (its `lt` is the prelude's text at the placeholder) and at any objects `σ` is `Tm.leDef`; where
    `α` is an integer-stored atom, it is the row (`Tm.le_row_den`). -/
theorem Tm.leDef_den (ph : List QAtomicType) (σ : List Obj) (ρ : Val)
    {t' : Tm ((Obj.prod (.atom .general) (.atom .general)).inst ph σ)
      ((Obj.prod (.atom .general) (.atom .general)).inst ph σ)}
    (ht : Rel.Programs.prelude.le.body.instObj ph σ = .ok t') :
    t'.den ρ = (Tm.leDef ((Obj.atom .general).inst ph σ)).den ρ ∧
      ∀ t, (Obj.atom .general).inst ph σ = .atom t → t.intOrd = true →
        t'.den ρ = (Tm.prim (cmpRow "le")).den ρ := by
  have h1 : t'.den ρ = (Tm.leDef ((Obj.atom .general).inst ph σ)).den ρ := by
    obtain rfl := Except.ok.inj ht
    have hz := Tm.zeroLit_den ρ
    simp only [Tm.den] at hz
    simp only [Tm.leDef, Tm.ltDef, Tm.at0, Tm.dom, Tm.den, Tm.argDen, Gen.atom_zero, cast_eq, hz]
    rfl
  refine ⟨h1, fun t hB hi => ?_⟩
  rw [h1]
  show (Tm.leDef ((Obj.atom .general).inst ph σ)).den ρ = Prim.den (cmpRow "le") _ _ []
  generalize (Obj.atom .general).inst ph σ = B at hB ⊢
  subst hB
  rw [Prim.den_cmpRow_le, Tm.le_row_den ρ hi]

/-- `(Tm.lt U)°` is `>` on `dom U` at an atom the row `lt` fuses (`num` outside `native`, the integer-stored ones):
    the row is `Tm.cmpDef` of the test `lt` (`Tm.cmpDef_lt_den`), which is `Tm.ltDef` there (`Tm.lt_row_den`). A float
    atom has no such instance of `Tm.ascDef_of_len`'s `hG`: its `ltAt` is IEEE's `<`, not `Obj.lt`. -/
theorem Tm.gt_of_ltRow (ρ : Val) {t : QAtomicType} (ho : t.ordNum.isSome) (hf : t ∉ (cmpRow "lt").native)
    (U : Tm (.atom t) (.atom t)) (x y : (Obj.atom t).El) (hx : ∃ v, U.den ρ x v) (hy : ∃ v, U.den ρ y v) :
    (Tm.conv (Tm.lt U)).den ρ x y ↔ (Obj.atom t).lt y x := by
  have hi : t.intOrd = true := by revert ho hf; cases t <;> decide
  have hc : (Tm.prim (cmpRow "lt") : Tm (.prod (.atom t) (.atom t)) (.prod (.atom t) (.atom t))).den ρ =
      (Tm.ltDef (.atom t)).den ρ := by
    show Prim.den (cmpRow "lt") _ _ [] = _
    rw [Prim.den_cmpRow_lt, Tm.lt_row_den ρ hi]
  show (Tm.lt U).den ρ y x ↔ _
  rw [← Tm.cmpDef_lt_den]
  exact Tm.gt_of_lt ρ _ U hc x y hx hy

/-- **`asc`'s text means `ascDen` at every object** (Q3 = H): `prelude.asc.body` is built generic over `β` (its `>`
    is `(Tm.cmpDef c U)°`, `c` the prelude's `lt`, `U` the universe variable 0), so at any objects `σ` it is
    `Tm.ascDef` at `B = β.inst ph σ`: `G` by `Tm.gt_of_lt` (`c` means `Tm.ltDef`, as `Tm.ltDef_den`; `dom P ⊆ dom U`
    by `hPU`), `L` the call of `length` with the universe variable 1 (`Tm.lengthDef_den`), `P` the variable 2. -/
theorem Tm.ascDef_den (ph : List QAtomicType) (σ : List Obj) (ρ : Val) {Q : Obj.long.El → Prop}
    (hQ : (∀ x, Q x) ∨ Seg .long Q) (hU : ∀ x y, ρ 1 .long .long x y ↔ x = y ∧ Q x) (h0 : Q 0)
    (hPU : ∀ b c, ρ 2 ((Obj.atom .general).inst ph σ) ((Obj.atom .general).inst ph σ) b c →
      ∃ v, ρ 0 ((Obj.atom .general).inst ph σ) ((Obj.atom .general).inst ph σ) b v)
    (hp : ∃ ys : List ((Obj.atom .general).inst ph σ).El, ys.Pairwise (Obj.lt _) ∧
      (∀ b, b ∈ ys ↔ ∃ c, ρ 2 ((Obj.atom .general).inst ph σ) ((Obj.atom .general).inst ph σ) b c) ∧
      ys.length < 2 ^ 63)
    {t' : Tm ((Obj.atom .i64).inst ph σ) ((Obj.atom .general).inst ph σ)}
    (ht : Rel.Programs.prelude.asc.body.instObj ph σ = .ok t') (j : Int64) (a : ((Obj.atom .general).inst ph σ).El) :
    t'.den ρ j a ↔ Q j ∧ ascDen _ (fun b => ∃ c, ρ 2 ((Obj.atom .general).inst ph σ)
      ((Obj.atom .general).inst ph σ) b c) j a := by
  obtain rfl := Except.ok.inj ht
  have hz := Tm.zeroLit_den ρ
  simp only [Tm.den] at hz
  refine Tm.ascDef_of_len ρ (.var 2) _ _ Q ?_ ?_ hp j a
  · intro x y ⟨c, hx⟩ ⟨d, hy⟩
    rw [Tm.den, Tm.argDen]
    refine Tm.gt_of_lt _ _ (.var 0) ?_ x y ?_ ?_
    · simp only [Tm.ltDef, Tm.at0, Tm.dom, Tm.den, Tm.argDen, Gen.atom_zero, cast_eq, hz]
      rfl
    · simp only [Tm.den, Val.args, Val.bind, if_true, and_self]; exact hPU x c hx
    · simp only [Tm.den, Val.args, Val.bind, if_true, and_self]; exact hPU y d hy
  · intro zs hs w
    -- `i64` is no placeholder: `σ` keeps it
    have hU' : ∀ x y, ρ 1 ((Obj.atom .i64).inst ph σ) ((Obj.atom .i64).inst ph σ) x y ↔ x = y ∧ Q x := hU
    rw [Tm.den, Tm.argDen]
    refine ((Tm.lengthDef_den [.general] [(Obj.atom .general).inst ph σ] _ hQ ?_ h0 rfl zs hs w).1).trans ?_
    · intro x y; simp only [Tm.den, Val.args, Val.bind, if_true, and_self]; exact hU' x y
    -- `length` is called at `[β]`: its row at `(Obj.arr α).inst [α] [β]`, which is `[β]`
    have hl : ∀ b, Prim.den lengthRow ((Obj.arr (.atom .general)).inst [.general] [(Obj.atom .general).inst ph σ])
        .long [] zs b ↔ b = Int64.ofNat zs.length :=
      fun b => iff_of_eq (congrFun (congrFun (Prim.den_lengthRow (E := (Obj.atom .general).inst ph σ)) zs) b)
    simp only [Tm.den, Core.Rel.comp, Val.args, Val.bind, if_true, and_self]
    constructor
    · rintro ⟨b, hb, h⟩; obtain rfl := (hl b).1 hb; obtain ⟨rfl, hb⟩ := (hU' _ _).1 h; exact ⟨rfl, hb⟩
    · rintro ⟨rfl, hb⟩; exact ⟨_, (hl _).2 rfl, (hU' _ _).2 ⟨rfl, hb⟩⟩

end Rel.Lang
