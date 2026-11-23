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

/-- **`le`'s text means the row `le`** (Q3 = H, O2): `prelude.le.body` is built at `i64` (its `lt` is the row's
    constant, which `once` keeps at a number object) and is `Tm.leDef` there, the row (`Tm.le_row_den`). -/
theorem Tm.leDef_den (ph : List QAtomicType) (σ : List Obj) (ρ : Val)
    {t' : Tm ((Obj.prod (.atom .i64) (.atom .i64)).inst ph σ) ((Obj.prod (.atom .i64) (.atom .i64)).inst ph σ)}
    (ht : Rel.Programs.prelude.le.body.instObj ph σ = .ok t') :
    t'.den ρ = (Tm.leDef (.atom .i64)).den ρ ∧ t'.den ρ = (Tm.prim (cmpRow "le")).den ρ := by
  have h1 : t'.den ρ = (Tm.leDef (.atom .i64)).den ρ := by
    obtain rfl := Except.ok.inj ht
    have hz := Tm.zeroLit_den ρ
    simp only [Tm.den] at hz
    simp only [Tm.leDef, Tm.ltDef, Tm.at0, Tm.den, Tm.argDen, Gen.atom_zero, cast_eq, hz]
    rfl
  refine ⟨h1, ?_⟩
  rw [h1]
  show _ = Prim.den (cmpRow "le") (.prod (.atom .i64) (.atom .i64)) (.prod (.atom .i64) (.atom .i64)) []
  rw [Prim.den_cmpRow_le, Tm.le_row_den ρ rfl]

end Rel.Lang
