module

public import Rel.Lang.DfnLaw
public import Rel.Programs.Prelude

@[expose] public section

/-! The definitions of `flat`, `foldI`, `dom`, `ran`, `nil`, `front` (`Programs/Prelude.lean`) mean their rows (B10c2):
    `Tm.<sym>Def_row` proves each term equal to the row at every object (these rows have no `num` variable, so need
    no universe). `length` and `sum` (C3) carry the universes of their base and step, so their theorems take the
    universe hypotheses themselves.
    Q3 = H (B10d): `Tm.<sym>Def_den` is about the body the prelude elaborates, `prelude.<sym>.body` (`Expand.emit`),
    at any objects (`Tm.instObj`); the Lean-built term's theorem, renamed `Tm.<sym>Def_row`, is its middle step. -/

namespace Rel.Lang

/-- `flat(R) ≜ ⟨π₁R,π₂⟩dom(π₁π₁ ∩ π₂)π₁π₂`. -/
def Tm.flatDef {I A B : Obj} (R : Tm I (.prod A B)) : Tm (.prod I A) B :=
  .comp (.pair (.comp .outl R) .outr) (.comp (.dom (.meet (.comp .outl .outl) .outr)) (.comp .outl .outr))

/-- `foldI(e, S) ≜ (π₁π₁° ∩ π₂⦇ran⟨𝟙,eπ₂⟩, S ∩ π₁π₁π₁°⦈)π₂`. -/
def Tm.foldIDef {I E V : Obj} (e : Tm I (.prod V V)) (S : Tm (.prod (.prod I V) E) (.prod I V)) :
    Tm (.prod I (.arr E)) V :=
  .comp (.meet (.comp .outl (.conv .outl)) (.comp .outr (.fold (.ran (.pair .id (.comp e .outr)))
    (.meet S (.comp .outl (.comp .outl (.conv .outl))))))) .outr

/-- `dom(R) ≜ ⟨𝟙,R⟩π₁`. -/
def Tm.domDef {A B : Obj} (R : Tm A B) : Tm A A := .comp (.pair .id R) .outl

/-- `ran(R) ≜ dom(R°)`. -/
def Tm.ranDef {A B : Obj} (R : Tm A B) : Tm B B := .dom (.conv R)

/-- `nil ≜ Λ(𝟘)`. -/
def Tm.nilDef {A B : Obj} : Tm A (.arr B) := .lam .zero

/-- `front(Q) ≜ Λ(∋ − ∋ (Q − Q°))`. -/
def Tm.frontDef {B : Obj} (Q : Tm B B) : Tm (.arr B) (.arr B) := .lam (.diff .mem (.comp .mem (.diff Q (.conv Q))))

/-- `est(Q) ≜ ∋ − (⟨∋,∋⟩(𝟙 − cor(Q ∪ 𝟙))π₁)`, with the call `cor(S) = dom(π₁S ∩ π₂)` as the prelude elaborates it (`S` the variable 2). -/
def Tm.estDef {B : Obj} (Q : Tm B B) : Tm (.arr B) B :=
  .diff .mem (.comp (.comp (.pair .mem .mem) (.diff .id (.arg (.call [2] (.num `Rel.Programs.prelude.cor.form 1) none [B, B]
    (.dom (.meet (.comp .outl (.var 2)) .outr))) (.join Q .id)))) .outl)

/-- `length ≜ ⦇[0, π₁ succ]⦈`, the base `0` on the universe `u₀`, the step on `u`. -/
def Tm.lengthDef {E : Obj} (u₀ u : Tm .long .long) : Tm (.arr E) .long :=
  .fold (.ran (.comp u₀ (.uni (A := .atom .i64) (zeroCol .i64 rfl)))) (.comp .outl (Tm.cut1 succRow u))

/-- `sum ≜ ⦇[0, plus]⦈` at the atom `t`. -/
def Tm.sumDef {t : QAtomicType} (h : t.ordNum.isSome) (u₀ u : Tm (.atom t) (.atom t)) :
    Tm (.arr (.atom t)) (.atom t) :=
  .fold (.ran (.comp u₀ (.uni (A := .atom t) (zeroCol t h)))) (Tm.cut2 (arithRow "plus") u)

/-- At the universes `u₀`, `u` the coreflexive on `P` (every number, or an initial segment), `length` means the row
    cut to `u`; at every number, the row. -/
theorem Tm.lengthDef_row (ρ : Val) {E : Obj} (u₀ u : Tm .long .long) {P : Obj.long.El → Prop}
    (hP : (∀ x, P x) ∨ Seg .long P) (hU₀ : ∀ x y, u₀.den ρ x y ↔ x = y ∧ P x) (hU : ∀ x y, u.den ρ x y ↔ x = y ∧ P x)
    (x : (Obj.arr E).El) (hx : Short _ x) (w : Obj.long.El) :
    ((Tm.lengthDef u₀ u).den ρ x w ↔ (Tm.comp (.prim lengthRow) u).den ρ x w) ∧
      ((∀ x, P x) → ((Tm.lengthDef u₀ u).den ρ x w ↔ (Tm.prim lengthRow : Tm (.arr E) .long).den ρ x w)) := by
  -- `⦇[0, π₁ succ]⦈`: the counts `0…n` rise from `0`, so all are in `P` iff `n` is
  have hd := count_iff (ranZeroCol_den (t := .i64) rfl u₀ ρ hU₀) hU x hx w
  simp only [Tm.lengthDef, Tm.den, Prim.den_lengthRow, Tm.cut1_succ_den ρ u fun x y h => ((hU x y).1 h).1]
  rw [hd]
  have hx : x.length < 2 ^ 63 := hx
  have hc : (∀ t ≤ x.length, P (Int64.ofNat t)) ↔ P (Int64.ofNat x.length) :=
    chain_in hP Int64.ofNat x.length fun _ => ⟨by decide, fun t ht => by
      rw [Int64.toInt_ofNat_of_lt (by omega), Int64.toInt_ofNat_of_lt (by omega)]; omega⟩
  refine ⟨⟨fun ⟨hp, hw⟩ => Exists.intro _ ⟨rfl, (hU _ _).2 ⟨hw.symm, hc.1 hp⟩⟩, ?_⟩,
    fun hall => ⟨fun h => h.2, fun h => ⟨fun _ _ => hall _, h⟩⟩⟩
  rintro ⟨b, rfl, hbw⟩
  obtain ⟨hw, hp⟩ := (hU _ _).1 hbw
  exact ⟨hc.2 hp, hw.symm⟩

/-- As `Tm.lengthDef_row`, for `sum` at an atom `t` that is not a float (`hf`, the row's `native` atoms: a float's
    `sum` rounds once and has no fold of `plus`). -/
theorem Tm.sumDef_row (ρ : Val) {t : QAtomicType} (h : t.ordNum.isSome) (hf : t ∉ sumRow.native)
    (u₀ u : Tm (.atom t) (.atom t)) {P : (Obj.atom t).El → Prop} (hP : (∀ x, P x) ∨ Seg (.atom t) P)
    (hU₀ : ∀ x y, u₀.den ρ x y ↔ x = y ∧ P x) (hU : ∀ x y, u.den ρ x y ↔ x = y ∧ P x)
    (x : (Obj.arr (.atom t)).El) (hx : Short _ x) (w : (Obj.atom t).El) :
    ((Tm.sumDef h u₀ u).den ρ x w ↔ (Tm.comp (.comp (.arg (.prim mapRow : Tm (.arr (.atom t)) (.arr (.atom t))) u)
      (.prim sumRow : Tm (.arr (.atom t)) (.atom t))) u).den ρ x w) ∧
      ((∀ x, P x) → ((Tm.sumDef h u₀ u).den ρ x w ↔ (Tm.prim sumRow : Tm (.arr (.atom t)) (.atom t)).den ρ x w)) := by
  -- `⦇[0, plus]⦈`: `plus_iff` reads the fold kept in the universe as the row cut to it
  simp only [Tm.sumDef, Tm.den, Tm.argDen, Prim.den_sumRow, sumDen_fold hf,
    Tm.cut2_plus_den ρ u fun x y h => ((hU x y).1 h).1]
  rw [foldDen_start]
  simp only [ranZeroCol_den h u₀ ρ hU₀]
  rw [plus_iff hP hU]
  refine ⟨⟨fun ⟨hE, hw, hf⟩ => ⟨w, ⟨x, (Prim.den_mapRow_corefl hU x x).2 ⟨rfl, hE⟩, hf⟩, (hU _ _).2 ⟨rfl, hw⟩⟩,
    fun ⟨w', ⟨y, hy, hf⟩, hw⟩ => ?_⟩, fun hall => ⟨fun h => h.2.2, fun h => ⟨fun _ _ => hall _, hall _, h⟩⟩⟩
  obtain ⟨rfl, hE⟩ := (Prim.den_mapRow_corefl hU x y).1 hy
  obtain ⟨rfl, hPw⟩ := (hU _ _).1 hw
  exact ⟨hE, hPw, hf⟩

/-- The seed of the `length` and `sum` bodies, the table `{((), 0)}` (its column the literal `0`, `Gen.atom_zero`):
    its one value is `0`. -/
theorem Gen.relVZero_rep (ρ : Val) (a : Obj.one.El) (b : Int64) : Rep.rep (Gen.relV Obj.one (.atom .i64) (USize.ofNat 1)
    (Gen.oneV false (USize.ofNat 1)) (zeroCol .i64 rfl, true)).fst a b ↔ b = 0 :=
  (Tm.relV_den (A := .one) (B := .atom .i64) (n := USize.ofNat 1) ρ (Gen.oneV false (USize.ofNat 1))
      ((zeroCol .i64 rfl : Arr .i64 (USize.ofNat 1)), true) a b).trans ⟨fun ⟨i, _, h⟩ => by rw [← h, zeroCol_row]; rfl,
    fun h => ⟨⟨0, by simp [USize.toNat_ofNat]⟩, Subsingleton.elim _ _, by rw [h, zeroCol_row]; rfl⟩⟩

/-- **`length`'s text means the row** (Q3 = H): `prelude.length.body` at any objects `σ` is `Tm.lengthDef` with both
    universes the variable 1 (`P`, every number or an initial segment), but seeded by `ran` of the literal `{((), 0)}`,
    which carries no universe: so `P 0` is assumed. -/
theorem Tm.lengthDef_den (ph : List QAtomicType) (σ : List Obj) (ρ : Val) {P : Obj.long.El → Prop}
    (hP : (∀ x, P x) ∨ Seg .long P) (hU : ∀ x y, ρ 1 .long .long x y ↔ x = y ∧ P x) (h0 : P 0)
    {t' : Tm ((Obj.arr (Obj.atom .general)).inst ph σ) ((Obj.atom .i64).inst ph σ)}
    (ht : Rel.Programs.prelude.length.body.instObj ph σ = .ok t') (x) (hx : Short _ x) (w : Obj.long.El) :
    (t'.den ρ x w ↔ (Tm.comp (.prim lengthRow) (.var 1 : Tm .long .long)).den ρ x w) ∧
      ((∀ x, P x) →
        (t'.den ρ x w ↔ (Tm.prim lengthRow : Tm ((Obj.arr (Obj.atom .general)).inst ph σ) .long).den ρ x w)) := by
  obtain rfl := Except.ok.inj ht
  have hl := Tm.lengthDef_row ρ (E := (Obj.atom .general).inst ph σ) (.var 1) (.var 1) hP hU hU x hx w
  have hz := ranZeroCol_den (t := .i64) rfl (.var 1) ρ (P := P) hU
  have hb : QAtomicType.ofBits .i64 0 = (0 : Int64) := rfl
  haveI : Nonempty (Obj.inst ph σ Obj.one).El := ⟨()⟩
  simp only [Tm.lengthDef, Tm.den, Tm.argDen, Gen.atom_zero, cast_eq] at hl hz ⊢
  rw [foldDen_start] at hl ⊢
  erw [Prim.den_ranRow]
  simp only [hz, hb, h0, and_true, Core.Rel.inter, Core.Rel.id, Core.Rel.comp, Core.Rel.recip, Gen.relVZero_rep ρ,
    exists_eq_left, exists_eq_left', and_self, exists_const, Tm.cut1, Tm.den] at hl ⊢
  exact hl

/-- **`sum`'s text means the row** (Q3 = H), as `Tm.lengthDef_den`: `Tm.sumDef` at `i64` (not a float, so `sumRow`
    has a fold) with both universes the variable 0. -/
theorem Tm.sumDef_den (ph : List QAtomicType) (σ : List Obj) (ρ : Val) {P : (Obj.atom .i64).El → Prop}
    (hP : (∀ x, P x) ∨ Seg (.atom .i64) P) (hU : ∀ x y, ρ 0 (.atom .i64) (.atom .i64) x y ↔ x = y ∧ P x) (h0 : P 0)
    {t' : Tm ((Obj.arr (Obj.atom .i64)).inst ph σ) ((Obj.atom .i64).inst ph σ)}
    (ht : Rel.Programs.prelude.sum.body.instObj ph σ = .ok t') (x) (hx : Short _ x) (w : (Obj.atom .i64).El) :
    (t'.den ρ x w ↔ (Tm.comp (.comp (.arg (.prim mapRow : Tm (.arr (.atom .i64)) (.arr (.atom .i64)))
      (.var 0 : Tm (.atom .i64) (.atom .i64))) (.prim sumRow : Tm (.arr (.atom .i64)) (.atom .i64))) (.var 0)).den ρ x w) ∧
      ((∀ x, P x) → (t'.den ρ x w ↔ (Tm.prim sumRow : Tm (.arr (.atom .i64)) (.atom .i64)).den ρ x w)) := by
  obtain rfl := Except.ok.inj ht
  have hl := Tm.sumDef_row ρ (t := .i64) rfl (by decide) (.var 0) (.var 0) hP hU hU x hx w
  have hz := ranZeroCol_den (t := .i64) rfl (.var 0) ρ (P := P) hU
  have hb : QAtomicType.ofBits .i64 0 = (0 : Int64) := rfl
  haveI : Nonempty (Obj.inst ph σ Obj.one).El := ⟨()⟩
  simp only [Tm.sumDef, Tm.den, Tm.argDen, Gen.atom_zero, cast_eq] at hl hz ⊢
  rw [foldDen_start] at hl ⊢
  erw [Prim.den_ranRow]
  simp only [hz, hb, h0, and_true, Core.Rel.inter, Core.Rel.id, Core.Rel.comp, Core.Rel.recip, Gen.relVZero_rep ρ,
    exists_eq_left, exists_eq_left', and_self, exists_const, Tm.cut2, Tm.den] at hl ⊢
  exact hl

end Rel.Lang
