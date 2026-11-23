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

/-- Pointwise `estDen`: `b` of `xs` unless some `c` of `xs` is outside `Q ∪ 𝟙` at `(b, c)`; from `Tm.est_den`. -/
theorem Tm.estDef_row (ρ : Val) {B : Obj} (Q : Tm B B) : (Tm.estDef Q).den ρ = (Tm.est (pairTest Q)).den ρ := by
  rw [Tm.est_den]
  funext xs b
  apply propext
  simp [Tm.estDef, pairTest, Tm.den, Tm.argDen, Val.args, Val.bind, estDen, Tm.dom_den, Core.Rel.id, Core.Rel.graph, Core.Rel.rpair]
  intro hb
  constructor
  · intro h c hc hne
    rcases (h c b c hb hc rfl rfl).2.2.1 with h | h
    · exact h
    · exact absurd h.symm hne
  · rintro h x a c ha hc rfl rfl
    by_cases e : c = a
    · subst e; simp
    · exact ⟨rfl, rfl, Or.inl (h c hc e), rfl, fun hn => absurd (h c hc e) hn⟩

/-- `est`'s text means the row (Q3 = H), as `Tm.frontDef_den`: `prelude.est.body` at `β = general`, parameter `Q` the
    variable 1, means `est(τ(Q))` at any objects `σ`. -/
theorem Tm.estDef_den (ph : List QAtomicType) (σ : List Obj) (ρ : Val) {t' : Tm (Obj.arr ((Obj.atom .general).inst ph σ))
    ((Obj.atom .general).inst ph σ)} (ht : Rel.Programs.prelude.est.body.instObj ph σ = .ok t') :
    t'.den ρ = (Tm.est (pairTest (.var 1 : Tm ((Obj.atom .general).inst ph σ) ((Obj.atom .general).inst ph σ)))).den ρ := by
  obtain rfl : Tm.estDef (.var 1) = t' := Except.ok.inj ht
  exact Tm.estDef_row ρ _

theorem Tm.flatDef_row (ρ : Val) {I A B : Obj} (R : Tm I (.prod A B)) (x : (Obj.prod I A).El) (hx : Short _ x) (w : B.El) :
    (Tm.flatDef R).den ρ x w ↔ (Tm.arg (.prim flatRow) R).den ρ x w := by
  -- `⟨π₁R,π₂⟩dom(π₁π₁ ∩ π₂)π₁π₂` is `flatDen` (`Tm.flat_den`), the row's meaning at every object
  have hd := congrFun (congrFun (Tm.flat_den ρ R) x) w
  simp only [Tm.flatDef, ↓Tm.dom_den, Tm.dom_den, Tm.den, Tm.argDen, Prim.den_flatRow] at hd ⊢
  exact hd.to_iff

/-- **`flat`'s text means the row** (Q3 = H): `prelude.flat.body` (placeholders `general`, `u1`, `u8` of `ι`, `α`, `β`;
    `R` the variable 3) at any objects `σ` means `flat(R)` there. The body groups `flatDef`'s composition the other way
    (`Core.Rel` composition is associative). -/
theorem Tm.flatDef_den (ph : List QAtomicType) (σ : List Obj) (ρ : Val) {t' : Tm (((Obj.atom .general).prod
    (Obj.atom .u1)).inst ph σ) ((Obj.atom .u8).inst ph σ)} (ht : Rel.Programs.prelude.flat.body.instObj ph σ = .ok t')
    (x) (hx : Short _ x) (w) : t'.den ρ x w ↔ (Tm.arg (.prim flatRow) (.var 3 : Tm ((Obj.atom .general).inst ph σ)
      (.prod ((Obj.atom .u1).inst ph σ) ((Obj.atom .u8).inst ph σ)))).den ρ x w := by
  obtain rfl := Except.ok.inj ht
  rw [← Tm.flatDef_row ρ (.var 3) x hx w]
  show Tm.den ρ (.comp (.comp (.comp _ (Tm.dom _)) .outl) .outr) x w ↔ Tm.den ρ (.comp _ (.comp (Tm.dom _) (.comp .outl .outr))) x w
  generalize Tm.dom _ = D
  simp only [Tm.den, Core.Rel.comp_assoc]
  exact Iff.rfl

theorem Tm.foldIDef_row (ρ : Val) {I E V : Obj} (e : Tm I (.prod V V)) (S : Tm (.prod (.prod I V) E) (.prod I V))
    (x : (Obj.prod I (.arr E)).El) (hx : Short _ x) (w : V.El) :
    (Tm.foldIDef e S).den ρ x w ↔ (Tm.arg (.arg (.prim foldIRow) e) S).den ρ x w := by
  -- `(π₁π₁° ∩ π₂⦇ran⟨𝟙,eπ₂⟩, S ∩ π₁π₁π₁°⦈)π₂` is `foldIDen` by definition, the row's meaning at every object
  simp only [Tm.foldIDef, ↓Tm.ran_den, Tm.ran_den, Tm.den, Tm.argDen, Prim.den_foldIRow]

/-- **`foldI`'s text means the row** (Q3 = H): `prelude.foldI.body` (placeholders `general`, `u1`, `u8` of `ι`, `β`, `α`;
    `e`, `S` the variables 3, 4) at any objects `σ` means `foldI(e, S)` there, where its universe variables 0, 1 (of `ι`,
    `β`) are the full universes `𝟙`: the body restricts `π₁π₁°` and the step to them, and seeds the fold with `⊤`
    through `Tm.uni` of one value, which `foldDen` reads only as the set `∃ a, Te a v` (`foldDen_start`). -/
theorem Tm.foldIDef_den (ph : List QAtomicType) (σ : List Obj) (ρ : Val)
    (hU0 : ∀ x y, ρ 0 ((Obj.atom .general).inst ph σ) ((Obj.atom .general).inst ph σ) x y ↔ x = y)
    (hU1 : ∀ x y, ρ 1 ((Obj.atom .u1).inst ph σ) ((Obj.atom .u1).inst ph σ) x y ↔ x = y)
    {t' : Tm (((Obj.atom .general).prod (Obj.atom .u8).arr).inst ph σ) ((Obj.atom .u1).inst ph σ)}
    (ht : Rel.Programs.prelude.foldI.body.instObj ph σ = .ok t')
    (x) (hx : Short _ x) (w) : t'.den ρ x w ↔ (Tm.arg (.arg (.prim foldIRow)
      (.var 3 : Tm ((Obj.atom .general).inst ph σ) (.prod ((Obj.atom .u1).inst ph σ) ((Obj.atom .u1).inst ph σ))))
      (.var 4 : Tm (.prod (.prod ((Obj.atom .general).inst ph σ) ((Obj.atom .u1).inst ph σ)) ((Obj.atom .u8).inst ph σ))
        (.prod ((Obj.atom .general).inst ph σ) ((Obj.atom .u1).inst ph σ)))).den ρ x w := by
  obtain rfl := Except.ok.inj ht
  rw [← Tm.foldIDef_row ρ (.var 3) (.var 4) x hx w]
  have hran := @Prim.den_ranRow
  simp only [ranRow] at hran
  have hRU : (Core.Rel.id (Obj.inst ph σ ((Obj.atom .general).prod (Obj.atom .u1))).El).inter
      ((((ρ 0 ((Obj.atom .general).inst ph σ) ((Obj.atom .general).inst ph σ)).rpair
        (Core.Rel.top.comp (ρ 1 ((Obj.atom .u1).inst ph σ) ((Obj.atom .u1).inst ph σ)))).recip).comp
      ((ρ 0 ((Obj.atom .general).inst ph σ) ((Obj.atom .general).inst ph σ)).rpair
        (Core.Rel.top.comp (ρ 1 ((Obj.atom .u1).inst ph σ) ((Obj.atom .u1).inst ph σ)))).recip.recip) =
      Core.Rel.id (Obj.inst ph σ ((Obj.atom .general).prod (Obj.atom .u1))).El := by
    funext p q
    apply propext
    simp [Core.Rel.id, Core.Rel.inter, Core.Rel.comp, Core.Rel.recip, Core.Rel.rpair, Core.Rel.top, hU0, hU1]
    rintro rfl; rfl
  have key : ∀ {E V : Obj} (Te Te' : Core.Rel V.El V.El) (TS : Core.Rel (Obj.prod V E).El V.El),
      (∀ v, (∃ a, Te a v) ↔ ∃ a, Te' a v) → foldDen Te TS = foldDen Te' TS := fun Te Te' TS h => by
    funext xs w; apply propext; rw [foldDen_start, foldDen_start]; simp only [h]
  simp only [Tm.foldIDef, Tm.den, Tm.argDen, hran, hRU, cast_eq, Core.Rel.comp_id, Core.Rel.id_comp, Core.Rel.comp_assoc]
  rw [key (E := Obj.inst ph σ (Obj.atom .u8)) (V := Obj.inst ph σ ((Obj.atom .general).prod (Obj.atom .u1))) _ (Tm.den ρ (Tm.ran (Tm.pair Tm.id (Tm.comp (Tm.var 3 : Tm (Obj.inst ph σ (Obj.atom .general)) (.prod (Obj.inst ph σ (Obj.atom .u1)) (Obj.inst ph σ (Obj.atom .u1)))) Tm.outr) : Tm (Obj.inst ph σ (Obj.atom .general)) (Obj.inst ph σ ((Obj.atom .general).prod (Obj.atom .u1)))) : Tm (Obj.inst ph σ ((Obj.atom .general).prod (Obj.atom .u1))) (Obj.inst ph σ ((Obj.atom .general).prod (Obj.atom .u1))))) _ ?hseed]
  · exact Iff.rfl
  case hseed =>
    intro v
    simp only [Tm.ran_den, Tm.den, Core.Rel.id, Core.Rel.inter, Core.Rel.comp, Core.Rel.recip, Core.Rel.top, Core.Rel.graph, Core.Rel.rpair]
    simp only [exists_eq_left, true_and]
    exact ⟨fun ⟨_, ⟨_, _, hq⟩, _⟩ => hq, fun hq => ⟨_, ⟨⟨0, by simp [USize.toNat_ofNat]⟩, rfl, hq⟩, ⟨0, by simp [USize.toNat_ofNat]⟩, rfl, hq⟩⟩

theorem Tm.domDef_row (ρ : Val) {A B : Obj} (R : Tm A B) (x : A.El) (hx : Short A x) (w : A.El) :
    (Tm.domDef R).den ρ x w ↔ (Tm.dom R).den ρ x w := by
  -- `⟨𝟙,R⟩π₁` keeps `a` with some `b` of `R`: `𝟙 ∩ R R°` (`Prim.den_domRow`), the row's meaning at every object
  simp only [Tm.domDef, Tm.dom, Tm.den, Tm.argDen, Prim.den_domRow, Core.Rel.comp, Core.Rel.rpair, Core.Rel.inter,
    Core.Rel.recip, Core.Rel.graph, Core.Rel.id]
  constructor
  · rintro ⟨⟨a, b⟩, ⟨rfl, hb⟩, rfl⟩; exact ⟨rfl, b, hb, hb⟩
  · rintro ⟨rfl, b, hb, -⟩; exact ⟨(x, b), ⟨rfl, hb⟩, rfl⟩

/-- **`dom`'s text means the row** (Q3 = H): the body the prelude elaborates, `prelude.dom.body` (built at the
    placeholders `general`, `u1` of `α`, `β`; its parameter `R` the variable 2), at any objects `σ` (`Tm.instObj`,
    any `ph`, as `convTm_instObj_den`), means `dom(R)` there. -/
theorem Tm.domDef_den (ph : List QAtomicType) (σ : List Obj) (ρ : Val) {t' : Tm ((Obj.atom .general).inst ph σ)
    ((Obj.atom .general).inst ph σ)} (ht : Rel.Programs.prelude.dom.body.instObj ph σ = .ok t') (x) (hx : Short _ x)
    (w) : t'.den ρ x w ↔ (Tm.dom (.var 2 : Tm ((Obj.atom .general).inst ph σ) ((Obj.atom .u1).inst ph σ))).den ρ x w := by
  obtain rfl : Tm.domDef (.var 2) = t' := Except.ok.inj ht
  exact Tm.domDef_row ρ _ x hx w

theorem Tm.ranDef_row (ρ : Val) {A B : Obj} (R : Tm A B) (x : B.El) (hx : Short B x) (w : B.El) :
    (Tm.ranDef R).den ρ x w ↔ (Tm.ran R).den ρ x w := by
  -- `dom(R°)` is `𝟙 ∩ R° R°°` (`Prim.den_domRow` at `R°`), `ranRow`'s meaning (`Prim.den_ranRow`)
  simp only [Tm.ranDef, Tm.dom, Tm.ran, Tm.den, Tm.argDen, Prim.den_domRow, Prim.den_ranRow]

theorem Tm.nilDef_row (ρ : Val) {A B : Obj} (x : A.El) (hx : Short A x) (w : (Obj.arr B).El) :
    (Tm.nilDef (A := A) (B := B)).den ρ x w ↔ (Tm.nil (A := A) (B := B)).den ρ x w := by
  -- `Λ(𝟘)` maps every source to the list of no elements, `[]` (`Prim.den_nilRow`)
  simp only [Tm.nilDef, Tm.nil, Tm.den, Prim.den_nilRow, nilDen]
  rw [lamDen_iff]
  constructor
  · rintro ⟨-, h⟩; exact List.eq_nil_iff_forall_not_mem.2 fun b hb => (h b).1 hb
  · rintro rfl; exact ⟨List.Pairwise.nil, fun b => iff_of_false (List.not_mem_nil) fun h => h⟩

theorem Tm.frontDef_row (ρ : Val) {B : Obj} (Q : Tm B B) (x : (Obj.arr B).El) (hx : Short _ x) (w : (Obj.arr B).El) :
    (Tm.frontDef Q).den ρ x w ↔ (Tm.front (pairTest Q)).den ρ x w := by
  -- `∋ − ∋ (Q − Q°)` keeps `c` of `x` that no `b` of `x` beats strictly, `frontDen` of `τ(Q)` on its diagonal
  have hτ : ∀ a b, (pairTest Q).den ρ (a, b) (a, b) ↔ Q.den ρ a b := fun a b => by
    simp [pairTest, Tm.dom_den, Tm.den, Core.Rel.comp, Core.Rel.inter, Core.Rel.recip, Core.Rel.graph, Core.Rel.id]
  rw [Tm.front_den]
  simp only [Tm.frontDef, Tm.den, frontDen]
  rw [lamDen_iff, lamDen_iff]
  refine and_congr_right fun _ => forall_congr' fun c => iff_congr Iff.rfl ?_
  simp only [Core.Rel.diff, Core.Rel.comp, Core.Rel.recip, memDen, hτ]

/-- `ran`'s text means the row (Q3 = H), as `Tm.domDef_den`: its body at `α = general`, `β = u1`, parameter `R` the
    variable 2. -/
theorem Tm.ranDef_den (ph : List QAtomicType) (σ : List Obj) (ρ : Val) {t' : Tm ((Obj.atom .u1).inst ph σ)
    ((Obj.atom .u1).inst ph σ)} (ht : Rel.Programs.prelude.ran.body.instObj ph σ = .ok t') (x) (hx : Short _ x)
    (w) : t'.den ρ x w ↔ (Tm.ran (.var 2 : Tm ((Obj.atom .general).inst ph σ) ((Obj.atom .u1).inst ph σ))).den ρ x w := by
  obtain rfl : Tm.ranDef (.var 2) = t' := Except.ok.inj ht
  exact Tm.ranDef_row ρ _ x hx w

/-- `nil`'s text means the row (Q3 = H), as `Tm.domDef_den`. -/
theorem Tm.nilDef_den (ph : List QAtomicType) (σ : List Obj) (ρ : Val) {t' : Tm ((Obj.atom .general).inst ph σ)
    ((Obj.arr (Obj.atom .u1)).inst ph σ)} (ht : Rel.Programs.prelude.nil.body.instObj ph σ = .ok t') (x) (hx : Short _ x)
    (w) : t'.den ρ x w ↔ (Tm.nil : Tm ((Obj.atom .general).inst ph σ) ((Obj.arr (Obj.atom .u1)).inst ph σ)).den ρ x w := by
  obtain rfl : Tm.nilDef = t' := Except.ok.inj ht
  exact Tm.nilDef_row ρ x hx w

/-- `front`'s text means the row (Q3 = H), as `Tm.ranDef_den`: its body at `β = u1`, parameter `Q` the variable 1. -/
theorem Tm.frontDef_den (ph : List QAtomicType) (σ : List Obj) (ρ : Val) {t' : Tm ((Obj.arr (Obj.atom .general)).inst ph σ)
    ((Obj.arr (Obj.atom .general)).inst ph σ)} (ht : Rel.Programs.prelude.front.body.instObj ph σ = .ok t') (x)
    (hx : Short _ x) (w) : t'.den ρ x w ↔
      (Tm.front (pairTest (.var 1 : Tm ((Obj.atom .general).inst ph σ) ((Obj.atom .general).inst ph σ)))).den ρ x w := by
  obtain rfl : Tm.frontDef (.var 1) = t' := Except.ok.inj ht
  exact Tm.frontDef_row ρ _ x hx w

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

/-- At the universes `u₀`, `u` of `length` (`P` every number, or an initial segment), `asc(P)`'s definition, with the
    count `Tm.lengthDef u₀ u`, means the row cut to `P` where `dom P` has a short list ascending by `Obj.lt`; at every
    number, the row (`ascDen`, `Prim.den_ascRow`); `G` is `>` on `dom Pa` (`hG`). -/
theorem Tm.ascDef_row (ρ : Val) {B : Obj} (Pa G : Tm B B) (u₀ u : Tm .long .long) {P : Obj.long.El → Prop}
    (hG : ∀ x y, (∃ c, Pa.den ρ x c) → (∃ c, Pa.den ρ y c) → (G.den ρ x y ↔ B.lt y x))
    (hP : (∀ x, P x) ∨ Seg .long P) (hU₀ : ∀ x y, u₀.den ρ x y ↔ x = y ∧ P x) (hU : ∀ x y, u.den ρ x y ↔ x = y ∧ P x)
    (hp : ∃ ys : List B.El, ys.Pairwise B.lt ∧ (∀ b, b ∈ ys ↔ ∃ c, Pa.den ρ b c) ∧ ys.length < 2 ^ 63) (j : Int64)
    (a : B.El) :
    ((Tm.ascDef Pa G (Tm.lengthDef u₀ u)).den ρ j a ↔ P j ∧ ascDen B (fun b => ∃ c, Pa.den ρ b c) j a) ∧
      ((∀ x, P x) → ((Tm.ascDef Pa G (Tm.lengthDef u₀ u)).den ρ j a ↔ ascDen B (fun b => ∃ c, Pa.den ρ b c) j a)) := by
  have h := Tm.ascDef_of_len ρ Pa G (Tm.lengthDef u₀ u) P hG (fun zs hs w => by
    rw [(Tm.lengthDef_row ρ u₀ u hP hU₀ hU zs hs w).1]
    simp only [Tm.den, Prim.den_lengthRow, Core.Rel.comp, hU]
    constructor
    · rintro ⟨b, rfl, rfl, hb⟩; exact ⟨rfl, hb⟩
    · rintro ⟨rfl, hb⟩; exact ⟨_, rfl, rfl, hb⟩) hp j a
  exact ⟨h, fun hall => by rw [h]; exact ⟨fun h => h.2, fun h => ⟨hall j, h⟩⟩⟩

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
