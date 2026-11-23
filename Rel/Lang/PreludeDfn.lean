module

public import Rel.Lang.DfnLaw

@[expose] public section

/-! The definitions of `flat`, `foldI`, `dom`, `ran`, `nil`, `front` (`Programs/Prelude.lean`) mean their rows (B10c2):
    each term is the index of the matching `DfnCut` constructor, and the theorem specialises `Tm.dfnCut_den`
    at the trivial universe (these constructors have `uni = none`, so `hUs` is vacuous). `length` and `sum` (C3)
    carry the universes of their base and step, so their theorems take the universe hypotheses themselves. -/

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

theorem Tm.flatDef_den (ρ : Val) {I A B : Obj} (R : Tm I (.prod A B)) (x : (Obj.prod I A).El) (hx : Short _ x) (w : B.El) :
    (Tm.flatDef R).den ρ x w ↔ (Tm.arg (.prim flatRow) R).den ρ x w :=
  (Tm.dfnCut_den (.flat R) ρ (P := fun _ => True) (Or.inl fun _ => trivial) (by simp [DfnCut.uni]) x hx w).2
    (fun _ => trivial)

theorem Tm.foldIDef_den (ρ : Val) {I E V : Obj} (e : Tm I (.prod V V)) (S : Tm (.prod (.prod I V) E) (.prod I V))
    (x : (Obj.prod I (.arr E)).El) (hx : Short _ x) (w : V.El) :
    (Tm.foldIDef e S).den ρ x w ↔ (Tm.arg (.arg (.prim foldIRow) e) S).den ρ x w :=
  (Tm.dfnCut_den (.foldI e S) ρ (P := fun _ => True) (Or.inl fun _ => trivial) (by simp [DfnCut.uni]) x hx w).2
    (fun _ => trivial)

theorem Tm.domDef_den (ρ : Val) {A B : Obj} (R : Tm A B) (x : A.El) (hx : Short A x) (w : A.El) :
    (Tm.domDef R).den ρ x w ↔ (Tm.dom R).den ρ x w :=
  (Tm.dfnCut_den (.dom R) ρ (P := fun _ => True) (Or.inl fun _ => trivial) (by simp [DfnCut.uni]) x hx w).2
    (fun _ => trivial)

theorem Tm.ranDef_den (ρ : Val) {A B : Obj} (R : Tm A B) (x : B.El) (hx : Short B x) (w : B.El) :
    (Tm.ranDef R).den ρ x w ↔ (Tm.ran R).den ρ x w :=
  (Tm.dfnCut_den (.ran R) ρ (P := fun _ => True) (Or.inl fun _ => trivial) (by simp [DfnCut.uni]) x hx w).2
    (fun _ => trivial)

theorem Tm.nilDef_den (ρ : Val) {A B : Obj} (x : A.El) (hx : Short A x) (w : (Obj.arr B).El) :
    (Tm.nilDef (A := A) (B := B)).den ρ x w ↔ (Tm.nil (A := A) (B := B)).den ρ x w :=
  (Tm.dfnCut_den (.nil (A := A) (B := B)) ρ (P := fun _ => True) (Or.inl fun _ => trivial) (by simp [DfnCut.uni]) x hx
    w).2 (fun _ => trivial)

theorem Tm.frontDef_den (ρ : Val) {B : Obj} (Q : Tm B B) (x : (Obj.arr B).El) (hx : Short _ x) (w : (Obj.arr B).El) :
    (Tm.frontDef Q).den ρ x w ↔ (Tm.front (pairTest Q)).den ρ x w :=
  (Tm.dfnCut_den (.front Q) ρ (P := fun _ => True) (Or.inl fun _ => trivial) (by simp [DfnCut.uni]) x hx w).2
    (fun _ => trivial)

/-- `length ≜ ⦇[0, π₁ succ]⦈`, the base `0` on the universe `u₀`, the step on `u`. -/
def Tm.lengthDef {E : Obj} (u₀ u : Tm .long .long) : Tm (.arr E) .long :=
  .fold (zeroTm (t := .i64) rfl u₀) (.comp .outl (Tm.cut1 succRow u))

/-- `sum ≜ ⦇[0, plus]⦈` at the atom `t`. -/
def Tm.sumDef {t : QAtomicType} (h : t.ordNum.isSome) (u₀ u : Tm (.atom t) (.atom t)) :
    Tm (.arr (.atom t)) (.atom t) :=
  .fold (zeroTm h u₀) (Tm.cut2 (arithRow "plus") u)

/-- At the universes `u₀`, `u` the coreflexive on `P` (every number, or an initial segment), `length` means the row
    cut to `u`; at every number, the row. -/
theorem Tm.lengthDef_den (ρ : Val) {E : Obj} (u₀ u : Tm .long .long) {P : Obj.long.El → Prop}
    (hP : (∀ x, P x) ∨ Seg .long P) (hU₀ : ∀ x y, u₀.den ρ x y ↔ x = y ∧ P x) (hU : ∀ x y, u.den ρ x y ↔ x = y ∧ P x)
    (x : (Obj.arr E).El) (hx : Short _ x) (w : Obj.long.El) :
    ((Tm.lengthDef u₀ u).den ρ x w ↔ (Tm.comp (.prim lengthRow) u).den ρ x w) ∧
      ((∀ x, P x) → ((Tm.lengthDef u₀ u).den ρ x w ↔ (Tm.prim lengthRow : Tm (.arr E) .long).den ρ x w)) :=
  Tm.dfnCut_den (.length u₀ u) ρ hP (fun a b h => by
    obtain ⟨rfl, rfl⟩ := Option.some.inj h
    exact ⟨hU₀, hU⟩) x hx w

/-- As `Tm.lengthDef_den`, for `sum` at an atom `t` that is not a float (`hf`, the row's `native` atoms: a float's
    `sum` rounds once and has no fold of `plus`). -/
theorem Tm.sumDef_den (ρ : Val) {t : QAtomicType} (h : t.ordNum.isSome) (hf : t ∉ floatAtoms)
    (u₀ u : Tm (.atom t) (.atom t)) {P : (Obj.atom t).El → Prop} (hP : (∀ x, P x) ∨ Seg (.atom t) P)
    (hU₀ : ∀ x y, u₀.den ρ x y ↔ x = y ∧ P x) (hU : ∀ x y, u.den ρ x y ↔ x = y ∧ P x)
    (x : (Obj.arr (.atom t)).El) (hx : Short _ x) (w : (Obj.atom t).El) :
    ((Tm.sumDef h u₀ u).den ρ x w ↔ (Tm.comp (.comp (.arg (.prim mapRow : Tm (.arr (.atom t)) (.arr (.atom t))) u)
      (.prim sumRow : Tm (.arr (.atom t)) (.atom t))) u).den ρ x w) ∧
      ((∀ x, P x) → ((Tm.sumDef h u₀ u).den ρ x w ↔ (Tm.prim sumRow : Tm (.arr (.atom t)) (.atom t)).den ρ x w)) :=
  Tm.dfnCut_den (.sum h hf u₀ u) ρ hP (fun a b h => by
    obtain ⟨rfl, rfl⟩ := Option.some.inj h
    exact ⟨hU₀, hU⟩) x hx w

/-- At the universes `u₀`, `u` of `length` (`P` every number, or an initial segment), `asc(P)`'s definition, with the
    count `Tm.lengthDef u₀ u`, means the row cut to `P` where `dom P` has a short list ascending by `Obj.lt`; at every
    number, the row (`ascDen`, `Prim.den_ascRow`). -/
theorem Tm.ascDef_den (ρ : Val) {B : Obj} (Pa : Tm B B) (u₀ u : Tm .long .long) {P : Obj.long.El → Prop}
    (hP : (∀ x, P x) ∨ Seg .long P) (hU₀ : ∀ x y, u₀.den ρ x y ↔ x = y ∧ P x) (hU : ∀ x y, u.den ρ x y ↔ x = y ∧ P x)
    (hp : ∃ ys : List B.El, ys.Pairwise B.lt ∧ (∀ b, b ∈ ys ↔ ∃ c, Pa.den ρ b c) ∧ ys.length < 2 ^ 63) (j : Int64)
    (a : B.El) :
    ((Tm.ascDef Pa (Tm.lengthDef u₀ u)).den ρ j a ↔ P j ∧ ascDen B (fun b => ∃ c, Pa.den ρ b c) j a) ∧
      ((∀ x, P x) → ((Tm.ascDef Pa (Tm.lengthDef u₀ u)).den ρ j a ↔ ascDen B (fun b => ∃ c, Pa.den ρ b c) j a)) := by
  have h := Tm.ascDef_of_len ρ Pa (Tm.lengthDef u₀ u) P (fun zs hs w => by
    rw [(Tm.lengthDef_den ρ u₀ u hP hU₀ hU zs hs w).1]
    simp only [Tm.den, Prim.den_lengthRow, Core.Rel.comp, hU]
    constructor
    · rintro ⟨b, rfl, rfl, hb⟩; exact ⟨rfl, hb⟩
    · rintro ⟨rfl, hb⟩; exact ⟨_, rfl, rfl, hb⟩) hp j a
  exact ⟨h, fun hall => by rw [h]; exact ⟨fun h => h.2, fun h => ⟨hall j, h⟩⟩⟩

end Rel.Lang
