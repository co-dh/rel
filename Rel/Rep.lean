/-
  A table read in the allegory of sets: `rep R` is the relation `R.Holds` as a `Rel(Set)` arrow, and `Reps` says
  what a runtime `Rel` computes agrees with a `Rel(Set)` arrow on what its context knows.
-/
import Rel.Core.Rel
import Rel.Run.Lang.Lazy

namespace Rel.Rep

open Tab
open scoped Rel.Core.Rel
open Rel.Core.Rel hiding id comp recip inter union zero le inl inr junc

variable {A B C : Obj}

/-- The `Rel(Set)` arrow a `Rel` denotes: `x` to `y` when some row holds `(x, y)`. -/
def rep (R : Tab A B) : Core.Rel (A.El) (B.El) := R.Holds

/-- The coreflexives `K` confines a relation's two sides to: `𝟙` on an unknown side, the coreflexive on `c`'s
    values on a known one. -/
def _root_.Rel.Known.den (K : Known A B) : Core.Rel A.El A.El × Core.Rel B.El B.El :=
  (K.dom.elim (𝟙 _) fun c => corefl fun x => ∃ i, c.2.row i = x,
   K.ran.elim (𝟙 _) fun c => corefl fun y => ∃ i, c.2.row i = y)

/-- `r` represents `R` in the context `K`, as `run` computes it there: a table agrees with `R` on `K`'s sides
    only, since `Gen.Sound` fixes a term only at the keys it is given and a caller that passes `K.ran` cuts the
    result itself; a `tab none` (a run past capacity) represents anything. -/
def _root_.Rel.Rel.Reps (K : Known A B) : Rel A B → Core.Rel A.El B.El → Prop
  | .tab (.error _), _ => True
  | .tab (.ok t), R => K.den.1 ≫ rep t ≫ K.den.2 = K.den.1 ≫ R ≫ K.den.2
  | .lazy f, R => (f K).Reps K R
  | .bits g w o x ra y rc, R => match Tab.ofBits g w o x ra y rc with
    | .error _ => True
    | .ok t => K.den.1 ≫ rep t ≫ K.den.2 = K.den.1 ≫ R ≫ K.den.2

/-- `rep R x y` is `R.Holds x y`, by definition. -/
theorem rep_apply (R : Tab A B) (x : A.El) (y : B.El) : rep R x y = R.Holds x y := rfl

/-- Where `P ≫ R ≫ 𝟙 = P ≫ S ≫ 𝟙` and `x` is a key of the coreflexive `P`, `R` and `S` agree at `x`. -/
theorem atKey {P : Core.Rel A.El A.El} {R S : Core.Rel A.El B.El} (hP : ∀ x y, P x y → x = y)
    (E : P ≫ R ≫ 𝟙 _ = P ≫ S ≫ 𝟙 _) {x : A.El} (hx : P x x) (y : B.El) : R x y ↔ S x y := by
  have f : ∀ R' S' : Core.Rel A.El B.El, P ≫ R' ≫ 𝟙 _ = P ≫ S' ≫ 𝟙 _ → R' x y → S' x y := by
    intro R' S' E' r
    have h : (P ≫ R' ≫ 𝟙 _) x y := ⟨x, hx, y, r, rfl⟩
    rw [E'] at h; obtain ⟨z, p, w, s, e⟩ := h; cases hP x z p; cases (e : w = y); exact s
  exact ⟨f R S E, f S R E.symm⟩

/-- What a context knows of each side is a coreflexive. -/
theorem _root_.Rel.Known.cor (K : Known A B) : (∀ x y, K.den.1 x y → x = y) ∧ (∀ x y, K.den.2 x y → x = y) := by
  have e : ∀ {C : Obj} (o : Option ((n : USize) × Vals C n)) (x y : C.El),
      o.elim (𝟙 _) (fun c => corefl fun x => ∃ i, c.2.row i = x) x y → x = y := fun o x y h => by
    cases o with
    | none => exact h
    | some _ => exact h.1
  exact ⟨e K.dom, e K.ran⟩

/-- Inside `K`'s sides, `X` cut to them is `X`. -/
theorem restrict (K : Known A B) {X : Core.Rel A.El B.El} {x : A.El} {y : B.El} (hx : K.den.1 x x)
    (hy : K.den.2 y y) : (K.den.1 ≫ X ≫ K.den.2) x y ↔ X x y :=
  ⟨fun ⟨a, p, b, r, q⟩ => by cases K.cor.1 x a p; cases K.cor.2 b y q; exact r, fun r => ⟨x, hx, y, r, hy⟩⟩

/-- A coreflexive's row values: on the keys of `D`, every key is one of `D.val`'s rows. -/
theorem keyRow {D : Tab A A} {x : A.El} (h : rep D x x) : ∃ i, D.val.row i = x :=
  let ⟨i, _, e⟩ := h; ⟨i, e⟩

theorem rowKey {D : Tab A A} (hD : ∀ x y, rep D x y → x = y) {x : A.El} :
    (∃ i, D.val.row i = x) → rep D x x := by
  rintro ⟨i, rfl⟩
  have h : rep D (D.key.row i) (D.val.row i) := ⟨i, rfl, rfl⟩
  rw [hD _ _ h] at h; exact h

/-- A relation's key rows are the keys its `rep` relates. -/
theorem keyRowRep (U : Tab A B) (a : A.El) : (∃ p, U.key.row p = a) ↔ ∃ b, rep U a b :=
  ⟨fun ⟨p, e⟩ => ⟨U.val.row p, p, e, rfl⟩, fun ⟨_, p, e, _⟩ => ⟨p, e⟩⟩

/-- The range coreflexive of `R`, read pointwise. -/
theorem ran_iff (R : Core.Rel A.El B.El) (y y' : B.El) :
    (𝟙 _ ∩ R° ≫ R°° : Core.Rel B.El B.El) y y' ↔ y = y' ∧ ∃ x, R x y ∧ R x y' := Iff.rfl

/-- `⟨X,Y⟩ = Xπ₁° ∩ Yπ₂°`: the converse `convTm` gives two sides each read through one projection
    (`Proj.meet`), which is how `(P×Q)° = P°×Q°` runs on demand. -/
theorem rpair_eq_meet_proj {α β γ : Type} (X : Core.Rel γ α) (Y : Core.Rel γ β) :
    (X ≫ (graph Prod.fst : Core.Rel (α × β) α)° ∩ Y ≫ (graph Prod.snd : Core.Rel (α × β) β)°) = rpair X Y :=
  funext fun _ => funext fun _ => propext
    ⟨fun ⟨⟨_, ha, ea⟩, ⟨_, hb, eb⟩⟩ => ⟨ea ▸ ha, eb ▸ hb⟩, fun ⟨ha, hb⟩ => ⟨⟨_, ha, rfl⟩, ⟨_, hb, rfl⟩⟩⟩

/-- `Xf° ∩ Yf° = (X∩Y)f°` for a map `f`: two sides read through one projection stay so (`Proj.meet`). -/
theorem meet_comp_conv_graph {α β γ : Type} (f : α → β) (X Y : Core.Rel γ β) :
    (X ≫ (graph f)° ∩ Y ≫ (graph f)°) = (X ∩ Y) ≫ (graph f)° :=
  funext fun _ => funext fun a => propext
    ⟨fun ⟨⟨w, hx, ex⟩, ⟨w', hy, ey⟩⟩ =>
      ⟨w, ⟨hx, ((show w' = f a from ey).trans (show w = f a from ex).symm) ▸ hy⟩, ex⟩,
      fun ⟨_, ⟨hx, hy⟩, e⟩ => ⟨⟨_, hx, e⟩, ⟨_, hy, e⟩⟩⟩

-- `Classical.choice` below comes with `Rel.Holds` itself (through qlean's `Carrier`), not from the proofs
#print axioms Holds
/-- What `thinLOn` computes from one array `xs`, `le` its test read as an order: the chain `ys` from `[]`, each
    `ys[t]` the element `xs[t]` bumped into `ys[t+1]`, `w` its head. -/
def thinLDen {B : Obj} (le : B.El → B.El → Bool) (xs w : List B.El) : Prop :=
      ∃ ys : List (Obj.arr B).El, ∃ hy : ys.length = xs.length + 1,
        ys[xs.length]'(Nat.lt_of_lt_of_eq (Nat.lt_succ_self _) hy.symm) = [] ∧
        (∀ t (ht : t < xs.length),
          (ys[t + 1]'(Nat.lt_of_lt_of_eq (Nat.succ_lt_succ ht) hy.symm) = [] ∧
              ys[t]'(Nat.lt_of_lt_of_eq (Nat.lt_succ_of_lt ht) hy.symm) = [xs[t]'ht]) ∨
            ∃ b bs, ys[t + 1]'(Nat.lt_of_lt_of_eq (Nat.succ_lt_succ ht) hy.symm) = b :: bs ∧
              ((le (xs[t]'ht) b = true ∧ ys[t]'(Nat.lt_of_lt_of_eq (Nat.lt_succ_of_lt ht) hy.symm) = xs[t]'ht :: bs) ∨
               (le b (xs[t]'ht) = true ∧ ys[t]'(Nat.lt_of_lt_of_eq (Nat.lt_succ_of_lt ht) hy.symm) =
                 ys[t + 1]'(Nat.lt_of_lt_of_eq (Nat.succ_lt_succ ht) hy.symm)) ∨
               (le (xs[t]'ht) b = false ∧ le b (xs[t]'ht) = false ∧
                ys[t]'(Nat.lt_of_lt_of_eq (Nat.lt_succ_of_lt ht) hy.symm) =
                  xs[t]'ht :: ys[t + 1]'(Nat.lt_of_lt_of_eq (Nat.succ_lt_succ ht) hy.symm)))) ∧
        w = ys[0]'(Nat.lt_of_lt_of_eq (Nat.zero_lt_succ _) hy.symm)

end Rel.Rep
