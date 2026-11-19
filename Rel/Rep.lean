/-
  The executable relation algebra `Alg` read in the allegory of sets: `rep R` is the relation `R.Holds` as a
  `Rel(Set)` arrow, and each theorem says `rep` of an `Alg` op is the `Rel(Set)` op on the `rep`s.
-/
import Rel.Run.Alg
import Rel.Core.Rel
import Rel.Run.Lang.Lazy

namespace Rel.Rep

open Tab
open scoped Rel.Core.Rel
open Rel.Core.Rel hiding id comp recip inter union zero le inl inr junc

variable {A B C : Obj}

/-- The `Rel(Set)` arrow a `Rel` denotes: `x` to `y` when some row holds `(x, y)`. -/
def rep (R : Tab A B) : Core.Rel (A.El) (B.El) := R.Holds

/-- The coreflexives `K` confines a relation's two sides to: `𝟙` on an unknown side, `rep (idU c)` (the
    coreflexive on `c`'s values, `rep_idU`) on a known one. -/
def _root_.Rel.Known.den (K : Known A B) : Core.Rel A.El A.El × Core.Rel B.El B.El :=
  (K.dom.elim (𝟙 _) fun c => rep (Alg.idU c.2), K.ran.elim (𝟙 _) fun c => rep (Alg.idU c.2))

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

/-- What `r` computes in `K` agrees with `R` on `K`'s sides, where `r` represents `R` there. -/
theorem _root_.Rel.Rel.Reps.run {K : Known A B} : ∀ {r : Rel A B} {R : Core.Rel A.El B.El} {t : Tab A B},
    r.Reps K R → r.run K = some t → K.den.1 ≫ rep t ≫ K.den.2 = K.den.1 ≫ R ≫ K.den.2
  | .tab (.error _), _, _, _, e => by simp [Rel.run, Except.toOption] at e
  | .tab (.ok _), _, _, h, e => by simp only [Rel.run, Except.toOption, Option.some.injEq] at e; subst e; exact h
  | .lazy f, _, _, h, e => Rel.Reps.run (r := f K) h e
  | .bits g w o x ra y rc, _, _, h, e => by
    simp only [Rel.Reps] at h; simp only [Rel.run] at e
    revert h e; cases Tab.ofBits g w o x ra y rc <;> intro h e <;>
      simp only [Except.toOption, Option.some.injEq, reduceCtorEq] at e h ⊢ <;> (try subst e) <;> (try exact h)

/-- `rep R x y` is `R.Holds x y`, by definition. -/
theorem rep_apply (R : Tab A B) (x : A.El) (y : B.El) : rep R x y = R.Holds x y := rfl

section Ops

open Rel.Alg

/-- `rep (R°) = (rep R)°`: the converse swaps the two fields. -/
theorem rep_conv (R : Tab A B) : rep (R°) = (rep R)° :=
  Core.Rel.ext fun y x => convArr_holds R.key R.val x y

/-- `rep 𝟘 = 𝟘`: no row, no pair. -/
theorem rep_zero : rep (Alg.zero : Tab A B) = 𝟘 :=
  Core.Rel.ext fun _ _ => ⟨fun ⟨i, _⟩ => i.elim0, False.elim⟩

/-- `rep (idU U)` is the coreflexive on the elements `U` lists — not `𝟙`, which it is only when `U` lists every
    element of `A.El`. -/
theorem rep_idU {m : USize} (U : Vals A m) :
    rep (idU U) = corefl (α := A.El) fun x => ∃ i, U.row i = x :=
  Core.Rel.ext fun x y => (idU_holds U x y).trans ⟨fun ⟨h, hx⟩ => ⟨h, hx⟩, fun ⟨h, hx⟩ => ⟨h, hx⟩⟩

/-- `rep (outl T) = rep T ≫ π₁`: `outl` on a relation into a product is that relation followed by the first
    projection, the graph of `Prod.fst` (`relProd`'s `π₁`). -/
theorem rep_outl (T : Tab A (.prod B C)) :
    rep (outl T) = rep T ≫ (graph Prod.fst : Core.Rel (B.El × C.El) (B.El)) :=
  Core.Rel.ext fun x y => (outl_holds T x y).trans
    ⟨fun ⟨z, h⟩ => ⟨(y, z), h, rfl⟩, fun ⟨⟨y', z⟩, h, e⟩ => ⟨z, (show y = y' from e) ▸ h⟩⟩

/-- `rep (outr T) = rep T ≫ π₂`: the second projection, the graph of `Prod.snd`. -/
theorem rep_outr (T : Tab A (.prod B C)) :
    rep (outr T) = rep T ≫ (graph Prod.snd : Core.Rel (B.El × C.El) (C.El)) :=
  Core.Rel.ext fun x z => (outr_holds T x z).trans
    ⟨fun ⟨y, h⟩ => ⟨(y, z), h, rfl⟩, fun ⟨⟨y, z'⟩, h, e⟩ => ⟨y, (show z = z' from e) ▸ h⟩⟩

/-- `idU X` is a coreflexive: composed with itself it is itself. -/
theorem idU_idem {m : USize} (X : Vals A m) : rep (idU X) ≫ rep (idU X) = rep (idU X) :=
  Core.Rel.ext fun x y => ⟨fun ⟨z, h, k⟩ => ((idU_holds X x z).1 h).1 ▸ k,
    fun h => ⟨x, (idU_holds X x x).2 ⟨rfl, ((idU_holds X x y).1 h).2⟩, h⟩⟩

/-- `R` relates exactly the values listed in `X`, each by `T`, so on them it is `T`: how a kernel's pointwise
    lemma reads as an equation cut to `X`'s values. -/
theorem idU_ext {n : USize} {X : Vals A n} {R T : Core.Rel A.El B.El}
    (h : ∀ x y, R x y ↔ (∃ j, X.row j = x) ∧ T x y) : rep (idU X) ≫ R = rep (idU X) ≫ T := by
  have e : R = rep (idU X) ≫ T := Core.Rel.ext fun x y => by
    rw [h, comp_apply, rep_idU]
    exact ⟨fun ⟨hx, t⟩ => ⟨x, ⟨rfl, hx⟩, t⟩, fun ⟨_, ⟨e, hx⟩, t⟩ => by subst e; exact ⟨hx, t⟩⟩
  rw [e, ← comp_assoc, idU_idem]

end Ops

/-- Where `P ≫ R ≫ 𝟙 = P ≫ S ≫ 𝟙` and `x` is a key of the coreflexive `P`, `R` and `S` agree at `x`. -/
theorem atKey {P : Core.Rel A.El A.El} {R S : Core.Rel A.El B.El} (hP : ∀ x y, P x y → x = y)
    (E : P ≫ R ≫ 𝟙 _ = P ≫ S ≫ 𝟙 _) {x : A.El} (hx : P x x) (y : B.El) : R x y ↔ S x y := by
  have f : ∀ R' S' : Core.Rel A.El B.El, P ≫ R' ≫ 𝟙 _ = P ≫ S' ≫ 𝟙 _ → R' x y → S' x y := by
    intro R' S' E' r
    have h : (P ≫ R' ≫ 𝟙 _) x y := ⟨x, hx, y, r, rfl⟩
    rw [E'] at h; obtain ⟨z, p, w, s, e⟩ := h; cases hP x z p; cases (e : w = y); exact s
  exact ⟨f R S E, f S R E.symm⟩

/-- A table represents `T` in `K` where, when present, it agrees with `T` on `K`'s sides. -/
theorem tab_reps {K : Known A B} {c : CRel A B} {T : Core.Rel A.El B.El}
    (h : c.ok = true → K.den.1 ≫ rep c.rel ≫ K.den.2 = K.den.1 ≫ T ≫ K.den.2) : Rel.Reps K (.tab c) T :=
  match c, h with
  | none, _ => trivial
  | some _, h => h rfl

/-- What a context knows of each side is a coreflexive. -/
theorem _root_.Rel.Known.cor (K : Known A B) : (∀ x y, K.den.1 x y → x = y) ∧ (∀ x y, K.den.2 x y → x = y) := by
  have e : ∀ {C : Obj} (o : Option ((n : USize) × Vals C n)) (x y : C.El),
      o.elim (𝟙 _) (fun c => rep (Alg.idU c.2)) x y → x = y := fun o x y h => by
    cases o with
    | none => exact h
    | some c => exact ((Alg.idU_holds c.2 x y).1 h).1
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
#print axioms rep_conv
#print axioms rep_zero
#print axioms rep_idU
#print axioms rep_outl
#print axioms rep_outr
/-- What `thinLOn` computes from one array `xs`, `le` its test read as an order: the chain `ys` from `[]`, each
    `ys[t]` the element `xs[t]` bumped into `ys[t+1]`, `w` its head. -/
def thinLDen {B : Obj} (le : B.El → B.El → Bool) (xs w : List B.El) : Prop :=
      ∃ ys : List (Obj.arr B).El, ∃ hy : ys.length = xs.length + 1,
        (∃ p, (Alg.nilVal B).row p = ys[xs.length]'(Nat.lt_of_lt_of_eq (Nat.lt_succ_self _) hy.symm)) ∧
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
