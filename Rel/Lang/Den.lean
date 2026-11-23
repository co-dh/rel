/-
  `⟦−⟧`: the meaning of a core term `Tm` as an arrow of `Rel(Set)` (`doc/rel-denotation-design.md` §1, §2, §7.3).
  Total and structural: each node is the `T` its `Gen.*_sound` lemma proves, written with the allegory's operators
  (`≫ ° ∩ ∪ 𝟙 𝟘`, D3 = E); `μ`, `ν` are `Core.Rel.mu`, `nu`, defined for every body, so no monotonicity is assumed here.
-/
module

public import Rel.Run.Lang.Tm
public import Rel.Run.Where
public import Rel.AscOrder
public import Rel.Rep
public import Rel.ObjOrder
public import Rel.Core.Fix
public import Rel.Core.Div
public import Rel.Kernel.Cast

-- exposed: every def body is a spec a downstream `rfl`/`decide`/`simp` may unfold (PLAN W.8)
@[expose] public section

namespace Rel.Lang

open Rel.Kernel Tab Rel.Rep
open scoped Rel.Core.Rel
open Rel.Core.Rel hiding id comp recip inter union zero le inl inr junc

/-- The meaning of each variable `k`, at the objects the term asks for: an arrow `A ⟶ B` of `Rel(Set)` between the
    elements of the two objects. -/
abbrev Val := Nat → (A B : Obj) → Core.Rel (Obj.El A) (Obj.El B)

/-- No variable bound: what a closed term (a call's body) is read under. -/
def Val.empty : Val := fun _ _ _ => 𝟘

open Classical in
/-- `ρ` with the variable `k` bound to `X : A ⟶ B`. A use of `k` at other objects is ill-typed and reads `𝟘`, so
    the binder hides every outer `k`, as `Tm.fv` drops it. -/
noncomputable def Val.bind (ρ : Val) (k : Nat) {A B : Obj} (X : Core.Rel (Obj.El A) (Obj.El B)) : Val := fun j A' B' =>
  if j = k then (if h : A = A' ∧ B = B' then h.1 ▸ h.2 ▸ X else 𝟘) else ρ j A' B'

theorem Val.bind_ne {ρ : Val} {k j : Nat} {A B : Obj} {X : Core.Rel (Obj.El A) (Obj.El B)} (h : j ≠ k) : ρ.bind k X j = ρ j := by
  funext A' B'; simp [Val.bind, h]

theorem Val.bind_same {ρ ρ' : Val} {k : Nat} {A B : Obj} {X : Core.Rel (Obj.El A) (Obj.El B)} : ρ.bind k X k = ρ'.bind k X k := by
  funext A' B'; simp [Val.bind]

variable {A B C : Obj} {Φ Ψ : Core.Rel (Obj.El A) (Obj.El B) → Core.Rel (Obj.El A) (Obj.El B)} {Y : Core.Rel (Obj.El A) (Obj.El B)}

/-! ### The named meanings: each the `T` of its node's `Gen.*_sound` lemma -/



/-- `R\S` within the universes `UB`, `UC`: the book's left division where `R` has a column (`R° ≫ ⊤`), every pair
    of the universes where it has none (`UB° ≫ ⊤ ≫ UC`). -/
abbrev ldivDen (TR : Core.Rel (Obj.El A) (Obj.El B)) (TS : Core.Rel (Obj.El A) (Obj.El C)) (TB : Core.Rel (Obj.El B) (Obj.El B)) (TC : Core.Rel (Obj.El C) (Obj.El C)) : Core.Rel (Obj.El B) (Obj.El C) :=
  ldiv TR TS ∩ ((TR° ≫ top) ∪ (TB° ≫ top ≫ TC))

/-- `R/S = (S° \ R°)°` within the universes `UA`, `UB`. -/
abbrev rdivDen (TR : Core.Rel (Obj.El A) (Obj.El C)) (TS : Core.Rel (Obj.El B) (Obj.El C)) (TA : Core.Rel (Obj.El A) (Obj.El A)) (TB : Core.Rel (Obj.El B) (Obj.El B)) : Core.Rel (Obj.El A) (Obj.El B) :=
  (ldivDen TS° TR° TB TA)°

/-- `ldivDen` at a pair: `c` is in `S` at every `a` of `R`'s column `b`, and `b` has a column or both are in the universes. -/
theorem ldivDen_iff {TR : Core.Rel (Obj.El A) (Obj.El B)} {TS : Core.Rel (Obj.El A) (Obj.El C)} {TB : Core.Rel (Obj.El B) (Obj.El B)} {TC : Core.Rel (Obj.El C) (Obj.El C)} {b : Obj.El B} {c : Obj.El C} :
    ldivDen TR TS TB TC b c ↔ (∀ a, TR a b → TS a c) ∧ ((∃ a, TR a b) ∨ ((∃ b', TB b' b) ∧ ∃ c', TC c' c)) :=
  and_congr Iff.rfl (or_congr ⟨fun ⟨a, h, _⟩ => ⟨a, h⟩, fun ⟨a, h⟩ => ⟨a, h, trivial⟩⟩
    ⟨fun ⟨b', hb, c', _, hc⟩ => ⟨⟨b', hb⟩, c', hc⟩, fun ⟨⟨b', hb⟩, c', hc⟩ => ⟨b', hb, c', trivial, hc⟩⟩)

/-- `rdivDen` at a pair, the mirror of `ldivDen_iff`. -/
theorem rdivDen_iff {TR : Core.Rel (Obj.El A) (Obj.El C)} {TS : Core.Rel (Obj.El B) (Obj.El C)} {TA : Core.Rel (Obj.El A) (Obj.El A)} {TB : Core.Rel (Obj.El B) (Obj.El B)} {x : Obj.El A} {y : Obj.El B} :
    rdivDen TR TS TA TB x y ↔ (∀ c, TS y c → TR x c) ∧ ((∃ c, TS y c) ∨ ((∃ a, TA a x) ∧ ∃ b, TB b y)) :=
  ldivDen_iff.trans (and_congr Iff.rfl (or_congr Iff.rfl and_comm))

/-- `R÷S = R/S ∩ (S/R)°` within the universes `UA`, `UB`: `x` to `y` when `R x` and `S y` are one image. -/
abbrev symDivDen (TA : Core.Rel (Obj.El A) (Obj.El A)) (TB : Core.Rel (Obj.El B) (Obj.El B)) (TR : Core.Rel (Obj.El A) (Obj.El C)) (TS : Core.Rel (Obj.El B) (Obj.El C)) : Core.Rel (Obj.El A) (Obj.El B) :=
  rdivDen TR TS TA TB ∩ (rdivDen TS TR TB TA)°

/-- The test `a ∈ TU`: the coreflexive on the points `TU` relates to something. -/
abbrev inU {α : Type} (TU : Core.Rel α α) : Core.Rel α α := 𝟙 α ∩ TU ≫ TU°

theorem inU_iff {α : Type} (TU : Core.Rel α α) (a b : α) : inU TU a b ↔ a = b ∧ ∃ v, TU a v :=
  ⟨fun ⟨h, v, hv, _⟩ => ⟨h, v, hv⟩, fun ⟨h, v, hv⟩ => ⟨h, v, hv, by subst h; exact hv⟩⟩

/-- `nil`: every source to the empty array. -/
abbrev nilDen : Core.Rel (Obj.El A) (Obj.El (.arr B)) := graph fun _ => []

/-- `at(k)`: the element at position `k`. -/
abbrev atDen (k : Nat) : Core.Rel (Obj.El (.arr B)) (Obj.El B) := graph (fun xs => xs[k]?) ≫ (graph some)°

theorem atDen_iff (k : Nat) (xs : Obj.El (.arr B)) (x : Obj.El B) : atDen k xs x ↔ ∃ h : k < xs.length, x = xs[k]'h :=
  (graph_recip_graph _ _ _ _).trans (List.getElem?_eq_some_iff.trans (exists_congr fun _ => eq_comm))

/-- The row `at` at `A×N ⟶ A`'s arrays: at `i64` the pair `(xs, k)` to `xs[k]` for a nonneg `k` (`atDen`), `𝟘` elsewhere. -/
def atOn (B : Obj) : (N : Obj) → Core.Rel (Obj.El (.prod (.arr B) N)) (Obj.El B)
  | .atom .i64 => rpair (graph Prod.snd ≫ graph Int64.toInt ≫ (graph Int.ofNat)°) (graph Prod.fst) ≫
      keyOf atDen ≫ graph Prod.snd
  | _ => 𝟘

theorem atOn_iff (p : Obj.El (.prod (.arr B) (.atom .i64))) (x : Obj.El B) :
    atOn B (.atom .i64) p x ↔ 0 ≤ p.2.toInt ∧ atDen p.2.toInt.toNat p.1 x := by
  constructor
  · rintro ⟨q, ⟨⟨_, rfl, _, rfl, hk⟩, hq⟩, r, ⟨hr, hat⟩, rfl⟩
    have hk : p.2.toInt = Int.ofNat q.1 := hk
    have hq : q.2 = p.1 := hq
    refine ⟨by rw [hk]; exact Int.natCast_nonneg _, ?_⟩
    rw [hk, ← hq]; exact hat
  · rintro ⟨h0, hat⟩
    exact ⟨(p.2.toInt.toNat, p.1), ⟨⟨_, rfl, _, rfl, (Int.toNat_of_nonneg h0).symm⟩, rfl⟩, (_, x), ⟨rfl, hat⟩, rfl⟩

/-- `succ` on the universe `TU`: `u` and its successor both in it. -/
abbrev succDen (TU : Core.Rel (Obj.El .long) (Obj.El .long)) : Core.Rel (Obj.El .long) (Obj.El .long) :=
  inU TU ≫ graph (Ew.intStep Ew.add Alg.nul · 1) ≫ inU TU

theorem succDen_iff (TU : Core.Rel (Obj.El .long) (Obj.El .long)) (u w : Obj.El .long) :
    succDen TU u w ↔ (∃ v, TU u v) ∧ w = Ew.intStep Ew.add Alg.nul u 1 ∧ ∃ v, TU w v := by
  simp only [Core.Rel.comp_apply, graph, inU_iff]
  constructor
  · rintro ⟨_, ⟨rfl, hu⟩, _, rfl, rfl, hw⟩; exact ⟨hu, rfl, hw⟩
  · rintro ⟨hu, rfl, hw⟩; exact ⟨u, ⟨rfl, hu⟩, _, rfl, rfl, hw⟩

/-- The float order `o` (`Op.flt`, `Op.fle`) on two values of `t`: IEEE's on their `f64` words (`fval`); no pair at an
    atom holding no float. -/
abbrev fordAt (o : Rel.Kernel.Op) (t : QAtomicType) (a b : (Obj.atom t).El) : Prop :=
  ∃ x y, fval t a = some x ∧ fval t b = some y ∧ o.eval x y = .ok 1

/-- The word `R` of an answer `r` as a value of `u`'s atom (`ofBits`); none for an error and where `R` is `2^63` (the
    IEEE answer is NaN, or no value of `u`'s atom). -/
def wordOut (u : QAtomicType) (r : Except String UInt64) : Option (Obj.atom u).El :=
  r.toOption.bind fun R => if R = 0x8000000000000000 then none else some (QAtomicType.ofBits u R)

theorem wordOut_eq_some (u : QAtomicType) (r : Except String UInt64) (w : (Obj.atom u).El) :
    wordOut u r = some w ↔ ∃ R, r = .ok R ∧ R ≠ 0x8000000000000000 ∧ w = QAtomicType.ofBits u R := by
  cases r <;> simp [wordOut, Except.toOption] <;> grind

/-- The integer order `o` (`Op.lt`, `Op.le`) on two values of the ordered atom `t` stored as the number atom `r`
    (`ordNum`): `Int64`'s on the `i64` words of their values (`castWord r .i64`, q's null the least), read from any
    words that hold them (`ofBits`); no pair at an atom with no order. -/
abbrev iordAt (o : Rel.Kernel.Op) (t : QAtomicType) (a b : (Obj.atom t).El) : Prop :=
  ∃ r x y, t.ordNum = some r ∧ QAtomicType.ofBits t x = a ∧ QAtomicType.ofBits t y = b ∧
    o.eval (QAtomicType.castWord r .i64 x) (QAtomicType.castWord r .i64 y) = .ok 1

/-- `<` on the values of the atom `t`: `Int64`'s at `i64`, IEEE's at a float atom (`fordAt .flt`), the integer order
    of the stored values at every other ordered atom (`iordAt .lt`: the narrow integers, `char`, `date`,
    `datetime`), none elsewhere. -/
def ltAt : (t : QAtomicType) → (Obj.atom t).El → (Obj.atom t).El → Prop
  | .i64, a, b => a < b
  | .f32, a, b => fordAt Rel.Kernel.Op.flt .f32 a b
  | .f64, a, b => fordAt Rel.Kernel.Op.flt .f64 a b
  | t, a, b => iordAt Rel.Kernel.Op.lt t a b

/-- `≤` on the values of the atom `t`, as `ltAt`. -/
def leAt : (t : QAtomicType) → (Obj.atom t).El → (Obj.atom t).El → Prop
  | .i64, a, b => a ≤ b
  | .f32, a, b => fordAt Rel.Kernel.Op.fle .f32 a b
  | .f64, a, b => fordAt Rel.Kernel.Op.fle .f64 a b
  | t, a, b => iordAt Rel.Kernel.Op.le t a b

/-- `≤` on the universe `TU` of the atom `t`. -/
abbrev leqDen (t : QAtomicType) (TU : Core.Rel (Obj.El (.atom t)) (Obj.El (.atom t))) : Core.Rel (Obj.El (.atom t)) (Obj.El (.atom t)) :=
  inU TU ≫ (leAt t : Core.Rel (Obj.El (.atom t)) (Obj.El (.atom t))) ≫ inU TU

theorem leqDen_iff (t : QAtomicType) (TU : Core.Rel (Obj.El (.atom t)) (Obj.El (.atom t))) (a b : Obj.El (.atom t)) :
    leqDen t TU a b ↔ (∃ v, TU a v) ∧ (∃ v, TU b v) ∧ leAt t a b := by
  simp only [Core.Rel.comp_apply, inU_iff]
  constructor
  · rintro ⟨_, ⟨rfl, ha⟩, _, h, rfl, hb⟩; exact ⟨ha, hb, h⟩
  · rintro ⟨ha, hb, h⟩; exact ⟨a, ⟨rfl, ha⟩, b, h, rfl, hb⟩

/-- `<` on the universe `TU` of the atom `t`. -/
abbrev ltDen (t : QAtomicType) (TU : Core.Rel (Obj.El (.atom t)) (Obj.El (.atom t))) : Core.Rel (Obj.El (.atom t)) (Obj.El (.atom t)) :=
  inU TU ≫ (ltAt t : Core.Rel (Obj.El (.atom t)) (Obj.El (.atom t))) ≫ inU TU

theorem ltDen_iff (t : QAtomicType) (TU : Core.Rel (Obj.El (.atom t)) (Obj.El (.atom t))) (a b : Obj.El (.atom t)) :
    ltDen t TU a b ↔ (∃ v, TU a v) ∧ (∃ v, TU b v) ∧ ltAt t a b := by
  simp only [Core.Rel.comp_apply, inU_iff]
  constructor
  · rintro ⟨_, ⟨rfl, ha⟩, _, h, rfl, hb⟩; exact ⟨ha, hb, h⟩
  · rintro ⟨ha, hb, h⟩; exact ⟨a, ⟨rfl, ha⟩, b, h, rfl, hb⟩

/-- The value verb `k` itself (`Alg.arith`): `Int64`'s step, not the null and, for `+ - *`, not wrapped. -/
abbrev stepDen (k : UInt8) : Core.Rel (Obj.El (.prod .long .long)) (Obj.El .long) :=
  fun p w => w = Ew.intStep k Alg.nul p.1 p.2 ∧ w ≠ Alg.nul ∧
    (if k == Ew.add then (0 ≤ p.2 ↔ p.1 ≤ w) else if k == Ew.sub then (0 ≤ p.2 ↔ w ≤ p.1)
     else if k == Ew.mul then (Ew.intStep Ew.idiv Alg.nul w p.1 = p.2 ∨ p.1 = 0) else True)

/-- The value verb `k` at the atom `t`: `stepDen k` at `i64`; at a float atom `fstep` on the operands' `f64` words
    (`fval`), the word of `t` it answers, no row where that is `2^63` (the IEEE answer is NaN); none elsewhere. -/
theorem exceptBind_eq_ok {ε α β : Type} (e : Except ε α) (g : α → Except ε β) (R : β) :
    e.bind g = .ok R ↔ ∃ Y, e = .ok Y ∧ g Y = .ok R := by cases e <;> simp [Except.bind]

/-- `stepAt` at a float atom: the graph of the `Option` computation of `fstep` on the operands' words. -/
abbrev fstepDen (t : QAtomicType) (k : UInt8) : Core.Rel (Obj.El (.prod (.atom t) (.atom t))) (Obj.El (.atom t)) :=
  graph (fun p => (fval t p.1).bind fun x => (fval t p.2).bind fun y => wordOut t (fstep t k x y)) ≫ (graph some)°

def stepAt : (t : QAtomicType) → UInt8 → Core.Rel (Obj.El (.prod (.atom t) (.atom t))) (Obj.El (.atom t))
  | .i64, k => stepDen k
  | t, k => fstepDen t k

theorem stepAt_ne (t : QAtomicType) (k : UInt8) (h : t ≠ .i64) : stepAt t k = fstepDen t k := by
  cases t <;> first | rfl | exact absurd rfl h

theorem fstepDen_iff (t : QAtomicType) (k : UInt8) (p : Obj.El (.prod (.atom t) (.atom t))) (w : Obj.El (.atom t)) :
    fstepDen t k p w ↔ ∃ x y r, fval t p.1 = some x ∧ fval t p.2 = some y ∧ fstep t k x y = .ok r ∧
      r ≠ 0x8000000000000000 ∧ w = QAtomicType.ofBits t r := by
  refine (graph_recip_graph _ _ _ _).trans ?_
  simp only [Option.bind_eq_some_iff]
  constructor
  · rintro ⟨x, hx, y, hy, h⟩; obtain ⟨r, hr, hne, rfl⟩ := (wordOut_eq_some _ _ _).1 h; exact ⟨x, y, r, hx, hy, hr, hne, rfl⟩
  · rintro ⟨x, y, r, hx, hy, hr, hne, rfl⟩; exact ⟨x, hx, y, hy, (wordOut_eq_some _ _ _).2 ⟨r, hr, hne, rfl⟩⟩

/-- The value verb `k` on the universe `TU` of the atom `t`: both inputs in `TU` (`dom(π₁ TU)`, `dom(π₂ TU)`), as
    `succDen`'s, then the step, its result in `TU`. The input test makes `(TU×TU) arith = arith` at a coreflexive
    `TU`. -/
abbrev arithDen (t : QAtomicType) (k : UInt8) (TU : Core.Rel (Obj.El (.atom t)) (Obj.El (.atom t))) : Core.Rel (Obj.El (.prod (.atom t) (.atom t))) (Obj.El (.atom t)) :=
  (𝟙 _ ∩ (graph Prod.fst ≫ TU) ≫ (graph Prod.fst ≫ TU)°) ≫
    ((𝟙 _ ∩ (graph Prod.snd ≫ TU) ≫ (graph Prod.snd ≫ TU)°) ≫ (stepAt t k ≫ TU))

/-- `fold(e, S)`: a chain of values `ys`, its last from `e`, each the step `S` of the element and the next value. -/
abbrev foldrDen {E V : Obj} (Te : Core.Rel (Obj.El V) (Obj.El V)) (TS : Core.Rel (Obj.El (.prod E V)) (Obj.El V)) : Core.Rel (Obj.El (.arr E)) (Obj.El V) :=
  fun xs w => ∃ ys : List V.El, ∃ hy : ys.length = xs.length + 1,
    (∃ a, Te a (ys[xs.length]'(Nat.lt_of_lt_of_eq (Nat.lt_succ_self _) hy.symm))) ∧
    (∀ t (ht : t < xs.length), TS (xs[t]'ht, ys[t + 1]'(Nat.lt_of_lt_of_eq (Nat.succ_lt_succ ht) hy.symm))
      (ys[t]'(Nat.lt_of_lt_of_eq (Nat.lt_succ_of_lt ht) hy.symm))) ∧
    w = ys[0]'(Nat.lt_of_lt_of_eq (Nat.zero_lt_succ _) hy.symm)

/-- The left fold `⦇e, S⦈` over `[nil, snoc]`: a chain of values `ys`, its first from `e`, each the step `S` of the
    value before and the element (`(acc, x)`, index 0 first), the result its last. -/
abbrev foldDen {E V : Obj} (Te : Core.Rel (Obj.El V) (Obj.El V)) (TS : Core.Rel (Obj.El (.prod V E)) (Obj.El V)) : Core.Rel (Obj.El (.arr E)) (Obj.El V) :=
  fun xs w => ∃ ys : List V.El, ∃ hy : ys.length = xs.length + 1,
    (∃ a, Te a (ys[0]'(by omega))) ∧
    (∀ t (ht : t < xs.length), TS (ys[t]'(by omega), xs[t]'ht) (ys[t + 1]'(by omega))) ∧
    w = ys[xs.length]'(by omega)


/-- `fold(e, S)` given a family: at the key `i`, the left fold whose start is the fibre of `e` at `i` and whose step
    is `S` at `i`, keeping the key. -/
abbrev foldIDen {I E V : Obj} (Te : Core.Rel (Obj.El I) (Obj.El (.prod V V))) (TS : Core.Rel (Obj.El (.prod (.prod I V) E)) (Obj.El (.prod I V))) :
    Core.Rel (Obj.El (.prod I (.arr E))) (Obj.El V) :=
  ((graph Prod.fst ≫ (graph Prod.fst)°) ∩
    (graph Prod.snd ≫ foldDen (E := E) (V := .prod I V)
      (𝟙 _ ∩ (rpair (𝟙 _) (Te ≫ graph Prod.snd))° ≫ (rpair (𝟙 _) (Te ≫ graph Prod.snd))°°)
      (TS ∩ (graph Prod.fst ≫ graph Prod.fst ≫ (graph Prod.fst)°)))) ≫ graph Prod.snd

/-- `foldIDen` is one `foldDen` on the carrier `I×V`: start `ran⟨𝟙, Te ≫ π₂⟩`, step `TS` met with
    `π₁ ≫ π₁ ≫ π₁°` (the step keeps the index), its result's index met with the key's, then `π₂`; at a pair it is the
    `foldDen` of the family at the key. -/
theorem foldIDen_iff {I E V : Obj} (Te : Core.Rel (Obj.El I) (Obj.El (.prod V V))) (TS : Core.Rel (Obj.El (.prod (.prod I V) E)) (Obj.El (.prod I V))) (p : Obj.El (.prod I (.arr E))) (w : Obj.El V) :
    foldIDen Te TS p w ↔ foldDen (fun a b => Te p.1 (a, b)) (fun q v => TS ((p.1, q.1), q.2) (p.1, v)) p.2 w := by
  simp only [foldIDen, foldDen, Core.Rel.comp, Core.Rel.inter, Core.Rel.recip, Core.Rel.graph, Core.Rel.rpair,
    Core.Rel.id]
  constructor
  · rintro ⟨q, ⟨⟨i, rfl, hq⟩, xs, rfl, zs, hz, ⟨_, rfl, j, ⟨rfl, b, hb, hb2⟩, -, -⟩, hS, rfl⟩, rfl⟩
    -- the step keeps the index, so every value of the chain carries the seed's, which the result's is the key's
    have hz0 : ∀ t (ht : t < zs.length), zs[t].1 = zs[0].1 := by
      intro t
      induction t with
      | zero => intro _; rfl
      | succ t ih =>
        intro ht
        obtain ⟨-, _, rfl, _, rfl, he⟩ := hS t (by omega)
        exact he.symm.trans (ih (by omega))
    have hidx : ∀ t (ht : t < zs.length), zs[t].1 = p.1 := fun t ht =>
      (hz0 t ht).trans ((hz0 p.2.length (by omega)).symm.trans hq.symm)
    refine ⟨zs.map Prod.snd, by simp [hz], ⟨b.1, ?_⟩, fun t ht => ?_, by simp⟩
    · have e := hidx 0 (by omega)
      simp only [List.getElem_map, hb2, ← e]
      exact hb
    · obtain ⟨h, -⟩ := hS t ht
      have h1 : ((p.1, zs[t + 1].2) : (I.prod V).El) = zs[t + 1] := Prod.ext (hidx (t + 1) (by omega)).symm rfl
      have h0 : ((p.1, zs[t].2) : (I.prod V).El) = zs[t] := Prod.ext (hidx t (by omega)).symm rfl
      simp only [List.getElem_map]
      rw [h1, h0]
      exact h
  · rintro ⟨ys, hy, ⟨a, ha⟩, hS, rfl⟩
    refine ⟨(p.1, ys[p.2.length]), ⟨⟨_, rfl, rfl⟩, _, rfl, ys.map (p.1, ·), by simp [hy],
      ⟨_, rfl, p.1, ⟨?_, _, ha, ?_⟩, ?_, _, ha, ?_⟩, fun t ht => ⟨?_, _, rfl, _, rfl, ?_⟩, ?_⟩, rfl⟩
    all_goals simp
    simpa using hS t (by simpa using ht)


/-- `Rᴵ`: the family `R : I ⟶ A×B` as one relation of the key and the source. -/
abbrev flatDen {I A B : Obj} (T : Core.Rel (Obj.El I) (Obj.El (.prod A B))) : Core.Rel (Obj.El (.prod I A)) (Obj.El B) :=
  ((graph Prod.fst ≫ T) ∩ (graph Prod.snd ≫ (graph Prod.fst)°)) ≫ graph Prod.snd

theorem flatDen_iff {I A B : Obj} (T : Core.Rel (Obj.El I) (Obj.El (.prod A B))) (x : Obj.El (.prod I A)) (b : Obj.El B) :
    flatDen T x b ↔ T x.1 (x.2, b) :=
  ⟨fun ⟨p, ⟨⟨_, rfl, hT⟩, _, rfl, hp⟩, hb⟩ => by obtain ⟨a, c⟩ := p; cases hp; cases hb; exact hT,
   fun h => ⟨(x.2, b), ⟨⟨_, rfl, h⟩, _, rfl, rfl⟩, rfl⟩⟩


/-- `∋`: an array to each of its elements. The leaf every power operation composes. -/
abbrev memDen : Core.Rel (Obj.El (.arr A)) (Obj.El A) := fun xs a => a ∈ xs

/-- The pair test `TQ` read at `(b, c)` as a relation `B ⟶ B`: `qtDen TQ b c ↔ TQ (b, c) (b, c)`. -/
abbrev qtDen (TQ : Core.Rel (Obj.El (.prod B B)) (Obj.El (.prod B B))) : Core.Rel (Obj.El B) (Obj.El B) :=
  (graph Prod.fst)° ≫ (𝟙 _ ∩ TQ) ≫ graph Prod.snd

theorem qtDen_iff (TQ : Core.Rel (Obj.El (.prod B B)) (Obj.El (.prod B B))) (b c : Obj.El B) :
    qtDen TQ b c ↔ TQ (b, c) (b, c) :=
  ⟨fun ⟨p, hp, q, ⟨hpq, hT⟩, hc⟩ => by obtain ⟨b', c'⟩ := p; cases hp; cases hpq; cases hc; exact hT,
   fun h => ⟨(b, c), rfl, _, ⟨rfl, h⟩, rfl⟩⟩

/-- `est(Q)` keeps `b` of `xs` unless some other `c` of `xs` fails `Q` at `(b, c)`: `∋ ∩ (∋° \ (𝟙 ∪ Qt°))`. -/
abbrev estDen (TQ : Core.Rel (Obj.El (.prod B B)) (Obj.El (.prod B B))) : Core.Rel (Obj.El (.arr B)) (Obj.El B) :=
  memDen ∩ (ldiv memDen° (𝟙 _ ∪ (qtDen TQ)°))

theorem estDen_iff (TQ : Core.Rel (Obj.El (.prod B B)) (Obj.El (.prod B B))) (xs : Obj.El (.arr B)) (b : Obj.El B) :
    estDen TQ xs b ↔ b ∈ xs ∧ ¬ ∃ c, c ∈ xs ∧ c ≠ b ∧ ¬ TQ (b, c) (b, c) :=
  and_congr_right fun _ => by
    simp only [ldiv_apply, Core.Rel.union, Core.Rel.id, Core.Rel.recip, qtDen_iff]
    exact ⟨fun h ⟨c, hc, hne, hq⟩ => (h c hc).elim hne hq, fun h c hc => by
      by_cases e : c = b
      · exact .inl e
      · exact .inr (Classical.byContradiction fun hq => h ⟨c, hc, e, hq⟩)⟩

/-- `Λ(T)` with `𝒫B` held as `[B]` (D2 = C): `a` to the one list of its image strictly ascending by `Obj.lt`, the
    order `Rel.Canon` puts a table's rows in; no list where that image has no such list. -/
def lamDen (T : Core.Rel (Obj.El A) (Obj.El B)) : Core.Rel (Obj.El A) (Obj.El (.arr B)) :=
  (rdiv T memDen ∩ (rdiv memDen T)°) ≫ corefl (List.Pairwise B.lt)

theorem lamDen_iff (T : Core.Rel (Obj.El A) (Obj.El B)) (a : Obj.El A) (ys : Obj.El (.arr B)) :
    lamDen T a ys ↔ ys.Pairwise B.lt ∧ ∀ b, b ∈ ys ↔ T a b :=
  ⟨fun ⟨_, ⟨h1, h2⟩, rfl, hp⟩ => ⟨hp, fun b => ⟨h1 b, h2 b⟩⟩,
   fun ⟨hp, h⟩ => ⟨_, ⟨fun b => (h b).1, fun b => (h b).2⟩, rfl, hp⟩⟩

theorem lamDen_fun (T : Core.Rel (Obj.El A) (Obj.El B)) :
    lamDen T = fun a ys => ys.Pairwise B.lt ∧ ∀ b, b ∈ ys ↔ T a b := funext fun a => funext fun ys => propext (lamDen_iff T a ys)

/-- `F(T)`: two arrays of one length, related elementwise by `T`. -/
abbrev mapDen {A B : Obj} (T : Core.Rel (Obj.El A) (Obj.El B)) : Core.Rel (Obj.El (.arr A)) (Obj.El (.arr B)) :=
  foldDen (E := A) (V := .arr B) ((graph fun _ : Unit => ([] : Obj.El (.arr B)))° ≫ graph fun _ : Unit => [])
    (rpair (graph Prod.fst) (graph Prod.snd ≫ T) ≫ graph fun p : Obj.El (.prod (.arr B) B) => p.1 ++ [p.2])

theorem mapDen_iff {A B : Obj} (T : Core.Rel (Obj.El A) (Obj.El B)) (xs : Obj.El (.arr A)) (ys : Obj.El (.arr B)) :
    mapDen T xs ys ↔ ys.length = xs.length ∧ ∀ t (ht : t < xs.length) (ht' : t < ys.length), T (xs[t]'ht) (ys[t]'ht') := by
  simp only [mapDen, foldDen, Core.Rel.comp, Core.Rel.recip, Core.Rel.graph, Core.Rel.rpair]
  constructor
  · rintro ⟨zs, hz, ⟨_, _, rfl, h0⟩, hs, rfl⟩
    -- the chain's `t`-th value is the first `t` answers
    have key : ∀ t (h : t ≤ xs.length), (zs[t]'(by omega)).length = t ∧
        ∀ i (hi : i < t) (hi' : i < (zs[t]'(by omega)).length), T (xs[i]'(by omega)) ((zs[t]'(by omega))[i]'hi') := by
      intro t
      induction t with
      | zero => intro _; simp [h0]
      | succ t ih =>
        intro h
        obtain ⟨⟨a, y⟩, ⟨rfl, x, rfl, hT⟩, he⟩ := hs t (by omega)
        obtain ⟨hl, hT'⟩ := ih (by omega)
        simp only [he, List.length_append, List.length_singleton, hl, true_and]
        intro i hi hi'
        by_cases hit : i < t
        · rw [List.getElem_append_left (by omega)]; exact hT' i hit _
        · have : i = t := by omega
          subst this
          rw [List.getElem_concat_length hl.symm]
          exact hT
    obtain ⟨hl, hT⟩ := key xs.length (Nat.le_refl _)
    exact ⟨hl, fun t ht ht' => hT t ht ht'⟩
  · rintro ⟨hl, hT⟩
    refine ⟨(List.range (xs.length + 1)).map ys.take, by simp, ⟨[], (), rfl, by simp⟩, fun t ht => ?_, by simp [← hl]⟩
    refine ⟨(ys.take t, ys[t]'(by omega)), ⟨by simp, xs[t], rfl, hT t ht _⟩, ?_⟩
    simp only [List.getElem_map, List.getElem_range, List.take_succ_eq_append_getElem (by omega : t < ys.length)]

/-- `dom(T) (𝟙 × ≥) dom(T)`: `(k, i)` to `(k, j)`, both in `dom(T)`, `j ≤ i` in the order `leAt t` of the position
    atom `t`; `𝟙 × ≥` is `π₁ π₁° ∩ π₂ ≥ π₂°`. -/
abbrev upToDen {K V : Obj} {t : QAtomicType} (T : Core.Rel (Obj.El (.prod K (.atom t))) (Obj.El V)) :
    Core.Rel (Obj.El (.prod K (.atom t))) (Obj.El (.prod K (.atom t))) :=
  (𝟙 _ ∩ T ≫ T°) ≫ ((graph Prod.fst ≫ (graph Prod.fst)°) ∩
    (graph Prod.snd ≫ (leAt t : Core.Rel (Obj.El (.atom t)) (Obj.El (.atom t)))° ≫ (graph Prod.snd)°)) ≫ (𝟙 _ ∩ T ≫ T°)

/-- A value of the atom `t` to its `f64` word (`fval`): none at an atom holding no float. -/
abbrev fwideDen (t : QAtomicType) : Core.Rel (Obj.El (.atom t)) (Obj.El (.atom .f64)) := graph (fval t) ≫ (graph some)°
theorem fwideDen_iff (t : QAtomicType) (x : Obj.El (.atom t)) (X : Obj.El (.atom .f64)) :
    fwideDen t x X ↔ fval t x = some X := graph_recip_graph _ _ _ _

/-- `Op.fadd` of two `f64` words, not rounded. -/
abbrev faddDen : Core.Rel (Obj.El (.prod (.atom .f64) (.atom .f64))) (Obj.El (.atom .f64)) :=
  graph (fun p : Obj.El (.prod (.atom .f64) (.atom .f64)) => Rel.Kernel.Op.fadd.eval p.1 p.2) ≫ (graph Except.ok)°
theorem faddDen_iff (p : Obj.El (.prod (.atom .f64) (.atom .f64))) (r : Obj.El (.atom .f64)) :
    faddDen p r ↔ Rel.Kernel.Op.fadd.eval p.1 p.2 = .ok r := graph_recip_graph _ _ _ _

/-- An `f64` word to the word of the atom `t` nearest it: `Op.fto t`, then the coreflexive `corefl` dropping `2^63` (a NaN),
    then the value `ofBits t` of the word. -/
abbrev froundDen (t : QAtomicType) : Core.Rel (Obj.El (.atom .f64)) (Obj.El (.atom t)) :=
  (graph ((Rel.Kernel.Op.fto t).eval 0) ≫ (graph Except.ok)° : Core.Rel (Obj.El (.atom .f64)) UInt64) ≫
    Core.Rel.diff (𝟙 _) ((graph fun _ : Unit => (0x8000000000000000 : UInt64))° ≫ graph fun _ : Unit => 0x8000000000000000) ≫
    (graph (QAtomicType.ofBits t) : Core.Rel UInt64 (Obj.El (.atom t)))

theorem froundDen_iff (t : QAtomicType) (r : Obj.El (.atom .f64)) (y : Obj.El (.atom t)) :
    froundDen t r y ↔ ∃ R, (Rel.Kernel.Op.fto t).eval 0 r = .ok R ∧ R ≠ 0x8000000000000000 ∧ y = QAtomicType.ofBits t R :=
  ⟨fun ⟨R, h, _, ⟨rfl, hn⟩, hy⟩ => ⟨R, (Core.Rel.graph_recip_graph _ _ _ _).1 h, fun e => hn ⟨(), e, e⟩, hy⟩,
   fun ⟨R, h, hn, hy⟩ => ⟨R, (Core.Rel.graph_recip_graph _ _ _ _).2 h, _, ⟨rfl, fun ⟨_, e, _⟩ => hn e⟩, hy⟩⟩

/-- **`⦇[0, plus]⦈` at the float atom `u`**: the left fold over pairs (carry, value) from `u`'s `0` paired with
    its `f64` word (`fwideDen`, as the kernel widens its seed), each element widened likewise, added to the carry in
    `f64` unrounded (`faddDen`), the new carry paired with its one rounding to `u` (`froundDen`, none at a NaN); then
    the value `π₂`. So a float sum accumulates in `f64` and rounds once to `u`, every prefix being checked for a NaN. -/
abbrev fsumDen (u : QAtomicType) : Core.Rel (Obj.El (.arr (.atom u))) (Obj.El (.atom u)) :=
  foldDen (E := .atom u) (V := .prod (.atom .f64) (.atom u))
      ((graph fun _ => QAtomicType.ofBits u 0) ≫ rpair (fwideDen u) (𝟙 _))
      (rpair (graph fun p : Obj.El (.prod (.prod (.atom .f64) (.atom u)) (.atom u)) => p.1.1)
          (graph Prod.snd ≫ fwideDen u) ≫ faddDen ≫ rpair (𝟙 _) (froundDen u)) ≫ graph Prod.snd

theorem fsumDen_seed (u : QAtomicType) (a b : Obj.El (.prod (.atom .f64) (.atom u))) :
    ((graph fun _ => QAtomicType.ofBits u 0) ≫ rpair (fwideDen u) (𝟙 _)) a b ↔
      b.2 = QAtomicType.ofBits u 0 ∧ fwideDen u b.2 b.1 :=
  ⟨fun ⟨_, rfl, h, e⟩ => ⟨e.symm, e ▸ h⟩, fun ⟨e, h⟩ => ⟨_, rfl, e ▸ h, e.symm⟩⟩

/-- **`⦇[0, plus]⦈` at the atom `u`**, the one fold `sum` and `sums` read: `fsumDen` at a float atom (one rule for
    every float atom: added in `f64`, rounded once); at any other atom the left fold of `stepAt u add` from the word
    `0` (exact at `i64`, none past a wrap or the null). -/
def sumDen : (u : QAtomicType) → Core.Rel (Obj.El (.arr (.atom u))) (Obj.El (.atom u))
  | .f32 => fsumDen .f32
  | .f64 => fsumDen .f64
  | u => foldDen (graph fun _ => QAtomicType.ofBits u 0) (stepAt u Ew.add)

/-- q's `sums` per key, `agg(dom(x) (𝟙 × ≥) dom(x), F(x) sumDen)` with `agg(R, f) = dom(R) Λ(R) f`: `(k, i)` to
    `sumDen u` of `x`'s values at `(k, j)`, `j ≤ i` ascending: none at or after a step `plus` refuses (a wrap, the
    null, a NaN); at a float atom each prefix the `f64` sum rounded once to `u`. -/
abbrev sumsDen {K : Obj} {t u : QAtomicType} (T : Core.Rel (Obj.El (.prod K (.atom t))) (Obj.El (.atom u))) :
    Core.Rel (Obj.El (.prod K (.atom t))) (Obj.El (.atom u)) :=
  (𝟙 _ ∩ upToDen T ≫ (upToDen T)°) ≫ lamDen (upToDen T) ≫ mapDen T ≫ sumDen u

/-- `sums` at the position object `P` and the value object `V`: `sumsDen` where both are atoms, `𝟘` elsewhere (no
    `≤`, no `plus`). -/
def sumsAt (K : Obj) : (P V : Obj) → Core.Rel (Obj.El (.prod K P)) (Obj.El V) → Core.Rel (Obj.El (.prod K P)) (Obj.El V)
  | .atom _, .atom _, T => sumsDen T
  | _, _, _ => 𝟘

/-- `sum` at the element object `V`: `sumDen t` where `V` is the atom `t` (q's order, index `0` up), `𝟘` where `V`
    is no atom (no `plus`). -/
def sumAt : (V : Obj) → Core.Rel (Obj.El (.arr V)) (Obj.El V)
  | .atom t => sumDen t
  | _ => 𝟘

/-- `E(T) = Λ(∋ T)`: an array to the canonical list of the images of its elements. -/
abbrev EDen (T : Core.Rel (Obj.El A) (Obj.El B)) : Core.Rel (Obj.El (.arr A)) (Obj.El (.arr B)) := lamDen (memDen ≫ T)

/-- `front(Q)`: the canonical list of the `c` of `xs` that no `b` of `xs` beats
    strictly, `Q` read as its pair test as in `estDen`. -/
abbrev frontDen (TQ : Core.Rel (Obj.El (.prod B B)) (Obj.El (.prod B B))) : Core.Rel (Obj.El (.arr B)) (Obj.El (.arr B)) :=
  lamDen (memDen ∩ ldiv memDen° (diff top (diff (qtDen TQ) (qtDen TQ)°)))

theorem frontDen_iff (TQ : Core.Rel (Obj.El (.prod B B)) (Obj.El (.prod B B))) (xs ys : Obj.El (.arr B)) :
    frontDen TQ xs ys ↔ ys.Pairwise B.lt ∧ ∀ c, c ∈ ys ↔ c ∈ xs ∧ ¬ ∃ b, b ∈ xs ∧ TQ (b, c) (b, c) ∧ ¬ TQ (c, b) (c, b) := by
  simp only [frontDen, lamDen_iff, Core.Rel.inter, ldiv_apply, Core.Rel.diff, Core.Rel.top, Core.Rel.recip, qtDen_iff]
  refine and_congr_right fun _ => forall_congr' fun c => iff_congr Iff.rfl (and_congr_right fun _ => ?_)
  exact ⟨fun h ⟨b, hb, h1, h2⟩ => (h b hb).2 ⟨h1, h2⟩, fun h b hb => ⟨trivial, fun h' => h ⟨b, hb, h'⟩⟩⟩

/-! ### The rows of `prims` -/

/-- A relation argument's meaning with its objects. -/
abbrev Sem := (X Y : Obj) × Core.Rel (Obj.El X) (Obj.El Y)

/-- A row's meaning `D` of its one relation argument, read at `X ⟶ Y`; `𝟘` where the arguments are not one at
    `X ⟶ Y`, where `RowCode.unary` has no code. -/
def Sem.one {X Y A B : Obj} (D : Core.Rel (Obj.El X) (Obj.El Y) → Core.Rel (Obj.El A) (Obj.El B)) : List Sem → Core.Rel (Obj.El A) (Obj.El B)
  | [⟨X', Y', T⟩] => if h : X' = X ∧ Y' = Y then D (h.1 ▸ h.2 ▸ T) else 𝟘
  | _ => 𝟘

/-- `Sem.one` for a row of two relation arguments, read at `X ⟶ Y` and `X₂ ⟶ Y₂`. -/
def Sem.two {X Y X₂ Y₂ A B : Obj} (D : Core.Rel (Obj.El X) (Obj.El Y) → Core.Rel (Obj.El X₂) (Obj.El Y₂) → Core.Rel (Obj.El A) (Obj.El B)) : List Sem → Core.Rel (Obj.El A) (Obj.El B)
  | [⟨X', Y', T⟩, ⟨X₂', Y₂', U⟩] =>
    if h : X' = X ∧ Y' = Y ∧ X₂' = X₂ ∧ Y₂' = Y₂ then D (h.1 ▸ h.2.1 ▸ T) (h.2.2.1 ▸ h.2.2.2 ▸ U) else 𝟘
  | _ => 𝟘

/-- The arguments `ss` bound to the variables `ks`, one for one, the first outermost (as `List.lookup` finds the
    first); every other variable `𝟘`: what a call's body is read under (`Tm.call`). -/
noncomputable def Val.args : List Nat → List Sem → Val
  | k :: ks, ⟨_, _, T⟩ :: ss => (Val.args ks ss).bind k T
  | _, _ => Val.empty

/-- A row of `prims`: its symbol and its objects at its object variables `σ`. -/
structure RowCode where
  sym : String
  ty : List Obj → Obj × Obj

/-- The first and second object variables. -/
abbrev σ₁ (σ : List Obj) : Obj := σ.headD .long
abbrev σ₂ (σ : List Obj) : Obj := σ.getD 1 .long

/-! The rows, each named so its meaning names it. -/
namespace RowCode
def tau : RowCode := ⟨"τ", fun σ => (σ₁ σ, .arr (σ₁ σ))⟩
def cons : RowCode := ⟨"cons", fun σ => (.prod (σ₁ σ) (.arr (σ₁ σ)), .arr (σ₁ σ))⟩
def map : RowCode := ⟨"F", fun σ => (.arr (σ₁ σ), .arr (σ₂ σ))⟩
def filter : RowCode := ⟨"filter", fun σ => (.arr (σ₁ σ), .arr (σ₁ σ))⟩
def takewhile : RowCode := ⟨"takewhile", fun σ => (.arr (σ₁ σ), .arr (σ₁ σ))⟩
def thinL : RowCode := ⟨"thinL", fun σ => (.arr (σ₁ σ), .arr (σ₁ σ))⟩
def merge : RowCode := ⟨"merge", fun σ => (.prod (.arr (σ₁ σ)) (.arr (σ₁ σ)), .arr (σ₁ σ))⟩
def loop : RowCode := ⟨"loop", fun σ => (.prod (σ₁ σ) (.arr (σ₂ σ)), σ₁ σ)⟩
def uncons : RowCode := ⟨"uncons", fun σ => (.arr (σ₁ σ), .prod (σ₁ σ) (.arr (σ₁ σ)))⟩
def length : RowCode := ⟨"length", fun σ => (.arr (σ₁ σ), .long)⟩
def sum : RowCode := ⟨"sum", fun σ => (.arr (σ₁ σ), σ₁ σ)⟩
def inits : RowCode := ⟨"inits", fun σ => (.arr (σ₁ σ), .arr (.arr (σ₁ σ)))⟩
def tails : RowCode := ⟨"tails", fun σ => (.arr (σ₁ σ), .arr (.arr (σ₁ σ)))⟩
def «prefix» : RowCode := ⟨"prefix", fun σ => (.arr (σ₁ σ), .arr (σ₁ σ))⟩
def suffix : RowCode := ⟨"suffix", fun σ => (.arr (σ₁ σ), .arr (σ₁ σ))⟩
def concat : RowCode := ⟨"concat", fun σ => (.arr (.arr (σ₁ σ)), .arr (σ₁ σ))⟩
def cat : RowCode := ⟨"cat", fun σ => (.prod (.arr (σ₁ σ)) (.arr (σ₁ σ)), .arr (σ₁ σ))⟩
def uncat : RowCode := ⟨"uncat", fun σ => (.arr (σ₁ σ), .prod (.arr (σ₁ σ)) (.arr (σ₁ σ)))⟩
def star : RowCode := ⟨"star", fun σ => (σ₁ σ, σ₁ σ)⟩
def zip : RowCode := ⟨"zip", fun σ => (.prod (.arr (σ₁ σ)) (.arr (σ₂ σ)), .arr (.prod (σ₁ σ) (σ₂ σ)))⟩
def snoc : RowCode := ⟨"snoc", fun σ => (.prod (.arr (σ₁ σ)) (σ₁ σ), .arr (σ₁ σ))⟩
def unsnoc : RowCode := ⟨"unsnoc", fun σ => (.arr (σ₁ σ), .prod (.arr (σ₁ σ)) (σ₁ σ))⟩
def setify : RowCode := ⟨"setify", fun σ => (.arr (σ₁ σ), .arr (σ₁ σ))⟩
def positions : RowCode := ⟨"positions", fun σ => (.arr (σ₁ σ), .arr .long)⟩
def asc : RowCode := ⟨"asc", fun σ => (.long, σ₁ σ)⟩
def sums : RowCode := ⟨"sums", fun σ => (.prod (σ₁ σ) (σ₂ σ), σ.getD 2 .long)⟩
def flat : RowCode := ⟨"flat", fun σ => (.prod (σ₁ σ) (σ₂ σ), σ.getD 2 .long)⟩
def cast : RowCode := ⟨"$", fun σ => (σ₁ σ, σ₂ σ)⟩
def ymd : RowCode := ⟨"ymd", fun σ => (.arr (σ₁ σ), σ₂ σ)⟩
def foldI : RowCode := ⟨"foldI", fun σ => (.prod (σ₁ σ) (.arr (σ.getD 2 .long)), σ₂ σ)⟩
def dom : RowCode := ⟨"dom", fun σ => (σ₁ σ, σ₁ σ)⟩
def ran : RowCode := ⟨"ran", fun σ => (σ₂ σ, σ₂ σ)⟩
def nil : RowCode := ⟨"nil", fun σ => (σ₁ σ, .arr (σ₂ σ))⟩
def est : RowCode := ⟨"est", fun σ => (.arr (σ₁ σ), σ₁ σ)⟩
def front : RowCode := ⟨"front", fun σ => (.arr (σ₁ σ), .arr (σ₁ σ))⟩
end RowCode

/-- `ymd` at `[char] ⟶ date`: the graph of `Db.Csv.ymd` on the text's chars (a partial function, the formula not
    copied), the day at `date`'s carrier; `𝟘` at any other objects. -/
def ymdDen : (A B : Obj) → Core.Rel (Obj.El A) (Obj.El B)
  | .arr (.atom .char), .atom .date => graph (fun cs => (Db.Csv.ymd cs).map Int32.ofInt) ≫ (graph some)°
  | _, _ => 𝟘
theorem ymdDen_iff (cs : Obj.El (.arr (.atom .char))) (d : Obj.El (.atom .date)) :
    ymdDen _ _ cs d ↔ (Db.Csv.ymd cs).map Int32.ofInt = some d := graph_recip_graph _ _ _ _

/-- `$` at `A ⟶ B`: the graph of the embedding of `A`'s atom in `B`'s (`QAtomicType.embed`), a partial function that
    never rounds; `𝟘` where a side is no atom. -/
def castDen : (A B : Obj) → Core.Rel (Obj.El A) (Obj.El B)
  | .atom s, .atom t => graph (QAtomicType.embed s t) ≫ (graph some)°
  | _, _ => 𝟘
theorem castDen_iff (s t : QAtomicType) (x : Obj.El (.atom s)) (y : Obj.El (.atom t)) :
    castDen _ _ x y ↔ QAtomicType.embed s t x = some y := graph_recip_graph _ _ _ _

/-- A float verb `o` of `floatOps`: at `F ⟶ D` for an `o` reading one operand, `o` on the value's `f64` word (`fval`);
    at `F×F ⟶ D` for one reading two, `o` on the two components' words; then the word of `D`'s atom for the answer
    (`Op.ofF64`), no row where that is `2^63` (NaN, or no value of `D`'s atom); `𝟘` at any other objects. -/
def floatDen (o : Rel.Kernel.Op) : (A B : Obj) → Core.Rel (Obj.El A) (Obj.El B)
  | .atom t, .atom u => if o.readsAcc = false then
      graph (fun x => (fval t x).bind fun X => wordOut u ((o.eval 0 X).bind fun Y => (Rel.Kernel.Op.ofF64 u).eval 0 Y)) ≫
        (graph some)° else 𝟘
  | .prod (.atom t) (.atom t'), .atom u => if o.readsAcc = true ∧ t = t' then
      graph (fun x => (fval t x.1).bind fun X => (fval t' x.2).bind fun X' =>
        wordOut u ((o.eval X X').bind fun Y => (Rel.Kernel.Op.ofF64 u).eval 0 Y)) ≫ (graph some)° else 𝟘
  | _, _ => 𝟘

theorem floatDen_iff₁ (o : Rel.Kernel.Op) (t u : QAtomicType) (x : Obj.El (.atom t)) (w : Obj.El (.atom u)) :
    floatDen o (.atom t) (.atom u) x w ↔ o.readsAcc = false ∧ ∃ X Y R, fval t x = some X ∧ o.eval 0 X = .ok Y ∧
      (Rel.Kernel.Op.ofF64 u).eval 0 Y = .ok R ∧ R ≠ 0x8000000000000000 ∧ w = QAtomicType.ofBits u R := by
  by_cases h : o.readsAcc = false
  · simp only [floatDen, h, if_true, true_and]
    refine (graph_recip_graph _ _ _ _).trans ?_
    simp only [Option.bind_eq_some_iff]
    constructor
    · rintro ⟨X, hX, hw⟩; obtain ⟨R, hR, hne, rfl⟩ := (wordOut_eq_some _ _ _).1 hw
      obtain ⟨Y, hY, hR'⟩ := (exceptBind_eq_ok _ _ _).1 hR; exact ⟨X, Y, R, hX, hY, hR', hne, rfl⟩
    · rintro ⟨X, Y, R, hX, hY, hR, hne, rfl⟩
      exact ⟨X, hX, (wordOut_eq_some _ _ _).2 ⟨R, (exceptBind_eq_ok _ _ _).2 ⟨Y, hY, hR⟩, hne, rfl⟩⟩
  · simp only [floatDen]; rw [if_neg h]; exact ⟨False.elim, fun ⟨h', _⟩ => absurd h' h⟩

theorem floatDen_iff₂ (o : Rel.Kernel.Op) (t t' u : QAtomicType) (x : Obj.El (.prod (.atom t) (.atom t')))
    (w : Obj.El (.atom u)) : floatDen o (.prod (.atom t) (.atom t')) (.atom u) x w ↔ o.readsAcc = true ∧ t = t' ∧
      ∃ X X' Y R, fval t x.1 = some X ∧ fval t' x.2 = some X' ∧ o.eval X X' = .ok Y ∧
      (Rel.Kernel.Op.ofF64 u).eval 0 Y = .ok R ∧ R ≠ 0x8000000000000000 ∧ w = QAtomicType.ofBits u R := by
  by_cases h : o.readsAcc = true ∧ t = t'
  · simp only [floatDen, h, if_true, h.1, h.2, true_and]
    refine (graph_recip_graph _ _ _ _).trans ?_
    simp only [Option.bind_eq_some_iff]
    constructor
    · rintro ⟨X, hX, X', hX', hw⟩; obtain ⟨R, hR, hne, rfl⟩ := (wordOut_eq_some _ _ _).1 hw
      obtain ⟨Y, hY, hR'⟩ := (exceptBind_eq_ok _ _ _).1 hR; exact ⟨X, X', Y, R, hX, hX', hY, hR', hne, rfl⟩
    · rintro ⟨X, X', Y, R, hX, hX', hY, hR, hne, rfl⟩
      exact ⟨X, hX, X', hX', (wordOut_eq_some _ _ _).2 ⟨R, (exceptBind_eq_ok _ _ _).2 ⟨Y, hY, hR⟩, hne, rfl⟩⟩
  · simp only [floatDen]; rw [if_neg h]; exact ⟨False.elim, fun ⟨a, b, _⟩ => absurd ⟨a, b⟩ h⟩

/-- A value verb `k` at `1+i64` where it orders null (`nulVerb k = some (o, b, _)`, `Op.nulFold`): null is below every
    value, so two values give `Ew.intStep k` of them, and a null beside a value gives the value where `b` is `and`
    (`max`) and the null where it is `or` (`min`); two nulls give the null. As `maxO`/`minO` of
    `Rel/Lang/TestNullMaxMin.lean`, which compose the same cases from `inl°`, `inr°` and the atom verb. -/
def nulStep (k : UInt8) : Core.Rel (Obj.El (.prod (.opt .long) (.opt .long))) (Obj.El (.opt .long)) :=
  match nulVerb k with
  | some (_, b, _) =>
    (rprodMap Core.Rel.inr° Core.Rel.inr° ≫ graph (fun p : Int64 × Int64 => Ew.intStep k Alg.nul p.1 p.2) ≫
      Core.Rel.inr) ∪
    (if b = Op.and then (rprodMap Core.Rel.inr° Core.Rel.inl° ≫ graph Prod.fst ≫ Core.Rel.inr) ∪
        (rprodMap Core.Rel.inl° Core.Rel.inr° ≫ graph Prod.snd ≫ Core.Rel.inr) ∪
        (rprodMap Core.Rel.inl° Core.Rel.inl° ≫ graph Prod.fst ≫ Core.Rel.inl)
     else (graph Prod.fst ≫ Core.Rel.inl° ≫ Core.Rel.inl) ∪ (graph Prod.snd ≫ Core.Rel.inl° ≫ Core.Rel.inl))
  | none => 𝟘

theorem nulStep_iff (k : UInt8) (p : Obj.El (.prod (.opt .long) (.opt .long))) (w : Obj.El (.opt .long)) :
    nulStep k p w ↔ ∃ o b f, nulVerb k = some (o, b, f) ∧ match p.1, p.2 with
      | .inr x, .inr y => w = .inr (Ew.intStep k Alg.nul x y)
      | .inr x, .inl _ | .inl _, .inr x => b = Op.and ∧ w = .inr x ∨ b ≠ Op.and ∧ w = .inl ()
      | .inl _, .inl _ => w = .inl () := by
  obtain ⟨p1, p2⟩ := p
  unfold nulStep
  cases hv : nulVerb k with
  | none => simp [Core.Rel.zero]
  | some v =>
    obtain ⟨o, b, f⟩ := v
    by_cases hb : b = Op.and <;> rcases p1 with ⟨⟩ | x <;> rcases p2 with ⟨⟩ | y <;> rcases w with ⟨⟩ | z <;>
      simp [hb, Core.Rel.comp, Core.Rel.union, Core.Rel.recip, Core.Rel.inl, Core.Rel.inr, Core.Rel.graph,
        Core.Rel.rprodMap, and_assoc]

/-- A value verb `k` of `arithOps` at `A`: `stepAt` at an atom (`arithDen` with no universe), `𝟘` elsewhere. -/
def stepOn (k : UInt8) : (A : Obj) → Core.Rel (Obj.El (.prod A A)) (Obj.El A)
  | .atom t => stepAt t k
  | .opt .long => nulStep k
  | _ => 𝟘

/-- The row `succ` at `A`: at `i64` each value to `Ew.intStep`'s `u + 1` (`succDen` with no universe), `𝟘` elsewhere. -/
def succOn : (A : Obj) → Core.Rel (Obj.El A) (Obj.El A)
  | .atom .i64 => graph fun u => Ew.intStep Ew.add Alg.nul u 1
  | _ => 𝟘

/-- The row `mix` at `A`: at `i64` each counter `u` to `Op.mixWord u`, splitmix64 there; `𝟘` elsewhere. -/
def mixOn : (A : Obj) → Core.Rel (Obj.El A) (Obj.El A)
  | .atom .i64 => graph fun u => (Rel.Kernel.Op.mixWord u.toUInt64).toInt64
  | _ => 𝟘

/-- An order test of `cmpOps` at `A`: at an atom the coreflexive on the pairs `(a, b)` with `ltAt t a b` (`s`) or
    `leAt t a b`, `𝟘` elsewhere. -/
def ordDen (s : Bool) : (A : Obj) → Core.Rel (Obj.El (.prod A A)) (Obj.El (.prod A A))
  | .atom t => 𝟙 _ ∩ (graph Prod.fst ≫ (if s then (ltAt t : Core.Rel _ _) else leAt t) ≫ (graph Prod.snd)°)
  | _ => 𝟘

theorem ordDen_iff (s : Bool) (t : QAtomicType) (p q : Obj.El (.prod (.atom t) (.atom t))) :
    ordDen s (.atom t) p q ↔ q = p ∧ if s then ltAt t p.1 p.2 else leAt t p.1 p.2 := by
  cases s <;> exact ⟨fun ⟨h, _, rfl, _, hR, hq⟩ => ⟨h.symm, by cases h; cases hq; exact hR⟩,
    fun ⟨h, hR⟩ => ⟨h.symm, _, rfl, _, hR, by cases h; rfl⟩⟩

/-- The row `cmpRelRow` at `A` given the universe `U`: `ltDen`/`leqDen` at an atom, `𝟘` elsewhere. -/
def ordRelDen (s : Bool) : (A : Obj) → Core.Rel (Obj.El A) (Obj.El A) → Core.Rel (Obj.El A) (Obj.El A)
  | .atom t => fun U => if s then ltDen t U else leqDen t U
  | _ => fun _ => 𝟘

/-- A row's meaning at its object variables `σ`, given its relation arguments' meanings. -/
abbrev RowDen (c : RowCode) := (σ : List Obj) → List Sem → Core.Rel (Obj.El (c.ty σ).1) (Obj.El (c.ty σ).2)

/-- `a` is in the domain of `T`: the test a row with a relation argument (`filter`, `takewhile`, `positions`, `asc`)
    applies to an element. A test, not a relation, so its body is a predicate of points by nature. -/
abbrev inDom {α β : Type} (T : Core.Rel α β) (a : α) : Prop := ∃ b, T a b

/-- The rows `prefix`/`suffix`: the first/second component of a splitting of `xs` (`uncat`). -/
def splitDen (s : Bool) (A : Type) : Core.Rel (List A) (List A) :=
  (graph fun p : List A × List A => p.1 ++ p.2)° ≫ if s then graph Prod.fst else graph Prod.snd

theorem splitDen_iff (s : Bool) {A : Type} (xs ys : List A) : splitDen s A xs ys ↔ if s then ys <+: xs else ys <:+ xs := by
  cases s
  · exact ⟨fun ⟨p, h, e⟩ => ⟨p.1, by subst e; exact h.symm⟩, fun ⟨t, h⟩ => ⟨(t, ys), h.symm, rfl⟩⟩
  · exact ⟨fun ⟨p, h, e⟩ => ⟨p.2, by subst e; exact h.symm⟩, fun ⟨t, h⟩ => ⟨(ys, t), h.symm, rfl⟩⟩

/-- The row `loop` given the step `T`: the left fold `foldDen` of `T` over the list whose start is the pair's own first
    component (`foldDen_iter`). Pointwise until `foldDen` has a start read from the input (PF-FOLD), which this row
    needs and no relation `Rel (V × List E) V` built from `foldDen`'s constant-start form gives. -/
def loopDen {X Y : Obj} (T : Core.Rel (Obj.El (.prod X Y)) (Obj.El X)) : Core.Rel (Obj.El (.prod X (.arr Y))) (Obj.El X) :=
  fun p c => ∃ g : Nat → X.El, g 0 = p.1 ∧ (∀ t (ht : t < p.2.length), T (g t, p.2[t]'ht) (g (t + 1))) ∧ c = g p.2.length

open Classical RowCode in
/-- Every row of `prims` with its meaning. `setify` is `Λ(∋)`. -/
def rowDens : List ((c : RowCode) × RowDen c) :=
  [⟨tau, fun _ _ => graph fun a => [a]⟩,
   ⟨cons, fun _ _ => graph fun p => p.1 :: p.2⟩,
   ⟨map, fun σ => Sem.one (X := σ₁ σ) (Y := σ₂ σ) mapDen⟩,
   ⟨filter, fun σ => Sem.one (X := σ₁ σ) (Y := σ₁ σ) fun T => graph fun xs => xs.filter fun x => decide (inDom T x)⟩,
   ⟨takewhile, fun σ => Sem.one (X := σ₁ σ) (Y := σ₁ σ) fun T =>
      graph fun xs => xs.takeWhile fun x => decide (inDom T x)⟩,
   ⟨thinL, fun σ => Sem.one (X := .prod (σ₁ σ) (σ₁ σ)) (Y := .prod (σ₁ σ) (σ₁ σ)) fun T =>
      thinLDen fun a b => decide (T (a, b) (a, b))⟩,
   ⟨merge, fun σ => Sem.one (X := .prod (σ₁ σ) (σ₁ σ)) (Y := .prod (σ₁ σ) (σ₁ σ)) fun T =>
      graph fun p => List.merge p.1 p.2 fun a b => decide (T (a, b) (a, b))⟩,
   ⟨loop, fun σ => Sem.one (X := .prod (σ₁ σ) (σ₂ σ)) (Y := σ₁ σ) loopDen⟩,
   ⟨uncons, fun _ _ => (graph fun p => p.1 :: p.2)°⟩,
   ⟨length, fun _ _ => graph fun xs => Int64.ofNat xs.length⟩,
   ⟨sum, fun σ _ => sumAt (σ₁ σ)⟩,
   ⟨inits, fun _ _ => graph fun xs => (List.range (xs.length + 1)).map fun k => xs.take k⟩,
   ⟨tails, fun _ _ => graph fun xs => (List.range (xs.length + 1)).map fun k => xs.drop k⟩,
   -- the prefixes of `xs` are the first components of its splittings `uncat`, the suffixes the second
   ⟨«prefix», fun σ _ => splitDen true (σ₁ σ).El⟩,
   ⟨suffix, fun σ _ => splitDen false (σ₁ σ).El⟩,
   ⟨concat, fun _ _ => graph fun xss => xss.flatten⟩,
   ⟨cat, fun _ _ => graph fun p => p.1 ++ p.2⟩,
   ⟨uncat, fun _ _ => (graph fun p => p.1 ++ p.2)°⟩,
   ⟨zip, fun _ _ => graph fun p => p.1.zip p.2⟩,
   ⟨snoc, fun _ _ => graph fun p => p.1 ++ [p.2]⟩,
   ⟨unsnoc, fun _ _ => (graph fun p => p.1 ++ [p.2])°⟩,
   ⟨setify, fun σ _ => lamDen (memDen (A := σ₁ σ))⟩,
   -- dataframe §3.1's `where(dom(xs ≫ p))`: the positions of `xs` whose element is in `dom(p)`, ascending
   ⟨positions, fun σ => Sem.one (X := σ₁ σ) (Y := σ₁ σ) fun T =>
      graph (positionsL fun x => decide (inDom T x))⟩,
   -- q's `asc` of the set `dom P`: `j` to its `j`-th element in `Obj.lt` order
   ⟨asc, fun σ => Sem.one (X := σ₁ σ) (Y := σ₁ σ) fun T => ascDen (σ₁ σ) (inDom T)⟩,
   ⟨sums, fun σ => Sem.one (X := .prod (σ₁ σ) (σ₂ σ)) (Y := σ.getD 2 .long) (sumsAt (σ₁ σ) (σ₂ σ) (σ.getD 2 .long))⟩,
   ⟨flat, fun σ => Sem.one (X := σ₁ σ) (Y := .prod (σ₂ σ) (σ.getD 2 .long)) flatDen⟩,
   ⟨cast, fun σ _ => castDen (σ₁ σ) (σ₂ σ)⟩,
   -- a text to the day it spells (`ymdDen`)
   ⟨ymd, fun σ _ => ymdDen (.arr (σ₁ σ)) (σ₂ σ)⟩,
   ⟨foldI, fun σ => Sem.two (X := σ₁ σ) (Y := .prod (σ₂ σ) (σ₂ σ))
      (X₂ := .prod (.prod (σ₁ σ) (σ₂ σ)) (σ.getD 2 .long)) (Y₂ := .prod (σ₁ σ) (σ₂ σ)) foldIDen⟩,
   -- the prelude's `star(R) ≜ μX : 𝟙 ∪ R X`, its body as `Tm.den` reads the definition's `μ`
   ⟨star, fun σ => Sem.one (X := σ₁ σ) (Y := σ₁ σ) fun T => Core.Rel.mu fun X => 𝟙 _ ∪ T ≫ X⟩,
   ⟨dom, fun σ => Sem.one (X := σ₁ σ) (Y := σ₂ σ) fun T => 𝟙 _ ∩ T ≫ T°⟩,
   ⟨ran, fun σ => Sem.one (X := σ₁ σ) (Y := σ₂ σ) fun T => 𝟙 _ ∩ T° ≫ T°°⟩,
   ⟨nil, fun _ _ => nilDen⟩,
   ⟨est, fun σ => Sem.one (X := .prod (σ₁ σ) (σ₁ σ)) (Y := .prod (σ₁ σ) (σ₁ σ)) estDen⟩,
   ⟨front, fun σ => Sem.one (X := .prod (σ₁ σ) (σ₁ σ)) (Y := .prod (σ₁ σ) (σ₁ σ)) frontDen⟩] ++
  floatOps.map (fun (s, o, _) =>
    ⟨⟨s, fun σ => (if o.readsAcc then .prod (σ₁ σ) (σ₁ σ) else σ₁ σ, σ₂ σ)⟩, fun _ _ => floatDen o _ _⟩) ++
  arithOps.map (fun (s, k) => ⟨⟨s, fun σ => (.prod (σ₁ σ) (σ₁ σ), σ₁ σ)⟩, fun σ _ => stepOn k (σ₁ σ)⟩) ++
  [⟨⟨"succ", fun σ => (σ₁ σ, σ₁ σ)⟩, fun σ _ => succOn (σ₁ σ)⟩,
   ⟨⟨"mix", fun σ => (σ₁ σ, σ₁ σ)⟩, fun σ _ => mixOn (σ₁ σ)⟩,
   ⟨⟨"at", fun σ => (.prod (.arr (σ₁ σ)) (σ₂ σ), σ₁ σ)⟩, fun σ _ => atOn (σ₁ σ) (σ₂ σ)⟩] ++
  cmpOps.map (fun (s, b) => ⟨⟨s, fun σ => (.prod (σ₁ σ) (σ₁ σ), .prod (σ₁ σ) (σ₁ σ))⟩, fun σ _ => ordDen b (σ₁ σ)⟩) ++
  cmpOps.map fun (_, b) => ⟨⟨ordSym b, fun σ => (σ₁ σ, σ₁ σ)⟩,
    fun σ => Sem.one (X := σ₁ σ) (Y := σ₁ σ) (ordRelDen b (σ₁ σ))⟩


/-- The row `r`'s meaning at `A ⟶ B` given its relation arguments' meanings, found as `Prim.run` finds its code;
    `𝟘` where it has none there. -/
def Prim.den (r : Prim) (A B : Obj) (ss : List Sem) : Core.Rel (Obj.El A) (Obj.El B) :=
  match rowDens.find? (·.1.sym == r.sym), r.objs A B (ss.map fun s => (s.1, s.2.1)) with
  | some ⟨c, D⟩, some σ => if h : (c.ty σ).1 = A ∧ (c.ty σ).2 = B then h.1 ▸ h.2 ▸ D σ ss else 𝟘
  | _, _ => 𝟘

/-! ### `⟦−⟧` -/

mutual
/-- `⟦t⟧ρ`, one clause per constructor. A row and its arguments (`prim` under `arg`s) mean the row's meaning of
    its arguments' (`Tm.argDen`). A call (the `let` node) is its body read under its arguments bound at `ks`
    (`Val.args`), never under the caller's `ρ`; given none, under no variable. -/
noncomputable def Tm.den : Val → {A B : Obj} → Tm A B → Core.Rel (Obj.El A) (Obj.El B)
  | _, _, _, .val R => rep R
  | _, _, _, .uni U => (graph U.row)° ≫ graph U.row
  | _, _, _, .zero => 𝟘
  | _, _, _, .id => 𝟙 _
  | ρ, _, _, .top V => Core.Rel.top ≫ V.den ρ
  | _, _, _, .outl => graph Prod.fst
  | _, _, _, .outr => graph Prod.snd
  | ρ, _, _, .comp R S => R.den ρ ≫ S.den ρ
  | ρ, _, _, .conv R => (R.den ρ)°
  | ρ, _, _, .meet R S => R.den ρ ∩ S.den ρ
  | ρ, _, _, .join R S => R.den ρ ∪ S.den ρ
  | ρ, _, _, .diff R S => Core.Rel.diff (R.den ρ) (S.den ρ)
  | ρ, _, _, .ldiv R S U V => ldivDen (R.den ρ) (S.den ρ) (U.den ρ) (V.den ρ)
  | ρ, _, _, .rdiv R S U V => rdivDen (R.den ρ) (S.den ρ) (U.den ρ) (V.den ρ)
  | ρ, _, _, .pair R S => rpair (R.den ρ) (S.den ρ)
  | ρ, _, _, .lam R => lamDen (R.den ρ)
  | _, _, _, .mem => memDen
  | _, _, _, .inl => Core.Rel.inl
  | _, _, _, .inr => Core.Rel.inr
  | _, A, B, .prim r => Prim.den r A B []
  | ρ, _, _, .foldr e S => foldrDen (e.den ρ) (S.den ρ)
  | ρ, _, _, .fold e S => foldDen (e.den ρ) (S.den ρ)
  | ρ, A, B, .var k => ρ k A B
  | _, _, _, .call ks _ _ _ b => b.den (Val.args ks [])
  | ρ, _, _, .arg f x => f.argDen ρ [⟨_, _, x.den ρ⟩]
  -- the rounds start at `⟦S⟧` and meet each with it (`Gen.nu`), so `S` bounds the greatest fixed point
  | ρ, _, _, .nu k S b => Core.Rel.nu fun X => S.den ρ ∩ b.den (ρ.bind k X)
  | ρ, _, _, .mu k _ _ b => Core.Rel.mu fun X => b.den (ρ.bind k X)
  | ρ, _, _, .hylo k _ b => Core.Rel.mu fun X => b.den (ρ.bind k X)

/-- The spine `f` of a row given the meanings `ss` of its later arguments: the row's meaning of all of them, in
    the order `compile` passes their codes; a call's body with them bound at its `ks`; `𝟘` where `f` is neither
    a row nor a call under `arg`s. -/
noncomputable def Tm.argDen : Val → {A B : Obj} → Tm A B → List Sem → Core.Rel (Obj.El A) (Obj.El B)
  | _, A, B, .prim r, ss => Prim.den r A B ss
  | _, _, _, .call ks _ _ _ b, ss => b.den (Val.args ks ss)
  | ρ, _, _, .arg f x, ss => f.argDen ρ (⟨_, _, x.den ρ⟩ :: ss)
  -- a spine's converse (`convTm` of a row with no converse row) means its meaning conversed
  | ρ, _, _, .conv R, ss => (R.argDen ρ ss)°
  | _, _, _, _, _ => 𝟘
end

/-- `domRow` at `A ⟶ A` given `T : A ⟶ B` means `𝟙 ∩ T T°`; its definition `⟨𝟙,R⟩π₁` means the same
    (`Tm.domDef_den`). -/
theorem Prim.den_domRow {A B : Obj} (T : Core.Rel (Obj.El A) (Obj.El B)) :
    Prim.den domRow A A [⟨A, B, T⟩] = 𝟙 _ ∩ T ≫ T° := by
  have ho : domRow.objs A A [(A, B)] = some [A, B] := by
    simp [Prim.objs, Option.orElse, domRow, OExp.unify, Prim.vars, OExp.vars, List.eraseDups, List.eraseDupsBy,
      List.eraseDupsBy.loop, List.lookup]
  have hf : rowDens.find? (·.1.sym == domRow.sym) =
      some ⟨RowCode.dom, fun σ => Sem.one (X := σ₁ σ) (Y := σ₂ σ) fun T => 𝟙 _ ∩ T ≫ T°⟩ := rfl
  unfold Prim.den; simp only [List.map_cons, List.map_nil]
  rw [hf, ho]; dsimp only; rw [dif_pos ⟨rfl, rfl⟩]
  simp only [Sem.one]; exact dif_pos ⟨rfl, rfl⟩

/-- `ranRow` at `B ⟶ B` given `T : A ⟶ B` means `𝟙 ∩ T° T`; its definition `dom(R°)` means the same
    (`Tm.ranDef_den`). -/
theorem Prim.den_ranRow {A B : Obj} (T : Core.Rel (Obj.El A) (Obj.El B)) :
    Prim.den ranRow B B [⟨A, B, T⟩] = 𝟙 _ ∩ T° ≫ T°° := by
  have ho : ranRow.objs B B [(A, B)] = some [A, B] := by
    simp [Prim.objs, Option.orElse, ranRow, OExp.unify, Prim.vars, OExp.vars, List.eraseDups, List.eraseDupsBy,
      List.eraseDupsBy.loop, List.lookup]
  have hf : rowDens.find? (·.1.sym == ranRow.sym) =
      some ⟨RowCode.ran, fun σ => Sem.one (X := σ₁ σ) (Y := σ₂ σ) fun T => 𝟙 _ ∩ T° ≫ T°°⟩ := rfl
  unfold Prim.den; simp only [List.map_cons, List.map_nil]
  rw [hf, ho]; dsimp only; rw [dif_pos ⟨rfl, rfl⟩]
  simp only [Sem.one]; exact dif_pos ⟨rfl, rfl⟩

/-- `nilRow` at `A ⟶ [B]` means `nilDen`; its definition `Λ(𝟘)` means the same (`Tm.nilDef_den`). -/
theorem Prim.den_nilRow {A B : Obj} : Prim.den nilRow A (.arr B) [] = nilDen := by
  have ho : nilRow.objs A (.arr B) [] = some [A, B] := by
    simp [Prim.objs, Option.orElse, nilRow, OExp.unify, Prim.vars, OExp.vars, List.eraseDups, List.eraseDupsBy,
      List.eraseDupsBy.loop, List.lookup]
  have hf : rowDens.find? (·.1.sym == nilRow.sym) = some ⟨RowCode.nil, fun _ _ => nilDen⟩ := rfl
  unfold Prim.den; simp only [List.map_nil]
  rw [hf, ho]; dsimp only; rw [dif_pos ⟨rfl, rfl⟩]; rfl

/-- `Tm.dom R`, `domRow` given `R`, means `𝟙 ∩ R R°` (`Prim.den_domRow`). -/
theorem Tm.dom_den (ρ : Val) {A B : Obj} (R : Tm A B) : (Tm.dom R).den ρ = 𝟙 _ ∩ R.den ρ ≫ (R.den ρ)° := by
  simp only [Tm.dom, Tm.den, Tm.argDen]; exact Prim.den_domRow _

/-- `Tm.ran R`, `ranRow` given `R`, means `𝟙 ∩ R° R` (`Prim.den_ranRow`). -/
theorem Tm.ran_den (ρ : Val) {A B : Obj} (R : Tm A B) : (Tm.ran R).den ρ = 𝟙 _ ∩ (R.den ρ)° ≫ (R.den ρ)°° := by
  simp only [Tm.ran, Tm.den, Tm.argDen]; exact Prim.den_ranRow _

/-- `estRow` at `[B] ⟶ B` given the pair test `T` means `estDen T`; its definition `∋ ∩ (∈ \ (Q ∪ 𝟙)°)` means the
    same where `T` is `τ(Q)` (`Tm.estDef_den`). -/
theorem Prim.den_estRow {B : Obj} (T : Core.Rel (Obj.El (.prod B B)) (Obj.El (.prod B B))) :
    Prim.den estRow (.arr B) B [⟨.prod B B, .prod B B, T⟩] = estDen T := by
  have ho : estRow.objs (.arr B) B [(.prod B B, .prod B B)] = some [B] := by
    simp [Prim.objs, Option.orElse, estRow, OExp.unify, Prim.vars, OExp.vars, List.eraseDups, List.eraseDupsBy,
      List.eraseDupsBy.loop, List.lookup]
  have hf : rowDens.find? (·.1.sym == estRow.sym) = some ⟨RowCode.est, fun σ =>
      Sem.one (X := .prod (σ₁ σ) (σ₁ σ)) (Y := .prod (σ₁ σ) (σ₁ σ)) estDen⟩ := rfl
  unfold Prim.den; simp only [List.map_cons, List.map_nil]
  rw [hf, ho]; dsimp only; rw [dif_pos ⟨rfl, rfl⟩]
  simp only [Sem.one]; exact dif_pos ⟨rfl, rfl⟩

/-- `frontRow` at `[B] ⟶ [B]` given the pair test `T` means `frontDen T`; its definition `Λ(∋ − ∋ (Q − Q°))` means
    the same where `T` is `τ(Q)` (`Tm.frontDef_den`). -/
theorem Prim.den_frontRow {B : Obj} (T : Core.Rel (Obj.El (.prod B B)) (Obj.El (.prod B B))) :
    Prim.den frontRow (.arr B) (.arr B) [⟨.prod B B, .prod B B, T⟩] = frontDen T := by
  have ho : frontRow.objs (.arr B) (.arr B) [(.prod B B, .prod B B)] = some [B] := by
    simp [Prim.objs, Option.orElse, frontRow, OExp.unify, Prim.vars, OExp.vars, List.eraseDups, List.eraseDupsBy,
      List.eraseDupsBy.loop, List.lookup]
  have hf : rowDens.find? (·.1.sym == frontRow.sym) = some ⟨RowCode.front, fun σ =>
      Sem.one (X := .prod (σ₁ σ) (σ₁ σ)) (Y := .prod (σ₁ σ) (σ₁ σ)) frontDen⟩ := rfl
  unfold Prim.den; simp only [List.map_cons, List.map_nil]
  rw [hf, ho]; dsimp only; rw [dif_pos ⟨rfl, rfl⟩]
  simp only [Sem.one]; exact dif_pos ⟨rfl, rfl⟩

/-- `Tm.est Q`, `estRow` given the pair test `Q`, means `estDen` of it (`Prim.den_estRow`). -/
theorem Tm.est_den (ρ : Val) {B : Obj} (Q : Tm (.prod B B) (.prod B B)) : (Tm.est Q).den ρ = estDen (Q.den ρ) := by
  simp only [Tm.est, Tm.den, Tm.argDen]; exact Prim.den_estRow _

/-- `Tm.front Q`, `frontRow` given the pair test `Q`, means `frontDen` of it (`Prim.den_frontRow`). -/
theorem Tm.front_den (ρ : Val) {B : Obj} (Q : Tm (.prod B B) (.prod B B)) :
    (Tm.front Q).den ρ = frontDen (Q.den ρ) := by
  simp only [Tm.front, Tm.den, Tm.argDen]; exact Prim.den_frontRow _

/-- `succRow` at `ℕ ⟶ ℕ` is `Ew.intStep`'s `u + 1` (`succOn`). -/
theorem Prim.den_succRow : Prim.den succRow .long .long [] = fun u w => w = Ew.intStep Ew.add Alg.nul u 1 := by
  have ho : ∀ ps, succRow.objs .long .long ps = some [.long] := by
    simp [Prim.objs, Option.orElse, succRow, OExp.unify, Prim.vars, OExp.vars, List.eraseDups, List.eraseDupsBy,
      List.eraseDupsBy.loop, List.lookup]
  have hf : rowDens.find? (·.1.sym == succRow.sym) =
      some ⟨⟨"succ", fun σ => (σ₁ σ, σ₁ σ)⟩, fun σ _ => succOn (σ₁ σ)⟩ := rfl
  unfold Prim.den; rw [hf, ho]; dsimp only; rw [dif_pos ⟨rfl, rfl⟩]; rfl

/-- `arithRow "plus"` at the atom `t` is `stepAt t add` (`stepOn`). -/
theorem Prim.den_plusRow {t : QAtomicType} :
    Prim.den (arithRow "plus") (.prod (.atom t) (.atom t)) (.atom t) [] = stepAt t Ew.add := by
  have ho : ∀ ps, (arithRow "plus").objs (.prod (.atom t) (.atom t)) (.atom t) ps = some [.atom t] := by
    simp [Prim.objs, Option.orElse, arithRow, OExp.unify, Prim.vars, OExp.vars, List.eraseDups, List.eraseDupsBy,
      List.eraseDupsBy.loop, List.lookup]
  have hf : rowDens.find? (·.1.sym == (arithRow "plus").sym) =
      some ⟨⟨"plus", fun σ => (.prod (σ₁ σ) (σ₁ σ), σ₁ σ)⟩, fun σ _ => stepOn Ew.add (σ₁ σ)⟩ := rfl
  unfold Prim.den; rw [hf, ho]; dsimp only; rw [dif_pos ⟨rfl, rfl⟩]; rfl

/-- **`succ` cut to a coreflexive `U` is `succDen`**: `U succ U` (`Tm.cut1`) keeps `u` and `u + 1` both in `U`. -/
theorem Tm.cut1_succ_den (ρ : Val) (U : Tm .long .long) (hU : ∀ x y, U.den ρ x y → x = y) :
    (Tm.cut1 succRow U).den ρ = succDen (U.den ρ) := by
  funext a w; apply propext
  rw [succDen_iff]
  simp only [Tm.cut1, Tm.den, Tm.argDen, Prim.den_succRow, Core.Rel.comp]
  constructor
  · rintro ⟨a', h1, w', rfl, h2⟩; obtain rfl := hU _ _ h1; obtain rfl := hU _ _ h2; exact ⟨⟨_, h1⟩, rfl, _, h2⟩
  · rintro ⟨⟨v, h1⟩, rfl, v', h2⟩; obtain rfl := hU _ _ h1; obtain rfl := hU _ _ h2; exact ⟨_, h1, _, rfl, h2⟩

/-- `Rᴵ`'s definition `⟨π₁R,π₂⟩dom(π₁π₁ ∩ π₂)π₁π₂` (`Pre.flat`) means `flatDen`: the `(a', b)` of `R` at the key,
    kept where `a'` is the source, then `b`. -/
theorem Tm.flat_den (ρ : Val) {I A B : Obj} (R : Tm I (.prod A B)) :
    (Tm.comp (.pair (.comp .outl R) .outr) (.comp (.dom (.meet (.comp .outl .outl) .outr)) (.comp .outl .outr))).den ρ
      = flatDen (R.den ρ) := by
  apply Core.Rel.ext; intro x b
  simp [Tm.den, Tm.dom_den, flatDen, Core.Rel.comp, Core.Rel.rpair, Core.Rel.inter, Core.Rel.recip, Core.Rel.graph]
  constructor
  · rintro ⟨a, b', ⟨h, rfl⟩, he⟩
    cases (show ((x.2, b'), x.2) = ((x.2, b), x.2) from he); exact h
  · intro h; exact ⟨_, _, ⟨h, rfl⟩, rfl⟩

/-- **`R × S` is a definition**: `⟨π₁R, π₂S⟩` (`Tm.prod`) means `rprodMap`, each side of a pair through its
    operand (`Rep.rpair_eq_meet_proj` for the pair as a meet of projections). -/
theorem Tm.prod_den (ρ : Val) {A B C D : Obj} (R : Tm A B) (S : Tm C D) :
    (R.prod S).den ρ = rprodMap (R.den ρ) (S.den ρ) := by
  apply Core.Rel.ext; intro p q
  simp [Tm.prod, Tm.den, Core.Rel.comp, Core.Rel.rpair, Core.Rel.rprodMap, Core.Rel.graph]

/-- The closed product universe `ran(⟨u, ⊤(v)⟩)` (`Tm.prodUni`) means `u × v` where `u` and `v` are coreflexives,
    as a universe is. -/
theorem Tm.prodUni_den (ρ : Val) {A B : Obj} (u : Tm A A) (v : Tm B B) (hu : ∀ x y, u.den ρ x y → x = y)
    (hv : ∀ x y, v.den ρ x y → x = y) : (u.prodUni v).den ρ = rprodMap (u.den ρ) (v.den ρ) := by
  apply Core.Rel.ext; intro p q
  simp only [Tm.prodUni, Tm.ran_den, Tm.den, Core.Rel.comp, Core.Rel.rpair, Core.Rel.rprodMap, Core.Rel.inter,
    Core.Rel.recip, Core.Rel.top, Core.Rel.id]
  constructor
  · rintro ⟨rfl, m, ⟨h1, y, -, h2⟩, -⟩
    obtain rfl := hu _ _ h1; obtain rfl := hv _ _ h2; exact ⟨h1, h2⟩
  · rintro ⟨h1, h2⟩
    obtain ⟨a, b⟩ := p; obtain ⟨c, d⟩ := q
    obtain rfl := hu _ _ h1; obtain rfl := hv _ _ h2
    exact ⟨rfl, a, ⟨h1, b, trivial, h2⟩, h1, b, trivial, h2⟩

/-- **Symmetric division is a definition**: the term `R/S ∩ (S/R)°` that `Pre.symDiv` builds means `R÷S` within the
    universes `UA`, `UB`. -/
theorem Tm.symDiv_den (ρ : Val) {A B C : Obj} (R : Tm A C) (S : Tm B C) (UA : Tm A A) (UB : Tm B B) :
    (Tm.meet (.rdiv R S UA UB) (.conv (.rdiv S R UB UA))).den ρ =
      symDivDen (UA.den ρ) (UB.den ρ) (R.den ρ) (S.den ρ) := by
  simp only [Tm.den]

/-- `⟦t⟧`, and `t`'s meaning as a row's spine, read `ρ` only at the variables free in `t`. -/
theorem Tm.den_congr : ∀ {A B : Obj} (t : Tm A B) (ρ ρ' : Val), (∀ i ∈ t.fv, ρ i = ρ' i) →
    t.den ρ = t.den ρ' ∧ ∀ ss, t.argDen ρ ss = t.argDen ρ' ss := by
  intro A B t
  induction t with
  | var k => intro ρ ρ' h; exact ⟨by simp only [Tm.den, h k (by simp [Tm.fv])], fun _ => rfl⟩
  | top V ih => intro ρ ρ' h; exact ⟨by simp only [Tm.den, (ih ρ ρ' fun i hi => h i (by simp [Tm.fv, hi])).1], fun _ => rfl⟩
  | comp R S ihR ihS | meet R S ihR ihS | join R S ihR ihS | diff R S ihR ihS | pair R S ihR ihS
  | foldr R S ihR ihS | fold R S ihR ihS =>
    intro ρ ρ' h
    exact ⟨by simp only [Tm.den, (ihR ρ ρ' fun i hi => h i (by simp [Tm.fv, hi])).1,
      (ihS ρ ρ' fun i hi => h i (by simp [Tm.fv, hi])).1], fun _ => rfl⟩
  | arg f x ihf ihx =>
    intro ρ ρ' h
    have hx := (ihx ρ ρ' fun i hi => h i (by simp [Tm.fv, hi])).1
    have hf := (ihf ρ ρ' fun i hi => h i (by simp [Tm.fv, hi])).2
    exact ⟨by simp only [Tm.den, hx, hf], fun _ => by simp only [Tm.argDen, hx, hf]⟩
  | conv R ih =>
    intro ρ ρ' h
    have e := ih ρ ρ' fun i hi => h i (by simp [Tm.fv, hi])
    exact ⟨by simp only [Tm.den, e.1], fun ss => by simp only [Tm.argDen, e.2 ss]⟩
  | lam R ih =>
    intro ρ ρ' h; exact ⟨by simp only [Tm.den, (ih ρ ρ' fun i hi => h i (by simp [Tm.fv, hi])).1], fun _ => rfl⟩
  | ldiv R S U V ihR ihS ihU ihV | rdiv R S U V ihR ihS ihU ihV =>
    intro ρ ρ' h
    exact ⟨by simp only [Tm.den, (ihR ρ ρ' fun i hi => h i (by simp [Tm.fv, hi])).1,
      (ihS ρ ρ' fun i hi => h i (by simp [Tm.fv, hi])).1, (ihU ρ ρ' fun i hi => h i (by simp [Tm.fv, hi])).1,
      (ihV ρ ρ' fun i hi => h i (by simp [Tm.fv, hi])).1], fun _ => rfl⟩
  | nu k S b ihS ih =>
    intro ρ ρ' h
    refine ⟨?_, fun _ => rfl⟩
    simp only [Tm.den, (ihS ρ ρ' fun i hi => h i (by simp [Tm.fv, hi])).1]
    congr 1; funext X; congr 1
    refine (ih _ _ fun i hi => ?_).1
    by_cases e : i = k
    · subst e; exact Val.bind_same
    · rw [Val.bind_ne e, Val.bind_ne e]; exact h i (by simp [Tm.fv, hi, e])
  | mu k _ _ b ih | hylo k _ b ih =>
    intro ρ ρ' h
    refine ⟨?_, fun _ => rfl⟩
    simp only [Tm.den]
    congr 1; funext X
    refine (ih _ _ fun i hi => ?_).1
    by_cases e : i = k
    · subst e; exact Val.bind_same
    · rw [Val.bind_ne e, Val.bind_ne e]; exact h i (by simp [Tm.fv, hi, e])
  | _ => intro ρ ρ' _; exact ⟨rfl, fun _ => rfl⟩

/-! ### Substitution -/









/-! ### Monotonicity -/

/-- `ρ'` grows `ρ` at the variable `k` and agrees with it at every other. -/
def Val.Grow (k : Nat) (ρ ρ' : Val) : Prop := (∀ A B, ρ k A B ⊑ ρ' k A B) ∧ ∀ i, i ≠ k → ρ i = ρ' i

/-- `X ⊑ Y` read with the sign `s`: `true` keeps it, `false` turns it round. -/
def sle (s : Bool) {A B : Obj} (X Y : Core.Rel (Obj.El A) (Obj.El B)) : Prop := cond s (X ⊑ Y) (Y ⊑ X)

theorem Val.Grow.congr {k : Nat} {ρ ρ' : Val} (g : Grow k ρ ρ') {A B : Obj} {t : Tm A B}
    (h : t.fv.contains k = false) : t.den ρ = t.den ρ' :=
  (t.den_congr ρ ρ' fun i hi => g.2 i fun e => by subst e; simp [hi] at h).1

theorem Val.Grow.bind {k j : Nat} {ρ ρ' : Val} (g : Grow k ρ ρ') (hj : j ≠ k) {A B : Obj} (X : Core.Rel (Obj.El A) (Obj.El B)) :
    Grow k (ρ.bind j X) (ρ'.bind j X) := by
  refine ⟨fun A' B' => ?_, fun i hi => ?_⟩
  · rw [Val.bind_ne (Ne.symm hj), Val.bind_ne (Ne.symm hj)]; exact g.1 A' B'
  · by_cases e : i = j
    · subst e; exact Val.bind_same
    · rw [Val.bind_ne e, Val.bind_ne e]; exact g.2 i hi

/-- Binding `k` to a larger `Y` grows the valuation at `k`. -/
theorem Val.Grow.of_le {k : Nat} {ρ : Val} {X Y : Core.Rel (Obj.El A) (Obj.El B)} (hXY : X ⊑ Y) : Grow k (ρ.bind k X) (ρ.bind k Y) := by
  refine ⟨fun A' B' => ?_, fun i hi => by rw [Val.bind_ne hi, Val.bind_ne hi]⟩
  simp only [Val.bind, if_true]
  by_cases h : A = A' ∧ B = B'
  · obtain ⟨rfl, rfl⟩ := h; simpa using hXY
  · simp only [dif_neg h]; exact Core.Rel.le_refl _

section ops
variable {D E F : Obj}

theorem comp_le' {X X' : Core.Rel (Obj.El A) (Obj.El B)} {Y Y' : Core.Rel (Obj.El B) (Obj.El C)} (hX : X ⊑ X') (hY : Y ⊑ Y') : X ≫ Y ⊑ X' ≫ Y' :=
  le_iff.2 fun a c h => by
    rw [comp_apply] at h ⊢; obtain ⟨b, h1, h2⟩ := h; exact ⟨b, le_iff.1 hX _ _ h1, le_iff.1 hY _ _ h2⟩

theorem conv_le' {X X' : Core.Rel (Obj.El A) (Obj.El B)} (hX : X ⊑ X') : X° ⊑ X'° :=
  le_iff.2 fun a b h => by rw [recip_apply] at h ⊢; exact le_iff.1 hX _ _ h

theorem inter_le' {X X' Y Y' : Core.Rel (Obj.El A) (Obj.El B)} (hX : X ⊑ X') (hY : Y ⊑ Y') : X ∩ Y ⊑ X' ∩ Y' :=
  le_iff.2 fun a b h => by rw [inter_apply] at h ⊢; exact ⟨le_iff.1 hX _ _ h.1, le_iff.1 hY _ _ h.2⟩

theorem union_le' {X X' Y Y' : Core.Rel (Obj.El A) (Obj.El B)} (hX : X ⊑ X') (hY : Y ⊑ Y') : X ∪ Y ⊑ X' ∪ Y' :=
  le_iff.2 fun a b h => by rw [union_apply] at h ⊢; exact h.imp (le_iff.1 hX _ _) (le_iff.1 hY _ _)

theorem diff_le {X X' Y Y' : Core.Rel (Obj.El A) (Obj.El B)} (hX : X ⊑ X') (hY : Y' ⊑ Y) : Core.Rel.diff X Y ⊑ Core.Rel.diff X' Y' :=
  le_iff.2 fun _ _ h => ⟨le_iff.1 hX _ _ h.1, fun h' => h.2 (le_iff.1 hY _ _ h')⟩

theorem ldiv_le {R : Core.Rel (Obj.El A) (Obj.El B)} {S S' : Core.Rel (Obj.El A) (Obj.El C)} {U U' : Core.Rel (Obj.El B) (Obj.El B)} {V V' : Core.Rel (Obj.El C) (Obj.El C)} (hS : S ⊑ S') (hU : U ⊑ U')
    (hV : V ⊑ V') : ldivDen R S U V ⊑ ldivDen R S' U' V' :=
  le_iff.2 fun _ _ h => have h := ldivDen_iff.1 h
    ldivDen_iff.2 ⟨fun a ha => le_iff.1 hS _ _ (h.1 a ha),
      h.2.imp id fun ⟨⟨b', hb⟩, c', hc⟩ => ⟨⟨b', le_iff.1 hU _ _ hb⟩, c', le_iff.1 hV _ _ hc⟩⟩

theorem rdiv_le {R R' : Core.Rel (Obj.El A) (Obj.El C)} {S : Core.Rel (Obj.El B) (Obj.El C)} {U U' : Core.Rel (Obj.El A) (Obj.El A)} {V V' : Core.Rel (Obj.El B) (Obj.El B)} (hR : R ⊑ R') (hU : U ⊑ U')
    (hV : V ⊑ V') : rdivDen R S U V ⊑ rdivDen R' S U' V' :=
  le_iff.2 fun _ _ h => have h := rdivDen_iff.1 h
    rdivDen_iff.2 ⟨fun c hc => le_iff.1 hR _ _ (h.1 c hc),
      h.2.imp id fun ⟨⟨a, ha⟩, b, hb⟩ => ⟨⟨a, le_iff.1 hU _ _ ha⟩, b, le_iff.1 hV _ _ hb⟩⟩

theorem pair_le {X X' : Core.Rel (Obj.El A) (Obj.El B)} {Y Y' : Core.Rel (Obj.El A) (Obj.El C)} (hX : X ⊑ X') (hY : Y ⊑ Y') : rpair X Y ⊑ rpair X' Y' :=
  le_iff.2 fun _ _ h => ⟨le_iff.1 hX _ _ h.1, le_iff.1 hY _ _ h.2⟩

-- `est` drops `b` only where `Q` fails, so a larger `Q` drops fewer
theorem est_le {Q Q' : Core.Rel (Obj.El (.prod B B)) (Obj.El (.prod B B))} (hQ : Q ⊑ Q') : estDen Q ⊑ estDen Q' :=
  le_iff.2 fun _ _ h => (estDen_iff ..).2 (let h := (estDen_iff ..).1 h; ⟨h.1, fun ⟨c, hc, hne, hq⟩ => h.2 ⟨c, hc, hne, fun h' => hq (le_iff.1 hQ _ _ h')⟩⟩)

theorem leq_le {t : QAtomicType} {U U' : Core.Rel (Obj.El (.atom t)) (Obj.El (.atom t))} (hU : U ⊑ U') : leqDen t U ⊑ leqDen t U' :=
  le_iff.2 fun _ _ h => by
    rw [leqDen_iff] at h ⊢; obtain ⟨⟨v, hv⟩, ⟨v', hv'⟩, e⟩ := h
    exact ⟨⟨v, le_iff.1 hU _ _ hv⟩, ⟨v', le_iff.1 hU _ _ hv'⟩, e⟩

theorem lt_le {t : QAtomicType} {U U' : Core.Rel (Obj.El (.atom t)) (Obj.El (.atom t))} (hU : U ⊑ U') : ltDen t U ⊑ ltDen t U' :=
  le_iff.2 fun _ _ h => by
    rw [ltDen_iff] at h ⊢; obtain ⟨⟨v, hv⟩, ⟨v', hv'⟩, e⟩ := h
    exact ⟨⟨v, le_iff.1 hU _ _ hv⟩, ⟨v', le_iff.1 hU _ _ hv'⟩, e⟩

theorem ordRelDen_le (s : Bool) (A : Obj) {U U' : Core.Rel (Obj.El A) (Obj.El A)} (hU : U ⊑ U') :
    ordRelDen s A U ⊑ ordRelDen s A U' := by
  cases A <;> simp only [ordRelDen]
  · cases s
    · exact leq_le hU
    · exact lt_le hU
  all_goals exact Core.Rel.le_refl _

theorem foldr_le {e e' : Core.Rel (Obj.El B) (Obj.El B)} {S S' : Core.Rel (Obj.El (.prod A B)) (Obj.El B)} (he : e ⊑ e') (hS : S ⊑ S') :
    foldrDen e S ⊑ foldrDen e' S' :=
  le_iff.2 fun _ _ ⟨ys, hy, ⟨a, ha⟩, hs, hw⟩ =>
    ⟨ys, hy, ⟨a, le_iff.1 he _ _ ha⟩, fun t ht => le_iff.1 hS _ _ (hs t ht), hw⟩

theorem fold_le {e e' : Core.Rel (Obj.El B) (Obj.El B)} {S S' : Core.Rel (Obj.El (.prod B A)) (Obj.El B)} (he : e ⊑ e') (hS : S ⊑ S') :
    foldDen e S ⊑ foldDen e' S' :=
  le_iff.2 fun _ _ ⟨ys, hy, ⟨a, ha⟩, hs, hw⟩ =>
    ⟨ys, hy, ⟨a, le_iff.1 he _ _ ha⟩, fun t ht => le_iff.1 hS _ _ (hs t ht), hw⟩

theorem foldI_le {e e' : Core.Rel (Obj.El C) (Obj.El (.prod B B))} {S S' : Core.Rel (Obj.El (.prod (.prod C B) A)) (Obj.El (.prod C B))} (he : e ⊑ e')
    (hS : S ⊑ S') : foldIDen e S ⊑ foldIDen e' S' :=
  le_iff.2 fun _ _ h => (foldIDen_iff _ _ _ _).2 (le_iff.1 (fold_le (le_iff.2 fun _ _ h => le_iff.1 he _ _ h)
    (le_iff.2 fun _ _ h => le_iff.1 hS _ _ h)) _ _ ((foldIDen_iff _ _ _ _).1 h))

end ops

/-- `ss'` grows `ss` argument by argument, each at the same objects. -/
inductive Sems.le : List Sem → List Sem → Prop
  | nil : Sems.le [] []
  | cons {X Y : Obj} {T T' : Core.Rel (Obj.El X) (Obj.El Y)} {ss ss' : List Sem} :
    T ⊑ T' → Sems.le ss ss' → Sems.le (⟨X, Y, T⟩ :: ss) (⟨X, Y, T'⟩ :: ss')

/-- `ss ⊑ ss'` are at the same objects, which `Prim.objs` reads. -/
theorem Sems.le.objs {ss ss' : List Sem} (h : Sems.le ss ss') :
    ss.map (fun s => (s.1, s.2.1)) = ss'.map fun s => (s.1, s.2.1) := by
  induction h with
  | nil => rfl
  | cons _ _ ih => simp only [List.map_cons, ih]

/-- `Sems.le` read with the sign `s`, as `sle` reads `⊑`. -/
def Sems.sle (s : Bool) (ss ss' : List Sem) : Prop := cond s (Sems.le ss ss') (Sems.le ss' ss)

theorem Sems.sle.nil (s : Bool) : Sems.sle s [] [] := by cases s <;> exact Sems.le.nil

theorem Sems.sle.cons {s : Bool} {X Y : Obj} {T T' : Core.Rel (Obj.El X) (Obj.El Y)} {ss ss' : List Sem} (h : Rel.Lang.sle s T T')
    (hs : Sems.sle s ss ss') : Sems.sle s (⟨X, Y, T⟩ :: ss) (⟨X, Y, T'⟩ :: ss') := by
  cases s
  · exact Sems.le.cons h hs
  · exact Sems.le.cons h hs

theorem Sem.one_mono {X Y A B : Obj} {D : Core.Rel (Obj.El X) (Obj.El Y) → Core.Rel (Obj.El A) (Obj.El B)} (hD : ∀ {T T'}, T ⊑ T' → D T ⊑ D T')
    {ss ss' : List Sem} (h : Sems.le ss ss') : Sem.one D ss ⊑ Sem.one D ss' := by
  cases h with
  | nil => exact Core.Rel.le_refl _
  | @cons X' Y' T T' _ _ h t =>
    cases t with
    | nil =>
      simp only [Sem.one]
      by_cases hh : X' = X ∧ Y' = Y
      · simp only [dif_pos hh]; obtain ⟨rfl, rfl⟩ := hh; exact hD h
      · simp only [dif_neg hh]; exact Core.Rel.le_refl _
    | cons => first | exact Core.Rel.le_refl _ | (simp only [Sem.one]; exact Core.Rel.le_refl _)

theorem Sem.two_mono {X Y X₂ Y₂ A B : Obj} {D : Core.Rel (Obj.El X) (Obj.El Y) → Core.Rel (Obj.El X₂) (Obj.El Y₂) → Core.Rel (Obj.El A) (Obj.El B)}
    (hD : ∀ {T T' U U'}, T ⊑ T' → U ⊑ U' → D T U ⊑ D T' U') {ss ss' : List Sem} (h : Sems.le ss ss') :
    Sem.two D ss ⊑ Sem.two D ss' := by
  rcases h with _ | @⟨X', Y', T, T', _, _, h, _ | @⟨X₂', Y₂', U, U', _, _, h', _ | _⟩⟩
  all_goals first | exact Core.Rel.le_refl _ | simp only [Sem.two]
  all_goals first | exact Core.Rel.le_refl _ | skip
  by_cases hh : X' = X ∧ Y' = Y ∧ X₂' = X₂ ∧ Y₂' = Y₂
  · simp only [dif_pos hh]; obtain ⟨rfl, rfl, rfl, rfl⟩ := hh; exact hD h h'
  · simp only [dif_neg hh]; exact Core.Rel.le_refl _

/-- Every row its `prims` entry marks `mono` reads its relation arguments monotonically, however many: the fact
    `Tm.spinePol` rests on. -/
theorem rowDens_mono : ∀ e ∈ rowDens, (Prim.find? e.1.sym).any (·.mono) = true →
    ∀ σ {ss ss' : List Sem}, Sems.le ss ss' → e.2 σ ss ⊑ e.2 σ ss' := by
  intro e he hm σ ss ss' h
  simp only [rowDens, List.mem_append, List.mem_map, List.mem_cons, List.not_mem_nil, or_false] at he
  -- a `floatOps`, `arithOps`, `succ`, `mix`, `at` or `cmpOps` row takes no relation; then one case per row whatever their number,
  -- in `rowDens` order
  rcases he with ((((he | ⟨_, -, rfl⟩) | ⟨_, -, rfl⟩) | (rfl | rfl | rfl)) | ⟨_, -, rfl⟩) | ⟨_, -, rfl⟩
  rotate_left
  iterate 6 exact Core.Rel.le_refl _
  · dsimp only; exact Sem.one_mono (fun hT => ordRelDen_le _ _ hT) h
  repeat' first | (rcases he with rfl | he) | subst he
  all_goals first | exact Core.Rel.le_refl _ | exact absurd hm (by decide) | skip
  · dsimp only; refine Sem.one_mono (fun hT => le_iff.2 fun _ _ hm => ?_) h
    obtain ⟨hl, hs⟩ := (mapDen_iff _ _ _).1 hm
    exact (mapDen_iff _ _ _).2 ⟨hl, fun t ht ht' => le_iff.1 hT _ _ (hs t ht ht')⟩
  · dsimp only; refine Sem.one_mono (fun hT => le_iff.2 fun _ _ hm => ?_) h
    obtain ⟨g, h0, hs, hc⟩ := hm
    exact ⟨g, h0, fun t ht => le_iff.1 hT _ _ (hs t ht), hc⟩
  · dsimp only; refine Sem.one_mono (fun hT => le_iff.2 fun _ _ hm => ?_) h
    exact (flatDen_iff _ _ _).2 (le_iff.1 hT _ _ ((flatDen_iff _ _ _).1 hm))
  · exact Sem.two_mono foldI_le h
  · dsimp only; refine Sem.one_mono (fun hT => Core.Rel.mu_mono fun _ => le_iff.2 fun _ _ hm => ?_) h
    exact hm.elim .inl fun ⟨b, hb, hx⟩ => .inr ⟨b, le_iff.1 hT _ _ hb, hx⟩
  -- `dom`, `ran`: `𝟙 ∩ T T°`, `𝟙 ∩ T° T` grow with `T`; `est`: a larger test refutes fewer elements
  all_goals
    dsimp only; refine Sem.one_mono (fun hT => le_iff.2 fun _ _ hm => ?_) h
    first
    | (obtain ⟨he, y, h1, h2⟩ := hm; exact ⟨he, y, le_iff.1 hT _ _ h1, le_iff.1 hT _ _ h2⟩)
    | exact le_iff.1 (est_le hT) _ _ hm

theorem Prim.den_mono {r : Prim} (hr : (Prim.find? r.sym).any (·.mono) = true) {A B : Obj} {ss ss' : List Sem}
    (h : Sems.le ss ss') : Prim.den r A B ss ⊑ Prim.den r A B ss' := by
  unfold Prim.den; rw [h.objs]
  split
  next c D σ hf _ =>
    have hc : c.sym = r.sym := by simpa using List.find?_some hf
    have hm := rowDens_mono ⟨c, D⟩ (List.mem_of_find?_eq_some hf) (by rw [hc]; exact hr) σ h
    by_cases hh : (c.ty σ).1 = A ∧ (c.ty σ).2 = B
    · simp only [dif_pos hh]; obtain ⟨rfl, rfl⟩ := hh; exact hm
    · simp only [dif_neg hh]; exact Core.Rel.le_refl _
  next => exact Core.Rel.le_refl _

theorem sle.refl {s : Bool} (X : Core.Rel (Obj.El A) (Obj.El B)) : sle s X X := by cases s <;> exact Core.Rel.le_refl X

theorem sle.of_eq {s : Bool} {X Y : Core.Rel (Obj.El A) (Obj.El B)} (h : X = Y) : sle s X Y := h ▸ sle.refl X

theorem sle.map1 {A' B' : Obj} {f : Core.Rel (Obj.El A) (Obj.El B) → Core.Rel (Obj.El A') (Obj.El B')} (hf : ∀ {X X'}, X ⊑ X' → f X ⊑ f X') :
    ∀ {s X X'}, sle s X X' → sle s (f X) (f X')
  | true, _, _, h | false, _, _, h => hf h

theorem sle.map2 {A' B' A'' B'' : Obj} {f : Core.Rel (Obj.El A) (Obj.El B) → Core.Rel (Obj.El A') (Obj.El B') → Core.Rel (Obj.El A'') (Obj.El B'')}
    (hf : ∀ {X X' Y Y'}, X ⊑ X' → Y ⊑ Y' → f X Y ⊑ f X' Y') :
    ∀ {s X X' Y Y'}, sle s X X' → sle s Y Y' → sle s (f X Y) (f X' Y')
  | true, _, _, _, _, h1, h2 | false, _, _, _, _, h1, h2 => hf h1 h2

/-- The second argument antitone: `diff`. -/
theorem sle.anti2 {f : Core.Rel (Obj.El A) (Obj.El B) → Core.Rel (Obj.El A) (Obj.El B) → Core.Rel (Obj.El A) (Obj.El B)} (hf : ∀ {X X' Y Y'}, X ⊑ X' → Y' ⊑ Y → f X Y ⊑ f X' Y') :
    ∀ {s X X' Y Y'}, sle s X X' → sle (!s) Y Y' → sle s (f X Y) (f X' Y')
  | true, _, _, _, _, h1, h2 | false, _, _, _, _, h1, h2 => hf h1 h2

theorem sle.map3 {A' B' A'' B'' A''' B''' : Obj} {f : Core.Rel (Obj.El A) (Obj.El B) → Core.Rel (Obj.El A') (Obj.El B') → Core.Rel (Obj.El A'') (Obj.El B'') → Core.Rel (Obj.El A''') (Obj.El B''')}
    (hf : ∀ {X X' Y Y' Z Z'}, X ⊑ X' → Y ⊑ Y' → Z ⊑ Z' → f X Y Z ⊑ f X' Y' Z') :
    ∀ {s X X' Y Y' Z Z'}, sle s X X' → sle s Y Y' → sle s Z Z' → sle s (f X Y Z) (f X' Y' Z')
  | true, _, _, _, _, _, _, h1, h2, h3 | false, _, _, _, _, _, _, h1, h2, h3 => hf h1 h2 h3

theorem sle.lfp {s : Bool} (h : ∀ X, sle s (Φ X) (Ψ X)) : sle s (Core.Rel.mu Φ) (Core.Rel.mu Ψ) := by
  cases s
  · exact Core.Rel.mu_mono h
  · exact Core.Rel.mu_mono h

theorem sle.gfp {s : Bool} (h : ∀ X, sle s (Φ X) (Ψ X)) : sle s (Core.Rel.nu Φ) (Core.Rel.nu Ψ) := by
  cases s
  · exact Core.Rel.nu_mono h
  · exact Core.Rel.nu_mono h

/-- **Polarity**: where `t.pol s k`, growing the variable `k` moves `⟦t⟧` with the sign `s`; where
    `t.spinePol s k`, it moves the spine's meaning given arguments `ss` that move with `s` too, so a row given `n`
    relations is one induction over its spine. `den_mono` and `den_anti` are the first half's two signs. -/
theorem Tm.den_pol_spine (k : Nat) : ∀ {A B : Obj} (t : Tm A B),
    (∀ (s : Bool) (ρ ρ' : Val), t.pol s k = true → Val.Grow k ρ ρ' → sle s (t.den ρ) (t.den ρ')) ∧
    ∀ (s : Bool) (ρ ρ' : Val) (ss ss' : List Sem), t.spinePol s k = true → Val.Grow k ρ ρ' →
      Sems.sle s ss ss' → sle s (t.argDen ρ ss) (t.argDen ρ' ss') := by
  intro A B t
  induction t with
  | var j =>
    refine ⟨fun s ρ ρ' hp g => ?_, fun _ _ _ _ _ h => by simp [Tm.spinePol] at h⟩
    simp only [Tm.den]
    by_cases e : j = k
    · subst e; simp only [Tm.pol, beq_self_eq_true, if_true] at hp; subst hp; exact g.1 _ _
    · rw [g.2 j e]; exact sle.refl _
  | top V ih => refine ⟨fun s ρ ρ' hp g => ?_, fun _ _ _ _ _ h => by simp [Tm.spinePol] at h⟩; exact sle.map1 (comp_le' (Core.Rel.le_refl _)) (ih.1 s ρ ρ' hp g)
  | conv R ih => refine ⟨fun s ρ ρ' hp g => ?_, fun _ _ _ _ _ h => by simp [Tm.spinePol] at h⟩; exact sle.map1 conv_le' (ih.1 s ρ ρ' hp g)
  | comp R S ihR ihS =>
    refine ⟨fun s ρ ρ' hp g => ?_, fun _ _ _ _ _ h => by simp [Tm.spinePol] at h⟩; simp only [Tm.pol, Bool.and_eq_true] at hp
    exact sle.map2 comp_le' (ihR.1 s ρ ρ' hp.1 g) (ihS.1 s ρ ρ' hp.2 g)
  | meet R S ihR ihS =>
    refine ⟨fun s ρ ρ' hp g => ?_, fun _ _ _ _ _ h => by simp [Tm.spinePol] at h⟩; simp only [Tm.pol, Bool.and_eq_true] at hp
    exact sle.map2 inter_le' (ihR.1 s ρ ρ' hp.1 g) (ihS.1 s ρ ρ' hp.2 g)
  | join R S ihR ihS =>
    refine ⟨fun s ρ ρ' hp g => ?_, fun _ _ _ _ _ h => by simp [Tm.spinePol] at h⟩; simp only [Tm.pol, Bool.and_eq_true] at hp
    exact sle.map2 union_le' (ihR.1 s ρ ρ' hp.1 g) (ihS.1 s ρ ρ' hp.2 g)
  | pair R S ihR ihS =>
    refine ⟨fun s ρ ρ' hp g => ?_, fun _ _ _ _ _ h => by simp [Tm.spinePol] at h⟩; simp only [Tm.pol, Bool.and_eq_true] at hp
    exact sle.map2 pair_le (ihR.1 s ρ ρ' hp.1 g) (ihS.1 s ρ ρ' hp.2 g)
  | diff R S ihR ihS =>
    refine ⟨fun s ρ ρ' hp g => ?_, fun _ _ _ _ _ h => by simp [Tm.spinePol] at h⟩; simp only [Tm.pol, Bool.and_eq_true] at hp
    exact sle.anti2 diff_le (ihR.1 s ρ ρ' hp.1 g) (ihS.1 (!s) ρ ρ' hp.2 g)
  | ldiv R S U V _ ihS ihU ihV =>
    refine ⟨fun s ρ ρ' hp g => ?_, fun _ _ _ _ _ h => by simp [Tm.spinePol] at h⟩; simp only [Tm.pol, Bool.and_eq_true, Bool.not_eq_true'] at hp
    simp only [Tm.den, g.congr hp.1.1.1]
    exact sle.map3 ldiv_le (ihS.1 s ρ ρ' hp.1.1.2 g) (ihU.1 s ρ ρ' hp.1.2 g) (ihV.1 s ρ ρ' hp.2 g)
  | rdiv R S U V ihR _ ihU ihV =>
    refine ⟨fun s ρ ρ' hp g => ?_, fun _ _ _ _ _ h => by simp [Tm.spinePol] at h⟩; simp only [Tm.pol, Bool.and_eq_true, Bool.not_eq_true'] at hp
    simp only [Tm.den, g.congr hp.1.1.2]
    exact sle.map3 rdiv_le (ihR.1 s ρ ρ' hp.1.1.1 g) (ihU.1 s ρ ρ' hp.1.2 g) (ihV.1 s ρ ρ' hp.2 g)
  | nu j S b ihS ih =>
    refine ⟨fun s ρ ρ' hp g => ?_, fun _ _ _ _ _ h => by simp [Tm.spinePol] at h⟩
    simp only [Tm.pol, Bool.and_eq_true] at hp
    simp only [Tm.den]
    have hS := ihS.1 s ρ ρ' hp.1 g
    by_cases e : j = k
    · subst e
      have hb : ∀ {A' B' : Obj} (X : Core.Rel (Obj.El A') (Obj.El B')), ρ.bind j X = ρ'.bind j X := fun X => funext fun i => by
        by_cases e' : i = j
        · subst e'; exact Val.bind_same
        · rw [Val.bind_ne e', Val.bind_ne e', g.2 i e']
      simp only [hb]; exact sle.gfp fun X => sle.map2 (f := fun X Y => X ∩ Y) inter_le' hS (sle.refl _)
    · simp only [Bool.or_eq_true, beq_iff_eq, e, false_or] at hp
      exact sle.gfp fun X => sle.map2 (f := fun X Y => X ∩ Y) inter_le' hS (ih.1 s _ _ hp.2 (g.bind e X))
  | mu j _ _ b ih | hylo j _ b ih =>
    refine ⟨fun s ρ ρ' hp g => ?_, fun _ _ _ _ _ h => by simp [Tm.spinePol] at h⟩
    simp only [Tm.den]
    by_cases e : j = k
    · subst e
      have hb : ∀ {A' B' : Obj} (X : Core.Rel (Obj.El A') (Obj.El B')), ρ.bind j X = ρ'.bind j X := fun X => funext fun i => by
        by_cases e' : i = j
        · subst e'; exact Val.bind_same
        · rw [Val.bind_ne e', Val.bind_ne e', g.2 i e']
      simp only [hb]; exact sle.refl _
    · simp only [Tm.pol, Bool.or_eq_true, beq_iff_eq, e, false_or] at hp
      exact sle.lfp fun X => ih.1 s _ _ hp (g.bind e X)
  | foldr e S ihe ihS =>
    refine ⟨fun s ρ ρ' hp g => ?_, fun _ _ _ _ _ h => by simp [Tm.spinePol] at h⟩; simp only [Tm.pol, Bool.and_eq_true] at hp
    exact sle.map2 foldr_le (ihe.1 s ρ ρ' hp.1 g) (ihS.1 s ρ ρ' hp.2 g)
  | fold e S ihe ihS =>
    refine ⟨fun s ρ ρ' hp g => ?_, fun _ _ _ _ _ h => by simp [Tm.spinePol] at h⟩; simp only [Tm.pol, Bool.and_eq_true] at hp
    exact sle.map2 fold_le (ihe.1 s ρ ρ' hp.1 g) (ihS.1 s ρ ρ' hp.2 g)
  | prim r =>
    refine ⟨fun s ρ ρ' _ _ => sle.refl _, fun s ρ ρ' ss ss' hp _ h => ?_⟩
    simp only [Tm.spinePol] at hp
    cases s
    · exact Prim.den_mono hp h
    · exact Prim.den_mono hp h
  | arg f x ihf ihx =>
    refine ⟨fun s ρ ρ' hp g => ?_, fun s ρ ρ' ss ss' hp g h => ?_⟩
    · by_cases hc : (Tm.arg f x).fv.contains k = false
      · exact sle.of_eq (g.congr hc)
      · have hc : k ∈ (Tm.arg f x).fv := by simpa using hc
        have hp : f.spinePol s k = true ∧ x.pol s k = true := by simpa [Tm.pol, hc] using hp
        exact ihf.2 s ρ ρ' _ _ hp.1 g (Sems.sle.cons (ihx.1 s ρ ρ' hp.2 g) (Sems.sle.nil s))
    · simp only [Tm.spinePol, Bool.and_eq_true] at hp
      exact ihf.2 s ρ ρ' _ _ hp.1 g (Sems.sle.cons (ihx.1 s ρ ρ' hp.2 g) h)
  | _ =>
    refine ⟨fun s ρ ρ' hp g => ?_, fun _ _ _ _ _ h => by simp [Tm.spinePol] at h⟩
    exact sle.of_eq (g.congr (by first | simpa [Tm.pol] using hp | simp [Tm.fv]))

theorem Tm.den_pol (k : Nat) {A B : Obj} (t : Tm A B) (s : Bool) (ρ ρ' : Val) (hp : t.pol s k = true)
    (g : Val.Grow k ρ ρ') : sle s (t.den ρ) (t.den ρ') := (t.den_pol_spine k).1 s ρ ρ' hp g

/-- `⟦t⟧` is monotone in `X` where `X` occurs only positively. -/
theorem Tm.den_mono {A' B' : Obj} {t : Tm A' B'} {k : Nat} (h : t.pol true k = true) {ρ : Val}
    {X Y : Core.Rel (Obj.El A) (Obj.El B)} (hXY : X ⊑ Y) : t.den (ρ.bind k X) ⊑ t.den (ρ.bind k Y) :=
  t.den_pol k true _ _ h (Val.Grow.of_le hXY)

/-- **`⟦t⟧` distributes over `∪` in `X`** where `t.linIn k`, by induction on `Tm.linIn`'s cases; a part free of `k`
    reads the same under the three bindings (`Val.Grow.congr`). What makes `Tab.muLin`'s rounds `Tab.mu`'s
    (`GenK.mu_sound`). -/
theorem Tm.den_linIn {k : Nat} {A' B' : Obj} {t : Tm A' B'} (h : t.linIn k = true) (ρ : Val)
    (X Y : Core.Rel (Obj.El A) (Obj.El B)) : t.den (ρ.bind k (X ∪ Y)) ⊑ t.den (ρ.bind k X) ∪ t.den (ρ.bind k Y) := by
  have g₁ : Val.Grow k (ρ.bind k X) (ρ.bind k (X ∪ Y)) := Val.Grow.of_le (le_iff.2 fun _ _ => Or.inl)
  have g₂ : Val.Grow k (ρ.bind k Y) (ρ.bind k (X ∪ Y)) := Val.Grow.of_le (le_iff.2 fun _ _ => Or.inr)
  have hk : ∀ A' B', ρ.bind k (X ∪ Y) k A' B' ⊑ ρ.bind k X k A' B' ∪ ρ.bind k Y k A' B' := fun A' B' => by
    simp only [Val.bind, if_true]
    by_cases e : A = A' ∧ B = B'
    · obtain ⟨rfl, rfl⟩ := e; simp only [dif_pos (show A = A ∧ B = B from ⟨rfl, rfl⟩)]
      exact le_iff.2 fun _ _ h => h
    · simp only [dif_neg e]; exact le_iff.2 fun _ _ h => h.elim
  generalize ρ.bind k (X ∪ Y) = ρ₀ at g₁ g₂ hk ⊢
  generalize ρ.bind k X = ρ₁ at g₁ g₂ hk ⊢
  generalize ρ.bind k Y = ρ₂ at g₁ g₂ hk ⊢
  have free : ∀ {A B : Obj} (t : Tm A B), t.fv.contains k = false → t.den ρ₀ ⊑ t.den ρ₁ ∪ t.den ρ₂ :=
    fun t hc => le_iff.2 fun a b h => Or.inl (by rw [g₁.congr hc]; exact h)
  revert h
  induction t with
  | var j =>
    intro _
    by_cases e : j = k
    · subst e; exact hk _ _
    · exact free _ (by simp [Tm.fv, Ne.symm e])
  | join R S ihR ihS =>
    intro h; simp only [Tm.linIn, Bool.and_eq_true] at h; simp only [Tm.den]
    exact le_iff.2 fun a b hab => hab.elim
      (fun hr => (le_iff.1 (ihR h.1) a b hr).elim (fun h => Or.inl (Or.inl h)) fun h => Or.inr (Or.inl h))
      fun hs => (le_iff.1 (ihS h.2) a b hs).elim (fun h => Or.inl (Or.inr h)) fun h => Or.inr (Or.inr h)
  | comp R S ihR ihS =>
    intro h; simp only [Tm.linIn, Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true'] at h; simp only [Tm.den]
    rcases h with ⟨hR, hS⟩ | ⟨hR, hS⟩
    · rw [g₁.congr hS, g₂.congr hS]
      exact le_iff.2 fun a c ⟨b, hab, hbc⟩ =>
        (le_iff.1 (ihR hR) a b hab).elim (fun h => Or.inl ⟨b, h, hbc⟩) fun h => Or.inr ⟨b, h, hbc⟩
    · rw [g₁.congr hR, g₂.congr hR]
      exact le_iff.2 fun a c ⟨b, hab, hbc⟩ =>
        (le_iff.1 (ihS hS) b c hbc).elim (fun h => Or.inl ⟨b, hab, h⟩) fun h => Or.inr ⟨b, hab, h⟩
  | meet R S ihR ihS =>
    intro h; simp only [Tm.linIn, Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true'] at h; simp only [Tm.den]
    rcases h with ⟨hR, hS⟩ | ⟨hR, hS⟩
    · rw [g₁.congr hS, g₂.congr hS]
      exact le_iff.2 fun a b ⟨hr, hs⟩ =>
        (le_iff.1 (ihR hR) a b hr).elim (fun h => Or.inl ⟨h, hs⟩) fun h => Or.inr ⟨h, hs⟩
    · rw [g₁.congr hR, g₂.congr hR]
      exact le_iff.2 fun a b ⟨hr, hs⟩ =>
        (le_iff.1 (ihS hS) a b hs).elim (fun h => Or.inl ⟨hr, h⟩) fun h => Or.inr ⟨hr, h⟩
  | pair R S ihR ihS =>
    intro h; simp only [Tm.linIn, Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true'] at h; simp only [Tm.den]
    rcases h with ⟨hR, hS⟩ | ⟨hR, hS⟩
    · rw [g₁.congr hS, g₂.congr hS]
      exact le_iff.2 fun a p ⟨hr, hs⟩ =>
        (le_iff.1 (ihR hR) a p.1 hr).elim (fun h => Or.inl ⟨h, hs⟩) fun h => Or.inr ⟨h, hs⟩
    · rw [g₁.congr hR, g₂.congr hR]
      exact le_iff.2 fun a p ⟨hr, hs⟩ =>
        (le_iff.1 (ihS hS) a p.2 hs).elim (fun h => Or.inl ⟨hr, h⟩) fun h => Or.inr ⟨hr, h⟩
  | conv R ih =>
    intro h; simp only [Tm.linIn] at h; simp only [Tm.den]
    exact le_iff.2 fun b a hab => le_iff.1 (ih h) a b hab
  | _ => intro h; exact free _ (by simpa [Tm.linIn] using h)




/-- `Tm.memAt` at `[E] ⟶ E` is `∋`: it relates a list to its members. -/
theorem Tm.den_memAt {ρ : Val} {E : Obj} : (Tm.memAt (.arr E) E).den ρ = fun (xs : (Obj.arr E).El) x => x ∈ xs := by
  simp only [Tm.memAt, dite_true]; rfl

/-- **`E` is a definition**: the term `Λ(∋ R)` that `applied` and `appliedL` build for `E(R)` means `EDen`. -/
theorem Tm.E_den (ρ : Val) {A B : Obj} (R : Tm A B) :
    (Tm.lam (.comp (.mem (B := A)) R)).den ρ = EDen (R.den ρ) := by
  simp only [Tm.den]

/-- A row `F(T)` at `xs` reads `T` only at the members of `xs`. -/
theorem Prim.den_map_congr {r : Prim} (hr : (r.sym == mapRow.sym) = true) {A B C D : Obj} {T T' : Core.Rel (Obj.El C) (Obj.El D)}
    {ρ : Val} {a : A.El} (h : ∀ m, (Tm.memAt A C).den ρ a m → ∀ e, (T m e ↔ T' m e)) (d : B.El) :
    r.den A B [⟨C, D, T⟩] a d ↔ r.den A B [⟨C, D, T'⟩] a d := by
  have hf : rowDens.find? (·.1.sym == mapRow.sym) =
      some ⟨RowCode.map, fun σ => Sem.one (X := σ₁ σ) (Y := σ₂ σ) mapDen⟩ := rfl
  unfold Prim.den; rw [eq_of_beq hr, hf]; simp only [List.map_cons, List.map_nil]
  cases r.objs A B [(C, D)] with
  | none => exact Iff.rfl
  | some σ =>
    dsimp only
    by_cases hh : (RowCode.map.ty σ).1 = A ∧ (RowCode.map.ty σ).2 = B
    · obtain ⟨rfl, rfl⟩ := hh
      rw [dif_pos ⟨rfl, rfl⟩, dif_pos ⟨rfl, rfl⟩]
      simp only [Sem.one]
      by_cases hc : C = σ₁ σ ∧ D = σ₂ σ
      · obtain ⟨rfl, rfl⟩ := hc
        rw [dif_pos ⟨rfl, rfl⟩, dif_pos ⟨rfl, rfl⟩, mapDen_iff, mapDen_iff]
        exact and_congr_right fun _ => forall_congr' fun t => forall_congr' fun ht => forall_congr' fun ht' =>
          h _ (Tm.den_memAt ▸ List.getElem_mem ht) _
      · rw [dif_neg hc, dif_neg hc]
    · rw [dif_neg hh, dif_neg hh]

/-- A row `dom(T)` at `a` reads `T` only at `a`. -/
theorem Prim.den_dom_congr {r : Prim} (hr : (r.sym == domRow.sym) = true) {A B C D : Obj} {T T' : Core.Rel (Obj.El C) (Obj.El D)}
    {ρ : Val} {a : A.El} (h : ∀ m, (Tm.idAt A C).den ρ a m → ∀ e, (T m e ↔ T' m e)) (d : B.El) :
    r.den A B [⟨C, D, T⟩] a d ↔ r.den A B [⟨C, D, T'⟩] a d := by
  have hf : rowDens.find? (·.1.sym == domRow.sym) =
      some ⟨RowCode.dom, fun σ => Sem.one (X := σ₁ σ) (Y := σ₂ σ) fun T => 𝟙 _ ∩ T ≫ T°⟩ := rfl
  unfold Prim.den; rw [eq_of_beq hr, hf]; simp only [List.map_cons, List.map_nil]
  cases r.objs A B [(C, D)] with
  | none => exact Iff.rfl
  | some σ =>
    dsimp only
    by_cases hh : (RowCode.dom.ty σ).1 = A ∧ (RowCode.dom.ty σ).2 = B
    · obtain ⟨rfl, rfl⟩ := hh
      rw [dif_pos ⟨rfl, rfl⟩, dif_pos ⟨rfl, rfl⟩]
      simp only [Sem.one]
      by_cases hc : C = σ₁ σ ∧ D = σ₂ σ
      · obtain ⟨rfl, rfl⟩ := hc
        rw [dif_pos ⟨rfl, rfl⟩, dif_pos ⟨rfl, rfl⟩]
        have hi : (Tm.idAt (σ₁ σ) (σ₁ σ)).den ρ a a := by simp only [Tm.idAt, dite_true]; exact (rfl : a = a)
        exact and_congr_right fun e => by
          subst e; exact exists_congr fun m => and_congr (h a hi m) (h a hi m)
      · rw [dif_neg hc, dif_neg hc]
    · rw [dif_neg hh, dif_neg hh]

/-- **`hylo`'s body is local along its children** (`Hylo.Local`): where `X` and `Y` agree at the children
    `t.kids k A` reaches from `a`, `t` reads the same at `a` under either bound to `k`. -/
theorem Tm.den_local (k : Nat) {A B : Obj} (ρ : Val) (X Y : Core.Rel (Obj.El A) (Obj.El B)) : ∀ {C D : Obj} (t : Tm C D) (c : Tm C A),
    t.kids k A = some c → ∀ a, (∀ a', c.den ρ a a' → ∀ b, (X a' b ↔ Y a' b)) →
      ∀ d, t.den (ρ.bind k X) a d ↔ t.den (ρ.bind k Y) a d := by
  have free : ∀ {C D : Obj} (t : Tm C D), t.fv.contains k = false → ∀ a d,
      t.den (ρ.bind k X) a d ↔ t.den (ρ.bind k Y) a d := fun t h a d => by
    rw [(t.den_congr _ (ρ.bind k Y) fun i hi => by
      rw [Val.bind_ne (by rintro rfl; simp [hi] at h), Val.bind_ne (by rintro rfl; simp [hi] at h)]).1]
  intro C D t
  induction t with
  | @var C' D' j =>
    intro c hc a hX d
    unfold Tm.kids at hc; split at hc
    · rename_i hk
      simp only [Tm.fv, List.contains_cons, List.contains_nil, Bool.or_false, beq_iff_eq] at hk
      subst hk
      dsimp only at hc
      simp only [Tm.den, Val.bind, if_true]
      by_cases h : A = C' ∧ B = D'
      · obtain ⟨rfl, rfl⟩ := h
        rw [dif_pos rfl] at hc; cases hc
        rw [dif_pos ⟨rfl, rfl⟩, dif_pos ⟨rfl, rfl⟩]
        exact hX a rfl d
      · simp only [dif_neg h]
    · exact free _ (Bool.eq_false_iff.mpr ‹_›) a d
  | comp R S ihR ihS =>
    intro c hc a hX d
    unfold Tm.kids at hc; split at hc
    · dsimp only at hc
      cases hS : S.fv.contains k
      · simp only [hS, Bool.not_false, if_true] at hc
        simp only [Tm.den]
        exact exists_congr fun m => and_congr (ihR c hc a hX m) (free S hS m d)
      · cases hR : R.fv.contains k
        rotate_left
        · simp only [hS, hR, Bool.not_true, Bool.false_eq_true, ↓reduceIte, reduceCtorEq] at hc
        simp only [hS, hR, Bool.not_true, Bool.false_eq_true, if_false] at hc
        cases hs : S.kids k A <;> simp only [hs, reduceCtorEq, Option.some.injEq] at hc
        subst hc
        rename_i s
        have eX := (R.den_congr (ρ.bind k X) ρ fun i hi => Val.bind_ne (by rintro rfl; simp [hi] at hR)).1
        have eY := (R.den_congr (ρ.bind k Y) ρ fun i hi => Val.bind_ne (by rintro rfl; simp [hi] at hR)).1
        simp only [Tm.den, eX, eY]
        exact exists_congr fun m => and_congr_right fun hm => ihS s hs m (fun a' h' => hX a' ⟨m, hm, h'⟩) d
    · exact free _ (Bool.eq_false_iff.mpr ‹_›) a d
  | meet R S ihR ihS =>
    intro c hc a hX d
    unfold Tm.kids at hc; split at hc
    · dsimp only at hc
      cases hr : R.kids k A <;> cases hs : S.kids k A <;> simp only [hr, hs, reduceCtorEq, Option.some.injEq] at hc
      subst hc
      exact and_congr (ihR _ hr a (fun a' h => hX a' (Or.inl h)) d) (ihS _ hs a (fun a' h => hX a' (Or.inr h)) d)
    · exact free _ (Bool.eq_false_iff.mpr ‹_›) a d
  | join R S ihR ihS =>
    intro c hc a hX d
    unfold Tm.kids at hc; split at hc
    · dsimp only at hc
      cases hr : R.kids k A <;> cases hs : S.kids k A <;> simp only [hr, hs, reduceCtorEq, Option.some.injEq] at hc
      subst hc
      exact or_congr (ihR _ hr a (fun a' h => hX a' (Or.inl h)) d) (ihS _ hs a (fun a' h => hX a' (Or.inr h)) d)
    · exact free _ (Bool.eq_false_iff.mpr ‹_›) a d
  | pair R S ihR ihS =>
    intro c hc a hX d
    unfold Tm.kids at hc; split at hc
    · dsimp only at hc
      cases hr : R.kids k A <;> cases hs : S.kids k A <;> simp only [hr, hs, reduceCtorEq, Option.some.injEq] at hc
      subst hc
      exact and_congr (ihR _ hr a (fun a' h => hX a' (Or.inl h)) d.1)
        (ihS _ hs a (fun a' h => hX a' (Or.inr h)) d.2)
    · exact free _ (Bool.eq_false_iff.mpr ‹_›) a d
  | arg f x _ ihx =>
    intro c hc a hX d
    unfold Tm.kids at hc; split at hc
    · cases f with
      | prim r =>
        dsimp only at hc
        split at hc
        · rename_i hr
          cases hs : x.kids k A <;> simp only [hs, reduceCtorEq, Option.some.injEq] at hc
          subst hc
          rename_i s
          simp only [Tm.den, Tm.argDen]
          refine Prim.den_map_congr (ρ := ρ) hr (fun m hm e => ?_) d
          exact ihx s hs m (fun a' h' => hX a' ⟨m, hm, h'⟩) e
        · split at hc
          · rename_i hr
            cases hs : x.kids k A <;> simp only [hs, reduceCtorEq, Option.some.injEq] at hc
            subst hc
            rename_i s
            simp only [Tm.den, Tm.argDen]
            refine Prim.den_dom_congr (ρ := ρ) hr (fun m hm e => ?_) d
            exact ihx s hs m (fun a' h' => hX a' ⟨m, hm, h'⟩) e
          · cases hc
      | _ => dsimp only at hc; cases hc
    · exact free _ (Bool.eq_false_iff.mpr ‹_›) a d
  | _ =>
    intro c hc a hX d
    unfold Tm.kids at hc; split at hc
    · dsimp only at hc; cases hc
    · exact free _ (Bool.eq_false_iff.mpr ‹_›) a d


end Rel.Lang
