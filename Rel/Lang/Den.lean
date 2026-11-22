/-
  `⟦−⟧`: the meaning of a core term `Tm` as an arrow of `Rel(Set)` (`doc/rel-denotation-design.md` §1, §2, §7.3).
  Total and structural: each node is the `T` its `Gen.*_sound` lemma proves, written with the allegory's operators
  (`≫ ° ∩ ∪ 𝟙 𝟘`, D3 = E); `μ`, `ν` are `Core.Rel.mu`, `nu`, defined for every body, so no monotonicity is assumed here.
-/
import Rel.Run.Lang.Tm
import Rel.Run.Where
import Rel.AscOrder
import Rel.Rep
import Rel.ObjOrder
import Rel.Core.Fix
import Rel.Kernel.Cast

namespace Rel.Lang

open Rel.Kernel Tab Rel.Rep
open scoped Rel.Core.Rel
open Rel.Core.Rel hiding id comp recip inter union zero le inl inr junc

/-- An arrow `A ⟶ B` of `Rel(Set)` between the elements of two objects. -/
abbrev Den (A B : Obj) := Core.Rel (A.El) (B.El)

/-- The meaning of each variable `k`, at the objects the term asks for. -/
abbrev Val := Nat → (A B : Obj) → Den A B

/-- No variable bound: what a closed term (`share`) is read under. -/
def Val.empty : Val := fun _ _ _ => 𝟘

open Classical in
/-- `ρ` with the variable `k` bound to `X : A ⟶ B`. A use of `k` at other objects is ill-typed and reads `𝟘`, so
    the binder hides every outer `k`, as `Tm.fv` drops it. -/
noncomputable def Val.bind (ρ : Val) (k : Nat) {A B : Obj} (X : Den A B) : Val := fun j A' B' =>
  if j = k then (if h : A = A' ∧ B = B' then h.1 ▸ h.2 ▸ X else 𝟘) else ρ j A' B'

theorem Val.bind_ne {ρ : Val} {k j : Nat} {A B : Obj} {X : Den A B} (h : j ≠ k) : ρ.bind k X j = ρ j := by
  funext A' B'; simp [Val.bind, h]

theorem Val.bind_same {ρ ρ' : Val} {k : Nat} {A B : Obj} {X : Den A B} : ρ.bind k X k = ρ'.bind k X k := by
  funext A' B'; simp [Val.bind]

variable {A B C : Obj} {Φ Ψ : Den A B → Den A B} {Y : Den A B}

/-! ### The named meanings: each the `T` of its node's `Gen.*_sound` lemma -/


/-- `R − S`, pointwise. -/
abbrev diffDen (TR TS : Den A B) : Den A B := fun x y => TR x y ∧ ¬ TS x y

/-- `R\S` within the universes `UB`, `UC`: the book's left division where `R` has a column, every pair of the
    universes where it has none. -/
abbrev ldivDen (TR : Den A B) (TS : Den A C) (TB : Den B B) (TC : Den C C) : Den B C :=
  fun b c => (∀ a, TR a b → TS a c) ∧ ((∃ a, TR a b) ∨ ((∃ b', TB b' b) ∧ ∃ c', TC c' c))

/-- `R/S` within the universes `UA`, `UB`, the mirror of `ldivDen`. -/
abbrev rdivDen (TR : Den A C) (TS : Den B C) (TA : Den A A) (TB : Den B B) : Den A B :=
  fun x y => (∀ c, TS y c → TR x c) ∧ ((∃ c, TS y c) ∨ ((∃ a, TA a x) ∧ ∃ b, TB b y))

/-- `R÷S = R/S ∩ (S/R)°` within the universes `UA`, `UB`: `x` to `y` when `R x` and `S y` are one image. -/
abbrev symDivDen (TA : Den A A) (TB : Den B B) (TR : Den A C) (TS : Den B C) : Den A B :=
  rdivDen TR TS TA TB ∩ (rdivDen TS TR TB TA)°

/-- `nil`: every source to the empty array. -/
abbrev nilDen : Den A (.arr B) := fun _ Y => Y = []

/-- `at(k)`: the element at position `k`. -/
abbrev atDen (k : Nat) : Den (.arr B) B := fun xs x => ∃ h : k < xs.length, x = xs[k]'h

/-- `succ` on the universe `TU`: `u` and its successor both in it. -/
abbrev succDen (TU : Den .long .long) : Den .long .long :=
  fun u w => (∃ v, TU u v) ∧ w = Ew.intStep Ew.add Alg.nul u 1 ∧ ∃ v, TU w v

/-- The float order `o` (`Op.flt`, `Op.fle`) on two values of `t`: IEEE's on their `f64` words (`fval`); no pair at an
    atom holding no float. -/
abbrev fordAt (o : Rel.Kernel.Op) (t : QAtomicType) (a b : (Obj.atom t).El) : Prop :=
  ∃ x y, fval t a = some x ∧ fval t b = some y ∧ o.eval x y = .ok 1

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
abbrev leqDen (t : QAtomicType) (TU : Den (.atom t) (.atom t)) : Den (.atom t) (.atom t) :=
  fun a b => (∃ v, TU a v) ∧ (∃ v, TU b v) ∧ leAt t a b

/-- `<` on the universe `TU` of the atom `t`. -/
abbrev ltDen (t : QAtomicType) (TU : Den (.atom t) (.atom t)) : Den (.atom t) (.atom t) :=
  fun a b => (∃ v, TU a v) ∧ (∃ v, TU b v) ∧ ltAt t a b

/-- The value verb `k` itself (`Alg.arith`): `Int64`'s step, not the null and, for `+ - *`, not wrapped. -/
abbrev stepDen (k : UInt8) : Den (.prod .long .long) .long :=
  fun p w => w = Ew.intStep k Alg.nul p.1 p.2 ∧ w ≠ Alg.nul ∧
    (if k == Ew.add then (0 ≤ p.2 ↔ p.1 ≤ w) else if k == Ew.sub then (0 ≤ p.2 ↔ w ≤ p.1)
     else if k == Ew.mul then (Ew.intStep Ew.idiv Alg.nul w p.1 = p.2 ∨ p.1 = 0) else True)

/-- The value verb `k` at the atom `t`: `stepDen k` at `i64`; at a float atom `fstep` on the operands' `f64` words
    (`fval`), the word of `t` it answers, no row where that is `2^63` (the IEEE answer is NaN); none elsewhere. -/
def stepAt : (t : QAtomicType) → UInt8 → Den (.prod (.atom t) (.atom t)) (.atom t)
  | .i64, k => stepDen k
  | t, k => fun p w => ∃ x y r, fval t p.1 = some x ∧ fval t p.2 = some y ∧ fstep t k x y = .ok r ∧
      r ≠ 0x8000000000000000 ∧ w = QAtomicType.ofBits t r

/-- The value verb `k` on the universe `TU` of the atom `t`: both inputs in `TU` (`dom(π₁ TU)`, `dom(π₂ TU)`), as
    `succDen`'s, then the step, its result in `TU`. The input test makes `(TU×TU) arith = arith` at a coreflexive
    `TU`. -/
abbrev arithDen (t : QAtomicType) (k : UInt8) (TU : Den (.atom t) (.atom t)) : Den (.prod (.atom t) (.atom t)) (.atom t) :=
  (𝟙 _ ∩ (graph Prod.fst ≫ TU) ≫ (graph Prod.fst ≫ TU)°) ≫
    ((𝟙 _ ∩ (graph Prod.snd ≫ TU) ≫ (graph Prod.snd ≫ TU)°) ≫ (stepAt t k ≫ TU))

/-- `fold(e, S)`: a chain of values `ys`, its last from `e`, each the step `S` of the element and the next value. -/
abbrev foldrDen {E V : Obj} (Te : Den V V) (TS : Den (.prod E V) V) : Den (.arr E) V :=
  fun xs w => ∃ ys : List V.El, ∃ hy : ys.length = xs.length + 1,
    (∃ a, Te a (ys[xs.length]'(Nat.lt_of_lt_of_eq (Nat.lt_succ_self _) hy.symm))) ∧
    (∀ t (ht : t < xs.length), TS (xs[t]'ht, ys[t + 1]'(Nat.lt_of_lt_of_eq (Nat.succ_lt_succ ht) hy.symm))
      (ys[t]'(Nat.lt_of_lt_of_eq (Nat.lt_succ_of_lt ht) hy.symm))) ∧
    w = ys[0]'(Nat.lt_of_lt_of_eq (Nat.zero_lt_succ _) hy.symm)

/-- The left fold `⦇e, S⦈` over `[nil, snoc]`: a chain of values `ys`, its first from `e`, each the step `S` of the
    value before and the element (`(acc, x)`, index 0 first), the result its last. -/
abbrev foldDen {E V : Obj} (Te : Den V V) (TS : Den (.prod V E) V) : Den (.arr E) V :=
  fun xs w => ∃ ys : List V.El, ∃ hy : ys.length = xs.length + 1,
    (∃ a, Te a (ys[0]'(by omega))) ∧
    (∀ t (ht : t < xs.length), TS (ys[t]'(by omega), xs[t]'ht) (ys[t + 1]'(by omega))) ∧
    w = ys[xs.length]'(by omega)


/-- `fold(e, S)` given a family: at the key `i`, the left fold whose start is the fibre of `e` at `i` and whose step
    is `S` at `i`, keeping the key. -/
abbrev foldIDen {I E V : Obj} (Te : Den I (.prod V V)) (TS : Den (.prod (.prod I V) E) (.prod I V)) :
    Den (.prod I (.arr E)) V :=
  fun p w => foldDen (fun a b => Te p.1 (a, b)) (fun q v => TS ((p.1, q.1), q.2) (p.1, v)) p.2 w

/-- `foldIDen` is one `foldDen` on the carrier `I×V`: start `ran⟨𝟙, Te ≫ π₂⟩`, step `TS` met with
    `π₁ ≫ π₁ ≫ π₁°` (the step keeps the index), its result's index met with the key's, then `π₂`. -/
theorem foldIDen_eq {I E V : Obj} (Te : Den I (.prod V V)) (TS : Den (.prod (.prod I V) E) (.prod I V)) :
    foldIDen Te TS =
      ((graph Prod.fst ≫ (graph Prod.fst)°) ∩
        (graph Prod.snd ≫ foldDen (E := E) (V := .prod I V)
          (𝟙 _ ∩ (rpair (𝟙 _) (Te ≫ graph Prod.snd))° ≫ (rpair (𝟙 _) (Te ≫ graph Prod.snd))°°)
          (TS ∩ (graph Prod.fst ≫ graph Prod.fst ≫ (graph Prod.fst)°)))) ≫ graph Prod.snd := by
  refine Core.Rel.ext fun p w => ?_
  simp only [foldIDen, foldDen, Core.Rel.comp, Core.Rel.inter, Core.Rel.recip, Core.Rel.graph, Core.Rel.rpair,
    Core.Rel.id]
  constructor
  · rintro ⟨ys, hy, ⟨a, ha⟩, hS, rfl⟩
    refine ⟨(p.1, ys[p.2.length]), ⟨⟨_, rfl, rfl⟩, _, rfl, ys.map (p.1, ·), by simp [hy],
      ⟨_, rfl, p.1, ⟨?_, _, ha, ?_⟩, ?_, _, ha, ?_⟩, fun t ht => ⟨?_, _, rfl, _, rfl, ?_⟩, ?_⟩, rfl⟩
    all_goals simp
    simpa using hS t (by simpa using ht)
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


/-- `Rᴵ`: the family `R : I ⟶ A×B` as one relation of the key and the source. -/
abbrev flatDen {I A B : Obj} (T : Den I (.prod A B)) : Den (.prod I A) B := fun x b => T x.1 (x.2, b)


/-- `est(Q)` keeps `b` of `xs` unless some other `c` of `xs` fails `Q` at `(b, c)`. -/
abbrev estDen (TQ : Den (.prod B B) (.prod B B)) : Den (.arr B) B :=
  fun xs b => b ∈ xs ∧ ¬ ∃ c, c ∈ xs ∧ c ≠ b ∧ ¬ TQ (b, c) (b, c)

/-- `Λ(T)` with `𝒫B` held as `[B]` (D2 = C): `a` to the one list of its image strictly ascending by `Obj.lt`, the
    order `Rel.Canon` puts a table's rows in; no list where that image has no such list. -/
abbrev lamDen (T : Den A B) : Den A (.arr B) := fun a ys => ys.Pairwise B.lt ∧ ∀ b, b ∈ ys ↔ T a b

/-- `F(T)`: two arrays of one length, related elementwise by `T`. -/
abbrev mapDen {A B : Obj} (T : Den A B) : Den (.arr A) (.arr B) := fun xs ys => ys.length = xs.length ∧
  ∀ t (ht : t < xs.length) (ht' : t < ys.length), T (xs[t]'ht) (ys[t]'ht')

/-- `dom(T) (𝟙 × ≥) dom(T)`: `(k, i)` to `(k, j)`, both in `dom(T)`, `j ≤ i` in the order `leAt t` of the position
    atom `t`; `𝟙 × ≥` is `π₁ π₁° ∩ π₂ ≥ π₂°`. -/
abbrev upToDen {K V : Obj} {t : QAtomicType} (T : Den (.prod K (.atom t)) V) :
    Den (.prod K (.atom t)) (.prod K (.atom t)) :=
  (𝟙 _ ∩ T ≫ T°) ≫ ((graph Prod.fst ≫ (graph Prod.fst)°) ∩
    (graph Prod.snd ≫ (fun a b => leAt t b a : Den (.atom t) (.atom t)) ≫ (graph Prod.snd)°)) ≫ (𝟙 _ ∩ T ≫ T°)

/-- q's `sums` per key, `agg(dom(x) (𝟙 × ≥) dom(x), F(x) ⦇[0, plus]⦈)` with `agg(R, f) = dom(R) Λ(R) f`: `(k, i)` to
    the left fold of `plus` from `0` over `x`'s values at `(k, j)`, `j ≤ i` ascending; none at or after a step that
    `plus` refuses (a wrap, the null, a NaN). The values are
    those of the atom `u`, the fold `stepAt u` from the word `0`: left to right at a float atom, q's order. -/
abbrev sumsDen {K : Obj} {t u : QAtomicType} (T : Den (.prod K (.atom t)) (.atom u)) :
    Den (.prod K (.atom t)) (.atom u) :=
  (𝟙 _ ∩ upToDen T ≫ (upToDen T)°) ≫ lamDen (upToDen T) ≫ mapDen T ≫
    foldDen (fun _ b => b = QAtomicType.ofBits u 0 : Den (.atom u) (.atom u)) (stepAt u Ew.add)

/-- `sums` at the position object `P` and the value object `V`: `sumsDen` where both are atoms, `𝟘` elsewhere (no
    `≤`, no `plus`). -/
def sumsAt (K : Obj) : (P V : Obj) → Den (.prod K P) V → Den (.prod K P) V
  | .atom _, .atom _, T => sumsDen T
  | _, _, _ => 𝟘

/-- `sum` at the element object `V`: the left fold `⦇[0, plus]⦈` of `stepAt t add` from the word `0`, from index `0`
    up (q's order), where `V` is an atom; none at or after a step `plus` refuses (a wrap, the null, a NaN). `𝟘` where
    `V` is no atom (no `plus`). -/
def sumAt : (V : Obj) → Den (.arr V) V
  | .atom t => foldDen (fun _ b => b = QAtomicType.ofBits t 0) (stepAt t Ew.add)
  | _ => 𝟘

/-- `E(T) = Λ(∋ T)`: an array to the canonical list of the images of its elements. -/
abbrev EDen (T : Den A B) : Den (.arr A) (.arr B) := lamDen ((fun xs a => a ∈ xs : Den (.arr A) A) ≫ T)

/-- `thin(Q)` as `CRel.thinOn` computes it: the canonical list of the `c` of `xs` that no `b` of `xs` beats
    strictly, `Q` read as its pair test as in `estDen`. -/
abbrev thinDen (TQ : Den (.prod B B) (.prod B B)) : Den (.arr B) (.arr B) :=
  lamDen fun xs c => c ∈ xs ∧ ¬ ∃ b, b ∈ xs ∧ TQ (b, c) (b, c) ∧ ¬ TQ (c, b) (c, b)

/-! ### The rows of `prims` -/

/-- A relation argument's meaning with its objects. -/
abbrev Sem := (X Y : Obj) × Den X Y

/-- A row's meaning `D` of its one relation argument, read at `X ⟶ Y`; `𝟘` where the arguments are not one at
    `X ⟶ Y`, where `RowCode.unary` has no code. -/
def Sem.one {X Y A B : Obj} (D : Den X Y → Den A B) : List Sem → Den A B
  | [⟨X', Y', T⟩] => if h : X' = X ∧ Y' = Y then D (h.1 ▸ h.2 ▸ T) else 𝟘
  | _ => 𝟘

/-- `Sem.one` for a row of two relation arguments, read at `X ⟶ Y` and `X₂ ⟶ Y₂`. -/
def Sem.two {X Y X₂ Y₂ A B : Obj} (D : Den X Y → Den X₂ Y₂ → Den A B) : List Sem → Den A B
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
def foldI : RowCode := ⟨"foldI", fun σ => (.prod (σ₁ σ) (.arr (σ.getD 2 .long)), σ₂ σ)⟩
def dom : RowCode := ⟨"dom", fun σ => (σ₁ σ, σ₁ σ)⟩
def ran : RowCode := ⟨"ran", fun σ => (σ₂ σ, σ₂ σ)⟩
def nil : RowCode := ⟨"nil", fun σ => (σ₁ σ, .arr (σ₂ σ))⟩
end RowCode

/-- `$` at `A ⟶ B`: the graph of the embedding of `A`'s atom in `B`'s (`QAtomicType.embed`), a partial function that
    never rounds; `𝟘` where a side is no atom. -/
def castDen : (A B : Obj) → Den A B
  | .atom s, .atom t => fun x y => QAtomicType.embed s t x = some y
  | _, _ => fun _ _ => False

/-- A float verb `o` of `floatOps`: at `F ⟶ D` for an `o` reading one operand, `o` on the value's `f64` word (`fval`);
    at `F×F ⟶ D` for one reading two, `o` on the two components' words; then the word of `D`'s atom for the answer
    (`Op.ofF64`), no row where that is `2^63` (NaN, or no value of `D`'s atom); `𝟘` at any other objects. -/
def floatDen (o : Rel.Kernel.Op) : (A B : Obj) → Den A B
  | .atom t, .atom u => fun x w => o.readsAcc = false ∧ ∃ X Y R, fval t x = some X ∧ o.eval 0 X = .ok Y ∧
      (Rel.Kernel.Op.ofF64 u).eval 0 Y = .ok R ∧ R ≠ 0x8000000000000000 ∧ w = QAtomicType.ofBits u R
  | .prod (.atom t) (.atom t'), .atom u => fun x w => o.readsAcc = true ∧ t = t' ∧ ∃ X X' Y R,
      fval t x.1 = some X ∧ fval t' x.2 = some X' ∧ o.eval X X' = .ok Y ∧
      (Rel.Kernel.Op.ofF64 u).eval 0 Y = .ok R ∧ R ≠ 0x8000000000000000 ∧ w = QAtomicType.ofBits u R
  | _, _ => fun _ _ => False

/-- A row's meaning at its object variables `σ`, given its relation arguments' meanings. -/
abbrev RowDen (c : RowCode) := (σ : List Obj) → List Sem → Den (c.ty σ).1 (c.ty σ).2

open Classical RowCode in
/-- Every row of `prims` with its meaning. `setify` is `Λ(∋)`. -/
def rowDens : List ((c : RowCode) × RowDen c) :=
  [⟨tau, fun _ _ a Y => Y = [a]⟩,
   ⟨cons, fun _ _ p ys => ys = p.1 :: p.2⟩,
   ⟨map, fun σ => Sem.one (X := σ₁ σ) (Y := σ₂ σ) mapDen⟩,
   ⟨filter, fun σ => Sem.one (X := σ₁ σ) (Y := σ₁ σ) fun T xs ys => ys = xs.filter fun x => decide (∃ y, T x y)⟩,
   ⟨takewhile, fun σ => Sem.one (X := σ₁ σ) (Y := σ₁ σ) fun T xs ys =>
      ys = xs.takeWhile fun x => decide (∃ y, T x y)⟩,
   ⟨thinL, fun σ => Sem.one (X := .prod (σ₁ σ) (σ₁ σ)) (Y := .prod (σ₁ σ) (σ₁ σ)) fun T =>
      thinLDen fun a b => decide (T (a, b) (a, b))⟩,
   ⟨merge, fun σ => Sem.one (X := .prod (σ₁ σ) (σ₁ σ)) (Y := .prod (σ₁ σ) (σ₁ σ)) fun T p zs =>
      zs = List.merge p.1 p.2 fun a b => decide (T (a, b) (a, b))⟩,
   ⟨loop, fun σ => Sem.one (X := .prod (σ₁ σ) (σ₂ σ)) (Y := σ₁ σ) fun T p c => ∃ g : Nat → (σ₁ σ).El, g 0 = p.1 ∧
      (∀ t (ht : t < p.2.length), T (g t, p.2[t]'ht) (g (t + 1))) ∧ c = g p.2.length⟩,
   ⟨uncons, fun _ _ xs p => xs = p.1 :: p.2⟩,
   ⟨length, fun _ _ xs w => w = Int64.ofNat xs.length⟩,
   ⟨sum, fun σ _ => sumAt (σ₁ σ)⟩,
   ⟨inits, fun _ _ xs yss => yss = (List.range (xs.length + 1)).map fun k => xs.take k⟩,
   ⟨tails, fun _ _ xs yss => yss = (List.range (xs.length + 1)).map fun k => xs.drop k⟩,
   ⟨«prefix», fun _ _ xs ys => ys <+: xs⟩,
   ⟨suffix, fun _ _ xs ys => ys <:+ xs⟩,
   ⟨concat, fun _ _ xss ys => ys = xss.flatten⟩,
   ⟨cat, fun _ _ p zs => zs = p.1 ++ p.2⟩,
   ⟨uncat, fun _ _ xs p => xs = p.1 ++ p.2⟩,
   ⟨zip, fun _ _ p zs => zs = p.1.zip p.2⟩,
   ⟨snoc, fun _ _ p ys => ys = p.1 ++ [p.2]⟩,
   ⟨unsnoc, fun _ _ xs p => xs = p.1 ++ [p.2]⟩,
   ⟨setify, fun σ _ => lamDen (fun xs a => a ∈ xs : Den (.arr (σ₁ σ)) (σ₁ σ))⟩,
   -- dataframe §3.1's `where(dom(xs ≫ p))`: the positions of `xs` whose element is in `dom(p)`, ascending
   ⟨positions, fun σ => Sem.one (X := σ₁ σ) (Y := σ₁ σ) fun T xs ys =>
      ys = positionsL (fun x => decide (∃ y, T x y)) xs⟩,
   -- q's `asc` of the set `dom P`: `j` to its `j`-th element in `Obj.lt` order
   ⟨asc, fun σ => Sem.one (X := σ₁ σ) (Y := σ₁ σ) fun T => ascDen (σ₁ σ) fun b => ∃ c, T b c⟩,
   ⟨sums, fun σ => Sem.one (X := .prod (σ₁ σ) (σ₂ σ)) (Y := σ.getD 2 .long) (sumsAt (σ₁ σ) (σ₂ σ) (σ.getD 2 .long))⟩,
   ⟨flat, fun σ => Sem.one (X := σ₁ σ) (Y := .prod (σ₂ σ) (σ.getD 2 .long)) flatDen⟩,
   ⟨cast, fun σ _ => castDen (σ₁ σ) (σ₂ σ)⟩,
   ⟨foldI, fun σ => Sem.two (X := σ₁ σ) (Y := .prod (σ₂ σ) (σ₂ σ))
      (X₂ := .prod (.prod (σ₁ σ) (σ₂ σ)) (σ.getD 2 .long)) (Y₂ := .prod (σ₁ σ) (σ₂ σ)) foldIDen⟩,
   -- the prelude's `star(R) ≜ μX : 𝟙 ∪ R X`, its body as `Tm.den` reads the definition's `μ`
   ⟨star, fun σ => Sem.one (X := σ₁ σ) (Y := σ₁ σ) fun T => Core.Rel.mu fun X => 𝟙 _ ∪ T ≫ X⟩,
   ⟨dom, fun σ => Sem.one (X := σ₁ σ) (Y := σ₂ σ) fun T => 𝟙 _ ∩ T ≫ T°⟩,
   ⟨ran, fun σ => Sem.one (X := σ₁ σ) (Y := σ₂ σ) fun T => 𝟙 _ ∩ T° ≫ T°°⟩,
   ⟨nil, fun _ _ => nilDen⟩] ++
  floatOps.map fun (s, o, _) =>
    ⟨⟨s, fun σ => (if o.readsAcc then .prod (σ₁ σ) (σ₁ σ) else σ₁ σ, σ₂ σ)⟩, fun _ _ => floatDen o _ _⟩


/-- The row `r`'s meaning at `A ⟶ B` given its relation arguments' meanings, found as `Prim.run` finds its code;
    `𝟘` where it has none there. -/
def Prim.den (r : Prim) (A B : Obj) (ss : List Sem) : Den A B :=
  match rowDens.find? (·.1.sym == r.sym), r.objs A B (ss.map fun s => (s.1, s.2.1)) with
  | some ⟨c, D⟩, some σ => if h : (c.ty σ).1 = A ∧ (c.ty σ).2 = B then h.1 ▸ h.2 ▸ D σ ss else 𝟘
  | _, _ => 𝟘

/-! ### `⟦−⟧` -/

mutual
/-- `⟦t⟧ρ`, one clause per constructor. A row and its arguments (`prim` under `arg`s) mean the row's meaning of
    its arguments' (`Tm.argDen`). A call (the `let` node) is its body read under its arguments bound at `ks`
    (`Val.args`), never under the caller's `ρ`; given none, under no variable. -/
noncomputable def Tm.den : Val → {A B : Obj} → Tm A B → Den A B
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
  | ρ, _, _, .diff R S => diffDen (R.den ρ) (S.den ρ)
  | ρ, _, _, .ldiv R S U V => ldivDen (R.den ρ) (S.den ρ) (U.den ρ) (V.den ρ)
  | ρ, _, _, .rdiv R S U V => rdivDen (R.den ρ) (S.den ρ) (U.den ρ) (V.den ρ)
  | ρ, _, _, .pair R S => rpair (R.den ρ) (S.den ρ)
  | ρ, _, _, .lam R => lamDen (R.den ρ)
  | ρ, _, _, .est Q => estDen (Q.den ρ)
  | ρ, _, _, .thin Q => thinDen (Q.den ρ)
  | _, _, _, .mem => fun xs x => x ∈ xs
  | _, _, _, .inl => Core.Rel.inl
  | _, _, _, .inr => Core.Rel.inr
  | _, A, B, .prim r => Prim.den r A B []
  | _, _, _, .atPos k => atDen k
  | ρ, _, _, .own R => R.den ρ
  | ρ, _, _, .succ U => succDen (U.den ρ)
  | ρ, _, _, .arith t k U => arithDen t k (U.den ρ)
  | ρ, _, _, .leq t U => leqDen t (U.den ρ)
  | ρ, _, _, .lt t U => ltDen t (U.den ρ)
  | ρ, _, _, .foldr e S => foldrDen (e.den ρ) (S.den ρ)
  | ρ, _, _, .fold e S => foldDen (e.den ρ) (S.den ρ)
  | _, _, _, .share _ R => R.den Val.empty
  | ρ, A, B, .var _ k => ρ k A B
  | _, _, _, .call ks _ _ b | _, _, _, .callCv ks _ _ _ b _ => b.den (Val.args ks [])
  | ρ, _, _, .arg f x => f.argDen ρ [⟨_, _, x.den ρ⟩]
  -- the rounds start at `⟦S⟧` and meet each with it (`Gen.nu`), so `S` bounds the greatest fixed point
  | ρ, _, _, .nu k S b => Core.Rel.nu fun X => S.den ρ ∩ b.den (ρ.bind k X)
  | ρ, _, _, .mu k _ _ b => Core.Rel.mu fun X => b.den (ρ.bind k X)
  | ρ, _, _, .hylo k _ b => Core.Rel.mu fun X => b.den (ρ.bind k X)

/-- The spine `f` of a row given the meanings `ss` of its later arguments: the row's meaning of all of them, in
    the order `compile` passes their codes; a call's body with them bound at its `ks`; `𝟘` where `f` is neither
    a row nor a call under `arg`s. `share` and `own` are seen through, as `Tm.gen` passes their part's row on. -/
noncomputable def Tm.argDen : Val → {A B : Obj} → Tm A B → List Sem → Den A B
  | _, A, B, .prim r, ss => Prim.den r A B ss
  | _, _, _, .call ks _ _ b, ss | _, _, _, .callCv ks _ _ _ b _, ss => b.den (Val.args ks ss)
  | ρ, _, _, .arg f x, ss => f.argDen ρ (⟨_, _, x.den ρ⟩ :: ss)
  | _, _, _, .share _ R, ss => R.argDen Val.empty ss
  | ρ, _, _, .own R, ss => R.argDen ρ ss
  | _, _, _, _, _ => 𝟘
end

/-- **`dom` is a row**: `Tm.dom R`, `domRow` given `R`, means `𝟙 ∩ R R°`. -/
theorem Tm.dom_den (ρ : Val) {A B : Obj} (R : Tm A B) : (Tm.dom R).den ρ = 𝟙 _ ∩ R.den ρ ≫ (R.den ρ)° := by
  have ho : domRow.objs A A [(A, B)] = some [A, B] := by
    simp [Prim.objs, Option.orElse, domRow, OExp.unify, Prim.vars, OExp.vars, List.eraseDups, List.eraseDupsBy,
      List.eraseDupsBy.loop, List.lookup]
  have hf : rowDens.find? (·.1.sym == domRow.sym) =
      some ⟨RowCode.dom, fun σ => Sem.one (X := σ₁ σ) (Y := σ₂ σ) fun T => 𝟙 _ ∩ T ≫ T°⟩ := rfl
  simp only [Tm.dom, Tm.den, Tm.argDen]; unfold Prim.den; simp only [List.map_cons, List.map_nil]
  rw [hf, ho]; dsimp only; rw [dif_pos ⟨rfl, rfl⟩]
  simp only [Sem.one]; exact dif_pos ⟨rfl, rfl⟩

/-- **`ran` is a row**: `Tm.ran R`, `ranRow` given `R`, means `𝟙 ∩ R° R`. -/
theorem Tm.ran_den (ρ : Val) {A B : Obj} (R : Tm A B) : (Tm.ran R).den ρ = 𝟙 _ ∩ (R.den ρ)° ≫ (R.den ρ)°° := by
  have ho : ranRow.objs B B [(A, B)] = some [A, B] := by
    simp [Prim.objs, Option.orElse, ranRow, OExp.unify, Prim.vars, OExp.vars, List.eraseDups, List.eraseDupsBy,
      List.eraseDupsBy.loop, List.lookup]
  have hf : rowDens.find? (·.1.sym == ranRow.sym) =
      some ⟨RowCode.ran, fun σ => Sem.one (X := σ₁ σ) (Y := σ₂ σ) fun T => 𝟙 _ ∩ T° ≫ T°°⟩ := rfl
  simp only [Tm.ran, Tm.den, Tm.argDen]; unfold Prim.den; simp only [List.map_cons, List.map_nil]
  rw [hf, ho]; dsimp only; rw [dif_pos ⟨rfl, rfl⟩]
  simp only [Sem.one]; exact dif_pos ⟨rfl, rfl⟩

/-- **`[]` is a row**: `Tm.nil`, `nilRow`, means `nilDen`. -/
theorem Tm.nil_den (ρ : Val) {A B : Obj} : (Tm.nil : Tm A (.arr B)).den ρ = nilDen := by
  have ho : nilRow.objs A (.arr B) [] = some [A, B] := by
    simp [Prim.objs, Option.orElse, nilRow, OExp.unify, Prim.vars, OExp.vars, List.eraseDups, List.eraseDupsBy,
      List.eraseDupsBy.loop, List.lookup]
  have hf : rowDens.find? (·.1.sym == nilRow.sym) = some ⟨RowCode.nil, fun _ _ => nilDen⟩ := rfl
  simp only [Tm.nil, Tm.den]; unfold Prim.den; simp only [List.map_nil]
  rw [hf, ho]; dsimp only; rw [dif_pos ⟨rfl, rfl⟩]; rfl

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
  | var _ k => intro ρ ρ' h; exact ⟨by simp only [Tm.den, h k (by simp [Tm.fv])], fun _ => rfl⟩
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
  | own R ih =>
    intro ρ ρ' h
    have e := ih ρ ρ' fun i hi => h i (by simp [Tm.fv, hi])
    exact ⟨by simp only [Tm.den, e.1], fun _ => by simp only [Tm.argDen, e.2]⟩
  | conv R ih | est R ih | succ R ih | arith _ _ R ih | leq _ R ih | lt _ R ih
  | lam R ih | thin R ih =>
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

/-- `σ` read under `ρ`: each entry binds its variable to its term's meaning, the first entry outermost. -/
noncomputable def Tm.Sub.den (ρ : Val) : Tm.Sub → Val
  | [] => ρ
  | (k, ⟨_, _, s⟩) :: σ => (Sub.den ρ σ).bind k (s.den ρ)

/-- No term of `σ` is a row's spine: a term put for a variable heading `arg`s keeps that spine's meaning `𝟘`, as
    the variable's own is (`compile` too runs a row only under a `prim` head). -/
def Tm.Sub.Plain (σ : Tm.Sub) : Prop := ∀ e ∈ σ, ∀ ρ ss, e.2.2.2.argDen ρ ss = 𝟘

theorem Tm.Sub.argDen_get {ρ : Val} {ss : List Sem} (i : Nat) {A' B' : Obj} (d : Bool) :
    ∀ σ : Tm.Sub, σ.Plain → (σ.get i d : Tm A' B').argDen ρ ss = 𝟘
  | [], _ => rfl
  | (k, ⟨A, B, s⟩) :: σ, hσ => by
    simp only [Sub.get]
    split
    · split
      · rename_i h; obtain ⟨rfl, rfl⟩ := h; exact hσ _ List.mem_cons_self ρ ss
      · rfl
    · exact argDen_get i d σ fun e he => hσ e (List.mem_cons_of_mem _ he)

theorem Tm.Sub.den_get (ρ : Val) (i : Nat) {A' B' : Obj} (d : Bool) :
    ∀ σ : Tm.Sub, (σ.get i d : Tm A' B').den ρ = σ.den ρ i A' B'
  | [] => rfl
  | (k, ⟨A, B, s⟩) :: σ => by
    by_cases e : i = k
    · subst e
      by_cases h : A = A' ∧ B = B'
      · obtain ⟨rfl, rfl⟩ := h; simp [Sub.get, Sub.den, Val.bind]
      · simp [Sub.get, Sub.den, Val.bind, h, Tm.den]
    · simp only [Sub.get, Sub.den, if_neg e, Val.bind_ne e]; exact den_get ρ i d σ

theorem Tm.lt_fresh : ∀ {l : List Nat} {i : Nat}, i ∈ l → i < Tm.fresh l
  | a :: l, i, h => by
    rcases List.mem_cons.1 h with rfl | h
    · exact Nat.lt_succ_of_le (Nat.le_max_left _ _)
    · exact Nat.lt_of_lt_of_le (lt_fresh h) (Nat.succ_le_succ (Nat.le_max_right _ _))

/-- Binding a variable `k` no term of `σ` mentions changes `σ`'s meaning only at `k`. -/
theorem Tm.Sub.den_bind {ρ : Val} {k : Nat} {A B : Obj} {X : Den A B} :
    ∀ σ : Tm.Sub, (∀ j ∈ σ.fvs, j ≠ k) → ∀ i, i ≠ k → σ.den (ρ.bind k X) i = σ.den ρ i
  | [], _, _, hi => Val.bind_ne hi
  | (j, ⟨_, _, s⟩) :: σ, h, i, hi => by
    simp only [Sub.den, (s.den_congr (ρ.bind k X) ρ fun l hl => Val.bind_ne (h l (by simp [Sub.fvs, hl]))).1]
    by_cases e : i = j
    · subst e; exact Val.bind_same
    · rw [Val.bind_ne e, Val.bind_ne e]; exact den_bind σ (fun l hl => h l (by simp [Sub.fvs, hl])) i hi

/-- Under a binder `k` renamed to `k'`, fresh for the body `b` and `σ`: the substituted body read with `k'` bound
    to `X` is the body read with `k` bound to `X` over `σ`'s meaning. -/
theorem Tm.Sub.den_rename {A B A' B' : Obj} (b : Tm A' B') (σ : Tm.Sub) (ρ : Val) (k : Nat)
    (X : Den A B) : b.den (Sub.den (ρ.bind (fresh (b.fv ++ σ.fvs)) X)
      ((k, ⟨A, B, .var false (fresh (b.fv ++ σ.fvs))⟩) :: σ)) = b.den ((σ.den ρ).bind k X) := by
  refine (b.den_congr _ _ fun i hi => ?_).1
  have hv : (Tm.var false (fresh (b.fv ++ σ.fvs)) : Tm A B).den (ρ.bind (fresh (b.fv ++ σ.fvs)) X) = X := by
    simp [Tm.den, Val.bind]
  simp only [Sub.den, hv]
  by_cases e : i = k
  · subst e; exact Val.bind_same
  · rw [Val.bind_ne e, Val.bind_ne e]
    exact den_bind σ (fun j hj => Nat.ne_of_lt (lt_fresh (List.mem_append_right _ hj))) i
      (Nat.ne_of_lt (lt_fresh (List.mem_append_left _ hi)))


/-! ### Monotonicity -/

/-- `ρ'` grows `ρ` at the variable `k` and agrees with it at every other. -/
def Val.Grow (k : Nat) (ρ ρ' : Val) : Prop := (∀ A B, ρ k A B ⊑ ρ' k A B) ∧ ∀ i, i ≠ k → ρ i = ρ' i

/-- `X ⊑ Y` read with the sign `s`: `true` keeps it, `false` turns it round. -/
def sle (s : Bool) {A B : Obj} (X Y : Den A B) : Prop := cond s (X ⊑ Y) (Y ⊑ X)

theorem Val.Grow.congr {k : Nat} {ρ ρ' : Val} (g : Grow k ρ ρ') {A B : Obj} {t : Tm A B}
    (h : t.fv.contains k = false) : t.den ρ = t.den ρ' :=
  (t.den_congr ρ ρ' fun i hi => g.2 i fun e => by subst e; simp [hi] at h).1

theorem Val.Grow.bind {k j : Nat} {ρ ρ' : Val} (g : Grow k ρ ρ') (hj : j ≠ k) {A B : Obj} (X : Den A B) :
    Grow k (ρ.bind j X) (ρ'.bind j X) := by
  refine ⟨fun A' B' => ?_, fun i hi => ?_⟩
  · rw [Val.bind_ne (Ne.symm hj), Val.bind_ne (Ne.symm hj)]; exact g.1 A' B'
  · by_cases e : i = j
    · subst e; exact Val.bind_same
    · rw [Val.bind_ne e, Val.bind_ne e]; exact g.2 i hi

/-- Binding `k` to a larger `Y` grows the valuation at `k`. -/
theorem Val.Grow.of_le {k : Nat} {ρ : Val} {X Y : Den A B} (hXY : X ⊑ Y) : Grow k (ρ.bind k X) (ρ.bind k Y) := by
  refine ⟨fun A' B' => ?_, fun i hi => by rw [Val.bind_ne hi, Val.bind_ne hi]⟩
  simp only [Val.bind, if_true]
  by_cases h : A = A' ∧ B = B'
  · obtain ⟨rfl, rfl⟩ := h; simpa using hXY
  · simp only [dif_neg h]; exact Core.Rel.le_refl _

section ops
variable {D E F : Obj}

theorem comp_le' {X X' : Den A B} {Y Y' : Den B C} (hX : X ⊑ X') (hY : Y ⊑ Y') : X ≫ Y ⊑ X' ≫ Y' :=
  le_iff.2 fun a c h => by
    rw [comp_apply] at h ⊢; obtain ⟨b, h1, h2⟩ := h; exact ⟨b, le_iff.1 hX _ _ h1, le_iff.1 hY _ _ h2⟩

theorem conv_le' {X X' : Den A B} (hX : X ⊑ X') : X° ⊑ X'° :=
  le_iff.2 fun a b h => by rw [recip_apply] at h ⊢; exact le_iff.1 hX _ _ h

theorem inter_le' {X X' Y Y' : Den A B} (hX : X ⊑ X') (hY : Y ⊑ Y') : X ∩ Y ⊑ X' ∩ Y' :=
  le_iff.2 fun a b h => by rw [inter_apply] at h ⊢; exact ⟨le_iff.1 hX _ _ h.1, le_iff.1 hY _ _ h.2⟩

theorem union_le' {X X' Y Y' : Den A B} (hX : X ⊑ X') (hY : Y ⊑ Y') : X ∪ Y ⊑ X' ∪ Y' :=
  le_iff.2 fun a b h => by rw [union_apply] at h ⊢; exact h.imp (le_iff.1 hX _ _) (le_iff.1 hY _ _)

theorem diff_le {X X' Y Y' : Den A B} (hX : X ⊑ X') (hY : Y' ⊑ Y) : diffDen X Y ⊑ diffDen X' Y' :=
  le_iff.2 fun _ _ h => ⟨le_iff.1 hX _ _ h.1, fun h' => h.2 (le_iff.1 hY _ _ h')⟩

theorem ldiv_le {R : Den A B} {S S' : Den A C} {U U' : Den B B} {V V' : Den C C} (hS : S ⊑ S') (hU : U ⊑ U')
    (hV : V ⊑ V') : ldivDen R S U V ⊑ ldivDen R S' U' V' :=
  le_iff.2 fun _ _ h => ⟨fun a ha => le_iff.1 hS _ _ (h.1 a ha),
    h.2.imp id fun ⟨⟨b', hb⟩, c', hc⟩ => ⟨⟨b', le_iff.1 hU _ _ hb⟩, c', le_iff.1 hV _ _ hc⟩⟩

theorem rdiv_le {R R' : Den A C} {S : Den B C} {U U' : Den A A} {V V' : Den B B} (hR : R ⊑ R') (hU : U ⊑ U')
    (hV : V ⊑ V') : rdivDen R S U V ⊑ rdivDen R' S U' V' :=
  le_iff.2 fun _ _ h => ⟨fun c hc => le_iff.1 hR _ _ (h.1 c hc),
    h.2.imp id fun ⟨⟨a, ha⟩, b, hb⟩ => ⟨⟨a, le_iff.1 hU _ _ ha⟩, b, le_iff.1 hV _ _ hb⟩⟩

theorem pair_le {X X' : Den A B} {Y Y' : Den A C} (hX : X ⊑ X') (hY : Y ⊑ Y') : rpair X Y ⊑ rpair X' Y' :=
  le_iff.2 fun _ _ h => ⟨le_iff.1 hX _ _ h.1, le_iff.1 hY _ _ h.2⟩

-- `est` drops `b` only where `Q` fails, so a larger `Q` drops fewer
theorem est_le {Q Q' : Den (.prod B B) (.prod B B)} (hQ : Q ⊑ Q') : estDen Q ⊑ estDen Q' :=
  le_iff.2 fun _ _ h => ⟨h.1, fun ⟨c, hc, hne, hq⟩ => h.2 ⟨c, hc, hne, fun h' => hq (le_iff.1 hQ _ _ h')⟩⟩

theorem succ_le {U U' : Den .long .long} (hU : U ⊑ U') : succDen U ⊑ succDen U' :=
  le_iff.2 fun _ _ ⟨⟨v, hv⟩, e, v', hv'⟩ => ⟨⟨v, le_iff.1 hU _ _ hv⟩, e, v', le_iff.1 hU _ _ hv'⟩

theorem leq_le {t : QAtomicType} {U U' : Den (.atom t) (.atom t)} (hU : U ⊑ U') : leqDen t U ⊑ leqDen t U' :=
  le_iff.2 fun _ _ ⟨⟨v, hv⟩, ⟨v', hv'⟩, e⟩ => ⟨⟨v, le_iff.1 hU _ _ hv⟩, ⟨v', le_iff.1 hU _ _ hv'⟩, e⟩

theorem lt_le {t : QAtomicType} {U U' : Den (.atom t) (.atom t)} (hU : U ⊑ U') : ltDen t U ⊑ ltDen t U' :=
  le_iff.2 fun _ _ ⟨⟨v, hv⟩, ⟨v', hv'⟩, e⟩ => ⟨⟨v, le_iff.1 hU _ _ hv⟩, ⟨v', le_iff.1 hU _ _ hv'⟩, e⟩

theorem arith_le {t : QAtomicType} {k : UInt8} {U U' : Den (.atom t) (.atom t)} (hU : U ⊑ U') :
    arithDen t k U ⊑ arithDen t k U' :=
  comp_le' (inter_le' (Core.Rel.le_refl _) (comp_le' (comp_le' (Core.Rel.le_refl _) hU)
      (conv_le' (comp_le' (Core.Rel.le_refl _) hU))))
    (comp_le' (inter_le' (Core.Rel.le_refl _) (comp_le' (comp_le' (Core.Rel.le_refl _) hU)
      (conv_le' (comp_le' (Core.Rel.le_refl _) hU)))) (comp_le' (Core.Rel.le_refl _) hU))

theorem foldr_le {e e' : Den B B} {S S' : Den (.prod A B) B} (he : e ⊑ e') (hS : S ⊑ S') :
    foldrDen e S ⊑ foldrDen e' S' :=
  le_iff.2 fun _ _ ⟨ys, hy, ⟨a, ha⟩, hs, hw⟩ =>
    ⟨ys, hy, ⟨a, le_iff.1 he _ _ ha⟩, fun t ht => le_iff.1 hS _ _ (hs t ht), hw⟩

theorem fold_le {e e' : Den B B} {S S' : Den (.prod B A) B} (he : e ⊑ e') (hS : S ⊑ S') :
    foldDen e S ⊑ foldDen e' S' :=
  le_iff.2 fun _ _ ⟨ys, hy, ⟨a, ha⟩, hs, hw⟩ =>
    ⟨ys, hy, ⟨a, le_iff.1 he _ _ ha⟩, fun t ht => le_iff.1 hS _ _ (hs t ht), hw⟩

theorem foldI_le {e e' : Den C (.prod B B)} {S S' : Den (.prod (.prod C B) A) (.prod C B)} (he : e ⊑ e')
    (hS : S ⊑ S') : foldIDen e S ⊑ foldIDen e' S' :=
  le_iff.2 fun _ _ h => le_iff.1 (fold_le (le_iff.2 fun _ _ h => le_iff.1 he _ _ h)
    (le_iff.2 fun _ _ h => le_iff.1 hS _ _ h)) _ _ h

end ops

/-- `ss'` grows `ss` argument by argument, each at the same objects. -/
inductive Sems.le : List Sem → List Sem → Prop
  | nil : Sems.le [] []
  | cons {X Y : Obj} {T T' : Den X Y} {ss ss' : List Sem} :
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

theorem Sems.sle.cons {s : Bool} {X Y : Obj} {T T' : Den X Y} {ss ss' : List Sem} (h : Rel.Lang.sle s T T')
    (hs : Sems.sle s ss ss') : Sems.sle s (⟨X, Y, T⟩ :: ss) (⟨X, Y, T'⟩ :: ss') := by
  cases s
  · exact Sems.le.cons h hs
  · exact Sems.le.cons h hs

theorem Sem.one_mono {X Y A B : Obj} {D : Den X Y → Den A B} (hD : ∀ {T T'}, T ⊑ T' → D T ⊑ D T')
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

theorem Sem.two_mono {X Y X₂ Y₂ A B : Obj} {D : Den X Y → Den X₂ Y₂ → Den A B}
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
  -- a `floatOps` row takes no relation; then one case per row whatever their number, in `rowDens` order
  rcases he with he | ⟨_, -, rfl⟩
  rotate_left
  · exact Core.Rel.le_refl _
  repeat' first | (rcases he with rfl | he) | subst he
  all_goals first | exact Core.Rel.le_refl _ | exact absurd hm (by decide) | skip
  · dsimp only; refine Sem.one_mono (fun hT => le_iff.2 fun _ _ hm => ?_) h
    exact ⟨hm.1, fun t ht ht' => le_iff.1 hT _ _ (hm.2 t ht ht')⟩
  · dsimp only; refine Sem.one_mono (fun hT => le_iff.2 fun _ _ hm => ?_) h
    obtain ⟨g, h0, hs, hc⟩ := hm
    exact ⟨g, h0, fun t ht => le_iff.1 hT _ _ (hs t ht), hc⟩
  · dsimp only; refine Sem.one_mono (fun hT => le_iff.2 fun _ _ hm => ?_) h
    exact le_iff.1 hT _ _ hm
  · exact Sem.two_mono foldI_le h
  · dsimp only; refine Sem.one_mono (fun hT => Core.Rel.mu_mono fun _ => le_iff.2 fun _ _ hm => ?_) h
    exact hm.elim .inl fun ⟨b, hb, hx⟩ => .inr ⟨b, le_iff.1 hT _ _ hb, hx⟩
  -- `dom`, `ran`: `𝟙 ∩ T T°`, `𝟙 ∩ T° T` grow with `T`
  all_goals
    dsimp only; refine Sem.one_mono (fun hT => le_iff.2 fun _ _ hm => ?_) h
    obtain ⟨he, y, h1, h2⟩ := hm; exact ⟨he, y, le_iff.1 hT _ _ h1, le_iff.1 hT _ _ h2⟩

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

theorem sle.refl {s : Bool} (X : Den A B) : sle s X X := by cases s <;> exact Core.Rel.le_refl X

theorem sle.of_eq {s : Bool} {X Y : Den A B} (h : X = Y) : sle s X Y := h ▸ sle.refl X

theorem sle.map1 {A' B' : Obj} {f : Den A B → Den A' B'} (hf : ∀ {X X'}, X ⊑ X' → f X ⊑ f X') :
    ∀ {s X X'}, sle s X X' → sle s (f X) (f X')
  | true, _, _, h | false, _, _, h => hf h

theorem sle.map2 {A' B' A'' B'' : Obj} {f : Den A B → Den A' B' → Den A'' B''}
    (hf : ∀ {X X' Y Y'}, X ⊑ X' → Y ⊑ Y' → f X Y ⊑ f X' Y') :
    ∀ {s X X' Y Y'}, sle s X X' → sle s Y Y' → sle s (f X Y) (f X' Y')
  | true, _, _, _, _, h1, h2 | false, _, _, _, _, h1, h2 => hf h1 h2

/-- The second argument antitone: `diff`. -/
theorem sle.anti2 {f : Den A B → Den A B → Den A B} (hf : ∀ {X X' Y Y'}, X ⊑ X' → Y' ⊑ Y → f X Y ⊑ f X' Y') :
    ∀ {s X X' Y Y'}, sle s X X' → sle (!s) Y Y' → sle s (f X Y) (f X' Y')
  | true, _, _, _, _, h1, h2 | false, _, _, _, _, h1, h2 => hf h1 h2

theorem sle.map3 {A' B' A'' B'' A''' B''' : Obj} {f : Den A B → Den A' B' → Den A'' B'' → Den A''' B'''}
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
  | var _ j =>
    refine ⟨fun s ρ ρ' hp g => ?_, fun _ _ _ _ _ h => by simp [Tm.spinePol] at h⟩
    simp only [Tm.den]
    by_cases e : j = k
    · subst e; simp only [Tm.pol, beq_self_eq_true, if_true] at hp; subst hp; exact g.1 _ _
    · rw [g.2 j e]; exact sle.refl _
  | top V ih => refine ⟨fun s ρ ρ' hp g => ?_, fun _ _ _ _ _ h => by simp [Tm.spinePol] at h⟩; exact sle.map1 (comp_le' (Core.Rel.le_refl _)) (ih.1 s ρ ρ' hp g)
  | conv R ih => refine ⟨fun s ρ ρ' hp g => ?_, fun _ _ _ _ _ h => by simp [Tm.spinePol] at h⟩; exact sle.map1 conv_le' (ih.1 s ρ ρ' hp g)
  | own R ih => refine ⟨fun s ρ ρ' hp g => ?_, fun _ _ _ _ _ h => by simp [Tm.spinePol] at h⟩; exact ih.1 s ρ ρ' hp g
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
      have hb : ∀ {A' B' : Obj} (X : Den A' B'), ρ.bind j X = ρ'.bind j X := fun X => funext fun i => by
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
      have hb : ∀ {A' B' : Obj} (X : Den A' B'), ρ.bind j X = ρ'.bind j X := fun X => funext fun i => by
        by_cases e' : i = j
        · subst e'; exact Val.bind_same
        · rw [Val.bind_ne e', Val.bind_ne e', g.2 i e']
      simp only [hb]; exact sle.refl _
    · simp only [Tm.pol, Bool.or_eq_true, beq_iff_eq, e, false_or] at hp
      exact sle.lfp fun X => ih.1 s _ _ hp (g.bind e X)
  | est Q ih => refine ⟨fun s ρ ρ' hp g => ?_, fun _ _ _ _ _ h => by simp [Tm.spinePol] at h⟩; exact sle.map1 est_le (ih.1 s ρ ρ' hp g)
  | succ U ih => refine ⟨fun s ρ ρ' hp g => ?_, fun _ _ _ _ _ h => by simp [Tm.spinePol] at h⟩; exact sle.map1 succ_le (ih.1 s ρ ρ' hp g)
  | arith _ _ U ih => refine ⟨fun s ρ ρ' hp g => ?_, fun _ _ _ _ _ h => by simp [Tm.spinePol] at h⟩; exact sle.map1 arith_le (ih.1 s ρ ρ' hp g)
  | leq _ U ih => refine ⟨fun s ρ ρ' hp g => ?_, fun _ _ _ _ _ h => by simp [Tm.spinePol] at h⟩; exact sle.map1 leq_le (ih.1 s ρ ρ' hp g)
  | lt _ U ih => refine ⟨fun s ρ ρ' hp g => ?_, fun _ _ _ _ _ h => by simp [Tm.spinePol] at h⟩; exact sle.map1 lt_le (ih.1 s ρ ρ' hp g)
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
    {X Y : Den A B} (hXY : X ⊑ Y) : t.den (ρ.bind k X) ⊑ t.den (ρ.bind k Y) :=
  t.den_pol k true _ _ h (Val.Grow.of_le hXY)




/-- `Tm.memAt` at `[E] ⟶ E` is `∋`: it relates a list to its members. -/
theorem Tm.den_memAt {ρ : Val} {E : Obj} : (Tm.memAt (.arr E) E).den ρ = fun (xs : (Obj.arr E).El) x => x ∈ xs := by
  simp only [Tm.memAt, dite_true]; rfl

/-- **`E` is a definition**: the term `Λ(∋ R)` that `applied` and `appliedL` build for `E(R)` means `EDen`. -/
theorem Tm.E_den (ρ : Val) {A B : Obj} (R : Tm A B) :
    (Tm.lam (.comp (.mem (B := A)) R)).den ρ = EDen (R.den ρ) := by
  simp only [Tm.den]

/-- A row `F(T)` at `xs` reads `T` only at the members of `xs`. -/
theorem Prim.den_map_congr {r : Prim} (hr : (r.sym == mapRow.sym) = true) {A B C D : Obj} {T T' : Den C D}
    {ρ : Val} {a : A.El} (h : ∀ m, (Tm.memAt A C).den ρ a m → ∀ e, (T m e ↔ T' m e)) (d : B.El) :
    r.den A B [⟨C, D, T⟩] a d ↔ r.den A B [⟨C, D, T'⟩] a d := by
  have hf : rowDens.find? (·.1.sym == mapRow.sym) = some ⟨RowCode.map, fun σ => Sem.one (X := σ₁ σ) (Y := σ₂ σ)
      fun T (xs : List (σ₁ σ).El) (ys : List (σ₂ σ).El) => ys.length = xs.length ∧
        ∀ t (ht : t < xs.length) (ht' : t < ys.length), T (xs[t]'ht) (ys[t]'ht')⟩ := rfl
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
        rw [dif_pos ⟨rfl, rfl⟩, dif_pos ⟨rfl, rfl⟩]
        exact and_congr_right fun _ => forall_congr' fun t => forall_congr' fun ht => forall_congr' fun ht' =>
          h _ (Tm.den_memAt ▸ List.getElem_mem ht) _
      · rw [dif_neg hc, dif_neg hc]
    · rw [dif_neg hh, dif_neg hh]

/-- A row `dom(T)` at `a` reads `T` only at `a`. -/
theorem Prim.den_dom_congr {r : Prim} (hr : (r.sym == domRow.sym) = true) {A B C D : Obj} {T T' : Den C D}
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
theorem Tm.den_local (k : Nat) {A B : Obj} (ρ : Val) (X Y : Den A B) : ∀ {C D : Obj} (t : Tm C D) (c : Tm C A),
    t.kids k A = some c → ∀ a, (∀ a', c.den ρ a a' → ∀ b, (X a' b ↔ Y a' b)) →
      ∀ d, t.den (ρ.bind k X) a d ↔ t.den (ρ.bind k Y) a d := by
  have free : ∀ {C D : Obj} (t : Tm C D), t.fv.contains k = false → ∀ a d,
      t.den (ρ.bind k X) a d ↔ t.den (ρ.bind k Y) a d := fun t h a d => by
    rw [(t.den_congr _ (ρ.bind k Y) fun i hi => by
      rw [Val.bind_ne (by rintro rfl; simp [hi] at h), Val.bind_ne (by rintro rfl; simp [hi] at h)]).1]
  intro C D t
  induction t with
  | @var C' D' _ j =>
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
  | own R ih =>
    intro c hc a hX d
    unfold Tm.kids at hc; split at hc
    · dsimp only at hc; exact ih c hc a hX d
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

#print axioms Tm.den_pol
#print axioms Core.Rel.mu_fix

end Rel.Lang
