/-
  `⟦−⟧`: the meaning of a core term `Tm` as an arrow of `Rel(Set)` (`doc/rel-denotation-design.md` §1, §2, §7.3).
  Total and structural: each node is the `T` its `Gen.*_sound` lemma proves, written with the allegory's operators
  (`≫ ° ∩ ∪ 𝟙 𝟘`, D3 = E); `μ`, `ν` are `Core.Rel.mu`, `nu`, defined for every body, so no monotonicity is assumed here.
-/
import Rel.Run.Lang.Tm
import Rel.Rep
import Rel.ObjOrder
import Rel.Core.Fix
import Rel.CRelFold
import Rel.Run.Lang.Compile

namespace Rel.Lang

open Rel.Kernel Rel Rel.Rep
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

/-- A table's value rows are the values its `rep` relates. -/
theorem valRow {A B : Obj} (U : Rel A B) (b : B.El) : (∃ p, U.val.row p = b) ↔ ∃ a, rep U a b :=
  ⟨fun ⟨p, e⟩ => ⟨U.key.row p, p, rfl, e⟩, fun ⟨_, p, _, e⟩ => ⟨p, e⟩⟩

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

/-- `rep_symDiv` is `symDivDen` with the universes the coreflexives of `Ua`, `Ub`. It sits here, not in
    `Rel.CRelRel`, because this module imports that one. -/
theorem rep_symDiv_den {ma mb : USize} (R : CRel A C) (S : CRel B C) (Ua : Vals A ma) (Ub : Vals B mb)
    (hb : (R.symDiv S Ua Ub).ok = true) :
    rep (R.symDiv S Ua Ub).rel = symDivDen (corefl fun x => ∃ p, Ua.row p = x) (corefl fun y => ∃ j, Ub.row j = y)
      (rep R.rel) (rep S.rel) := by
  funext x y; apply propext; rw [CRel.rep_symDiv R S Ua Ub hb x y]
  simp only [symDivDen, rdivDen, Core.Rel.inter, Core.Rel.recip, Core.Rel.corefl, exists_eq_left]
  constructor
  · rintro ⟨h, ⟨c, hc⟩ | hu⟩
    · exact ⟨⟨fun c => (h c).2, .inl ⟨c, (h c).1 hc⟩⟩, fun c => (h c).1, .inl ⟨c, hc⟩⟩
    · exact ⟨⟨fun c => (h c).2, .inr hu⟩, fun c => (h c).1, .inr hu.symm⟩
  · rintro ⟨⟨h2, -⟩, h1, hu⟩
    exact ⟨fun c => ⟨h1 c, h2 c⟩, hu.imp id And.symm⟩

/-- `nil`: every source to the empty array. -/
abbrev nilDen : Den A (.arr B) := fun _ Y => Y = []

/-- `at(k)`: the element at position `k`. -/
abbrev atDen (k : Nat) : Den (.arr B) B := fun xs x => ∃ h : k < xs.length, x = xs[k]'h

/-- `succ` on the universe `TU`: `u` and its successor both in it. -/
abbrev succDen (TU : Den .long .long) : Den .long .long :=
  fun u w => (∃ v, TU u v) ∧ w = Ew.intStep Ew.add Alg.nul u 1 ∧ ∃ v, TU w v

/-- `≤` on the universe `TU`. -/
abbrev leqDen (TU : Den .long .long) : Den .long .long := fun a b => (∃ v, TU a v) ∧ (∃ v, TU b v) ∧ a ≤ b

/-- `<` on the universe `TU`. -/
abbrev ltDen (TU : Den .long .long) : Den .long .long := fun a b => (∃ v, TU a v) ∧ (∃ v, TU b v) ∧ a < b

/-- The value verb `k` itself (`Alg.arith`): `Int64`'s step, not the null and, for `+ - *`, not wrapped. -/
abbrev stepDen (k : UInt8) : Den (.prod .long .long) .long :=
  fun p w => w = Ew.intStep k Alg.nul p.1 p.2 ∧ w ≠ Alg.nul ∧
    (if k == Ew.add then (0 ≤ p.2 ↔ p.1 ≤ w) else if k == Ew.sub then (0 ≤ p.2 ↔ w ≤ p.1)
     else if k == Ew.mul then (Ew.intStep Ew.idiv Alg.nul w p.1 = p.2 ∨ p.1 = 0) else True)

/-- The value verb `k` on the universe `TU`: both inputs in `TU` (`dom(π₁ TU)`, `dom(π₂ TU)`), as `succDen`'s,
    then the step, its result in `TU`. The input test makes `(TU×TU) arith = arith` at a coreflexive `TU`. -/
abbrev arithDen (k : UInt8) (TU : Den .long .long) : Den (.prod .long .long) .long :=
  (𝟙 _ ∩ (graph Prod.fst ≫ TU) ≫ (graph Prod.fst ≫ TU)°) ≫
    ((𝟙 _ ∩ (graph Prod.snd ≫ TU) ≫ (graph Prod.snd ≫ TU)°) ≫ (stepDen k ≫ TU))

/-- `fold(e, S)`: a chain of values `ys`, its last from `e`, each the step `S` of the element and the next value. -/
abbrev foldDen {E V : Obj} (Te : Den V V) (TS : Den (.prod E V) V) : Den (.arr E) V :=
  fun xs w => ∃ ys : List V.El, ∃ hy : ys.length = xs.length + 1,
    (∃ a, Te a (ys[xs.length]'(Nat.lt_of_lt_of_eq (Nat.lt_succ_self _) hy.symm))) ∧
    (∀ t (ht : t < xs.length), TS (xs[t]'ht, ys[t + 1]'(Nat.lt_of_lt_of_eq (Nat.succ_lt_succ ht) hy.symm))
      (ys[t]'(Nat.lt_of_lt_of_eq (Nat.lt_succ_of_lt ht) hy.symm))) ∧
    w = ys[0]'(Nat.lt_of_lt_of_eq (Nat.zero_lt_succ _) hy.symm)

/-- The left fold `⦇e, S⦈` over `[nil, snoc]`: a chain of values `ys`, its first from `e`, each the step `S` of the
    value before and the element (`(acc, x)`, index 0 first), the result its last. -/
abbrev foldlDen {E V : Obj} (Te : Den V V) (TS : Den (.prod V E) V) : Den (.arr E) V :=
  fun xs w => ∃ ys : List V.El, ∃ hy : ys.length = xs.length + 1,
    (∃ a, Te a (ys[0]'(by omega))) ∧
    (∀ t (ht : t < xs.length), TS (ys[t]'(by omega), xs[t]'ht) (ys[t + 1]'(by omega))) ∧
    w = ys[xs.length]'(by omega)

/-- The left fold read from the back: `foldlDen` on `xs` is the chain `rep_foldOnC` reads at `l` (`ordL`), the
    right fold's chain on `xs.reverse`, the pair `(acc, x)` and `ys` reversed. -/
theorem foldlDen_rev {E V : Obj} (Te : Den V V) (TS : Den (.prod V E) V) (xs : List E.El) (w : V.El) :
    foldlDen Te TS xs w ↔ ∃ ys : List V.El, ∃ hy : ys.length = xs.reverse.length + 1,
      (∃ a, Te a (ys[xs.reverse.length]'(by omega))) ∧
      (∀ t (ht : t < xs.reverse.length), TS (ys[t + 1]'(by omega), xs.reverse[t]'ht) (ys[t]'(by omega))) ∧
      w = ys[0]'(by omega) := by
  -- `ys ↦ ys.reverse` both ways: chain position `s` of one is `|xs| - s` of the other
  have rv : ∀ (zs : List V.El) (hz : zs.length = xs.length + 1) (i j : Nat) (hi : i < zs.reverse.length)
      (hj : j < zs.length), j = xs.length - i → zs.reverse[i] = zs[j] := by
    intro zs hz i j hi hj he; rw [List.getElem_reverse]; congr 1; simp only [List.length_reverse] at hi; omega
  have rx : ∀ (i j : Nat) (hi : i < xs.reverse.length) (hj : j < xs.length), j = xs.length - 1 - i →
      xs.reverse[i] = xs[j] := by
    intro i j hi hj he; rw [List.getElem_reverse]; congr 1; simp only [List.length_reverse] at hi; omega
  constructor
  · rintro ⟨ys, hy, ⟨a, ha⟩, hS, rfl⟩
    refine ⟨ys.reverse, by simp [hy], ⟨a, by rw [rv ys hy _ 0 _ (by omega) (by simp)]; exact ha⟩, fun t ht => ?_,
      by rw [rv ys hy 0 xs.length _ (by omega) (by simp)]⟩
    simp only [List.length_reverse] at ht
    rw [rv ys hy (t + 1) (xs.length - 1 - t) _ (by omega) (by omega), rv ys hy t (xs.length - 1 - t + 1) _ (by omega)
      (by omega), rx t (xs.length - 1 - t) _ (by omega) rfl]
    exact hS _ (by omega)
  · rintro ⟨ys, hy, ⟨a, ha⟩, hS, rfl⟩
    simp only [List.length_reverse] at hy ha hS
    refine ⟨ys.reverse, by simp [hy], ⟨a, ?_⟩, fun t ht => ?_, ?_⟩
    · rw [rv ys hy 0 xs.length _ (by omega) (by simp)]; exact ha
    · have h := hS (xs.length - 1 - t) (by omega)
      rw [rx _ t _ ht (by omega)] at h
      rw [rv ys hy t (xs.length - 1 - t + 1) _ (by omega) (by omega),
        rv ys hy (t + 1) (xs.length - 1 - t) _ (by omega) (by omega)]
      exact h
    · rw [rv ys hy xs.length 0 _ (by omega) (by simp)]

/-- `fold(e, S)` given a family: at the key `i`, the fold whose start is the fibre of `e` at `i` and whose step is
    `S` at `i`, keeping the key. -/
abbrev foldIDen {I E V : Obj} (Te : Den I (.prod V V)) (TS : Den (.prod E (.prod I V)) (.prod I V)) :
    Den (.prod I (.arr E)) V :=
  fun p w => foldDen (fun a b => Te p.1 (a, b)) (fun q v => TS (q.1, (p.1, q.2)) (p.1, v)) p.2 w

/-- `foldIDen` is one `foldDen` on the carrier `I×V`: start `ran⟨𝟙, Te ≫ π₂⟩`, step `TS` met with
    `π₂ ≫ π₁ ≫ π₁°` (the step keeps the index), its result's index met with the key's, then `π₂`. -/
theorem foldIDen_eq {I E V : Obj} (Te : Den I (.prod V V)) (TS : Den (.prod E (.prod I V)) (.prod I V)) :
    foldIDen Te TS =
      ((graph Prod.fst ≫ (graph Prod.fst)°) ∩
        (graph Prod.snd ≫ foldDen (E := E) (V := .prod I V)
          (𝟙 _ ∩ (rpair (𝟙 _) (Te ≫ graph Prod.snd))° ≫ (rpair (𝟙 _) (Te ≫ graph Prod.snd))°°)
          (TS ∩ (graph Prod.snd ≫ graph Prod.fst ≫ (graph Prod.fst)°)))) ≫ graph Prod.snd := by
  refine Core.Rel.ext fun p w => ?_
  simp only [foldIDen, foldDen, Core.Rel.comp, Core.Rel.inter, Core.Rel.recip, Core.Rel.graph, Core.Rel.rpair,
    Core.Rel.id]
  constructor
  · rintro ⟨ys, hy, ⟨a, ha⟩, hS, rfl⟩
    refine ⟨(p.1, ys[0]), ⟨⟨_, rfl, rfl⟩, _, rfl, ys.map (p.1, ·), by simp [hy],
      ⟨_, rfl, p.1, ⟨?_, _, ha, ?_⟩, ?_, _, ha, ?_⟩, fun t ht => ⟨?_, _, rfl, _, rfl, ?_⟩, ?_⟩, rfl⟩
    all_goals simp
    simpa using hS t (by simpa using ht)
  · rintro ⟨q, ⟨⟨i, rfl, hq⟩, xs, rfl, zs, hz, ⟨_, rfl, j, ⟨rfl, b, hb, hb2⟩, -, -⟩, hS, rfl⟩, rfl⟩
    -- the step keeps the index, so every value of the chain carries the key's
    have hidx : ∀ t (ht : t < zs.length), zs[t].1 = p.1 := by
      intro t
      induction t with
      | zero => intro _; exact hq.symm
      | succ t ih =>
        intro ht
        obtain ⟨-, _, rfl, _, rfl, he⟩ := hS t (by omega)
        exact he.trans (ih (by omega))
    refine ⟨zs.map Prod.snd, by simp [hz], ⟨b.1, ?_⟩, fun t ht => ?_, by simp⟩
    · have e := hidx p.2.length (by omega)
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

/-- `flatDen` is a composition: `(π₁ ≫ T) ∩ (π₂ ≫ π₁°)` keeps the `(a', b)` of `T` at the key with `a'` the
    source, then `π₂`. -/
theorem flatDen_eq {I A B : Obj} (T : Den I (.prod A B)) :
    flatDen T = ((graph Prod.fst ≫ T) ∩ (graph Prod.snd ≫ (graph Prod.fst)°)) ≫ graph Prod.snd :=
  Core.Rel.ext fun x b => ⟨fun h => ⟨(x.2, b), ⟨⟨x.1, rfl, h⟩, x.2, rfl, rfl⟩, rfl⟩,
    fun ⟨⟨_, _⟩, ⟨⟨_, hi, hT⟩, _, ha, ha'⟩, hb⟩ => by
      simp only [Core.Rel.recip, Core.Rel.graph, flatDen] at *; subst hi ha ha' hb; exact hT⟩

/-- `est(Q)` keeps `b` of `xs` unless some other `c` of `xs` fails `Q` at `(b, c)`. -/
abbrev estDen (TQ : Den (.prod B B) (.prod B B)) : Den (.arr B) B :=
  fun xs b => b ∈ xs ∧ ¬ ∃ c, c ∈ xs ∧ c ≠ b ∧ ¬ TQ (b, c) (b, c)

/-- `Λ(T)` with `𝒫B` held as `[B]` (D2 = C): `a` to the one list of its image strictly ascending by `Obj.lt`, the
    order `Rel.Canon` puts a table's rows in; no list where that image has no such list. -/
abbrev lamDen (T : Den A B) : Den A (.arr B) := fun a ys => ys.Pairwise B.lt ∧ ∀ b, b ∈ ys ↔ T a b

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

/-- A row's meaning at its object variables `σ`, given its relation arguments' meanings. -/
abbrev RowDen (c : RowCode) := (σ : List Obj) → List Sem → Den (c.ty σ).1 (c.ty σ).2

open Classical RowCode in
/-- Every row of `prims` with its meaning, in the order of `rowCodes` (`rowDens_codes`). `setify` is `Λ(∋)`; the
    meanings of `setify` and `asc` have no lemma yet (`rowGaps`). -/
def rowDens : List ((c : RowCode) × RowDen c) :=
  [⟨tau, fun _ _ a Y => Y = [a]⟩,
   ⟨cons, fun _ _ p ys => ys = p.1 :: p.2⟩,
   ⟨mem, fun σ _ (xs : List (σ₁ σ).El) x => x ∈ xs⟩,
   ⟨inl, fun _ _ => Core.Rel.inl⟩,
   ⟨inr, fun _ _ => Core.Rel.inr⟩,
   ⟨map, fun σ => Sem.one (X := σ₁ σ) (Y := σ₂ σ) fun T (xs : List (σ₁ σ).El) (ys : List (σ₂ σ).El) => ys.length = xs.length ∧
      ∀ t (ht : t < xs.length) (ht' : t < ys.length), T (xs[t]'ht) (ys[t]'ht')⟩,
   ⟨filter, fun σ => Sem.one (X := σ₁ σ) (Y := σ₁ σ) fun T xs ys => ys = xs.filter fun x => decide (∃ y, T x y)⟩,
   ⟨takewhile, fun σ => Sem.one (X := σ₁ σ) (Y := σ₁ σ) fun T xs ys =>
      ys = xs.takeWhile fun x => decide (∃ y, T x y)⟩,
   ⟨thinL, fun σ => Sem.one (X := .prod (σ₁ σ) (σ₁ σ)) (Y := .prod (σ₁ σ) (σ₁ σ)) fun T =>
      thinLDen fun a b => decide (∃ c, T (a, b) c)⟩,
   ⟨merge, fun σ => Sem.one (X := .prod (σ₁ σ) (σ₁ σ)) (Y := .prod (σ₁ σ) (σ₁ σ)) fun T p zs =>
      zs = List.merge p.1 p.2 fun a b => decide (∃ c, T (a, b) c)⟩,
   ⟨loop, fun σ => Sem.one (X := .prod (σ₁ σ) (σ₂ σ)) (Y := σ₁ σ) fun T p c => ∃ g : Nat → (σ₁ σ).El, g 0 = p.1 ∧
      (∀ t (ht : t < p.2.length), T (g t, p.2[t]'ht) (g (t + 1))) ∧ c = g p.2.length⟩,
   ⟨uncons, fun _ _ xs p => xs = p.1 :: p.2⟩,
   ⟨length, fun _ _ xs w => w = Int64.ofNat xs.length⟩,
   ⟨sum, fun _ _ (xs : List Int64) (w : Int64) =>
      (∀ t, t ≤ xs.length → -2 ^ 63 < List.sum (List.map Int64.toInt (List.drop t xs)) ∧
        List.sum (List.map Int64.toInt (List.drop t xs)) < 2 ^ 63) ∧ (∀ x ∈ xs, x ≠ Alg.nul) ∧
        w = xs.foldr (· + ·) 0⟩,
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
   ⟨distinct, fun _ _ xs ys => ys = xs.eraseDups⟩,
   ⟨asc, fun σ _ xs ys => ys.Perm xs ∧ ys.Pairwise fun x y => ¬ (σ₁ σ).lt y x⟩,
   ⟨tic, fun _ _ p zss => zss = (List.range (p.2.length + 1)).map fun j => (p.1 :: p.2).take (j + 1)⟩]

/-- The codes of `rowDens` are `rowCodes`, so `Prim.den` finds the code `Prim.run` runs. -/
theorem rowDens_codes : rowDens.map (·.1) = rowCodes := rfl

/-- The row `r`'s meaning at `A ⟶ B` given its relation arguments' meanings, found as `Prim.run` finds its code;
    `𝟘` where it has none there. -/
def Prim.den (r : Prim) (A B : Obj) (ss : List Sem) : Den A B :=
  match rowDens.find? (·.1.sym == r.sym), r.objs A B with
  | some ⟨c, D⟩, some σ => if h : (c.ty σ).1 = A ∧ (c.ty σ).2 = B then h.1 ▸ h.2 ▸ D σ ss else 𝟘
  | _, _ => 𝟘

/-! ### `⟦−⟧` -/

mutual
/-- `⟦t⟧ρ`, one clause per constructor. A row and its arguments (`prim` under `arg`s) mean the row's meaning of
    its arguments' (`Tm.argDen`). `𝟘` at `call` (a `let` node), whose meaning is not settled yet. -/
noncomputable def Tm.den : Val → {A B : Obj} → {d : Bool} → Tm A B d → Den A B
  | _, _, _, _, .val R => rep R
  | _, _, _, _, .uni U => rep (Alg.idU U)
  | _, _, _, _, .zero => 𝟘
  | _, _, _, _, .id => 𝟙 _
  | ρ, _, _, _, .top V => Core.Rel.top ≫ V.den ρ
  | _, _, _, _, .outl => graph Prod.fst
  | _, _, _, _, .outr => graph Prod.snd
  | ρ, _, _, _, .comp R S => R.den ρ ≫ S.den ρ
  | ρ, _, _, _, .conv R => (R.den ρ)°
  | ρ, _, _, _, .meet R S => R.den ρ ∩ S.den ρ
  | ρ, _, _, _, .join R S => R.den ρ ∪ S.den ρ
  | ρ, _, _, _, .diff R S => diffDen (R.den ρ) (S.den ρ)
  | ρ, _, _, _, .dom R => 𝟙 _ ∩ R.den ρ ≫ (R.den ρ)°
  | ρ, _, _, _, .ran R => 𝟙 _ ∩ (R.den ρ)° ≫ (R.den ρ)°°
  | ρ, _, _, _, .ldiv R S U V => ldivDen (R.den ρ) (S.den ρ) (U.den ρ) (V.den ρ)
  | ρ, _, _, _, .rdiv R S U V => rdivDen (R.den ρ) (S.den ρ) (U.den ρ) (V.den ρ)
  | ρ, _, _, _, .pair R S => rpair (R.den ρ) (S.den ρ)
  | ρ, _, _, _, .prod R S => rprodMap (R.den ρ) (S.den ρ)
  | ρ, _, _, _, .junc R S => Core.Rel.junc (R.den ρ) (S.den ρ)
  | ρ, _, _, _, .juncD R S => Core.Rel.junc (R.den ρ) (S.den ρ)
  | ρ, _, _, _, .lam R => lamDen (R.den ρ)
  | ρ, _, _, _, .E R => EDen (R.den ρ)
  | ρ, _, _, _, .est Q => estDen (Q.den ρ)
  | ρ, _, _, _, .thin Q => thinDen (Q.den ρ)
  | _, _, _, _, .nil => nilDen
  | _, A, B, _, .prim r => Prim.den r A B []
  | _, _, _, _, .atPos k => atDen k
  | ρ, _, _, _, .own R => R.den ρ
  | ρ, _, _, _, .succ U => succDen (U.den ρ)
  | ρ, _, _, _, .arith k U => arithDen k (U.den ρ)
  | ρ, _, _, _, .leq U => leqDen (U.den ρ)
  | ρ, _, _, _, .lt U => ltDen (U.den ρ)
  | ρ, _, _, _, .fold e S => foldDen (e.den ρ) (S.den ρ)
  | _, _, _, _, .share _ R => R.den Val.empty
  | ρ, _, _, _, .foldI e S => foldIDen (e.den ρ) (S.den ρ)
  | ρ, _, _, _, .flat R => flatDen (R.den ρ)
  | ρ, A, B, _, .var k => ρ k A B
  | _, _, _, _, .call .. => 𝟘
  | ρ, _, _, _, .arg f x => f.argDen ρ [⟨_, _, x.den ρ⟩]
  -- the rounds start at `⟦S⟧` and meet each with it (`Gen.nu`), so `S` bounds the greatest fixed point
  | ρ, _, _, _, .nu k S b => Core.Rel.nu fun X => S.den ρ ∩ b.den (ρ.bind k X)
  | ρ, _, _, _, .mu k _ _ b => Core.Rel.mu fun X => b.den (ρ.bind k X)
  | ρ, _, _, _, .hylo k _ _ b => Core.Rel.mu fun X => b.den (ρ.bind k X)

/-- The spine `f` of a row given the meanings `ss` of its later arguments: the row's meaning of all of them, in
    the order `compile` passes their codes; `𝟘` where `f` is not a row under `arg`s. `share` and `own` are seen
    through, as `Tm.gen` passes their part's row on. -/
noncomputable def Tm.argDen : Val → {A B : Obj} → {d : Bool} → Tm A B d → List Sem → Den A B
  | _, A, B, _, .prim r, ss => Prim.den r A B ss
  | ρ, _, _, _, .arg f x, ss => f.argDen ρ (⟨_, _, x.den ρ⟩ :: ss)
  | _, _, _, _, .share _ R, ss => R.argDen Val.empty ss
  | ρ, _, _, _, .own R, ss => R.argDen ρ ss
  | _, _, _, _, _, _ => 𝟘
end

/-- `⟦t⟧`, and `t`'s meaning as a row's spine, read `ρ` only at the variables free in `t`. -/
theorem Tm.den_congr : ∀ {A B : Obj} {d : Bool} (t : Tm A B d) (ρ ρ' : Val), (∀ i ∈ t.fv, ρ i = ρ' i) →
    t.den ρ = t.den ρ' ∧ ∀ ss, t.argDen ρ ss = t.argDen ρ' ss := by
  intro A B d t
  induction t with
  | var k => intro ρ ρ' h; exact ⟨by simp only [Tm.den, h k (by simp [Tm.fv])], fun _ => rfl⟩
  | top V ih => intro ρ ρ' h; exact ⟨by simp only [Tm.den, (ih ρ ρ' fun i hi => h i (by simp [Tm.fv, hi])).1], fun _ => rfl⟩
  | comp R S ihR ihS | meet R S ihR ihS | join R S ihR ihS | diff R S ihR ihS | pair R S ihR ihS
  | prod R S ihR ihS | junc R S ihR ihS | juncD R S ihR ihS | fold R S ihR ihS | foldI R S ihR ihS =>
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
  | conv R ih | dom R ih | ran R ih | est R ih | succ R ih | arith _ R ih | leq R ih | lt R ih
  | flat R ih | lam R ih | E R ih | thin R ih =>
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
  | mu k _ _ b ih | hylo k _ _ b _ ih =>
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

theorem Tm.den_lift (ρ : Val) (s : Tm A B false) : ∀ d, (s.lift d).den ρ = s.den ρ
  | false => rfl
  | true => Core.Rel.id_comp _

/-- No term of `σ` is a row's spine: a term put for a variable heading `arg`s keeps that spine's meaning `𝟘`, as
    the variable's own is (`compile` too runs a row only under a `prim` head). -/
def Tm.Sub.Plain (σ : Tm.Sub) : Prop := ∀ e ∈ σ, ∀ ρ ss, e.2.2.2.argDen ρ ss = 𝟘

theorem Tm.Sub.argDen_get {ρ : Val} {ss : List Sem} (i : Nat) {A' B' : Obj} (d : Bool) :
    ∀ σ : Tm.Sub, σ.Plain → (σ.get i d : Tm A' B' d).argDen ρ ss = 𝟘
  | [], _ => rfl
  | (k, ⟨A, B, s⟩) :: σ, hσ => by
    simp only [Sub.get]
    split
    · split
      · rename_i h; obtain ⟨rfl, rfl⟩ := h
        cases d
        · exact hσ _ List.mem_cons_self ρ ss
        · rfl
      · cases d <;> rfl
    · exact argDen_get i d σ fun e he => hσ e (List.mem_cons_of_mem _ he)

theorem Tm.Sub.den_get (ρ : Val) (i : Nat) {A' B' : Obj} (d : Bool) :
    ∀ σ : Tm.Sub, (σ.get i d : Tm A' B' d).den ρ = σ.den ρ i A' B'
  | [] => rfl
  | (k, ⟨A, B, s⟩) :: σ => by
    by_cases e : i = k
    · subst e
      by_cases h : A = A' ∧ B = B'
      · obtain ⟨rfl, rfl⟩ := h; simp [Sub.get, Sub.den, Val.bind, den_lift]
      · simp [Sub.get, Sub.den, Val.bind, h, den_lift, Tm.den]
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
theorem Tm.Sub.den_rename {A B A' B' : Obj} {d : Bool} (b : Tm A' B' d) (σ : Tm.Sub) (ρ : Val) (k : Nat)
    (X : Den A B) : b.den (Sub.den (ρ.bind (fresh (b.fv ++ σ.fvs)) X)
      ((k, ⟨A, B, .var (fresh (b.fv ++ σ.fvs))⟩) :: σ)) = b.den ((σ.den ρ).bind k X) := by
  refine (b.den_congr _ _ fun i hi => ?_).1
  have hv : (Tm.var (fresh (b.fv ++ σ.fvs)) : Tm A B false).den (ρ.bind (fresh (b.fv ++ σ.fvs)) X) = X := by
    simp [Tm.den, Val.bind]
  simp only [Sub.den, hv]
  by_cases e : i = k
  · subst e; exact Val.bind_same
  · rw [Val.bind_ne e, Val.bind_ne e]
    exact den_bind σ (fun j hj => Nat.ne_of_lt (lt_fresh (List.mem_append_right _ hj))) i
      (Nat.ne_of_lt (lt_fresh (List.mem_append_left _ hi)))

/-- **Substitution lemma**: `⟦t σ⟧ρ = ⟦t⟧(⟦σ⟧ρ)`. -/
theorem Tm.den_subst : ∀ {A B : Obj} {d : Bool} (t : Tm A B d) (σ : Tm.Sub), σ.Plain → ∀ ρ : Val,
    (t.subst σ).den ρ = t.den (σ.den ρ) ∧ ∀ ss, (t.subst σ).argDen ρ ss = t.argDen (σ.den ρ) ss := by
  intro A B d t
  induction t with
  | var i => intro σ hσ ρ; exact ⟨Sub.den_get ρ i _ σ, fun _ => Sub.argDen_get i _ σ hσ⟩
  | nu k S b ihS ih =>
    intro σ hσ ρ; refine ⟨?_, fun _ => rfl⟩; simp only [Tm.subst, Tm.den, (ihS σ hσ ρ).1]
    congr 1; funext X; congr 1
    refine (ih _ (fun e he ρ ss => ?_) _).1.trans (Sub.den_rename b σ ρ k X)
    rcases List.mem_cons.1 he with rfl | he
    · rfl
    · exact hσ e he ρ ss
  | mu k _ _ b ih | hylo k _ _ b _ ih =>
    intro σ hσ ρ; refine ⟨?_, fun _ => rfl⟩; simp only [Tm.subst, Tm.den]; congr 1; funext X
    refine (ih _ (fun e he ρ ss => ?_) _).1.trans (Sub.den_rename b σ ρ k X)
    rcases List.mem_cons.1 he with rfl | he
    · rfl
    · exact hσ e he ρ ss
  | arg f x ihf ihx =>
    intro σ hσ ρ
    have hx := (ihx σ hσ ρ).1
    have hf := (ihf σ hσ ρ).2
    exact ⟨by simp only [Tm.subst, Tm.den, hx, hf], fun _ => by simp only [Tm.subst, Tm.argDen, hx, hf]⟩
  | own R ih =>
    intro σ hσ ρ
    have e := ih σ hσ ρ
    exact ⟨by simp only [Tm.subst, Tm.den, e.1], fun _ => by simp only [Tm.subst, Tm.argDen, e.2]⟩
  | _ => intro σ hσ ρ; exact ⟨by simp only [Tm.subst, Tm.den, *], fun _ => rfl⟩

/-! ### Monotonicity -/

/-- `ρ'` grows `ρ` at the variable `k` and agrees with it at every other. -/
def Val.Grow (k : Nat) (ρ ρ' : Val) : Prop := (∀ A B, ρ k A B ⊑ ρ' k A B) ∧ ∀ i, i ≠ k → ρ i = ρ' i

/-- `X ⊑ Y` read with the sign `s`: `true` keeps it, `false` turns it round. -/
def sle (s : Bool) {A B : Obj} (X Y : Den A B) : Prop := cond s (X ⊑ Y) (Y ⊑ X)

theorem Val.Grow.congr {k : Nat} {ρ ρ' : Val} (g : Grow k ρ ρ') {A B : Obj} {d : Bool} {t : Tm A B d}
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

theorem prod_le {X X' : Den A B} {Y Y' : Den C D} (hX : X ⊑ X') (hY : Y ⊑ Y') : rprodMap X Y ⊑ rprodMap X' Y' :=
  le_iff.2 fun _ _ h => ⟨le_iff.1 hX _ _ h.1, le_iff.1 hY _ _ h.2⟩

theorem junc_le {X X' : Den A C} {Y Y' : Den B C} (hX : X ⊑ X') (hY : Y ⊑ Y') :
    Core.Rel.junc X Y ⊑ Core.Rel.junc X' Y' :=
  le_iff.2 fun x c h => by
    simp only [Core.Rel.junc, union_apply, comp_apply] at h ⊢
    exact h.imp (fun ⟨b, h1, h2⟩ => ⟨b, h1, le_iff.1 hX _ _ h2⟩) (fun ⟨b, h1, h2⟩ => ⟨b, h1, le_iff.1 hY _ _ h2⟩)

-- `est` drops `b` only where `Q` fails, so a larger `Q` drops fewer
theorem est_le {Q Q' : Den (.prod B B) (.prod B B)} (hQ : Q ⊑ Q') : estDen Q ⊑ estDen Q' :=
  le_iff.2 fun _ _ h => ⟨h.1, fun ⟨c, hc, hne, hq⟩ => h.2 ⟨c, hc, hne, fun h' => hq (le_iff.1 hQ _ _ h')⟩⟩

theorem succ_le {U U' : Den .long .long} (hU : U ⊑ U') : succDen U ⊑ succDen U' :=
  le_iff.2 fun _ _ ⟨⟨v, hv⟩, e, v', hv'⟩ => ⟨⟨v, le_iff.1 hU _ _ hv⟩, e, v', le_iff.1 hU _ _ hv'⟩

theorem leq_le {U U' : Den .long .long} (hU : U ⊑ U') : leqDen U ⊑ leqDen U' :=
  le_iff.2 fun _ _ ⟨⟨v, hv⟩, ⟨v', hv'⟩, e⟩ => ⟨⟨v, le_iff.1 hU _ _ hv⟩, ⟨v', le_iff.1 hU _ _ hv'⟩, e⟩

theorem lt_le {U U' : Den .long .long} (hU : U ⊑ U') : ltDen U ⊑ ltDen U' :=
  le_iff.2 fun _ _ ⟨⟨v, hv⟩, ⟨v', hv'⟩, e⟩ => ⟨⟨v, le_iff.1 hU _ _ hv⟩, ⟨v', le_iff.1 hU _ _ hv'⟩, e⟩

theorem arith_le {k : UInt8} {U U' : Den .long .long} (hU : U ⊑ U') : arithDen k U ⊑ arithDen k U' :=
  comp_le' (inter_le' (Core.Rel.le_refl _) (comp_le' (comp_le' (Core.Rel.le_refl _) hU)
      (conv_le' (comp_le' (Core.Rel.le_refl _) hU))))
    (comp_le' (inter_le' (Core.Rel.le_refl _) (comp_le' (comp_le' (Core.Rel.le_refl _) hU)
      (conv_le' (comp_le' (Core.Rel.le_refl _) hU)))) (comp_le' (Core.Rel.le_refl _) hU))

theorem fold_le {e e' : Den B B} {S S' : Den (.prod A B) B} (he : e ⊑ e') (hS : S ⊑ S') :
    foldDen e S ⊑ foldDen e' S' :=
  le_iff.2 fun _ _ ⟨ys, hy, ⟨a, ha⟩, hs, hw⟩ =>
    ⟨ys, hy, ⟨a, le_iff.1 he _ _ ha⟩, fun t ht => le_iff.1 hS _ _ (hs t ht), hw⟩

theorem foldI_le {e e' : Den C (.prod B B)} {S S' : Den (.prod A (.prod C B)) (.prod C B)} (he : e ⊑ e')
    (hS : S ⊑ S') : foldIDen e S ⊑ foldIDen e' S' :=
  le_iff.2 fun _ _ h => le_iff.1 (fold_le (le_iff.2 fun _ _ h => le_iff.1 he _ _ h)
    (le_iff.2 fun _ _ h => le_iff.1 hS _ _ h)) _ _ h

theorem flat_le {T T' : Den C (.prod A B)} (hT : T ⊑ T') : flatDen T ⊑ flatDen T' :=
  le_iff.2 fun _ _ h => le_iff.1 hT _ _ h

end ops

theorem Sem.one_mono {X Y A B X' Y' : Obj} {D : Den X Y → Den A B} (hD : ∀ {T T'}, T ⊑ T' → D T ⊑ D T')
    {T T' : Den X' Y'} (h : T ⊑ T') : Sem.one D [⟨X', Y', T⟩] ⊑ Sem.one D [⟨X', Y', T'⟩] := by
  simp only [Sem.one]
  by_cases hh : X' = X ∧ Y' = Y
  · simp only [dif_pos hh]; obtain ⟨rfl, rfl⟩ := hh; exact hD h
  · simp only [dif_neg hh]; exact Core.Rel.le_refl _

/-- Every row its `prims` entry marks `mono` reads its one relation argument monotonically: the fact `Tm.pol`'s
    rule for a row applied to an argument rests on. -/
theorem rowDens_mono : ∀ e ∈ rowDens, (Prim.find? e.1.sym).any (·.mono) = true →
    ∀ σ {X Y : Obj} {T T' : Den X Y}, T ⊑ T' → e.2 σ [⟨X, Y, T⟩] ⊑ e.2 σ [⟨X, Y, T'⟩] := by
  intro e he hm σ X Y T T' h
  simp only [rowDens, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first | exact Core.Rel.le_refl _ | exact absurd hm (by decide) | skip
  · dsimp only; refine Sem.one_mono (fun hT => le_iff.2 fun _ _ hm => ?_) h
    exact ⟨hm.1, fun t ht ht' => le_iff.1 hT _ _ (hm.2 t ht ht')⟩
  · dsimp only; refine Sem.one_mono (fun hT => le_iff.2 fun _ _ hm => ?_) h
    obtain ⟨g, h0, hs, hc⟩ := hm
    exact ⟨g, h0, fun t ht => le_iff.1 hT _ _ (hs t ht), hc⟩

theorem Prim.den_mono {r : Prim} (hr : (Prim.find? r.sym).any (·.mono) = true) {A B X Y : Obj} {T T' : Den X Y}
    (h : T ⊑ T') : Prim.den r A B [⟨X, Y, T⟩] ⊑ Prim.den r A B [⟨X, Y, T'⟩] := by
  unfold Prim.den
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

/-- **Polarity**: where `t.pol s k`, growing the variable `k` moves `⟦t⟧` with the sign `s`. `den_mono` and
    `den_anti` are its two signs, one induction. -/
theorem Tm.den_pol (k : Nat) : ∀ {A B : Obj} {d : Bool} (t : Tm A B d) (s : Bool) (ρ ρ' : Val),
    t.pol s k = true → Val.Grow k ρ ρ' → sle s (t.den ρ) (t.den ρ') := by
  intro A B d t
  induction t with
  | var j =>
    intro s ρ ρ' hp g
    simp only [Tm.den]
    by_cases e : j = k
    · subst e; simp only [Tm.pol, beq_self_eq_true, if_true] at hp; subst hp; exact g.1 _ _
    · rw [g.2 j e]; exact sle.refl _
  | top V ih => intro s ρ ρ' hp g; exact sle.map1 (comp_le' (Core.Rel.le_refl _)) (ih s ρ ρ' hp g)
  | conv R ih => intro s ρ ρ' hp g; exact sle.map1 conv_le' (ih s ρ ρ' hp g)
  | own R ih => intro s ρ ρ' hp g; exact ih s ρ ρ' hp g
  | dom R ih =>
    intro s ρ ρ' hp g
    exact sle.map1 (fun h => inter_le' (Core.Rel.le_refl _) (comp_le' h (conv_le' h))) (ih s ρ ρ' hp g)
  | ran R ih =>
    intro s ρ ρ' hp g
    exact sle.map1 (fun h => inter_le' (Core.Rel.le_refl _) (comp_le' (conv_le' h) (conv_le' (conv_le' h)))) (ih s ρ ρ' hp g)
  | comp R S ihR ihS =>
    intro s ρ ρ' hp g; simp only [Tm.pol, Bool.and_eq_true] at hp
    exact sle.map2 comp_le' (ihR s ρ ρ' hp.1 g) (ihS s ρ ρ' hp.2 g)
  | meet R S ihR ihS =>
    intro s ρ ρ' hp g; simp only [Tm.pol, Bool.and_eq_true] at hp
    exact sle.map2 inter_le' (ihR s ρ ρ' hp.1 g) (ihS s ρ ρ' hp.2 g)
  | join R S ihR ihS =>
    intro s ρ ρ' hp g; simp only [Tm.pol, Bool.and_eq_true] at hp
    exact sle.map2 union_le' (ihR s ρ ρ' hp.1 g) (ihS s ρ ρ' hp.2 g)
  | pair R S ihR ihS =>
    intro s ρ ρ' hp g; simp only [Tm.pol, Bool.and_eq_true] at hp
    exact sle.map2 pair_le (ihR s ρ ρ' hp.1 g) (ihS s ρ ρ' hp.2 g)
  | prod R S ihR ihS =>
    intro s ρ ρ' hp g; simp only [Tm.pol, Bool.and_eq_true] at hp
    exact sle.map2 prod_le (ihR s ρ ρ' hp.1 g) (ihS s ρ ρ' hp.2 g)
  | junc R S ihR ihS | juncD R S ihR ihS =>
    intro s ρ ρ' hp g; simp only [Tm.pol, Bool.and_eq_true] at hp
    exact sle.map2 junc_le (ihR s ρ ρ' hp.1 g) (ihS s ρ ρ' hp.2 g)
  | diff R S ihR ihS =>
    intro s ρ ρ' hp g; simp only [Tm.pol, Bool.and_eq_true] at hp
    exact sle.anti2 diff_le (ihR s ρ ρ' hp.1 g) (ihS (!s) ρ ρ' hp.2 g)
  | ldiv R S U V _ ihS ihU ihV =>
    intro s ρ ρ' hp g; simp only [Tm.pol, Bool.and_eq_true, Bool.not_eq_true'] at hp
    simp only [Tm.den, g.congr hp.1.1.1]
    exact sle.map3 ldiv_le (ihS s ρ ρ' hp.1.1.2 g) (ihU s ρ ρ' hp.1.2 g) (ihV s ρ ρ' hp.2 g)
  | rdiv R S U V ihR _ ihU ihV =>
    intro s ρ ρ' hp g; simp only [Tm.pol, Bool.and_eq_true, Bool.not_eq_true'] at hp
    simp only [Tm.den, g.congr hp.1.1.2]
    exact sle.map3 rdiv_le (ihR s ρ ρ' hp.1.1.1 g) (ihU s ρ ρ' hp.1.2 g) (ihV s ρ ρ' hp.2 g)
  | nu j S b ihS ih =>
    intro s ρ ρ' hp g
    simp only [Tm.pol, Bool.and_eq_true] at hp
    simp only [Tm.den]
    have hS := ihS s ρ ρ' hp.1 g
    by_cases e : j = k
    · subst e
      have hb : ∀ {A' B' : Obj} (X : Den A' B'), ρ.bind j X = ρ'.bind j X := fun X => funext fun i => by
        by_cases e' : i = j
        · subst e'; exact Val.bind_same
        · rw [Val.bind_ne e', Val.bind_ne e', g.2 i e']
      simp only [hb]; exact sle.gfp fun X => sle.map2 (f := fun X Y => X ∩ Y) inter_le' hS (sle.refl _)
    · simp only [Bool.or_eq_true, beq_iff_eq, e, false_or] at hp
      exact sle.gfp fun X => sle.map2 (f := fun X Y => X ∩ Y) inter_le' hS (ih s _ _ hp.2 (g.bind e X))
  | mu j _ _ b ih | hylo j _ _ b _ ih =>
    intro s ρ ρ' hp g
    simp only [Tm.den]
    by_cases e : j = k
    · subst e
      have hb : ∀ {A' B' : Obj} (X : Den A' B'), ρ.bind j X = ρ'.bind j X := fun X => funext fun i => by
        by_cases e' : i = j
        · subst e'; exact Val.bind_same
        · rw [Val.bind_ne e', Val.bind_ne e', g.2 i e']
      simp only [hb]; exact sle.refl _
    · simp only [Tm.pol, Bool.or_eq_true, beq_iff_eq, e, false_or] at hp
      exact sle.lfp fun X => ih s _ _ hp (g.bind e X)
  | est Q ih => intro s ρ ρ' hp g; exact sle.map1 est_le (ih s ρ ρ' hp g)
  | succ U ih => intro s ρ ρ' hp g; exact sle.map1 succ_le (ih s ρ ρ' hp g)
  | arith _ U ih => intro s ρ ρ' hp g; exact sle.map1 arith_le (ih s ρ ρ' hp g)
  | leq U ih => intro s ρ ρ' hp g; exact sle.map1 leq_le (ih s ρ ρ' hp g)
  | lt U ih => intro s ρ ρ' hp g; exact sle.map1 lt_le (ih s ρ ρ' hp g)
  | flat R ih => intro s ρ ρ' hp g; exact sle.map1 flat_le (ih s ρ ρ' hp g)
  | fold e S ihe ihS =>
    intro s ρ ρ' hp g; simp only [Tm.pol, Bool.and_eq_true] at hp
    exact sle.map2 fold_le (ihe s ρ ρ' hp.1 g) (ihS s ρ ρ' hp.2 g)
  | foldI e S ihe ihS =>
    intro s ρ ρ' hp g; simp only [Tm.pol, Bool.and_eq_true] at hp
    exact sle.map2 foldI_le (ihe s ρ ρ' hp.1 g) (ihS s ρ ρ' hp.2 g)
  | arg f x _ ihx =>
    intro s ρ ρ' hp g
    by_cases hc : (Tm.arg f x).fv.contains k = false
    · exact sle.of_eq (g.congr hc)
    · have hc : k ∈ (Tm.arg f x).fv := by simpa using hc
      cases f with
      | prim r =>
        have hp : (Prim.find? r.sym).any (·.mono) = true ∧ x.pol s k = true := by simpa [Tm.pol, hc] using hp
        exact sle.map1 (f := fun T => Prim.den r _ _ [⟨_, _, T⟩]) (Prim.den_mono hp.1) (ihx s ρ ρ' hp.2 g)
      -- a spine whose demand bit is `d || e` reduces `Tm.pol`'s match only once the two bits are known
      | @meet _ _ d₁ e₁ _ _ | @join _ _ d₁ e₁ _ _ | @diff _ _ d₁ e₁ _ _ | @pair _ _ _ d₁ e₁ _ _ =>
        revert hp; cases d₁ <;> cases e₁ <;> simp [Tm.pol, hc]
      | _ => simp [Tm.pol, hc] at hp
  | _ => intro s ρ ρ' hp g; exact sle.of_eq (g.congr (by first | simpa [Tm.pol] using hp | simp [Tm.fv]))

/-- `⟦t⟧` is monotone in `X` where `X` occurs only positively. -/
theorem Tm.den_mono {A' B' : Obj} {d : Bool} {t : Tm A' B' d} {k : Nat} (h : t.pol true k = true) {ρ : Val}
    {X Y : Den A B} (hXY : X ⊑ Y) : t.den (ρ.bind k X) ⊑ t.den (ρ.bind k Y) :=
  t.den_pol k true _ _ h (Val.Grow.of_le hXY)

/-- `⟦t⟧` is antitone in `X` where `X` occurs only negatively. -/
theorem Tm.den_anti {A' B' : Obj} {d : Bool} {t : Tm A' B' d} {k : Nat} (h : t.pol false k = true) {ρ : Val}
    {X Y : Den A B} (hXY : X ⊑ Y) : t.den (ρ.bind k Y) ⊑ t.den (ρ.bind k X) :=
  t.den_pol k false _ _ h (Val.Grow.of_le hXY)

/-- `μX : φ = φ[μX : φ]` where `X` occurs in `φ` only positively. -/
theorem Tm.den_mu_unfold {A B : Obj} (k : Nat) (what : String) (cap : Nat) (b : Tm A B false)
    (h : b.pol true k = true) (ρ : Val) :
    (Tm.mu k what cap b).den ρ = (b.subst [(k, ⟨A, B, .mu k what cap b⟩)]).den ρ := by
  rw [(b.den_subst _ (fun e he _ _ => by obtain rfl := List.mem_singleton.1 he; rfl) _).1]
  exact (Core.Rel.mu_fix fun _ _ hXY => den_mono h hXY).symm

/-- `νX : S ∩ φ = S ∩ φ[νX : S ∩ φ]` where `X` occurs in `φ` only positively; `S` is outside the binder. -/
theorem Tm.den_nu_unfold {A B : Obj} (k : Nat) (S b : Tm A B false) (h : b.pol true k = true) (ρ : Val) :
    (Tm.nu k S b).den ρ = (Tm.meet S (b.subst [(k, ⟨A, B, .nu k S b⟩)])).den ρ := by
  show _ = S.den ρ ∩ _
  rw [(b.den_subst _ (fun e he _ _ => by obtain rfl := List.mem_singleton.1 he; rfl) _).1]
  exact (Core.Rel.nu_fix fun _ _ hXY => inter_le' (Core.Rel.le_refl _) (den_mono h hXY)).symm

#print axioms Tm.den_pol
#print axioms Core.Rel.mu_fix

end Rel.Lang
