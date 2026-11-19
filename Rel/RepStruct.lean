import Rel.Run.Struct
import Rel.RepTabComp
import Rel.Run.CRelRelDef
import Rel.Core.Rel

/-! The laws of the structural operators (`Rel/Run/Struct.lean`), each with its `Tm` constructor's denotation
(`Tm.den`, `Rel/Lang/Den.lean`) as the right-hand side, and their checks against the old operators. -/

namespace Rel
open Rel.Ext Rel.Kernel Rel.Verify Ext.Enc
open scoped Rel.Core.Rel

/-- **CROSS's index columns**: `T = n · m` rows, row `t` reading `t / m` and `t % m`. -/
theorem crossIx_ok {n m T : USize} {iR iS : Enc} (h : crossIx n m = .ok (T, iR, iS)) :
    T.toNat = n.toNat * m.toNat ∧ ∀ t < T.toNat,
      ((raw .i64 T iR)[t]?.getD 0).toNat = t / m.toNat ∧ ((raw .i64 T iS)[t]?.getD 0).toNat = t % m.toNat := by
  unfold crossIx at h
  by_cases hb : 2 ^ 63 ≤ n.toNat * m.toNat + m.toNat ∨ USize.size ≤ n.toNat * m.toNat
  · simp [hb, bind, Except.bind] at h
  simp only [hb, if_false, bind, Except.bind, pure, Except.pure] at h
  split at h; · cases h
  rename_i c hc
  split at h; · cases h
  rename_i d hd
  split at h; · cases h
  rename_i e he
  simp only [Except.ok.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl, rfl⟩ := h
  have hT : (n.toNat * m.toNat).toUSize.toNat = n.toNat * m.toNat := USize.toNat_ofNat_of_lt' (by omega)
  refine ⟨hT, fun t ht => ?_⟩
  rw [hT] at ht
  have hm0 : 0 < m.toNat := Nat.pos_of_ne_zero fun h0 => by rw [h0, Nat.mul_zero] at ht; omega
  have hmU : m.toUInt64 = m.toNat.toUInt64 := UInt64.toNat_inj.mp (by simp)
  have hc' : (raw .i64 (n.toNat * m.toNat).toUSize c)[t]?.getD 0 = m.toNat.toUInt64 := by
    rw [colConst_raw hc, Array.getElem?_replicate, if_pos (by rw [hT]; exact ht), Option.getD_some, hmU]
  have hp : (raw .i64 (n.toNat * m.toNat).toUSize (.pos : Enc))[t]?.getD 0 = t.toUInt64 := raw_pos_word (by omega)
  have e1 := (colMap_raw hd).2.2.2 t (by omega)
  have e2 := (colMap_raw he).2.2.2 t (by omega)
  rw [hp, hc', eval_div_nat (by omega) (by omega) hm0, Except.ok.injEq] at e1
  rw [hp, hc', eval_mod_nat (by omega) (by omega) hm0, Except.ok.injEq] at e2
  rw [← e1, ← e2, toNat_toUInt64 (by have := Nat.div_le_self t m.toNat; omega),
    toNat_toUInt64 (by have := Nat.mod_lt t hm0; omega)]
  exact ⟨rfl, rfl⟩

/-- **CROSS holds every pair of rows**: a row of the answer is a row of `x` beside a row of `y`, and each such pair
is a row. -/
theorem Vals.cross_rows {A B : Obj} {n m : USize} {x : Vals A n} {y : Vals B m}
    {r : (T : USize) × Vals A T × Vals B T} (h : Vals.cross x y = .ok r) (a : A.El) (b : B.El) :
    (∃ t, Vals.row r.2.1 t = a ∧ Vals.row r.2.2 t = b) ↔ (∃ i, Vals.row x i = a) ∧ ∃ j, Vals.row y j = b := by
  unfold Vals.cross at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  split at h; · cases h
  rename_i c hc
  obtain ⟨T, iR, iS⟩ := c
  split at h; · cases h
  rename_i gx hx
  split at h; · cases h
  rename_i gy hy
  cases h
  obtain ⟨hT, hw⟩ := crossIx_ok hc
  constructor
  · rintro ⟨t, ha, hb⟩
    obtain ⟨i, -, hi⟩ := Vals.gather_row x hx t
    obtain ⟨j, -, hj⟩ := Vals.gather_row y hy t
    exact ⟨⟨i, hi.symm.trans ha⟩, ⟨j, hj.symm.trans hb⟩⟩
  · rintro ⟨⟨i, rfl⟩, ⟨j, rfl⟩⟩
    have hm0 : 0 < m.toNat := by have := j.2; omega
    have hle := Nat.mul_le_mul_left m.toNat (show i.1 + 1 ≤ n.toNat by have := i.2; omega)
    have ht : m.toNat * i.1 + j.1 < T.toNat := by
      rw [hT, Nat.mul_comm n.toNat m.toNat]; rw [Nat.mul_add, Nat.mul_one] at hle; have := j.2; omega
    obtain ⟨i', e1, hi⟩ := Vals.gather_row x hx ⟨_, ht⟩
    obtain ⟨j', e2, hj⟩ := Vals.gather_row y hy ⟨_, ht⟩
    rw [(hw _ ht).1, Nat.mul_add_div hm0, Nat.div_eq_of_lt j.2, Nat.add_zero] at e1
    rw [(hw _ ht).2, Nat.mul_add_mod, Nat.mod_eq_of_lt j.2] at e2
    exact ⟨⟨_, ht⟩, by rw [hi, Fin.ext e1], by rw [hj, Fin.ext e2]⟩

namespace Tab
variable {A B C D I : Obj}

/-- **`Tab.zero` denotes `𝟘`** (`Tm.den` at `zero`). -/
theorem zero_holds {T : Tab A B} (h : (Tab.zero : Except String (Tab A B)) = .ok T) (a : A.El) (b : B.El) :
    T.Holds a b ↔ False := by
  unfold Tab.zero at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  split at h; · cases h
  split at h; · cases h
  cases h
  exact ⟨fun ⟨i, _⟩ => absurd i.2 (by simp), False.elim⟩

/-- **`Tab.idU X` denotes `𝟙` on the values of `X`** (`Tm.den` at `id`, `uni`: `idU X ≫ 𝟙`). -/
theorem idU_holds {n : USize} {X : Vals A n} {T : Tab A A} (h : Tab.idU X = .ok T) (a b : A.El) :
    T.Holds a b ↔ a = b ∧ ∃ i, X.row i = a := by
  rw [dom_holds h]
  exact ⟨fun ⟨e, _, i, h1, _⟩ => ⟨e, i, h1⟩, fun ⟨e, i, h1⟩ => ⟨e, _, i, h1, rfl⟩⟩

/-- **`Tab.top X V` denotes `⊤ ≫ V` on the values of `X`** (`Tm.den` at `top`: `idU X ≫ ⊤ ≫ ⟦V⟧`). -/
theorem top_holds {n : USize} {X : Vals A n} {V : Tab B B} {T : Tab A B} (h : Tab.top X V = .ok T) (a : A.El)
    (b : B.El) : T.Holds a b ↔ (∃ i, X.row i = a) ∧ (Core.Rel.top ≫ V.Holds) a b := by
  unfold Tab.top at h
  simp only [bind, Except.bind] at h
  split at h; · cases h
  rename_i r hr
  obtain ⟨T', x, y⟩ := r
  rw [canon_holds h]
  refine (Vals.cross_rows hr a b).trans (and_congr_right fun _ => ⟨fun ⟨j, hj⟩ => ⟨_, trivial, j, rfl, hj⟩, fun ⟨_, _, j, _, hj⟩ => ⟨j, hj⟩⟩)

/-- **`Tab.outl X` denotes `π₁` on the pairs `X`** (`Tm.den` at `outl`: `idU X ≫ graph Prod.fst`). -/
theorem outl_holds {n : USize} {X : Vals (.prod A B) n} {T : Tab (.prod A B) A} (h : Tab.outl X = .ok T)
    (p : (Obj.prod A B).El) (a : A.El) : T.Holds p a ↔ (∃ i, X.row i = p) ∧ Core.Rel.graph Prod.fst p a := by
  rw [canon_holds h]
  exact ⟨fun ⟨i, h1, h2⟩ => ⟨⟨i, h1⟩, by subst h1 h2; rfl⟩, fun ⟨⟨i, h1⟩, h2⟩ => ⟨i, h1, by subst h1 h2; rfl⟩⟩

/-- **`Tab.outr X` denotes `π₂` on the pairs `X`** (`Tm.den` at `outr`: `idU X ≫ graph Prod.snd`). -/
theorem outr_holds {n : USize} {X : Vals (.prod A B) n} {T : Tab (.prod A B) B} (h : Tab.outr X = .ok T)
    (p : (Obj.prod A B).El) (b : B.El) : T.Holds p b ↔ (∃ i, X.row i = p) ∧ Core.Rel.graph Prod.snd p b := by
  rw [canon_holds h]
  exact ⟨fun ⟨i, h1, h2⟩ => ⟨⟨i, h1⟩, by subst h1 h2; rfl⟩, fun ⟨⟨i, h1⟩, h2⟩ => ⟨i, h1, by subst h1 h2; rfl⟩⟩

/-- **`R.pair S` denotes `⟨R, S⟩`** (`Tm.den` at `pair`: `rpair`). -/
theorem pair_holds {R : Tab A B} {S : Tab A C} {T : Tab A (.prod B C)} (h : R.pair S = .ok T) (a : A.El)
    (q : (Obj.prod B C).El) : T.Holds a q ↔ Core.Rel.rpair R.Holds S.Holds a q := by
  unfold Tab.pair at h
  cases hc : comp (⟨R.n, (R.key, R.val), R.key⟩ : Tab (.prod A B) A) S with
  | error s => simp [hc, Functor.map, Except.map] at h
  | ok U =>
    simp only [hc, Functor.map, Except.map, Except.ok.injEq] at h
    subst h
    obtain ⟨b, c⟩ := q
    have e := comp_holds hc (a, b) c
    simp only [Tab.Holds, Core.Rel.rpair, Vals.row, Prod.mk.injEq] at e ⊢
    rw [show (∃ i, U.key.1.row i = a ∧ U.key.2.row i = b ∧ U.val.row i = c) ↔
      ∃ i, (U.key.1.row i = a ∧ U.key.2.row i = b) ∧ U.val.row i = c from by simp only [and_assoc], e]
    exact ⟨fun ⟨_, ⟨i, ⟨h1, h2⟩, h3⟩, hS⟩ => ⟨⟨i, h1, h2⟩, by subst h3; rwa [h1] at hS⟩,
      fun ⟨⟨i, h1, h2⟩, hS⟩ => ⟨a, ⟨i, ⟨h1, h2⟩, h1⟩, hS⟩⟩

/-- **`R.prod S` denotes `R × S`** (`Tm.den` at `prod`: `rprodMap`). -/
theorem prod_holds {R : Tab A B} {S : Tab C D} {T : Tab (.prod A C) (.prod B D)} (h : R.prod S = .ok T)
    (p : (Obj.prod A C).El) (q : (Obj.prod B D).El) : T.Holds p q ↔ Core.Rel.rprodMap R.Holds S.Holds p q := by
  unfold Tab.prod at h
  simp only [bind, Except.bind] at h
  split at h; · cases h
  rename_i r hr
  obtain ⟨T', x, y⟩ := r
  rw [canon_holds h]
  obtain ⟨a, c⟩ := p; obtain ⟨b, d⟩ := q
  have e := Vals.cross_rows hr (a, b) (c, d)
  simp only [Tab.Holds, Core.Rel.rprodMap, Vals.row, Prod.mk.injEq] at e ⊢
  rw [← e]
  exact ⟨fun ⟨t, ⟨h1, h2⟩, h3, h4⟩ => ⟨t, ⟨h1, h3⟩, h2, h4⟩, fun ⟨t, ⟨h1, h3⟩, h2, h4⟩ => ⟨t, ⟨h1, h2⟩, h3, h4⟩⟩

/-- **`Tab.flat X R` denotes `Rᴵ` on the pairs `X`** (`Tm.den` at `flat`: `idU X ≫ flatDen ⟦R⟧`,
`flatDen T x b = T x.1 (x.2, b)`). -/
theorem flat_holds {n : USize} {X : Vals (.prod I A) n} {R : Tab I (.prod A B)} {T : Tab (.prod I A) B}
    (h : Tab.flat X R = .ok T) (p : (Obj.prod I A).El) (b : B.El) :
    T.Holds p b ↔ (∃ i, X.row i = p) ∧ R.Holds p.1 (p.2, b) := by
  unfold Tab.flat at h
  simp only [bind, Except.bind] at h
  split at h; · cases h
  rename_i U hU
  rw [comp_holds h]
  constructor
  · rintro ⟨p', hI, t, h1, h3⟩
    obtain ⟨rfl, hx⟩ := (idU_holds hU _ _).1 hI
    exact ⟨hx, t, by subst h1; rfl, by subst h1 h3; rfl⟩
  · rintro ⟨hx, t, h1, h2⟩
    exact ⟨p, (idU_holds hU _ _).2 ⟨rfl, hx⟩, t, Prod.ext h1 (congrArg Prod.fst h2), congrArg Prod.snd h2⟩

end Tab

/-! ## Checks on `foR` tables -/

section Checks

/-- Two lists hold the same elements: the old layer orders a float NaN first, `kasc` by `ordCode`. -/
private def setEq {α : Type} [BEq α] (a b : List α) : Bool := a.all b.contains && b.all a.contains

/-- The answer `r` runs, holds no row twice, and holds the rows `sp` (as a set). -/
private def specOk {A B : Obj} [BEq A.El] [BEq B.El] (r : Except String (Tab A B)) (sp : List (A.El × B.El)) : Bool :=
  match r with
  | .ok T => T.toList.eraseDups.length == T.toList.length && setEq T.toList sp
  | .error _ => false

/-- The answer `r` runs and holds the rows of the old table `o` (as a set), where `o` ran within capacity. -/
private def oldOk {A B : Obj} [BEq A.El] [BEq B.El] (r : Except String (Tab A B)) (o : Option (Tab A B)) : Bool :=
  match r, o with
  | .ok T, some U => setEq T.toList U.toList
  | _, _ => false

/-- The `i64` column of the integers `ws`, `foR` (`Arr.ofFn`). -/
private def col (ws : List Int64) : Arr .i64 ws.length.toUSize := Arr.ofFn .i64 _ fun i => (ws.getD i.1 0).toUInt64

/-- The table of the pairs `ps` as given, unsorted, both columns `col`. -/
private def tabW (ps : List (Int64 × Int64)) : Tab .long .long :=
  ⟨ps.length.toUSize, List.length_map _ ▸ col (ps.map (·.1)), List.length_map _ ▸ col (ps.map (·.2))⟩

/-- `-0.0`, `+0.0`, NaN with payloads `1` and `2`, `+inf`, `-inf`, `1.5`, `-0.0` again, as `f64` bits. -/
private def f64s : List UInt64 := [0x8000000000000000, 0, 0x7ff8000000000001, 0x7ff8000000000002, 0x7ff0000000000000,
  0xfff0000000000000, 0x3ff8000000000000, 0x8000000000000000]

/-- Integer tables: duplicate rows, negatives, one row, none. -/
private def ints : List (List (Int64 × Int64)) :=
  [[(3, 1), (1, 2), (3, 1), (-1, 2), (1, 2), (2, 7)], [(2, 5), (1, -3), (2, 6), (3, 3), (2, 5)], [(4, 8)], []]

/-- A float value column with a duplicate row (`-0.0` at key `3` twice). -/
private def F : Tab .long (.atom .f64) := ⟨8, col [3, 1, 2, 1, 4, 4, 0, 3], Arr.ofFn .f64 8 (f64s.getD · 0)⟩
/-- A tuple value column with duplicate rows. -/
private def P : Tab .long (.prod .long .long) := ⟨5, col [3, 1, 3, 1, 3], (col [1, 1, 1, 2, 1], col [5, 6, 5, 6, 5])⟩

/-- The canonical old table, where `canonC` ran within capacity. -/
private def oldC {A B : Obj} (T : Tab A B) : Option (Tab A B) := let c := Alg.canonC T; if c.2 then some c.1 else none

-- `𝟘` at an atom, a float, a tuple, an `arr` and a `sum` side
#guard specOk (Tab.zero : Except String (Tab .long (.atom .f64))) [] &&
  specOk (Tab.zero : Except String (Tab (.prod .long .long) (.arr .long))) [] &&
  specOk (Tab.zero : Except String (Tab (.sum .long .long) .long)) [] && (Alg.zero : Tab .long .long).toList.isEmpty

-- `𝟙` on the values `X`: duplicates, a float, a tuple, none
#guard ints.all fun ps => let R := tabW ps
  oldOk (Tab.idU R.key) (oldC (Alg.idU R.key)) && specOk (Tab.idU R.key) (R.key.toList.map fun a => (a, a))
#guard oldOk (Tab.idU F.val) (oldC (Alg.idU F.val)) && oldOk (Tab.idU P.val) (oldC (Alg.idU P.val))

/-- The rows of a side, in position order. -/
private def rows {A : Obj} {n : USize} (X : Vals A n) : List A.El := List.ofFn (Vals.row X)

/-- `top X V` against the old `topC` (on `V`'s values) and against `X × V.val` as a set. -/
private def topOk {A B : Obj} [BEq A.El] [BEq B.El] {n : USize} (X : Vals A n) (V : Tab B B) : Bool :=
  oldOk (Tab.top X V) (let c := Alg.topC X V.val; if c.2 then oldC c.1 else none) &&
    specOk (Tab.top X V) ((rows X).flatMap fun a => (rows V.val).map fun b => (a, b))

-- `⊤`: integers (an empty side on either end), a float, a tuple
#guard ints.all fun ps => ints.all fun qs => topOk (tabW ps).key (tabW qs)
#guard topOk P.val (⟨F.n, F.val, F.val⟩ : Tab (.atom .f64) (.atom .f64)) &&
  topOk F.val (⟨P.n, P.val, P.val⟩ : Tab (.prod .long .long) (.prod .long .long))

/-- `outl X`, `outr X` against the old `outl`, `outr` of `idU X` and against the projections as sets. -/
private def outOk {A B : Obj} [BEq A.El] [BEq B.El] {n : USize} (X : Vals (.prod A B) n) : Bool :=
  oldOk (Tab.outl X) (oldC (Alg.outl (Alg.idU X))) && oldOk (Tab.outr X) (oldC (Alg.outr (Alg.idU X))) &&
    specOk (Tab.outl X) ((rows X).map fun p => (p, p.1)) && specOk (Tab.outr X) ((rows X).map fun p => (p, p.2))

-- `π₁`, `π₂`: integer pairs with duplicates, none, a float component, a tuple component
#guard ints.all fun ps => let R := tabW ps; outOk (A := .long) (B := .long) (R.key, R.val)
#guard outOk (A := .long) (B := .atom .f64) (F.key, F.val) && outOk (A := .long) (B := .prod .long .long) (P.key, P.val)

/-- `pair` and `prod` against the old `CRel.pair`, `CRel.prod` and against their denotations as sets. -/
private def pairOk {A B C : Obj} [BEq A.El] [BEq B.El] [BEq C.El] (R : Tab A B) (S : Tab A C) : Bool :=
  oldOk (R.pair S) (CRel.pair (some R) (some S)) &&
    specOk (R.pair S) (R.toList.flatMap fun (a, b) => S.toList.filterMap fun (a', c) =>
      if a == a' then some (a, (b, c)) else none)
private def prodOk {A B C D : Obj} [BEq A.El] [BEq B.El] [BEq C.El] [BEq D.El] (R : Tab A B) (S : Tab C D) : Bool :=
  oldOk (R.prod S) (CRel.prod (some R) (some S)) &&
    specOk (R.prod S) (R.toList.flatMap fun (a, b) => S.toList.map fun (c, d) => ((a, c), (b, d)))

-- `⟨R, S⟩` and `R × S`: integers (duplicates, an empty side, no common key), a float and a tuple value
#guard ints.all fun ps => ints.all fun qs => pairOk (tabW ps) (tabW qs) && prodOk (tabW ps) (tabW qs)
#guard pairOk F P && pairOk P F && prodOk F P && prodOk P (tabW (ints.getD 0 []))

/-- `flat X R` against `Rᴵ` on `X` as a set: `((i, a), b)` for `(i, a)` of `X` and `(i, (a, b))` of `R`. -/
private def flatOk {I A B : Obj} [BEq I.El] [BEq A.El] [BEq B.El] {n : USize} (X : Vals (.prod I A) n)
    (R : Tab I (.prod A B)) : Bool :=
  specOk (Tab.flat X R) ((rows X).flatMap fun p => R.toList.filterMap fun (i, a, b) =>
    if p.1 == i && p.2 == a then some (p, b) else none)

-- `Rᴵ`: a tuple family on integer pairs (duplicates, a pair `R` misses), on none, and a float source
#guard flatOk (I := .long) (A := .long) (col [3, 1, 3, 3, 9], col [1, 2, 1, 5, 1]) P &&
  flatOk (I := .long) (A := .long) (col [], col []) P &&
  flatOk (I := .long) (A := .atom .f64) (F.key, F.val) (⟨F.n, F.key, (F.val, F.key)⟩ : Tab .long (.prod (.atom .f64) .long))

end Checks

end Rel
