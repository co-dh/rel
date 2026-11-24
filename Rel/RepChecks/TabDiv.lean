import Rel.RepChecks.Canon
import Rel.RepTabDiv

/-! The `#guard` checks of `Rel.RepTabDiv`, kept outside the module: a `#guard` runs compiled code, whose IR a `module` does not export (PLAN perf9e). -/

namespace Rel
open  Rel.Kernel Rel.Verify Enc


section Checks

/-- An operator's answer as a list, `none` on `.error`. -/
private def newL {k v : Obj} (r : Except String (Tab k v)) : Option (List (k.El × v.El)) := r.toOption.map Tab.toList

/-- The answer `r` runs and holds one row per key of `sp`, its cell the elements of `sp`'s cell as a set: an answer's
cell is in `kasc`'s order (`ordCode`), a spec's in its own. -/
private def cellsOk {k v : Obj} [BEq k.El] [BEq v.El] (r : Except String (Tab k (.arr v)))
    (sp : List (k.El × List v.El)) : Bool :=
  let sub (x y : List (k.El × List v.El)) := x.all fun (a, ys) => y.any fun (a', ys') =>
    a == a' && ys.length == ys'.length && ys.all ys'.contains && ys'.all ys.contains
  match r with
  | .ok T => let b := sp.eraseDups; T.toList.length == b.length && sub T.toList b && sub b T.toList
  | .error _ => false

/-- The answer is `.ok` and canonical: `canon` of it lists the same rows in the same order. -/
private def canonOk {k v : Obj} [BEq k.El] [BEq v.El] (r : Except String (Tab k v)) : Bool :=
  match r with
  | .ok T => (T.canon.toOption.map Tab.toList) == some T.toList
  | .error _ => false

/-- `𝟙` on `U`, the universe a `Tm` passes as a coreflexive. -/
private def idT {A : Obj} {n : USize} (U : Vals A n) : Tab A A := ⟨n, U, U⟩

/-- Tables with duplicate rows, negatives, keys of one value each, a value shared by every key, and no rows. -/
private def ts : List (List (Int64 × Int64)) :=
  [[(3, 1), (1, 2), (3, 1), (-1, 2), (1, 2), (2, 7), (-5, -5), (0, 0)],
   [(2, 5), (1, -3), (2, 6), (7, 7), (9, 0), (2, 5), (-5, 4), (0, 0)],
   [(1, 2), (1, 5), (2, 2), (2, 5), (3, 2), (3, 2)], []]

/-- The universe `1 2 5 7 9 -3 2`, a value twice. -/
private def us : List Int64 := [1, 2, 5, 7, 9, -3, 2]
private def U := Alg.col us

/-- `R\S` within the universes `UB`, `UC` (`ldivDen`): `(b, c)` when every `a` with `R a b` has `S a c`, and `b` is a
target of `R` or `b`, `c` lie in the universes. -/
private def ldivSp {A B C : Obj} [BEq A.El] [BEq B.El] [BEq C.El] (R : Tab A B) (S : Tab A C) (UB : Tab B B)
    (UC : Tab C C) : List (B.El × C.El) :=
  let r := R.toList; let s := S.toList; let ub := UB.toList.map (·.1); let uc := UC.toList.map (·.1)
  ((r.map (·.2) ++ ub).flatMap fun b => (s.map (·.2) ++ uc).map (b, ·)).filter fun (b, c) =>
    r.all (fun (a, b') => b' != b || s.contains (a, c)) && (r.any (·.2 == b) || ub.contains b && uc.contains c)

/-- `R/S` within the universes `UA`, `UB` (`rdivDen`): `(x, y)` when every `c` with `S y c` has `R x c`, and `y` is a
source of `S` or `x`, `y` lie in the universes. -/
private def rdivSp {A B C : Obj} [BEq A.El] [BEq B.El] [BEq C.El] (R : Tab A C) (S : Tab B C) (UA : Tab A A)
    (UB : Tab B B) : List (A.El × B.El) :=
  let r := R.toList; let s := S.toList; let ua := UA.toList.map (·.1); let ub := UB.toList.map (·.1)
  ((r.map (·.1) ++ ua).flatMap fun x => (s.map (·.1) ++ ub).map (x, ·)).filter fun (x, y) =>
    s.all (fun (y', c) => y' != y || r.contains (x, c)) && (s.any (·.1 == y) || ua.contains x && ub.contains y)

-- `\` and `/` against `ldivDen`, `rdivDen` on every pair of tables, within `U`; each answer canonical
#guard ts.all fun ps => ts.all fun qs =>
  let R := tab ps; let S := tab qs
  canonOk (R.ldiv S (idT U) (idT U)) && canonOk (R.rdiv S (idT U) (idT U)) &&
  specOk (R.ldiv S (idT U) (idT U)) (ldivSp R S (idT U) (idT U)) &&
  specOk (R.rdiv S (idT U) (idT U)) (rdivSp R S (idT U) (idT U))

#guard newL ((tab [(1, 2), (1, 5), (2, 2), (2, 5), (3, 2)]).ldiv (tab [(1, 7), (2, 7), (2, 8), (3, 7)])
  (idT (Alg.col [2, 5, 6])) (idT (Alg.col [7, 9]))) == some [(2, 7), (5, 7), (6, 7), (6, 9)]

/-- A two-sided operator `f` (`lt`, `leq`, `top`) on the whole universe `U`: both sides `dom U`. -/
private def whole {A : Obj} (f : ∀ {n m : USize}, Vals A n → Vals A m → Except String (Tab A A)) (U : Tab A A) :
    Except String (Tab A A) := do let d ← U.dom; f d.key d.key

/-- `f K L` is canonical and holds the rows of `K ≫ whole f U ≫ L` (`Tab.comp`), as a set. -/
private def sidesOk {A : Obj} [BEq A.El] (f : ∀ {n m : USize}, Vals A n → Vals A m → Except String (Tab A A))
    (U : Tab A A) {n m : USize} (K : Vals A n) (L : Vals A m) : Bool :=
  canonOk (f K L) && ((do (← (idT K).comp (← whole f U)).comp (idT L) : Except String (Tab A A))).toOption.any
    fun T => specOk (f K L) T.toList

-- `<`, `≤` on both sides `dom U` against `ltDen`, `leqDen`, on `U` and on no values
#guard canonOk (whole (Tab.lt .i64) (idT U)) && canonOk (whole (Tab.leq .i64) (idT U)) &&
  specOk (whole (Tab.lt .i64) (idT U)) (us.flatMap fun a => (us.filter (a < ·)).map (a, ·)) &&
  specOk (whole (Tab.leq .i64) (idT U)) (us.flatMap fun a => (us.filter (a ≤ ·)).map (a, ·)) &&
  newL (whole (Tab.lt .i64) (tab [])) == some [] &&
  newL (whole (Tab.leq .i64) (tab [(4, 0), (2, 0)])) == some [(2, 2), (2, 4), (4, 4)]

-- `K ≫ < ≫ L` at `i64` keeps the pair in order (3 < 5) only, not the equal (3, 3) nor the greater (3, 1)
#guard newL (Tab.lt .i64 (Alg.col [3]) (Alg.col [3, 5, 1])) == some [(3, 5)]
#guard newL (Tab.lt .i64 (Alg.col [5, 3]) (Alg.col [3])) == some []
-- `date` is ordered as its stored integer (`ordNum`); sym has no kernel order, its order is `rank`'s (`Elab.symOrd`)
#guard (match Tab.ordOp true .date with | .ok op => op == Op.lt | .error _ => false)
#guard (match Tab.ordOp true .sym with
  | .error e => e == "< on objects of Rel.QAtomicType.sym: no order" | .ok _ => false)

/-- Known sides inside `U`: none, a value twice, and two that differ. -/
private def sides : List ((n : USize) × Vals .long n) :=
  [⟨_, Alg.col []⟩, ⟨_, Alg.col [2, 9, -3, 2]⟩, ⟨_, Alg.col [5, 1, 7]⟩, ⟨_, Alg.col [1, 2, 5, 7, 9, -3]⟩]

/-- An `f64` column of the bits `ws`. -/
private def fcol (ws : List UInt64) : Vals (.atom .f64) ws.length.toUSize := Arr.ofFn .f64 _ (ws.getD · 0)

/-- The `f64` universe `-0.0`, `+0.0`, a NaN, `1.5`, `+inf`. -/
private def FU := fcol [0x8000000000000000, 0, 0x7ff8000000000001, 0x3ff8000000000000, 0x7ff0000000000000]

/-- Known `f64` sides inside `FU`: none, a value twice, two that differ, all of `FU`. -/
private def fsides : List ((n : USize) × Vals (.atom .f64) n) :=
  [⟨_, fcol []⟩, ⟨_, fcol [0x3ff8000000000000, 0x8000000000000000, 0x3ff8000000000000]⟩,
   ⟨_, fcol [0, 0x7ff8000000000001, 0x7ff0000000000000]⟩, ⟨_, FU⟩]

-- `<`, `≤`, `⊤` on the known sides `K`, `L` against `K ≫ (both sides dom U) ≫ L`, every pair of sides, at `i64`
-- and at `f64` (`FU`: `-0.0 = +0.0`, a NaN in no pair of `<` or `≤`)
#guard sides.all fun ⟨_, K⟩ => sides.all fun ⟨_, L⟩ =>
  sidesOk (Tab.lt .i64) (idT U) K L && sidesOk (Tab.leq .i64) (idT U) K L && sidesOk Tab.top (idT U) K L
#guard fsides.all fun ⟨_, K⟩ => fsides.all fun ⟨_, L⟩ =>
  sidesOk Tab.top (idT FU) K L && sidesOk (Tab.lt .f64) (idT FU) K L && sidesOk (Tab.leq .f64) (idT FU) K L

/-- The keys `3 1 4 -1 3`: `3` twice, `4` the key of no row. -/
private def ds : List Int64 := [3, 1, 4, -1, 3]
private def D := Alg.col ds

/-- `Λ(R)` (`lamDen`) on the keys `ks` in demand (`Tm.lam`): each key to the image of `R` at it, each element once. -/
private def lamSp {A B : Obj} [BEq A.El] [BEq B.El] (ks : List A.El) (R : Tab A B) : List (A.El × List B.El) :=
  ks.map fun a => (a, ((R.toList.filter (·.1 == a)).map (·.2)).eraseDups)

-- `Λ` on `D` against `lamDen` on `D`, and `nil`
#guard ts.all fun ps => canonOk (Tab.lam D (tab ps)) && cellsOk (Tab.lam D (tab ps)) (lamSp ds (tab ps))
#guard newL (Tab.lam D (tab [(3, 1), (1, 2), (3, 1), (-1, 2), (1, 2), (3, -7)])) ==
  some [(-1, [2]), (1, [2]), (3, [-7, 1]), (4, [])]
#guard canonOk (Tab.nil (A := .long) (B := .long) D) &&
  newL (Tab.nil (A := .long) (B := .long) D) == some [(-1, []), (1, []), (3, []), (4, [])]

/-- `-0.0`, `+0.0`, NaN with payloads `1` and `2`, `+inf`, `-inf`, `1.5`, `-0.0` again, as `f64` bits. -/
private def f64s : List UInt64 := [0x8000000000000000, 0, 0x7ff8000000000001, 0x7ff8000000000002, 0x7ff0000000000000,
  0xfff0000000000000, 0x3ff8000000000000, 0x8000000000000000]

-- `∋` on cells (empty ones, clamped ones, one cell twice) against `x ∋ a`, and on no cells
#guard [(arrCells, arrPay), (arrCells.take 3, arrPay), ([], arrPay), ([(0, 0, 1), (0, 0, 1)], [])].all fun (cs, ps) =>
  let X := (arrTab cs ps).key
  canonOk (Tab.mem X) && specOk (Tab.mem X) ((Vals.rows X).flatMap fun (x : List Int64) => x.map (x, ·))

-- a float value column (stored-bit equality) and a tuple value column, through `\`, `/` and `Λ`
#guard
  let x := Arr.ofFn .f64 8 (f64s.getD · 0) ⟨by decide, by decide⟩
  let R : Tab .long (.atom .f64) := ⟨8, Alg.col [3, 1, 2, 1, 4, 4, 0, 1], x⟩
  let S : Tab .long .long := tab [(3, 5), (1, 6), (2, 5), (1, 5), (4, 5), (0, 5), (0, 6)]
  let Ux := Arr.ofFn .f64 3 (f64s.getD · 0) ⟨by decide, by decide⟩
  canonOk (R.ldiv S (idT Ux) (idT U)) && specOk (R.ldiv S (idT Ux) (idT U)) (ldivSp R S (idT Ux) (idT U)) &&
  cellsOk (Tab.lam D R) (lamSp ds R)
#guard
  let R : Tab .long (.prod .long .long) := ⟨5, Alg.col [3, 1, 3, 1, 2], (Alg.col [1, 1, 2, 1, 2], Alg.col [5, 6, 5, 6, 5])⟩
  let S : Tab .long .long := tab [(3, 5), (1, 6), (1, 5), (2, 5)]
  let Up : Vals (.prod .long .long) 2 := (Alg.col [9, 9], Alg.col [9, 8])
  canonOk (R.ldiv S (idT Up) (idT U)) && specOk (R.ldiv S (idT Up) (idT U)) (ldivSp R S (idT Up) (idT U)) &&
  cellsOk (Tab.lam D R) (lamSp ds R)

/-! `Tab.nu`, `Tab.mu` (`Rel/Run/Fix.lean`) against fixed points worked by hand. -/

/-- `TestArcs`' body `t ∩ A\(X e)` on `V = {0,1}`, `D = {0,1,2}`: `A = {(1,0)}`, `e = 𝟙(D)`, `t` missing `(1,1)`. -/
private def arcT := tab [(0, 0), (0, 1), (0, 2), (1, 0), (1, 2)]
private def arcA := tab [(1, 0)]
private def arcE := tab [(0, 0), (1, 1), (2, 2)]
private def arcNew (X : Tab .long .long) : Except String (Tab .long .long) := do
  arcT.inter (← arcA.ldiv (← X.comp arcE) (idT (Alg.col [0, 1])) (idT (Alg.col [0, 1, 2])))
/-- `TestArcs`' answer: `(0,1)` drops, since `(1,1)` is not in `t`. -/
private def arcZ : List (Int64 × Int64) := [(0, 0), (0, 2), (1, 0), (1, 2)]

-- ν from `⊤(V,D)`, from its own fixed point, and from no rows
#guard specOk (Tab.nu arcNew (tab [(0, 0), (0, 1), (0, 2), (1, 0), (1, 1), (1, 2)])) arcZ &&
  specOk (Tab.nu arcNew (tab arcZ)) arcZ && specOk (Tab.nu arcNew (tab [])) []

/-- Transitive closure `μX : E ∪ X E` of the edges `E`. -/
private def tcNew (E X : Tab .long .long) : Except String (Tab .long .long) := do E.union (← X.comp E)

-- the cycle `2 → 3 → 4 → 2` entered from `1`, closed to `{1,2,3,4} × {2,3,4}`: 12 pairs at round 3, seen fixed at
-- round 4, so `cap = 4` fails and `cap = 5` passes
#guard let E := tab [(1, 2), (2, 3), (3, 4), (4, 2)]
  (newL (Tab.mu "tc" 4 (tcNew E))).isNone &&
    [5, 9].all fun cap => specOk (Tab.mu "tc" cap (tcNew E)) ([1, 2, 3, 4].flatMap fun a => [2, 3, 4].map (a, ·))
-- the cap reached is reported with the μ's text and its cap
#guard let E := tab [(1, 2), (2, 3), (3, 4), (4, 2)]
  match Tab.mu "tc" 4 (tcNew E) with | .error e => e == Tab.capMsg "tc" 4 | .ok _ => false
-- an already-closed `E` and no edges
#guard [tab [(1, 2), (2, 2), (1, 1)], tab []].all fun E => specOk (Tab.mu "tc" 3 (tcNew E)) E.toList
-- an error of the body is the loop's error
#guard match Tab.nu (fun _ => throw "body") (tab arcZ) with | .error e => e == "body" | .ok _ => false
#guard match Tab.mu "tc" 9 (fun (_ : Tab .long .long) => throw "body") with | .error e => e == "body" | .ok _ => false

/-! ### `Rel/Run/Power.lean` against the old layer -/

/-- Arrays of longs: `arrCells` (empty cells, one cell twice, unsorted), a prefix of it, no cells, and
empty cells over no payload. -/
private def arrXs : List (Tab (.arr .long) .long) :=
  [arrTab arrCells arrPay, arrTab (arrCells.take 3) arrPay, arrTab [] arrPay, arrTab [(0, 0, 1), (0, 0, 1)] []]

/-- Arrays of pairs over the payload `(1,5) (2,5) (1,5) (3,6)`: `[(1,5)]` from two ranges, the empty cell, a cell
to the end, one cell twice. -/
private def pairXs : Vals (.arr (.prod .long .long)) 6 :=
  (arrOn [(0, 1, 0), (2, 3, 0), (0, 4, 0), (1, 1, 0), (2, 4, 0), (0, 4, 0)]
    ((Alg.col [1, 2, 1, 3], Alg.col [5, 5, 5, 6]) : Vals (.prod .long .long) 4)).key

/-- The test of pairs of `Q`: the pairs `D` composed with `𝟙` on `Q`'s rows, so `(b, c)` to itself iff `Q b c`. -/
private def pairsIn {B : Obj} (Q : Tab B B) (D : Tab (.prod B B) (.prod B B)) :
    Except String (Tab (.prod B B) (.prod B B)) := do D.comp (← Tab.idU (Q.key, Q.val))

/-- `est(Q)` (`estDen`, `Q` read through `pairsIn`) on the arrays `xs`: `b` of `x` when every other `c` of `x` has
`Q b c`. -/
private def estSp {B : Obj} [BEq B.El] (Q : Tab B B) (xs : List (List B.El)) : List (List B.El × B.El) :=
  xs.flatMap fun x => (x.filter fun b => x.all fun c => c == b || Q.toList.contains (b, c)).map (x, ·)

/-- `front(Q)` (`frontDen`): each `x` to its `c` that no `b` of `x` beats strictly, each once. -/
private def frontSp {B : Obj} [BEq B.El] (Q : Tab B B) (xs : List (List B.El)) : List (List B.El × List B.El) :=
  xs.map fun x =>
    (x, (x.filter fun c => !x.any fun b => Q.toList.contains (b, c) && !Q.toList.contains (c, b)).eraseDups)

/-- Orders on longs: `≤` on `1 5 9`, a relation that is not one (`5` before `1`, `9` only to itself), and none. -/
private def ordLs : List (Tab .long .long) :=
  [tab [(1, 1), (1, 5), (1, 9), (5, 5), (5, 9), (9, 9), (1, 5)], tab [(5, 1), (9, 9)], tab []]

/-- Lexicographic `≤` on the pairs `(1,5) (2,5) (3,6)`. -/
private def ordPs : Tab (.prod .long .long) (.prod .long .long) :=
  ⟨6, (Alg.col [1, 1, 1, 2, 2, 3], Alg.col [5, 5, 5, 5, 5, 6]), (Alg.col [1, 2, 3, 2, 3, 3], Alg.col [5, 5, 6, 5, 6, 6])⟩

-- `setify`, `length` against `Λ(∋)` and the length on arrays of longs and of pairs (`at`: `rel_program` guards, Lang/Test/Lists)
#guard arrXs.all fun T => let X := T.key; let xs : List (List Int64) := Vals.rows X
  canonOk (Tab.setify X) && cellsOk (Tab.setify X) (xs.map fun x => (x, x.eraseDups)) &&
  canonOk (Tab.length X) && specOk (Tab.length X) (xs.map fun x => (x, Int64.ofNat x.length))
#guard let xs : List (List (Int64 × Int64)) := Vals.rows pairXs
  canonOk (Tab.setify pairXs) && cellsOk (Tab.setify pairXs) (xs.map fun x => (x, x.eraseDups)) &&
  canonOk (Tab.length pairXs) && specOk (Tab.length pairXs) (xs.map fun x => (x, Int64.ofNat x.length))

-- `τ` against `a ↦ [a]` on longs (a value twice), on no values, and on pairs
#guard [tab [(3, 0), (1, 0), (3, 0), (-2, 0)], tab []].all fun T => let X := T.key
  canonOk (Tab.tau X) && specOk (Tab.tau X) ((Vals.rows X).map fun a => (a, [a]))
#guard let X : Vals (.prod .long .long) 4 := (Alg.col [1, 2, 1, 3], Alg.col [5, 5, 5, 6])
  canonOk (Tab.tau X) && specOk (Tab.tau X) ((Vals.rows X).map fun a => (a, [a]))

-- `est`, `front` against `estDen`, `frontDen`, each order, on arrays of longs and of pairs
#guard arrXs.all fun T => let X := T.key; ordLs.all fun Q =>
  canonOk (Tab.est (pairsIn Q) X) && specOk (Tab.est (pairsIn Q) X) (estSp Q (Vals.rows X)) &&
  canonOk (Tab.front (pairsIn Q) X) && cellsOk (Tab.front (pairsIn Q) X) (frontSp Q (Vals.rows X))
#guard canonOk (Tab.est (pairsIn ordPs) pairXs) &&
  specOk (Tab.est (pairsIn ordPs) pairXs) (estSp ordPs (Vals.rows pairXs)) &&
  canonOk (Tab.front (pairsIn ordPs) pairXs) &&
  cellsOk (Tab.front (pairsIn ordPs) pairXs) (frontSp ordPs (Vals.rows pairXs))

/-- `arrCells`-style fixtures for the list rows (`Rel/Run/List.lean`): `arrCells` (empty, clamped and repeated cells,
so repeated rows), a prefix of it, no cells, empty cells over no payload, and cells over `2^63 - 1` and the null whose
sums overflow or meet the null. -/
private def listFix : List (List (Int64 × Int64 × Int64) × List Int64) :=
  [(arrCells, arrPay), (arrCells.take 3, arrPay), ([], arrPay), ([(0, 0, 1), (0, 0, 1)], []),
   ([(0, 2, 0), (1, 3, 0), (2, 3, 0), (0, 3, 0), (3, 4, 1)], [9223372036854775807, 1, -1, -9223372036854775807 - 1])]

/-- The `rowDens` rows `snoc`, `cat`, `cons`, `zip` after `P`; `uncons`, `unsnoc`, `uncat` and `sum` on the arrays
`xs`, each array to every decomposition of it. -/
private def snocSp {K B : Obj} (P : Tab K (.prod (.arr B) B)) : List (K.El × List B.El) :=
  P.toList.map fun (k, p) => (k, (p.1 : List B.El) ++ [p.2])
private def catSp {K B : Obj} (P : Tab K (.prod (.arr B) (.arr B))) : List (K.El × List B.El) :=
  P.toList.map fun (k, p) => (k, (p.1 : List B.El) ++ p.2)
private def consSp {K B : Obj} (P : Tab K (.prod B (.arr B))) : List (K.El × List B.El) :=
  P.toList.map fun (k, p) => (k, p.1 :: (p.2 : List B.El))
private def zipSp {K A B : Obj} (P : Tab K (.prod (.arr A) (.arr B))) : List (K.El × List (A.El × B.El)) :=
  P.toList.map fun (k, p) => (k, (p.1 : List A.El).zip p.2)
private def unconsSp {B : Obj} (xs : List (List B.El)) : List (List B.El × B.El × List B.El) :=
  xs.filterMap fun x => match x with | b :: r => some (x, b, r) | [] => none
private def unsnocSp {B : Obj} (xs : List (List B.El)) : List (List B.El × List B.El × B.El) :=
  xs.filterMap fun x => x.getLast?.map fun b => (x, x.dropLast, b)
private def uncatSp {B : Obj} (xs : List (List B.El)) : List (List B.El × List B.El × List B.El) :=
  xs.flatMap fun x => (List.range (x.length + 1)).map fun k => (x, x.take k, x.drop k)
private def sumSp (xs : List (List Int64)) : List (List Int64 × Int64) :=
  xs.filterMap fun x => if x.all (· != Alg.nul) && (List.range (x.length + 1)).all (fun t =>
    let s := ((x.take t).map Int64.toInt).sum; decide (-2 ^ 63 < s ∧ s < 2 ^ 63)) then some (x, x.foldl (· + ·) 0)
    else none

-- `snoc cat cons zip sum uncons unsnoc uncat` against their `rowDens`, on long and pair elements, as sets (`canon` of
-- the answer)
#guard listFix.all fun (cs, ps) =>
  let A := arrTab cs ps
  let X := A.key; let x := A.val
  let Y := (arrOn cs (Alg.col (ps.map (· * 10 + 3)))).key
  let Z := (arrOn cs ((Alg.col ps, List.length_map _ ▸ Alg.col (ps.map (· - 1))) :
    Vals (.prod .long .long) ps.length.toUSize)).key
  let P₁ : Tab .long (.prod (.arr .long) .long) := ⟨_, x, (X, x)⟩
  let P₂ : Tab .long (.prod (.arr .long) (.arr .long)) := ⟨_, x, (X, Y)⟩
  let P₃ : Tab .long (.prod .long (.arr .long)) := ⟨_, x, (x, Y)⟩
  let P₄ : Tab .long (.prod (.arr .long) (.arr (.prod .long .long))) := ⟨_, x, (Y, Z)⟩
  let Q₁ : Tab .long (.prod (.arr (.prod .long .long)) (.prod .long .long)) := ⟨_, x, (Z, (x, x))⟩
  let Q₂ : Tab .long (.prod (.arr (.prod .long .long)) (.arr (.prod .long .long))) := ⟨_, x, (Z, Z)⟩
  let Q₃ : Tab .long (.prod (.prod .long .long) (.arr (.prod .long .long))) := ⟨_, x, ((x, x), Z)⟩
  let ok {A B : Obj} [BEq A.El] [BEq B.El] (r : Except String (Tab A B)) (sp : List (A.El × B.El)) :=
    specOk (r >>= Tab.canon) sp
  canonOk (Tab.snoc P₁) && canonOk (Tab.uncat X) &&
  ok (Tab.snoc P₁) (snocSp P₁) && ok (Tab.cat P₂) (catSp P₂) && ok (Tab.cons P₃) (consSp P₃) &&
  ok (Tab.zip P₄) (zipSp P₄) && ok (Tab.sum X) (sumSp (Vals.rows X)) &&
  ok (Tab.uncons X) (unconsSp (Vals.rows X)) && ok (Tab.unsnoc X) (unsnocSp (Vals.rows X)) &&
  ok (Tab.uncat X) (uncatSp (Vals.rows X)) &&
  ok (Tab.snoc Q₁) (snocSp Q₁) && ok (Tab.cat Q₂) (catSp Q₂) && ok (Tab.cons Q₃) (consSp Q₃) &&
  ok (Tab.uncons Z) (unconsSp (Vals.rows Z)) && ok (Tab.unsnoc Z) (unsnocSp (Vals.rows Z)) &&
  ok (Tab.uncat Z) (uncatSp (Vals.rows Z))

-- `sum` drops `[2^63 - 1, 1]` (a suffix sum past `2^63`) and `[null]`, keeps `[2^63 - 1, 1, -1]` (every suffix sum
-- inside), as `rowDens` states
#guard specOk (Tab.sum (arrTab (listFix.getD 4 ([], [])).1 (listFix.getD 4 ([], [])).2).key)
  [([1, -1], 0), ([-1], -1)]

/-- One cell `[0, 1)` over `2^63` positions (`pos`, nothing stored): its row is `[0]`. -/
private def bigCell : Except String (Vals (.arr .long) 1) := do
  pure ⟨9223372036854775808, ← colArr .add 1 (← colConst 1 0) (← colConst 1 0),
    ← colArr .add 1 (← colConst 1 1) (← colConst 1 0),
    (⟨.pos, by simp [Enc.WF], rfl⟩ : Arr .i64 9223372036854775808)⟩

-- `ValsB.pack` past `2^63` elements is the error: `cellSpan` would read the size as the signed word `-2^63`, every
-- width `0`, and answer a payload of no rows
#guard match bigCell, bigCell >>= ValsB.pack 2 with
  | .ok _, .error e => e == "pack: 1 cells over 9223372036854775808 elements past 2^63"
  | _, _ => false

end Checks

end Rel
