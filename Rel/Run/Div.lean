import Rel.Run.Arith
import Rel.Run.Struct

/-! The `Tm` constructors `ldiv`, `rdiv`, `lam`, `E`, `nil`, `lt`, `leq` (`Rel/Run/Lang/Tm.lean`) as operators on `Tab`
over the five kernels (PLAN 6.14 W3), on the encoded columns as they are, as `Rel/Run/Comp.lean`. Each operator's
right-hand side is its constructor's denotation (`Rel/Lang/Den.lean`: `ldivDen`, `rdivDen`, `lamDen`, `EDen`,
`nilDen`, `ltDen`, `leqDen`). A denotation total on a whole type (`lamDen`, `EDen`, `nilDen`) is run on the keys in
demand `D`, as the compiled term reads it (`Tm.lam`'s doc). Their laws are in `Rel/RepTabDiv.lean`. -/

namespace Rel
open Rel.Ext Rel.Kernel Rel.Verify

namespace Tab
variable {A B C : Obj}

/-- **`∋` on the arrays `X`** (the step `EDen` composes, `(fun xs a => a ∈ xs) ≫ T`): each cell to each of its
elements. A cell is the slice `[lo, hi)` of the payload (`Vals.WF`, which every table keeps: `0 ≤ lo ≤ hi ≤ m`), so
its width `hi - lo` is never negative; EXPAND of the widths, the key the cell `X[G]`, the value the payload at
`lo[G] + u`; then `canon`. -/
def mem {n : USize} (X : Vals (.arr B) n) : Except String (Tab (.arr B) B) :=
  match X with
  | ⟨m, lo, hi, f⟩ => do
    -- `.sub`, `.add` read the widths and positions signed: every one is below `n * m + n + m`
    if 2 ^ 63 ≤ n.toNat * m.toNat + n.toNat + m.toNat then throw s!"mem: {n} cells × {m} elements past 2^63"
    let (T, G, u) ← expand n (← colMap .sub n hi.enc lo.enc)
    let ix ← colMap .add T (← kgather T G n lo.enc) u
    Tab.canon ⟨T, ← Vals.gather (A := .arr B) T G ⟨m, lo, hi, f⟩, ← Vals.gather T ix f⟩

/-- **`nil` on the keys `D`** (`nilDen`): each to the empty cell, `lo = hi = 0` over a payload of no rows; then
`canon`. -/
def nil {n : USize} (D : Vals A n) : Except String (Tab A (.arr B)) := do
  let z ← Arr.zeros .i64 n
  Tab.canon ⟨n, D, ⟨0, z, z, ← Vals.none B⟩⟩

/-- **`Λ(r)` on the keys `D`, `r` canonical** (`Tab.Canonical`; `lamDen`): each `a` of `D` to the cell of its values
in `r`, ascending and each once, `[]` where `r` has none. One GROUP over the keys of `D` then `r` (`Vals.concat`): `kasc` being stable, a
group's sorted rows are its `D` rows (`cD`, input row below `n`), then its `r` rows, which `canon` put in ascending
value order. The cell of group `G` is the sorted rows `[f + cD, f + c)` of the payload `r.val` gathered in sorted
order (a `D` row reads `r`'s row `0`, inside no cell); the groups with `0 < cD` are kept (`whereCol`), keyed by their
first row, a row of `D`. Then `canon`. An `r` of no rows is `nil D`: a cell's bounds index the payload beside it,
and over no rows the only cell is `[0, 0)`, where `[f + cD, f + c)` would point past it. -/
def lamOf {n : USize} (D : Vals A n) (r : Tab A B) : Except String (Tab A (.arr B)) :=
  if r.n.toNat = 0 then nil D else do
  let (N, sh) ← catPlan n r.n
  -- `.lt`, `.sub`, `.max` read positions and counts signed: every one is below `N`
  if 2 ^ 63 ≤ N.toNat then throw s!"lam: {N} rows past 2^63"
  let es ← Vals.cols (← Vals.concat N sh D r.key)
  let (vs, p) ← kasc N es
  let (k, g, f) ← kseen N ((es.map (·.1)).zip vs)
  let K := k.toUSize
  let nc ← colConst N n.toUInt64
  let cD ← kscatter .add N g (← colMap .lt N p nc) K 0
  let lo ← colArr .add K f cD
  let hi ← colArr .add K f (← kscatter .add N g (← colConst N 1) K 0)
  let (M, sel) ← whereCol K (← colMap .lt K (← colConst K 0) cD)
  let iD ← kgather M (← kgather M sel K f) N p
  let pay ← Vals.gather N (← colMap .max N (← colMap .sub N p nc) (← colConst N 0)) r.val
  Tab.canon ⟨M, ← Vals.gather M iD D, ⟨N, ← Arr.gather M sel lo, ← Arr.gather M sel hi, pay⟩⟩

/-- **`Λ(R)` on the keys `D`**: `lamOf` of `canon R`; a caller whose `R` is `Tab.Canonical` already calls `lamOf`. -/
def lam {n : USize} (D : Vals A n) (R : Tab A B) : Except String (Tab A (.arr B)) := R.canon >>= lamOf D

/-- **`r \ s` within `UB`, `UC`, `r`, `s` canonical** (`Tab.Canonical`; `ldivDen`), by counting: `b` of `ran r` to `c`
where `#{a | r a b ∧ s a c} = #{a | r a b}`, no complement (`doc/rel-architecture.zh.typ`, `R\S`): `Q = r° ≫ ⟨𝟙, s⟩`
(`r`, `s` canonical, so `Q`'s rows `(b, (a, c))` are distinct and hold each `a` once; `compOne`, not the blocked
`comp`: with no duplicate to remove, the expansion is `Q` itself and blocks would not lower the peak); GROUP over `(b, c)` and its
row count `cnt` (`groupFold .add`, a segmented `kscan`); the count `d` of `R`'s rows of `b`, read at each group's first row by CODE over
`r.val ++ Q.key` (the run of `r` rows of each `b` group, `groupFold .add` of `p < r.n`, each input row's group by
`kscatter .last` through `p`); the groups with `cnt = d` (`whereCol`). The vacuous part is `(ran UB − ran R) × ran UC`,
and the two are met by `∪`. -/
def ldivOf (r : Tab A B) (s : Tab A C) (UB : Tab B B) (UC : Tab C C) : Except String (Tab B C) := do
  let Q ← (Tab.mk r.n r.val r.key).compOne (Tab.mk s.n s.key (s.key, s.val) : Tab A (.prod A C))
  let x : Vals (.prod B C) Q.n := (Q.key, (Q.val : Vals A Q.n × Vals C Q.n).2)
  let es ← Vals.cols x
  let (vs, p) ← kasc Q.n es
  let (k, g, f) ← kseen Q.n ((es.map (·.1)).zip vs)
  let K := k.toUSize
  let cnt ← groupFold .add Q.n g f K 0 (← colConst Q.n 1)
  let (N, sh) ← catPlan r.n Q.n
  -- `.lt` reads positions signed: every one is below `N`
  if 2 ^ 63 ≤ N.toNat then throw s!"ldiv: {N} rows past 2^63"
  let bs ← Vals.cols (← Vals.concat N sh r.val Q.key)
  let (bv, bp) ← kasc N bs
  let (bk, bg, bf) ← kseen N ((bs.map (·.1)).zip bv)
  let cR ← groupFold .add N bg bf bk.toUSize 0 (← colMap .lt N bp (← colConst N r.n.toUInt64))
  let code ← kscatter .last N bp bg N 0
  let q ← kgather K f Q.n p
  let d ← kgather K (← kgather K (← colMap .add K q (← colConst K r.n.toUInt64)) N code) bk.toUSize cR
  let (M, sel) ← whereCol K (← colMap .eq K cnt d)
  let ix ← kgather M sel K q
  let P : Tab B C := ⟨M, ← Vals.gather M ix Q.key, ← Vals.gather M ix (Q.val : Vals A Q.n × Vals C Q.n).2⟩
  P.union (← cross (← (← UB.ran).diff (← r.ran)).key (← UC.ran).key)

/-- **`R \ S` within `UB`, `UC`**: `ldivOf` of `canon R`, `canon S`; a caller whose `R`, `S` are `Tab.Canonical`
calls `ldivOf`. -/
def ldiv (R : Tab A B) (S : Tab A C) (UB : Tab B B) (UC : Tab C C) : Except String (Tab B C) := do
  ldivOf (← R.canon) (← S.canon) UB UC

/-- **`R / S` within `UA`, `UB`** (`rdivDen`): `(S° \ R°)°` within `UB`, `UA`; the two converses are `canon` answers
(`Tab.conv`), so `ldivOf`. -/
def rdiv (R : Tab A C) (S : Tab B C) (UA : Tab A A) (UB : Tab B B) : Except String (Tab A B) := do
  (← ldivOf (← S.conv) (← R.conv) UB UA).conv

/-- The order `Op` of the atom `t` (`ltAt`, `leAt`): `<` (`s`) or `≤` on the `wideCol` words, IEEE's at a float
atom, signed at every other ordered atom (`ordNum`); the error naming an atom with no order. -/
def ordOp (s : Bool) (t : QAtomicType) : Except String Op :=
  match t with
  | .f32 | .f64 => pure (if s then .flt else .fle)
  | t => if t.ordNum.isSome then pure (if s then .lt else .le)
    else throw s!"{if s then "<" else "≤"} on objects of {repr t}: no order"

/-- `T ∩ op`: the rows of `T` whose words pass `op`, `keep` of `colMap op` of its two columns as the atom `t`'s
order reads them (`wideCol`), one element-wise test per row. -/
def cmpPairs (op : Op) {t : QAtomicType} (T : Tab (.atom t) (.atom t)) : Except String (Tab (.atom t) (.atom t)) := do
  T.keep (← colMap op T.n (← wideCol t T.n T.key.enc) (← wideCol t T.n T.val.enc))

/-- `K ≫ op ≫ L`: the pairs `(a, c)` of `K × L` whose words pass `op`: CROSS of the two known sides, then
`cmpPairs`. A side not known is `dom U`, exact since the denotation (`ltDen`, `leqDen`) lies inside `U`
(`doc/rel-architecture.zh.typ` §0). -/
def cmpOn (op : Op) {t : QAtomicType} {n m : USize} (K : Vals (.atom t) n) (L : Vals (.atom t) m) :
    Except String (Tab (.atom t) (.atom t)) := do
  cmpPairs op (← cross K L)

/-- **`K ≫ < ≫ L`** at the atom `t` (`ltDen t` on `dom U` when `K = L = dom U`). -/
def lt (t : QAtomicType) {n m : USize} (K : Vals (.atom t) n) (L : Vals (.atom t) m) :
    Except String (Tab (.atom t) (.atom t)) := do cmpOn (← ordOp true t) K L

/-- **`K ≫ ≤ ≫ L`** at the atom `t` (`leqDen t` on `dom U` when `K = L = dom U`). -/
def leq (t : QAtomicType) {n m : USize} (K : Vals (.atom t) n) (L : Vals (.atom t) m) :
    Except String (Tab (.atom t) (.atom t)) := do cmpOn (← ordOp false t) K L

end Tab

end Rel
