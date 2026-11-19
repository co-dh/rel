import Rel.Run.Comp
import Rel.Run.SetOps

/-! The `Tm` constructors `ldiv`, `rdiv`, `lam`, `E`, `nil`, `lt`, `leq` (`Rel/Run/Lang/Tm.lean`) as operators on `Tab`
over the five kernels (PLAN 6.14 W3), on the encoded columns as they are, as `Rel/Run/Comp.lean`. Each operator's
right-hand side is its constructor's denotation (`Rel/Lang/Den.lean`: `ldivDen`, `rdivDen`, `lamDen`, `EDen`,
`nilDen`, `ltDen`, `leqDen`). A denotation total on a whole type (`lamDen`, `EDen`, `nilDen`) is run on the keys in
demand `D`, as the compiled term reads it (`Tm.lam`'s doc). Their laws are in `Rel/RepTabDiv.lean`. -/

namespace Rel
open Rel.Ext Rel.Kernel Rel.Verify

/-- `colMap` as an `Arr` of its type `t` (`colMap_closed`). -/
def colArr (op : Op) (n : USize) (a b : Enc) (t : QAtomicType := .i64) : Except String (Arr t n) :=
  match h : colMap op n a b t with
  | .ok o => .ok (Arr.mk o (colMap_closed h).2)
  | .error s => .error s

/-- `n` zero words at `t`: `colArr .add` of two `colConst n 0`. -/
def Arr.zeros (t : QAtomicType) (n : USize) : Except String (Arr t n) := do
  colArr .add n (← colConst n 0) (← colConst n 0) t

/-- A side of no rows, every atom column `Arr.zeros _ 0`. -/
def Vals.noRows : (B : Obj) → Except String (Vals B 0)
  | .atom t => Arr.zeros t 0
  | .prod a b => do pure (← Vals.noRows a, ← Vals.noRows b)
  | .arr b => do pure ⟨0, ← Arr.zeros .i64 0, ← Arr.zeros .i64 0, ← Vals.noRows b⟩
  | .sum a b => do pure ⟨0, 0, ← Arr.zeros .u1 0, ← Arr.zeros .i64 0, ← Vals.noRows a, ← Vals.noRows b⟩

/-- **EXPAND** (`doc/rel-kernels.md`) of the `K` widths `w`: `T` output rows, each row's group `G` and its offset `u`
in the group. A prefix sum `P` places the groups (`o = P - w`), `kscatter (.max)` of each group id at its offset,
filled forward by `colPrefix (.max)`, the spare cell `T` cut off by `kgather`; `u = pos - o[G]`. The one scalar read
is the count `T` (`lastCount`). As `Tab.comp`'s expansion (to move there with it). -/
def expand (K : USize) (w : Enc) : Except String (USize × Enc × Enc) := do
  match hP : colPrefix .add K w with
  | .error s => throw s
  | .ok P =>
    let T := lastCount K P (by
      unfold colPrefix at hP; simp only [bind, Except.bind] at hP; split at hP; · cases hP
      exact (kscan_closed hP).2)
    if USize.size ≤ T + 1 then throw s!"expand: {T} output rows past USize"
    let T := T.toUSize
    let o ← colMap .sub K P w
    let G ← kgather T .pos (T + 1) (← colPrefix .max (T + 1) (← kscatter .max K o .pos (T + 1) 0))
    pure (T, G, ← colMap .sub T .pos (← kgather T G K o))

namespace Tab
variable {A B C : Obj}

/-- **`X × Y`**, every pair `(X[i], Y[j])`: CROSS (`T = n·m`, `i = pos div m`, `j = pos mod m`), both sides
`kgather`ed there, then `canon`. -/
def cross {n m : USize} (X : Vals A n) (Y : Vals B m) : Except String (Tab A B) := do
  if 2 ^ 63 ≤ n.toNat * m.toNat ∨ USize.size ≤ n.toNat * m.toNat then
    throw s!"cross: {n} × {m} rows past 2^63 or USize"
  let T := (n.toNat * m.toNat).toUSize
  let mc ← colConst T m.toNat.toUInt64
  Tab.canon ⟨T, ← Vals.gather T (← colMap .div T .pos mc) X, ← Vals.gather T (← colMap .mod T .pos mc) Y⟩

/-- The rows of `T` where the `0`/`1` words `b` are `1`: `whereCol`, both sides `kgather`ed there. Row order is
kept, so a canonical `T` stays canonical. -/
def keep (T : Tab A B) (b : Enc) : Except String (Tab A B) := do
  let (M, sel) ← whereCol T.n b
  pure ⟨M, ← Vals.gather M sel T.key, ← Vals.gather M sel T.val⟩

/-- **`∋` on the arrays `X`** (the step `EDen` composes, `(fun xs a => a ∈ xs) ≫ T`): each cell to each of its
elements. A cell `[lo, hi)` clamped to the payload's `[0, m)` is `[s, e)` with `s = max lo 0` and
`e = max (min hi m) s`, so its width `e - s` is never negative and never wraps; EXPAND of the widths, the key the
cell `X[G]`, the value the payload at `s[G] + u`; then `canon`. -/
def mem {n : USize} (X : Vals (.arr B) n) : Except String (Tab (.arr B) B) :=
  match X with
  | ⟨m, lo, hi, f⟩ => do
    -- `.max`, `.min`, `.sub` read the bounds and widths signed: every one is below `n * m + n + m`
    if 2 ^ 63 ≤ n.toNat * m.toNat + n.toNat + m.toNat then throw s!"mem: {n} cells × {m} elements past 2^63"
    let s ← colMap .max n lo.enc (← colConst n 0)
    let e ← colMap .max n (← colMap .min n hi.enc (← colConst n m.toUInt64)) s
    let (T, G, u) ← expand n (← colMap .sub n e s)
    let ix ← colMap .add T (← kgather T G n s) u
    Tab.canon ⟨T, ← Vals.gather (A := .arr B) T G ⟨m, lo, hi, f⟩, ← Vals.gather T ix f⟩

/-- **`Λ(R)` on the keys `D`** (`lamDen`): each `a` of `D` to the cell of its values in `R`, ascending and each once,
`[]` where `R` has none. One GROUP over the keys of `D` then `r = canon R` (`Vals.concat`): `kasc` being stable, a
group's sorted rows are its `D` rows (`cD`, input row below `n`), then its `r` rows, which `canon` put in ascending
value order. The cell of group `G` is the sorted rows `[f + cD, f + c)` of the payload `r.val` gathered in sorted
order (a `D` row reads `r`'s row `0`, inside no cell); the groups with `0 < cD` are kept (`whereCol`), keyed by their
first row, a row of `D`. Then `canon`. -/
def lam {n : USize} (D : Vals A n) (R : Tab A B) : Except String (Tab A (.arr B)) := do
  let r ← R.canon
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
  let pay ← if r.n.toNat = 0 then pure (⟨r.n, r.val⟩ : (m : USize) × Vals B m) else
    (fun y => (⟨N, y⟩ : (m : USize) × Vals B m)) <$>
      Vals.gather N (← colMap .max N (← colMap .sub N p nc) (← colConst N 0)) r.val
  Tab.canon ⟨M, ← Vals.gather M iD D, ⟨pay.1, ← Arr.gather M sel lo, ← Arr.gather M sel hi, pay.2⟩⟩

/-- **`E(R)` on the arrays `X`** (`EDen R = lamDen (∋ ≫ R)`): `lam` on `X` of `mem X ≫ R`. -/
def E {n : USize} (X : Vals (.arr A) n) (R : Tab A B) : Except String (Tab (.arr A) (.arr B)) := do
  lam X (← (← mem X).comp R)

/-- **`nil` on the keys `D`** (`nilDen`): each to the empty cell, `lo = hi = 0` over a payload of no rows; then
`canon`. -/
def nil {n : USize} (D : Vals A n) : Except String (Tab A (.arr B)) := do
  let z ← Arr.zeros .i64 n
  Tab.canon ⟨n, D, ⟨0, z, z, ← Vals.noRows B⟩⟩

/-- **`R \ S` within `UB`, `UC`** (`ldivDen`), by counting: `b` of `ran R` to `c` where
`#{a | R a b ∧ S a c} = #{a | R a b}`, no complement (`doc/rel-architecture.zh.typ`, `R\S`): `Q = r° ≫ ⟨𝟙, s⟩`
(`r`, `s` canonical, so `Q`'s rows `(b, (a, c))` are distinct and hold each `a` once); GROUP over `(b, c)` and its
row count `cnt` (`kscatter .add`); the count `d` of `R`'s rows of `b`, read at each group's first row by CODE over
`r.val ++ Q.key` (the run of `r` rows of each `b` group, `kscatter .add` of `p < r.n`, each input row's group by
`kscatter .last` through `p`); the groups with `cnt = d` (`whereCol`). The vacuous part is `(ran UB − ran R) × ran UC`,
and the two are met by `∪`. -/
def ldiv (R : Tab A B) (S : Tab A C) (UB : Tab B B) (UC : Tab C C) : Except String (Tab B C) := do
  let r ← R.canon; let s ← S.canon
  let Q ← (Tab.mk r.n r.val r.key).comp (Tab.mk s.n s.key (s.key, s.val) : Tab A (.prod A C))
  let x : Vals (.prod B C) Q.n := (Q.key, (Q.val : Vals A Q.n × Vals C Q.n).2)
  let es ← Vals.cols x
  let (vs, p) ← kasc Q.n es
  let (k, g, f) ← kseen Q.n ((es.map (·.1)).zip vs)
  let K := k.toUSize
  let cnt ← kscatter .add Q.n g (← colConst Q.n 1) K 0
  let (N, sh) ← catPlan r.n Q.n
  -- `.lt` reads positions signed: every one is below `N`
  if 2 ^ 63 ≤ N.toNat then throw s!"ldiv: {N} rows past 2^63"
  let bs ← Vals.cols (← Vals.concat N sh r.val Q.key)
  let (bv, bp) ← kasc N bs
  let (bk, bg, _) ← kseen N ((bs.map (·.1)).zip bv)
  let cR ← kscatter .add N bg (← colMap .lt N bp (← colConst N r.n.toUInt64)) bk.toUSize 0
  let code ← kscatter .last N bp bg N 0
  let q ← kgather K f Q.n p
  let d ← kgather K (← kgather K (← colMap .add K q (← colConst K r.n.toUInt64)) N code) bk.toUSize cR
  let (M, sel) ← whereCol K (← colMap .eq K cnt d)
  let ix ← kgather M sel K q
  let P : Tab B C := ⟨M, ← Vals.gather M ix Q.key, ← Vals.gather M ix (Q.val : Vals A Q.n × Vals C Q.n).2⟩
  P.union (← cross (← (← UB.ran).diff (← R.ran)).key (← UC.ran).key)

/-- **`R / S` within `UA`, `UB`** (`rdivDen`): `(S° \ R°)°` within `UB`, `UA`. -/
def rdiv (R : Tab A C) (S : Tab B C) (UA : Tab A A) (UB : Tab B B) : Except String (Tab A B) := do
  (← ldiv (← S.conv) (← R.conv) UB UA).conv

/-- The pairs `(a, b)` of `dom U × dom U` whose `i64` words pass `op` (signed, as `Int64`'s order): CROSS of the
domain with itself, then `keep` of `colMap op` of the two columns. -/
def cmpOn (op : Op) (U : Tab .long .long) : Except String (Tab .long .long) := do
  let d ← U.dom
  let T ← cross d.key d.key
  T.keep (← colMap op T.n T.key.enc T.val.enc)

/-- **`<` on `dom U`** (`ltDen`). -/
def lt (U : Tab .long .long) : Except String (Tab .long .long) := cmpOn .lt U

/-- **`≤` on `dom U`** (`leqDen`). -/
def leq (U : Tab .long .long) : Except String (Tab .long .long) := cmpOn .le U

end Tab

end Rel
