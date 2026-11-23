module

public import Rel.Run.SetOps
public import Rel.Run.Comp

-- exposed: every def body is a spec a downstream `rfl`/`decide`/`simp` may unfold (PLAN W.8)
@[expose] public section

/-! The structural operators of the core term `Tm` (`Rel/Run/Lang/Tm.lean`) on `Tab`, as compositions of the five
kernels (PLAN 6.14 W3), in the style of `Rel/Run/Comp.lean`: `zero`, `id` (on the values `X` its context gives),
`top`, `outl`, `outr`, `pair`, `prod`, `inl`, `inr`, their converses `inlConv`, `inrConv` (on the sum values in
demand, which `[R,S] = inl° ≫ R ∪ inr° ≫ S` runs on), and `flat` from `outl`, `outr` and an equality test. Each law (`Rel/RepStruct.lean`) has the
constructor's denotation `Tm.den` (`Rel/Lang/Den.lean`) as its right-hand side. `Tm.join` is `Tab.union`
(`Rel/Run/SetOps.lean`). No column is decoded or re-encoded between the calls.

CROSS (`doc/rel-kernels.md`): `n · m` rows, row `t` pairing row `t / m` of one side with row `t % m` of the other,
both index columns one `kscan` map (`colMap .div`, `.mod`) of the positions by the constant `m`. -/

namespace Rel
open Rel.Ext Rel.Kernel Rel.Verify

/-- `n` zero words at the atom type `t`: one `kscan` of the positions through the post step `(.and, 0)`, written at
`t`; a constant operand is a post step, not a `colConst` scatter (`colMap_const_eq`). -/
def Arr.zeros (t : QAtomicType) (n : USize) : Except String (Arr t n) :=
  colArr .first n .pos .pos t .i64 [] [(.and, 0)]

/-- No row of `A`: `Arr.zeros _ 0` per atom column; an `arr` side of no cells over no payload, a `sum` side over two
summands of no rows. -/
def Vals.none : (A : Obj) → Except String (Vals A 0)
  | .atom t => Arr.zeros t 0
  | .prod a b => do pure (← Vals.none a, ← Vals.none b)
  | .arr b => do pure ⟨0, ← Arr.zeros .i64 0, ← Arr.zeros .i64 0, ← Vals.none b⟩
  | .sum a b => match h : Obj.band a b with
    | some t => do pure (Vals.ofOpt h (Opt.ofArr (← Arr.zeros t 0)))
    | .none => do pure (Vals.ofGen h 0 0 (← Arr.zeros .u1 0) (← Arr.zeros .i64 0) (← Vals.none a) (← Vals.none b))
  | .one => pure ()

/-- The index columns of CROSS: `T = n · m` rows, `iR = pos / m`, `iS = pos % m` (`colMap` of the positions and
the post steps `(.rdiv, m)`, `(.rmod, m)`). `.rdiv`, `.rmod` read their words signed, so `n · m + m` stays below
`2^63`, and `T` fits a `USize`. -/
def crossIx (n m : USize) : Except String (USize × Enc × Enc) := do
  if 2 ^ 63 ≤ n.toNat * m.toNat + m.toNat ∨ USize.size ≤ n.toNat * m.toNat then
    throw s!"cross: {n} × {m} rows past 2^63 or USize"
  let T := (n.toNat * m.toNat).toUSize
  pure (T, ← colMap .first T .pos .pos .i64 .i64 [] [(.rdiv, m.toUInt64)],
    ← colMap .first T .pos .pos .i64 .i64 [] [(.rmod, m.toUInt64)])

/-- The most pairs `Vals.cross` builds, `2^28`: two `i64` columns of 4 GiB, a fifth of the memory cap. -/
def crossMax : Nat := 2 ^ 28

/-- **CROSS of two sides**, `x` and `y` side by side at every pair of their rows: `x` gathered at `iR`, `y` at `iS`
(`crossIx`). -/
def Vals.cross {A B : Obj} {n m : USize} (x : Vals A n) (y : Vals B m) :
    Except String ((T : USize) × Vals A T × Vals B T) := do
  -- checked here, not left to the allocator: past memory the Rust side aborts the process instead of returning
  if crossMax < n.toNat * m.toNat then
    throw s!"cross: {n} values of the left object by {m} of the right is {n.toNat * m.toNat} pairs, past the bound \
      {crossMax}: a relation on two whole objects (`≤`, `<`, `⊤`) read where nothing bounds it to fewer pairs; \
      meet it with a table (`T ∩ ≤` tests T's pairs only) or compose a smaller table on each side (`K ≤ L`)"
  expandNote s!"a product of {n} × {m} values (Vals.cross)" (n.toNat * m.toNat) fun _ => do
    let (T, iR, iS) ← crossIx n m
    pure ⟨T, ← Vals.gather T iR x, ← Vals.gather T iS y⟩

/-- `Y`'s rows as the band column of `a + b`, each `inr`: the storage as it is (`Opt.ofArr`). -/
def Vals.optInr {a b : Obj} {t : QAtomicType} {n : USize} (h : Obj.band a b = some t) (Y : Vals b n) : Opt t n := by
  obtain ⟨rfl, rfl⟩ := Obj.band_some h; exact Opt.ofArr Y

/-- The one row of the unit side `1`, as a side `A` known to be `1`. -/
def Vals.unit {A : Obj} (h : A = .one) : Vals A 1 := by subst h; exact ()

/-- `n` nulls of `1+t` (each `inl ()`): `n` zero words with every row flagged, written by `wordsFoR`, the kernel answer's
writer. Its `Enc.WF` is `Verify.wordsFoR_nul`'s clause (the `u1` one vacuous, every word `0`), so no element is read to
decide it; a `t` with no width (`general`) has no block to flag and is the error. -/
def Opt.nuls (t : QAtomicType) (n : USize) : Except String (Opt t n) :=
  if hw : t.width.isSome then
    .ok ⟨_, (Verify.wordsFoR_nul (Array.replicate n.toNat 0) (nulMap (Array.replicate n.toNat 1))
      (n := n) (by simp)).2.2.2 hw fun _ i hi _ => by simp⟩
  else .error s!"inl: nulls of {repr t}, which has no block to flag"

/-- The tag and position columns of a sum side whose `n` rows are all in one summand: every tag `s` (the positions
through the post chain `[(.and, 0), (.or, s)]`, written at `u1`), row `k` at position `k` (the positions written by one
`kscan`). A summand past `2^63` rows, which an `Int64` position cannot reach, is the error. -/
def injCols (n : USize) (s : Bool) : Except String (Arr .u1 n × Arr .i64 n) := do
  if 2 ^ 63 < n.toNat then throw s!"inj: {n} rows, past an Int64 position"
  pure (← colArr .first n .pos .pos .u1 .i64 [] [(.and, 0), (.or, if s then 1 else 0)], ← Arr.pos n)

namespace Tab
variable {A B C D I : Obj}

/-- **`𝟘`**: no row. -/
def zero : Except String (Tab A B) := do pure ⟨0, ← Vals.none A, ← Vals.none B⟩

/-- **`𝟙` on the values `X`**, `idU X`: the domain of `⟨n, X, X⟩` (`Tab.dom`), each value once, paired with itself. -/
def idU {n : USize} (X : Vals A n) : Except String (Tab A A) := Tab.dom ⟨n, X, X⟩

/-- **`X × Y`**, every pair `(X[i], Y[j])`: `Vals.cross`, canonical. -/
def cross {n m : USize} (X : Vals A n) (Y : Vals B m) : Except String (Tab A B) := do
  let ⟨T, x, y⟩ ← Vals.cross X Y
  canon ⟨T, x, y⟩

/-- **`⊤` between the known sides `K` and `L`**, `K ≫ ⊤ ≫ L = K × L`: every value of `K` beside every value of `L`
(`idU X ≫ ⊤ ≫ V` is `top X V.val`). -/
def top {n m : USize} (K : Vals A n) (L : Vals B m) : Except String (Tab A B) := cross K L

/-- **`π₁` on the pairs `X`**, `idU X ≫ π₁`: each pair beside its first component, canonical. -/
def outl {n : USize} (X : Vals (.prod A B) n) : Except String (Tab (.prod A B) A) := canon ⟨n, X, X.1⟩

/-- **`π₂` on the pairs `X`**, `idU X ≫ π₂`. -/
def outr {n : USize} (X : Vals (.prod A B) n) : Except String (Tab (.prod A B) B) := canon ⟨n, X, X.2⟩

/-- `L ≫ S` for `pair`, whose `L` has distinct rows, so `compGroups`' expansion (`compRows`) is the answer's row
count: where `L.n · S.n` passes `crossMax` it is counted first and refused past `crossMax`, as `Vals.cross` is, since
past memory the Rust side aborts the process; within it, `comp` (the same `compFrom` past `blockRows`). -/
def compPairs (L : Tab A B) (S : Tab B C) : Except String (Tab A C) :=
  if L.n.toNat * S.n.toNat ≤ crossMax then comp L S else do
    let x ← compGroups L S
    let k ← compRows x
    if crossMax < k then
      throw s!"pair: ⟨R, S⟩ is {k} pairs, past the bound {crossMax}: a product or pair of two relations read where \
        nothing bounds it to fewer pairs (`R × S` of two whole objects); meet it with a table or compose a smaller \
        table on its source"
    else compFrom blockRows L S x

/-- **`⟨R, S⟩`**: `L ≫ S` with `L = ⟨𝟙, R⟩°` on `R`'s rows (`((a, b), a)`), its rows `((a, b), c)` rebracketed as
`(a, (b, c))` — the join of `R` and `S` on equal keys that `Tab.comp` runs, `R.val` carried in the key. The
rebracketing keeps the column order, so the answer is `comp`'s canonical table. -/
def pair (R : Tab A B) (S : Tab A C) : Except String (Tab A (.prod B C)) :=
  (fun (T : Tab (.prod A B) C) => ⟨T.n, T.key.1, (T.key.2, T.val)⟩) <$>
    compPairs (⟨R.n, (R.key, R.val), R.key⟩ : Tab (.prod A B) A) S

/-- **`inl` on the values `X`**, `idU X ≫ inl`: row `k` is `X`'s row `k` beside the left summand's row `k`, the sum
side over `X` itself and no right row (`injCols` with tag `0`), canonical. -/
def inl {n : USize} (X : Vals A n) : Except String (Tab A (.sum A B)) := do
  match h : Obj.band A B with
  | some t => canon ⟨n, X, Vals.ofOpt h (← Opt.nuls t n)⟩
  | none => do
    let (tag, idx) ← injCols n false
    canon ⟨n, X, Vals.ofGen h n 0 tag idx X (← Vals.none B)⟩

/-- **`inr` on the values `Y`**, `idU Y ≫ inr`: the mirror of `inl`, tag `1`. -/
def inr {n : USize} (Y : Vals B n) : Except String (Tab B (.sum A B)) := do
  match h : Obj.band A B with
  | some _ => canon ⟨n, Y, Vals.ofOpt h (Vals.optInr h Y)⟩
  | none => do
    let (tag, idx) ← injCols n true
    canon ⟨n, Y, Vals.ofGen h 0 n tag idx (← Vals.none A) Y⟩

/-- **`inl°` on the sum values `X`**, `idU X ≫ inl°`: `X` beside `(inl x)°`, `x` its left payload, which every
left row reads. A left payload of no value reads `A.dflt` at a left row (`Vals.row`), which `x` cannot give: there
the answer is none where `X` has only right rows (`idU X − dom(idU X ≫ (inr y)°)` empty), else the error. -/
def inlConv {n : USize} (X : Vals (.sum A B) n) : Except String (Tab (.sum A B) A) := do
  match X.view with
  -- a band column's one left row is the null `inl ()`, so `inl°` is `D ≫ (inl ())°` on `inl`'s one null row
  | .opt h _ => do (← idU X).comp (← (← inl (B := B) (Vals.unit (Obj.band_some h).1)).conv)
  | .gen _ l _ _ _ x y =>
  let D ← idU X
  if l.toNat = 0 then
    if (← D.diff (← (← D.comp (← (← inr (A := A) y).conv)).dom)).n = 0 then zero
    else throw "inl°: a left row over a left payload of no value"
  else D.comp (← (← inl (B := B) x).conv)

/-- **`inr°` on a band column `x`** (`1 + t`, a null row the all-ones residual): `X ≫ inr°` keeps the rows that are no
null, each beside its value. The null test is a scan comparing with the residual (`kscan .null`, then `not`), `whereCol`
numbers the kept rows, and the key `X` and the value `x` are gathered there; `Arr.of` refuses a null, which none of the
kept rows is. -/
def inrConvBand {a b : Obj} {t : QAtomicType} {n : USize} (h : Obj.band a b = some t) (x : Opt t n) :
    Except String (Tab (.sum a b) b) := by
  -- two `Eq` casts, not one `And.rec`: a `rfl` cast reduces, so a proof about a band column unfolds this to the body
  obtain rfl := (Obj.band_some h).1
  obtain rfl := (Obj.band_some h).2
  exact do
    let (m, sel) ← whereCol n (← kscan .null false t .u1 n none [(n, x.enc)] [] [(.not, 0)]).1
    pure ⟨m, ← Vals.gather m sel (Vals.ofOpt h x), ← Arr.of t m (← Opt.gather m sel x).enc "inr°"⟩

/-- **`inr°` on the sum values `X`**, `idU X ≫ inr°`: the mirror of `inlConv`. -/
def inrConv {n : USize} (X : Vals (.sum A B) n) : Except String (Tab (.sum A B) B) := do
  match X.view with
  | .opt h x => inrConvBand h x
  | .gen _ _ r _ _ x y =>
  let D ← idU X
  if r.toNat = 0 then
    if (← D.diff (← (← D.comp (← (← inl (B := B) x).conv)).dom)).n = 0 then zero
    else throw "inr°: a right row over a right payload of no value"
  else D.comp (← (← inr (A := A) y).conv)

-- `inr°` on a `1 + long` column: the rows that are no null, each beside its value; none, some and all null
private def inrBand (xs : List (Option QAtom)) : Option (List ((Unit ⊕ Int64) × Int64)) := do
  let x ← Opt.ofAtoms .i64 xs.toArray
  let T ← (inrConvBand (a := .one) (b := .long) rfl x).toOption
  pure T.toList
#guard inrBand [some (.i64 5), none, some (.i64 7)] == some [(.inr 5, 5), (.inr 7, 7)]
#guard inrBand [some (.i64 5), some (.i64 6)] == some [(.inr 5, 5), (.inr 6, 6)]
#guard inrBand [none, none, none] == some []
#guard inrBand [] == some []

/-- **`Rᴵ` on the pairs `X`**, `idU X ≫ Rᴵ` = `((π₁ ≫ R) ∩ (π₂ ≫ π₁°)) ≫ π₂` (`flatDen_eq`): the rows `(i, a)` of `X`
beside `R`'s `(a', b)` at `i`, kept where the equality test `a = a'` holds (`∩` with `π₂ ≫ π₁°` on `R`'s values), then
`b`. -/
def flat {n : USize} (X : Vals (.prod I A) n) (R : Tab I (.prod A B)) : Except String (Tab (.prod I A) B) := do
  let L ← comp (← outl X) R
  let M ← comp (← outr X) (← conv (← outl R.val))
  comp (← inter L M) (← outr R.val)


end Tab

end Rel
