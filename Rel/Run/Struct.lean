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

/-- `wordsFoR` of `n` zero words with every row flagged is `Enc.WF` at every type with a width: the `u1` clause is vacuous,
every row being null (`bitAt_packOf`). Proved here so the writers below run no `Decidable (Enc.WF …)` instance, which
decodes the column. -/
theorem nulWords_wf {t : QAtomicType} {n : USize} (ht : t.width.isSome) :
    Ext.Enc.WF t n (wordsFoR (Array.replicate n.toNat 0) (nulMap (Array.replicate n.toNat 1))) :=
  (wordsFoR_nul _ _ (by simp)).2.2.2 ht fun _ i hi hb => by
    simp only [nulMap, Array.size_replicate] at hb hi
    rw [bitAt_packOf _ _ _ hi] at hb; simp [hi] at hb

/-- `n` nulls of `1+t` (each `inl ()`): `n` zero words with every row flagged, written by `wordsFoR`, the kernel answer's
writer, whose null flags `foRNuls_wordsFoR` reads back; `Opt.ofAtoms` has no such lemma for its width-`w` bytes. Only a
type with no width (`general`) has no such column, and is refused. -/
def Opt.nuls (t : QAtomicType) (n : USize) : Except String (Opt t n) :=
  if h : t.width.isSome then .ok ⟨_, nulWords_wf h⟩ else .error s!"inl: {repr t} has no width, so no flagged null column"

/-- The tag column of a sum side whose `n` rows are all in one summand: every tag `s` (the positions through the post
chain `[(.and, 0), (.or, s)]`, written at `u1`). -/
def tagCol (n : USize) (s : Bool) : Except String (Arr .u1 n) :=
  colArr .first n .pos .pos .u1 .i64 [] [(.and, 0), (.or, if s then 1 else 0)]

/-- `n` fillers of `1+t`, each null (`Opt.nuls`); a `general` payload has no block to flag, so its filler is `n` of its
`default`, which no row ever reads. -/
def Opt.fill (t : QAtomicType) (n : USize) : Except String (Opt t n) :=
  match t with
  | .general => .ok ⟨.gen (Array.replicate n.toNat default), by simp [Ext.Enc.WF]⟩
  | t => Opt.nuls t n

/-- `X` with every row owned as the summand column of a dense sum: each atom column `Opt.ofArr`, which leaves the storage
as it is. -/
def Vals.lift : {A : Obj} → {n : USize} → Vals A n → ValsB true A n
  | .atom _, _, x => Opt.ofArr x
  | .prod _ _, _, x => (Vals.lift x.1, Vals.lift x.2)
  | .arr _, _, ⟨m, lo, hi, f⟩ => ⟨m, Opt.ofArr lo, Opt.ofArr hi, f⟩
  | .sum _ _, _, x => x
  | .one, _, _ => ()

/-- No row of `A`: no zero word per atom, an `arr` side of no cells, a sum of no rows (its summands `Vals.lift`ed). -/
def Vals.none : (A : Obj) → Except String (Vals A 0)
  | .atom t => Arr.zeros t 0
  | .prod a b => do pure (← Vals.none a, ← Vals.none b)
  | .arr b => do pure ⟨0, ← Arr.zeros .i64 0, ← Arr.zeros .i64 0, ← Vals.none b⟩
  | .sum a b => match h : Obj.band a b with
    | some t => do pure (ValsB.ofOpt h (← Opt.nuls t 0))
    | .none => do pure (ValsB.ofGen h (← tagCol 0 false) (Vals.lift (← Vals.none a)) (Vals.lift (← Vals.none b)))
  | .one => pure ()

/-- `n` rows of `A` all in-band null, the filler of the rows a summand of a dense sum does not own (`ValsB true`): `Opt.fill`
per atom column; an `arr` side of `n` null cells over no payload; a band sum `n` nulls; another `sum` side of tag `0` over
two such summands. -/
def Vals.zeros : (A : Obj) → (n : USize) → Except String (ValsB true A n)
  | .atom t, n => Opt.fill t n
  | .prod a b, n => do pure (← Vals.zeros a n, ← Vals.zeros b n)
  | .arr b, n => do pure ⟨0, ← Opt.fill .i64 n, ← Opt.fill .i64 n, ← Vals.none b⟩
  | .sum a b, n => match h : Obj.band a b with
    | some t => do pure (ValsB.ofOpt h (← Opt.nuls t n))
    | .none => do pure (ValsB.ofGen h (← tagCol n false) (← Vals.zeros a n) (← Vals.zeros b n))
  | .one, _ => pure ()

/-- A summand column whose rows are all owned (`inl°`, `inr°` after the gather), as an `Arr` per atom: `Arr.of` refuses a
column holding a null, which no owned row is; `what` names the producer. -/
def Vals.unlift (what : String) : {A : Obj} → {n : USize} → ValsB true A n → Except String (Vals A n)
  | .atom t, n, x => Arr.of t n (Opt.enc x) what
  | .prod _ _, _, x => do pure (← Vals.unlift what x.1, ← Vals.unlift what x.2)
  | .arr _, n, ⟨m, lo, hi, f⟩ => do pure ⟨m, ← Arr.of .i64 n (Opt.enc lo) what, ← Arr.of .i64 n (Opt.enc hi) what, f⟩
  | .sum _ _, _, x => pure x
  | .one, _, _ => pure ()

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
    pure ⟨T, ← ValsB.gather T iR x, ← ValsB.gather T iS y⟩

/-- `Y`'s rows as the band column of `a + b`, each `inr`: the storage as it is (`Opt.ofArr`). -/
def Vals.optInr {a b : Obj} {t : QAtomicType} {n : USize} (h : Obj.band a b = some t) (Y : Vals b n) : Opt t n := by
  obtain ⟨rfl, rfl⟩ := Obj.band_some h; exact Opt.ofArr Y

/-- The one row of the unit side `1`, as a side `A` known to be `1`. -/
def Vals.unit {A : Obj} (h : A = .one) : Vals A 1 := by subst h; exact ()

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
side of tag `0` over `X` itself and a zero right column (`Vals.zeros`), canonical. -/
def inl {n : USize} (X : Vals A n) : Except String (Tab A (.sum A B)) := do
  match h : Obj.band A B with
  | some t => canon ⟨n, X, ValsB.ofOpt h (← Opt.nuls t n)⟩
  | none => do canon ⟨n, X, ValsB.ofGen h (← tagCol n false) (Vals.lift X) (← Vals.zeros B n)⟩

/-- **`inr` on the values `Y`**, `idU Y ≫ inr`: the mirror of `inl`, tag `1`. -/
def inr {n : USize} (Y : Vals B n) : Except String (Tab B (.sum A B)) := do
  match h : Obj.band A B with
  | some _ => canon ⟨n, Y, ValsB.ofOpt h (Vals.optInr h Y)⟩
  | none => do canon ⟨n, Y, ValsB.ofGen h (← tagCol n true) (← Vals.zeros A n) (Vals.lift Y)⟩

/-- **`inl°` on the sum values `X`**, `idU X ≫ inl°`: the rows of tag `0` (`whereCol` of the negated tags), each `X` row
beside its left column's row there, canonical: one `canon` of the selected rows, no `comp`. -/
def inlConv {n : USize} (X : Vals (.sum A B) n) : Except String (Tab (.sum A B) A) := do
  match X.view with
  -- a band column's one left row is the null `inl ()`, so `inl°` is `D ≫ (inl ())°` on `inl`'s one null row
  | .opt h _ => do (← idU X).comp (← (← inl (B := B) (Vals.unit (Obj.band_some h).1)).conv)
  | .gen _ tag x _ =>
    let (m, sel) ← whereCol n (← colMap .not n tag.enc tag.enc)
    canon ⟨m, ← ValsB.gather m sel X, ← Vals.unlift "inl°" (← ValsB.gather m sel x)⟩

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
    pure ⟨m, ← ValsB.gather m sel (ValsB.ofOpt h x), ← Arr.of t m (← Opt.gather m sel x).enc "inr°"⟩

/-- **`inr°` on the sum values `X`**, `idU X ≫ inr°`: the mirror of `inlConv`, the rows of tag `1`. -/
def inrConv {n : USize} (X : Vals (.sum A B) n) : Except String (Tab (.sum A B) B) := do
  match X.view with
  | .opt h x => inrConvBand h x
  | .gen _ tag _ y =>
    let (m, sel) ← whereCol n tag.enc
    canon ⟨m, ← ValsB.gather m sel X, ← Vals.unlift "inr°" (← ValsB.gather m sel y)⟩

/-- **`Rᴵ` on the pairs `X`**, `idU X ≫ Rᴵ` = `((π₁ ≫ R) ∩ (π₂ ≫ π₁°)) ≫ π₂` (`flatDen_eq`): the rows `(i, a)` of `X`
beside `R`'s `(a', b)` at `i`, kept where the equality test `a = a'` holds (`∩` with `π₂ ≫ π₁°` on `R`'s values), then
`b`. -/
def flat {n : USize} (X : Vals (.prod I A) n) (R : Tab I (.prod A B)) : Except String (Tab (.prod I A) B) := do
  let L ← comp (← outl X) R
  let M ← comp (← outr X) (← conv (← outl R.val))
  comp (← inter L M) (← outr R.val)


end Tab

end Rel
