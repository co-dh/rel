module

public import Rel.Run.SetOps
public import Rel.Run.Comp
public import Rel.Run.Struct
public import Rel.Run.Div

-- exposed: every def body is a spec a downstream `rfl`/`decide`/`simp` may unfold (PLAN W.8)
@[expose] public section

/-! The list rows of `prims` (`Rel/Lang/Den.lean`, `rowDens`) on `Tab`, as compositions of the five kernels (PLAN 6.14
W3, step T7), in the style of `Rel/Run/Comp.lean`: `snoc`, `cat`, `cons`, `zip` after a table of pairs of cells, and
`sum`, `uncons`, `unsnoc`, `uncat` on the cells `X` a context gives (as the old `RowCode.*` run them).

One composition builds every new cell: `Vals.cat`, the cell `X[i] ++ Y[i]` of two `arr` sides — the payloads joined
(`ValsB.concat`), EXPAND (`expand`) of the summed widths, and each output element `kgather`ed from the first slice or
the second. `snoc` is `cat` after `𝟙 × τ` (`Vals.tau`, the one-element cells over a side's own rows), `cons` after
`τ × 𝟙`, as the old `snocC`; `zip` reads both slices at one offset. The converses build no payload: each answer cell
is a slice `[lo, hi)` of the input's own payload. No column is decoded or re-encoded. -/

namespace Rel
open Rel.Ext Rel.Kernel Rel.Verify

/-- `n` cells of the widths `w`, laid out one after another over the payload `pay`: `hi` the running sum of `w`
(`colPrefix .add`, the layout `expand` places its groups by), `lo = hi - w`. -/
def Vals.cells {B : Obj} {T : USize} (n : USize) (w : Enc) (pay : Vals B T) : Except String (Vals (.arr B) n) := do
  let P ← colPrefix .add n w
  pure ⟨T, ← colArr .sub n P w, ← scanArr .first false .i64 .i64 n Option.none [(n, P)], pay⟩

/-- `x` with every array payload cut to the elements its cells read, where at most half of it is read (`2 · T ≤ m`,
`T` the summed widths): the widths EXPANDed, the payload `kgather`ed there, laid out by `Vals.cells`; nested payloads
the same. A payload joined to a copy of itself (`ValsB.concat` in `∪`, `cat`) doubles while its cells read one copy;
the cut is paid by the dead half, so a round's slices (`uncons`) are not copied each round. -/
def Vals.pack : {A : Obj} → {n : USize} → Vals A n → Except String (Vals A n)
  | .atom _, _, x => pure x
  | .prod _ _, _, x => do pure (← Vals.pack x.1, ← Vals.pack x.2)
  | .arr _, n, ⟨m, lo, hi, f⟩ => do
    -- the bounds, widths, their prefix sums and the positions `lo + u` are read signed: each below `n * m + n + m`
    if 2 ^ 63 ≤ n.toNat * m.toNat + n.toNat + m.toNat then throw s!"pack: {n} cells over {m} elements past 2^63"
    let w ← colMap .sub n hi.enc lo.enc
    match hP : colPrefix .add n w with
    | .error err => throw err
    | .ok P =>
      if 0 < m.toNat ∧ 2 * lastCount n P (colPrefix_closed hP).2 (colPrefix_plain hP) ≤ m.toNat then do
        let (T, G, u) ← expand n w
        Vals.cells n w (← Vals.pack (← ValsB.gather T (← colMap .add T (← kgather T G n lo.enc) u) f))
      else pure ⟨m, lo, hi, ← Vals.pack f⟩
  | .sum _ _, _, s => match s.view with
    | .opt .. => pure s
    | .gen h tag x y => do pure (ValsB.ofGen h tag (← Vals.pack x) (← Vals.pack y))
  | .one, _, _ => pure ()

/-- **`R` with its payloads cut** (`Vals.pack` of both sides): the same rows in the same order. -/
def Tab.pack {k v : Obj} (R : Tab k v) : Except String (Tab k v) := do
  pure ⟨R.n, ← Vals.pack R.key, ← Vals.pack R.val⟩

/-- **`τ` on the rows of `x`**: row `i` the one-element cell `[i, i + 1)` over `x` itself. -/
def Vals.tau {B : Obj} {n : USize} (x : Vals B n) : Except String (Vals (.arr B) n) := do
  pure ⟨n, ← Arr.pos n, ← colArr .first n .pos .pos .i64 .i64 [] [(.add, 1)], x⟩

/-- **Row `i` the cell `X[i] ++ Y[i]`**: the payloads `f₁`, `f₂` joined (`ValsB.concat`, `f₂` from `m₁` on), the
widths `w₁ + w₂` EXPANDed into `(G, u)`, and output element `u` of cell `G` read at `s₁[G] + u` where `u < w₁`, else
at `m₁ + s₂[G] + u - w₁` (`b + c · (a - b)`, `c` the `0`/`1` test `u < w₁`). -/
def Vals.cat {B : Obj} {n : USize} (X Y : Vals (.arr B) n) : Except String (Vals (.arr B) n) :=
  match X, Y with
  | ⟨m₁, lo₁, hi₁, f₁⟩, ⟨m₂, lo₂, hi₂, f₂⟩ => do
    -- `.lt`, `.sub` and the prefix sums read positions and widths signed: each is below `n * (m₁ + m₂) + n + m₁ + m₂`
    if 2 ^ 63 ≤ n.toNat * (m₁.toNat + m₂.toNat) + n.toNat + m₁.toNat + m₂.toNat then
      throw s!"cat: {n} cells over {m₁} + {m₂} elements past 2^63"
    let N ← catRows m₁ m₂
    let F ← ValsB.concat N f₁ f₂
    let w₁ ← colMap .sub n hi₁.enc lo₁.enc
    let w ← colMap .add n w₁ (← colMap .sub n hi₂.enc lo₂.enc)
    let (T, G, u) ← expand n w
    let a ← colMap .add T (← kgather T G n lo₁.enc) u
    let d ← colMap .sub n (← colMap .first n lo₂.enc lo₂.enc .i64 .i64 [] [(.add, m₁.toUInt64)]) w₁
    let b ← colMap .add T (← kgather T G n d) u
    let c ← colMap .lt T u (← kgather T G n w₁)
    Vals.cells n w (← ValsB.gather T (← colMap .add T b (← colMap .mul T c (← colMap .sub T a b))) F)

/-- **Row `i` the cell `zip X[i] Y[i]`**: the widths `min w₁ w₂` EXPANDed into `(G, u)`, output element `u` of cell
`G` the pair of `X`'s payload at `s₁[G] + u` and `Y`'s at `s₂[G] + u`. -/
def Vals.zip {A B : Obj} {n : USize} (X : Vals (.arr A) n) (Y : Vals (.arr B) n) :
    Except String (Vals (.arr (.prod A B)) n) :=
  match X, Y with
  | ⟨m₁, lo₁, hi₁, f₁⟩, ⟨m₂, lo₂, hi₂, f₂⟩ => do
    if 2 ^ 63 ≤ n.toNat * (m₁.toNat + m₂.toNat) + n.toNat + m₁.toNat + m₂.toNat then
      throw s!"zip: {n} cells over {m₁} + {m₂} elements past 2^63"
    let w ← colMap .min n (← colMap .sub n hi₁.enc lo₁.enc) (← colMap .sub n hi₂.enc lo₂.enc)
    let (T, G, u) ← expand n w
    let x ← ValsB.gather T (← colMap .add T (← kgather T G n lo₁.enc) u) f₁
    let y ← ValsB.gather T (← colMap .add T (← kgather T G n lo₂.enc) u) f₂
    Vals.cells n w ((x, y) : Vals (.prod A B) T)

namespace Tab
variable {K A B : Obj}

/-- **`P ≫ cat`**: `(xs, ys)` to `xs ++ ys` (`Vals.cat`), then `canon`. -/
def cat (P : Tab K (.prod (.arr B) (.arr B))) : Except String (Tab K (.arr B)) := do
  canon ⟨P.n, P.key, ← Vals.cat P.val.1 P.val.2⟩

/-- **`P ≫ snoc`** = `P ≫ (𝟙 × τ) ≫ cat`: `(xs, a)` to `xs ++ [a]`. -/
def snoc (P : Tab K (.prod (.arr B) B)) : Except String (Tab K (.arr B)) := do
  canon ⟨P.n, P.key, ← Vals.cat P.val.1 (← Vals.tau P.val.2)⟩

/-- **`P ≫ cons`** = `P ≫ (τ × 𝟙) ≫ cat`: `(a, xs)` to `[a] ++ xs`. -/
def cons (P : Tab K (.prod B (.arr B))) : Except String (Tab K (.arr B)) := do
  canon ⟨P.n, P.key, ← Vals.cat (← Vals.tau P.val.1) P.val.2⟩

/-- **`P ≫ zip`**: `(xs, ys)` to `xs.zip ys` (`Vals.zip`), then `canon`. -/
def zip (P : Tab K (.prod (.arr A) (.arr B))) : Except String (Tab K (.arr (.prod A B))) := do
  canon ⟨P.n, P.key, ← Vals.zip P.val.1 P.val.2⟩

/-- **`cons°` on the cells `X`**: each non-empty cell `[s, e)` (`whereCol` of `s < e`) to its first element (the
payload at `s`) and the slice `[s + 1, e)`. -/
def uncons {n : USize} (X : Vals (.arr B) n) : Except String (Tab (.arr B) (.prod B (.arr B))) :=
  match X with
  | ⟨m, lo, hi, f⟩ => do
    if 2 ^ 63 ≤ n.toNat + m.toNat + 1 then throw s!"uncons: {n} cells over {m} elements past 2^63"
    let (M, sel) ← whereCol n (← colMap .lt n lo.enc hi.enc)
    let sM ← Arr.gather M sel lo
    canon ⟨M, ← ValsB.gather (A := .arr B) M sel ⟨m, lo, hi, f⟩,
      (← ValsB.gather M sM.enc f, ⟨m, ← colArr .first M sM.enc sM.enc .i64 .i64 [] [(.add, 1)], ← Arr.gather M sel hi, f⟩)⟩

/-- **`snoc°` on the cells `X`**: each non-empty cell `[s, e)` to the slice `[s, e - 1)` and its last element (the
payload at `e - 1`). -/
def unsnoc {n : USize} (X : Vals (.arr B) n) : Except String (Tab (.arr B) (.prod (.arr B) B)) :=
  match X with
  | ⟨m, lo, hi, f⟩ => do
    if 2 ^ 63 ≤ n.toNat + m.toNat + 1 then throw s!"unsnoc: {n} cells over {m} elements past 2^63"
    let (M, sel) ← whereCol n (← colMap .lt n lo.enc hi.enc)
    let hM ← Arr.gather M sel hi
    let l ← colArr .first M hM.enc hM.enc .i64 .i64 [] [(.add, 0 - 1)]
    canon ⟨M, ← ValsB.gather (A := .arr B) M sel ⟨m, lo, hi, f⟩,
      (⟨m, ← Arr.gather M sel lo, l, f⟩, ← ValsB.gather M l.enc f)⟩

/-- **`cat°` on the cells `X`**: each cell `[s, e)` to its `e - s + 1` splits, EXPAND of those counts into `(G, u)`,
split `u` of cell `G` the slices `[s, s + u)` and `[s + u, e)`. -/
def uncat {n : USize} (X : Vals (.arr B) n) : Except String (Tab (.arr B) (.prod (.arr B) (.arr B))) :=
  match X with
  | ⟨m, lo, hi, f⟩ => do
    if 2 ^ 63 ≤ n.toNat * (m.toNat + 1) + n.toNat + m.toNat + 1 then
      throw s!"uncat: {n} cells over {m} elements past 2^63"
    let (T, G, u) ← expand n (← colMap .sub n hi.enc lo.enc .i64 .i64 [] [(.add, 1)])
    let sG ← Arr.gather T G lo
    let mid ← colArr .add T sG.enc u
    canon ⟨T, ← ValsB.gather (A := .arr B) T G ⟨m, lo, hi, f⟩, (⟨m, sG, mid, f⟩, ⟨m, mid, ← Arr.gather T G hi, f⟩)⟩

/-- **`prefix` on the cells `X`**: the prelude's `cat° π₁`, `uncat` then `outl` on its splits. -/
def «prefix» {n : USize} (X : Vals (.arr B) n) : Except String (Tab (.arr B) (.arr B)) := do
  let u ← uncat X; u.comp (← outl u.val)

/-- **`suffix` on the cells `X`**: the prelude's `cat° π₂`, `uncat` then `outr` on its splits. -/
def suffix {n : USize} (X : Vals (.arr B) n) : Except String (Tab (.arr B) (.arr B)) := do
  let u ← uncat X; u.comp (← outr u.val)

/-- **`inits` on the cells `X`** = `Λ(prefix)`: an array's prefixes are each a proper prefix of the longer ones, so
`Λ`'s ascending cell holds them by increasing length, `[]` first, each once. `prefix` is a `comp` answer, so
canonical (`Tab.comp_canon`): `lamOf`, no second `canon`. -/
def inits {n : USize} (X : Vals (.arr B) n) : Except String (Tab (.arr B) (.arr (.arr B))) := do
  lamOf X (← «prefix» X)

/-- **`tails` on the cells `X`** = `Λ(cat°) ≫ F(π₂)`: `Λ`'s ascending cell holds an array's splits by their first
part, so by increasing split point, and `F(π₂)` on that cell is its payload's second column, the bounds kept: the
suffixes by decreasing length, `[]` last. One row per key, so no `canon`; `uncat` is a `canon` answer
(`Tab.uncat_canonical`), so `lamOf`, no `canon` before `Λ` either. -/
def tails {n : USize} (X : Vals (.arr B) n) : Except String (Tab (.arr B) (.arr (.arr B))) := do
  let L ← lamOf X (← uncat X)
  match L.val with
  | ⟨m, lo, hi, f⟩ => pure ⟨L.n, L.key, ⟨m, lo, hi, f.2⟩⟩


/-- **`sum` on the cells `X` of the atom `u`** (`rowDens`: the left fold `⦇[0, plus]⦈`, `stepAt u add` from the word
`0`, q's order): the elements EXPANDed into `(G, u)`, a segment opened at each cell's first element (`u = 0`), and
`sumTail` (`sumsOn`'s) is each element's prefix sum in its cell and its bad word. A cell with a bad element
(`kscatter .or`) is dropped (`Tab.keep`); the others read the sum at their last element (`kscatter .last`, `0` at an
empty cell). -/
def sumOn {u : QAtomicType} {n : USize} (X : Vals (.arr (.atom u)) n) :
    Except String (Tab (.arr (.atom u)) (.atom u)) :=
  match X with
  | ⟨m, lo, hi, f⟩ => do
    if 2 ^ 63 ≤ n.toNat * m.toNat + n.toNat + m.toNat then throw s!"sum: {n} cells over {m} elements past 2^63"
    let w ← colMap .sub n hi.enc lo.enc
    let (T, G, i) ← expand n w
    let v ← kgather T (← colMap .add T (← kgather T G n lo.enc) i) m (Arr.enc (t := u) f)
    let seg ← colMap .first T i i .i64 .i64 [] [(.eq, 0)]
    let (W, bad) ← sumTail "sum" u T seg v
    let badC ← kscatter .or T G bad n 0
    let L ← kscatter .last T G W.enc n 0
    canon (← keep (⟨n, ⟨m, lo, hi, f⟩, ← colArr .or n L L u⟩ : Tab (.arr (.atom u)) (.atom u))
      (← colMap .not n badC badC))

/-- `sum` at the element object `V`: `sumOn` at an atom, the error elsewhere. -/
def sum : {V : Obj} → {n : USize} → Vals (.arr V) n → Except String (Tab (.arr V) V)
  | .atom _, _, X => sumOn X
  | _, _, _ => throw "sum: the elements are no atom"

end Tab

end Rel
