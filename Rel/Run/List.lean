import Rel.Run.SetOps
import Rel.Run.Comp
import Rel.Run.Struct
import Rel.Run.Div
import Rel.Run.Fix

/-! The list rows of `prims` (`Rel/Lang/Den.lean`, `rowDens`) on `Tab`, as compositions of the five kernels (PLAN 6.14
W3, step T7), in the style of `Rel/Run/Comp.lean`: `snoc`, `cat`, `cons`, `zip` after a table of pairs of cells, and
`sum`, `uncons`, `unsnoc`, `uncat` on the cells `X` a context gives (as the old `RowCode.*` run them).

One composition builds every new cell: `Vals.cat`, the cell `X[i] ++ Y[i]` of two `arr` sides — the payloads joined
(`Vals.concat`), EXPAND (`expand`) of the summed widths, and each output element `kgather`ed from the first slice or
the second. `snoc` is `cat` after `𝟙 × τ` (`Vals.tau`, the one-element cells over a side's own rows), `cons` after
`τ × 𝟙`, as the old `snocC`; `zip` reads both slices at one offset. The converses build no payload: each answer cell
is a slice `[lo, hi)` of the input's own payload. No column is decoded or re-encoded. -/

namespace Rel
open Rel.Ext Rel.Kernel Rel.Verify

/-- The bounds `[s, e)` of `n` cells `[lo, hi)` clamped to a payload of `m` rows, as `Vals.row` reads a cell:
`s = max lo 0`, `e = max (min hi m) s`, so the width `e - s` is never negative. -/
def cellSpan {n : USize} (m : USize) (lo hi : Arr .i64 n) : Except String (Arr .i64 n × Arr .i64 n) := do
  let s ← colArr .max n lo.enc (← colConst n 0)
  pure (s, ← colArr .max n (← colMap .min n hi.enc (← colConst n m.toUInt64)) s.enc)

/-- `n` cells of the widths `w`, laid out one after another over the payload `pay`: `hi` the running sum of `w`
(`colPrefix .add`, the layout `expand` places its groups by), `lo = hi - w`. -/
def Vals.cells {B : Obj} {T : USize} (n : USize) (w : Enc) (pay : Vals B T) : Except String (Vals (.arr B) n) := do
  let P ← colPrefix .add n w
  pure ⟨T, ← colArr .sub n P w, ← colArr .add n P (← colConst n 0), pay⟩

/-- **`τ` on the rows of `x`**: row `i` the one-element cell `[i, i + 1)` over `x` itself. -/
def Vals.tau {B : Obj} {n : USize} (x : Vals B n) : Except String (Vals (.arr B) n) := do
  pure ⟨n, ← Arr.pos n, ← colArr .add n .pos (← colConst n 1), x⟩

/-- **Row `i` the cell `X[i] ++ Y[i]`**: the payloads `f₁`, `f₂` joined (`Vals.concat`, `f₂` from `m₁` on), the
widths `w₁ + w₂` EXPANDed into `(G, u)`, and output element `u` of cell `G` read at `s₁[G] + u` where `u < w₁`, else
at `m₁ + s₂[G] + u - w₁` (`b + c · (a - b)`, `c` the `0`/`1` test `u < w₁`). -/
def Vals.cat {B : Obj} {n : USize} (X Y : Vals (.arr B) n) : Except String (Vals (.arr B) n) :=
  match X, Y with
  | ⟨m₁, lo₁, hi₁, f₁⟩, ⟨m₂, lo₂, hi₂, f₂⟩ => do
    -- `.lt`, `.sub` and the prefix sums read positions and widths signed: each is below `n * (m₁ + m₂) + n + m₁ + m₂`
    if 2 ^ 63 ≤ n.toNat * (m₁.toNat + m₂.toNat) + n.toNat + m₁.toNat + m₂.toNat then
      throw s!"cat: {n} cells over {m₁} + {m₂} elements past 2^63"
    let (N, off) ← catPlan m₁ m₂
    let F ← Vals.concat N off f₁ f₂
    let (s₁, e₁) ← cellSpan m₁ lo₁ hi₁
    let (s₂, e₂) ← cellSpan m₂ lo₂ hi₂
    let w₁ ← colMap .sub n e₁.enc s₁.enc
    let w ← colMap .add n w₁ (← colMap .sub n e₂.enc s₂.enc)
    let (T, G, u) ← expand n w
    let a ← colMap .add T (← kgather T G n s₁.enc) u
    let d ← colMap .sub n (← colMap .add n s₂.enc (← colConst n m₁.toUInt64)) w₁
    let b ← colMap .add T (← kgather T G n d) u
    let c ← colMap .lt T u (← kgather T G n w₁)
    Vals.cells n w (← Vals.gather T (← colMap .add T b (← colMap .mul T c (← colMap .sub T a b))) F)

/-- **Row `i` the cell `zip X[i] Y[i]`**: the widths `min w₁ w₂` EXPANDed into `(G, u)`, output element `u` of cell
`G` the pair of `X`'s payload at `s₁[G] + u` and `Y`'s at `s₂[G] + u`. -/
def Vals.zip {A B : Obj} {n : USize} (X : Vals (.arr A) n) (Y : Vals (.arr B) n) :
    Except String (Vals (.arr (.prod A B)) n) :=
  match X, Y with
  | ⟨m₁, lo₁, hi₁, f₁⟩, ⟨m₂, lo₂, hi₂, f₂⟩ => do
    if 2 ^ 63 ≤ n.toNat * (m₁.toNat + m₂.toNat) + n.toNat + m₁.toNat + m₂.toNat then
      throw s!"zip: {n} cells over {m₁} + {m₂} elements past 2^63"
    let (s₁, e₁) ← cellSpan m₁ lo₁ hi₁
    let (s₂, e₂) ← cellSpan m₂ lo₂ hi₂
    let w ← colMap .min n (← colMap .sub n e₁.enc s₁.enc) (← colMap .sub n e₂.enc s₂.enc)
    let (T, G, u) ← expand n w
    let x ← Vals.gather T (← colMap .add T (← kgather T G n s₁.enc) u) f₁
    let y ← Vals.gather T (← colMap .add T (← kgather T G n s₂.enc) u) f₂
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
    let (s, e) ← cellSpan m lo hi
    let (M, sel) ← whereCol n (← colMap .lt n s.enc e.enc)
    let sM ← Arr.gather M sel s
    canon ⟨M, ← Vals.gather (A := .arr B) M sel ⟨m, lo, hi, f⟩,
      (← Vals.gather M sM.enc f, ⟨m, ← colArr .add M sM.enc (← colConst M 1), ← Arr.gather M sel e, f⟩)⟩

/-- **`snoc°` on the cells `X`**: each non-empty cell `[s, e)` to the slice `[s, e - 1)` and its last element (the
payload at `e - 1`). -/
def unsnoc {n : USize} (X : Vals (.arr B) n) : Except String (Tab (.arr B) (.prod (.arr B) B)) :=
  match X with
  | ⟨m, lo, hi, f⟩ => do
    if 2 ^ 63 ≤ n.toNat + m.toNat + 1 then throw s!"unsnoc: {n} cells over {m} elements past 2^63"
    let (s, e) ← cellSpan m lo hi
    let (M, sel) ← whereCol n (← colMap .lt n s.enc e.enc)
    let l ← colArr .sub M (← Arr.gather M sel e).enc (← colConst M 1)
    canon ⟨M, ← Vals.gather (A := .arr B) M sel ⟨m, lo, hi, f⟩,
      (⟨m, ← Arr.gather M sel s, l, f⟩, ← Vals.gather M l.enc f)⟩

/-- **`cat°` on the cells `X`**: each cell `[s, e)` to its `e - s + 1` splits, EXPAND of those counts into `(G, u)`,
split `u` of cell `G` the slices `[s, s + u)` and `[s + u, e)`. -/
def uncat {n : USize} (X : Vals (.arr B) n) : Except String (Tab (.arr B) (.prod (.arr B) (.arr B))) :=
  match X with
  | ⟨m, lo, hi, f⟩ => do
    if 2 ^ 63 ≤ n.toNat * (m.toNat + 1) + n.toNat + m.toNat + 1 then
      throw s!"uncat: {n} cells over {m} elements past 2^63"
    let (s, e) ← cellSpan m lo hi
    let (T, G, u) ← expand n (← colMap .add n (← colMap .sub n e.enc s.enc) (← colConst n 1))
    let sG ← Arr.gather T G s
    let mid ← colArr .add T sG.enc u
    canon ⟨T, ← Vals.gather (A := .arr B) T G ⟨m, lo, hi, f⟩, (⟨m, sG, mid, f⟩, ⟨m, mid, ← Arr.gather T G e, f⟩)⟩

/-- **`prefix` on the cells `X`**: the prelude's `cat° π₁`, `uncat` then `outl` on its splits. -/
def «prefix» {n : USize} (X : Vals (.arr B) n) : Except String (Tab (.arr B) (.arr B)) := do
  let u ← uncat X; u.comp (← outl u.val)

/-- **`suffix` on the cells `X`**: the prelude's `cat° π₂`, `uncat` then `outr` on its splits. -/
def suffix {n : USize} (X : Vals (.arr B) n) : Except String (Tab (.arr B) (.arr B)) := do
  let u ← uncat X; u.comp (← outr u.val)

/-- **`inits` on the cells `X`** = `Λ(prefix)`: an array's prefixes are each a proper prefix of the longer ones, so
`Λ`'s ascending cell holds them by increasing length, `[]` first, each once. -/
def inits {n : USize} (X : Vals (.arr B) n) : Except String (Tab (.arr B) (.arr (.arr B))) := do
  lam X (← «prefix» X)

/-- **`tails` on the cells `X`** = `Λ(cat°) ≫ F(π₂)`: `Λ`'s ascending cell holds an array's splits by their first
part, so by increasing split point, and `F(π₂)` on that cell is its payload's second column, the bounds kept: the
suffixes by decreasing length, `[]` last. One row per key, so no `canon`. -/
def tails {n : USize} (X : Vals (.arr B) n) : Except String (Tab (.arr B) (.arr (.arr B))) := do
  let L ← lam X (← uncat X)
  match L.val with
  | ⟨m, lo, hi, f⟩ => pure ⟨L.n, L.key, ⟨m, lo, hi, f.2⟩⟩

/-- Round `k` of a left fold (`foldRounds`): `cons°` of what is left of each array, its head read now. -/
def peelL {E : Obj} (rest : Tab K (.arr E)) : Except String (Tab K E × Tab K (.arr E)) := do
  let c ← rest.comp (← uncons rest.val)
  pure (← c.comp (← outl c.val), ← c.comp (← outr c.val))
/-- Round `k` of a right fold: `snoc°`, its last element read now. -/
def peelR {E : Obj} (rest : Tab K (.arr E)) : Except String (Tab K E × Tab K (.arr E)) := do
  let c ← rest.comp (← unsnoc rest.val)
  pure (← c.comp (← outr c.val), ← c.comp (← outl c.val))

/-- **`concat` on the cells of cells `X`** = `⦇nil, cat⦈` (the prelude's `concat`, B&dM p.129): the rounds of a left
fold from `[]`, each `(acc, xs) ↦ acc ++ xs`. -/
def flatten {n : USize} (X : Vals (.arr (.arr B)) n) : Except String (Tab (.arr (.arr B)) (.arr B)) := do
  foldRounds peelL (fun acc el => do cat (← acc.pair el)) (X.1.toNat + 2) (← idU X) (← nil X) (← zero)

/-- **`filter(p)` on the cells `X`**, `P` the relation `p` = `⦇nil, dom(π₂p) snoc ∪ (𝟙 − dom(π₂p)) π₁⦈` (the prelude's
`filter`, B&dM p.66): a left fold, `x` appended where it is a key of `P` (`k = el ≫ dom P`), else `acc` kept. -/
def filter {n : USize} (P : Tab B B) (X : Vals (.arr B) n) : Except String (Tab (.arr B) (.arr B)) := do
  let D ← P.dom
  foldRounds peelL (fun acc el => do
      let k ← el.comp D
      (← snoc (← acc.pair k)).union (← acc.diff (← (← k.dom).comp acc)))
    (X.1.toNat + 2) (← idU X) (← nil X) (← zero)

/-- **`takewhile(p)` on the cells `X`**, `P` the relation `p` = `⦇nil, dom(π₁p) cons ∪ (𝟙 − dom(π₁p)) nil⦈ʳ` (the
prelude's `takewhile`, B&dM p.174): a right fold, `x :: acc` where `x` is a key of `P`, else `[]`. -/
def takewhile {n : USize} (P : Tab B B) (X : Vals (.arr B) n) : Except String (Tab (.arr B) (.arr B)) := do
  let D ← P.dom
  foldRounds peelR (fun acc el => do
      let k ← el.comp D
      (← cons (← k.pair acc)).union (← (← acc.diff (← (← k.dom).comp acc)).comp (← nil acc.val)))
    (X.1.toNat + 2) (← idU X) (← nil X) (← zero)

/-- **`sum` on the cells of longs `X`** (`rowDens`: `foldr (+) 0`, kept where every suffix sum lies strictly inside
`(-2^63, 2^63)` and no element is the null `-2^63`): the elements EXPANDed into `(G, u)`, the suffix sums `W` of each
cell by a backward `kscan .add` whose segments start at each cell's last element, and an element bad where it or `W`
is the null or `W = v + W'` overflowed (`v` and `W'` of one sign, `W` of the other: the first overflow from the right
is caught, every sum right of it being exact). A cell with a bad element (`kscatter .or`) is dropped (`Tab.keep`);
the others read their wrapped total (`kscatter .add`), which is the exact one. -/
def sum {n : USize} (X : Vals (.arr .long) n) : Except String (Tab (.arr .long) .long) :=
  match X with
  | ⟨m, lo, hi, f⟩ => do
    if 2 ^ 63 ≤ n.toNat * m.toNat + n.toNat + m.toNat then throw s!"sum: {n} cells over {m} elements past 2^63"
    let (s, e) ← cellSpan m lo hi
    let w ← colMap .sub n e.enc s.enc
    let (T, G, u) ← expand n w
    let v ← kgather T (← colMap .add T (← kgather T G n s.enc) u) m f.enc
    let z ← colConst T 0
    let last ← colMap .eq T u (← colMap .sub T (← kgather T G n w) (← colConst T 1))
    let W := (← kscan .add true .i64 .i64 T last [z, v]).1
    let sv ← colMap .lt T v z
    let ovf ← colMap .and T (← colMap .eq T sv (← colMap .lt T (← colMap .sub T W v) z)) (← colMap .ne T sv
      (← colMap .lt T W z))
    let nul ← colConst T 0x8000000000000000
    let bad ← colMap .or T ovf (← colMap .or T (← colMap .eq T W nul) (← colMap .eq T v nul))
    let badC ← kscatter .or T G bad n 0
    let tot ← colArr .add n (← kscatter .add T G v n 0) (← colConst n 0)
    canon (← keep (⟨n, ⟨m, lo, hi, f⟩, tot⟩ : Tab (.arr .long) .long) (← colMap .not n badC badC))

end Tab

end Rel
