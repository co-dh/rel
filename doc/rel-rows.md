# Rel: the 28 rows of `prims` as terms (PLAN.md step 2.6)

Source: `rowCodes` (`Rel/Run/Lang/Compile.lean` 77-112), their meanings `rowDens` (`Rel/Lang/Den.lean` 201-239), the
prelude (`Rel/Programs/Prelude.lean`), at e78e922. Analysis only: no term below was type-checked or proved; each
equation is against the row's meaning in `rowDens`. Feeds Q5 of PLAN.md. Owner decision: the kept list primitive is
`snoc` (appending at the end uses an array's spare capacity; `cons` shifts every element), so `fold` eliminates the
algebra `[nil, snoc]`: a left fold, index 0 first, as `scan` runs. Today `foldDen` (`Den.lean:107-113`) and the
fold kernel (`Alg.foldRound`, `Run/Alg.lean:686-700`, element `k` from the end) are right folds over `[nil, cons]`.

## 1. Notation

One symbol per target constructor of `Tm` (`doc/rel-architecture.zh.typ` §2, after P3 removes the index `d` and
P4 changes the constructors). `≫` binds tighter than `∩`, `∪`, `−`.

| written                    | `Tm`                                                                          |
|----------------------------|-------------------------------------------------------------------------------|
| `R ≫ S`, `R°`, `𝟙`         | `comp`, `conv`, `id`                                                          |
| `R ∩ S`, `R ∪ S`, `R − S`  | `meet`, `join`, `diff`                                                        |
| `dom(R)`, `ran(R)`         | `dom`, `ran`                                                                  |
| `π₁`, `π₂`, `⟨R,S⟩`, `R×S` | `outl`, `outr`, `pair`, `prod`                                                |
| `nil`, `at(k)`, `E(R)`     | `nil`, `atPos k`, `E`                                                         |
| `succ`, `arith(add)`       | `succ`, `arith Ew.add`                                                        |
| `⦇e, S⦈`                   | `fold e S`: seed the coreflexive `e`, step `S : V×E ⟶ V` reading `(acc, x)`   |
| `hylo X. b`                | `hylo k what ch b`: `X` is variable `k`, `ch` the part of `b` before `X`      |
| `snoc`                     | `prim snocRow`, the one row kept (§3); `snoc° = unsnoc`                       |

Named parts, each a term in the constructors above:

```
e₀         = ran(nil)                                   -- the coreflexive on [A] holding []
z          = uni [0]                                    -- the coreflexive on long holding 0
τ°         = snoc° ≫ dom(π₁ ≫ e₀) ≫ π₂                  -- [a] ↦ a, written so it runs from the array
t          = dom(π₂ ≫ p)                                -- on V×A: the element passes p
m          = dom(π₁ ≫ ∋ ∩ π₂)                           -- on [A]×A: the element is in the array
rev        = ⦇e₀, ⟨π₂, π₁⟩ ≫ cons⦈                      -- the array reversed: needs cons
foldI(e,S) = (π₁ ≫ π₁° ∩ π₂ ≫ ⦇ran⟨𝟙, e ≫ π₂⟩, S ∩ π₁ ≫ π₁ ≫ π₁°⦈) ≫ π₂   -- 2.3, 4.3: S : (I×V)×E ⟶ I×V
initsS     = ⟨π₁, ⟨π₁ ≫ snoc° ≫ π₂, π₂⟩ ≫ snoc⟩ ≫ snoc  -- (yss,x) ↦ yss ++ [last yss ++ [x]]
twS(p)     = w ≫ ⟨⟨π₁ ≫ π₁, π₂⟩ ≫ snoc, π₁ ≫ π₂⟩ ∪ (𝟙 − w) ≫ ⟨π₁ ≫ π₁, ⟨π₁ ≫ π₂, π₂⟩ ≫ snoc⟩
             where w = dom(π₁ ≫ π₂ ≫ e₀) ≫ t        -- ((k,d),x): nothing dropped yet and x passes p
uncatS     = ⟨π₁ ≫ π₁, ⟨π₁ ≫ π₂, π₂⟩ ≫ snoc⟩ ∪ dom(π₁ ≫ π₂ ≫ e₀) ≫ ⟨⟨π₁ ≫ π₁, π₂⟩ ≫ snoc, nil⟩
             -- ((p,s),a) ↦ (p, s ++ [a]), and (p ++ [a], []) where s = []
zipS       = dom(π₁ ≫ π₂ ≫ e₀) ≫ π₁ ∪ ⟨⟨π₁ ≫ π₁, ⟨π₂, π₁ ≫ π₂ ≫ uncons ≫ π₁⟩⟩ ≫ snoc, π₁ ≫ π₂ ≫ uncons ≫ π₂⟩
             -- ((zs,ys),x) ↦ (zs ++ [(x, head ys)], tail ys), unchanged once ys = []
thinS(Q)   = dom(π₁ ≫ e₀) ≫ π₂ ≫ τ
           ∪ (snoc° × 𝟙) ≫ (q ≫ ⟨π₁ ≫ π₁, π₂⟩ ≫ snoc ∪ q' ≫ π₁ ≫ snoc ∪ (𝟙 − (q ∪ q')) ≫ ⟨π₁ ≫ snoc, π₂⟩ ≫ snoc)
             where q = dom(⟨π₂, π₁ ≫ π₂⟩ ≫ Q), q' = dom(⟨π₁ ≫ π₂, π₂⟩ ≫ Q)     -- on ((bs,b),x): x Q b, b Q x
mergeB(Q,X) = dom(π₁ ≫ e₀) ≫ π₂ ∪ dom(π₂ ≫ e₀) ≫ π₁
            ∪ r ≫ ⟨π₁ ≫ uncons ≫ π₁, ⟨π₁ ≫ uncons ≫ π₂, π₂⟩ ≫ X⟩ ≫ cons
            ∪ (𝟙 − r) ≫ ⟨π₂ ≫ uncons ≫ π₁, ⟨π₁, π₂ ≫ uncons ≫ π₂⟩ ≫ X⟩ ≫ cons
             where r = dom(⟨π₁ ≫ uncons ≫ π₁, π₂ ≫ uncons ≫ π₁⟩ ≫ Q)           -- the two heads pass Q
```

`Q` is the pair test `B×B ⟶ B×B` the rows `thinL`, `merge` take today. `thinS` reads the last kept element with
`snoc°`; `rev` on both sides of `thinL` makes that the head of the row's right fold.

## 2. The table

Verdict: `def` = the row's meaning is the definition; `def` alone = its `RowCode`, `rowDens` entry and `*_sound`
lemma go. `+ slice` = Q5 answered L: the row stays a fused kernel, its present code computing it without a round per
position, and the definition is its specification, tied to it by the theorem `⟦row⟧ = ⟦definition⟧` (§4).
`no slice` = its present code already runs a round per position, so nothing is lost by running the definition.

| #  | row            | equals                                                         | verdict                       |
|----|----------------|----------------------------------------------------------------|-------------------------------|
| 0  | `τ`            | `⟨nil, 𝟙⟩ ≫ snoc`                                              | def                           |
| 1  | `cons`         | `(τ × 𝟙) ≫ cat`                                                | def + slice                   |
| 2  | `∋`            | `⦇e₀, π₁ ∪ π₂ ≫ τ⦈ ≫ at(0)`                                    | def + slice                   |
| 3  | `inl`          | `Tm.inl`                                                       | constructor (4.1)             |
| 4  | `inr`          | `Tm.inr`                                                       | constructor (4.1)             |
| 5  | `F(R)`         | `⦇e₀, (𝟙 × R) ≫ snoc⦈`                                         | def + slice                   |
| 6  | `filter(p)`    | `⦇e₀, t ≫ snoc ∪ (𝟙 − t) ≫ π₁⦈`                                | def (prelude) + slice         |
| 7  | `takewhile(p)` | `⦇e₀ × e₀, twS(p)⦈ ≫ π₁`                                       | def (prelude) + slice         |
| 8  | `thinL(Q)`     | `rev ≫ ⦇e₀, thinS(Q)⦈ ≫ rev`                                   | def, no slice                 |
| 9  | `merge(Q)`     | `hylo X. mergeB(Q, X)`                                         | def, hylo (gap 4), no slice   |
| 10 | `loop(F)`      | `foldI(⟨𝟙, 𝟙⟩, ⟨π₁ ≫ π₁, (π₂ × 𝟙) ≫ F⟩)`                       | def, no slice                 |
| 11 | `uncons`       | `uncat ≫ (τ° × 𝟙)`  (`= cons°`)                                | def + slice                   |
| 12 | `length`       | `⦇z, π₁ ≫ succ⦈`                                               | def below 2⁶³ + slice         |
| 13 | `sum`          | `⦇z, arith(add)⦈`                                              | def on prefix sums + slice    |
| 14 | `inits`        | `⦇ran(nil ≫ τ), initsS⦈`                                       | def + slice                   |
| 15 | `tails`        | `rev ≫ inits ≫ F(rev) ≫ rev`                                   | def (prelude) + slice         |
| 16 | `prefix`       | `uncat ≫ π₁`                                                   | def (prelude) + slice         |
| 17 | `suffix`       | `⦇e₀, nil ∪ snoc⦈`                                             | def (prelude) + slice         |
| 18 | `concat`       | `⦇e₀, cat⦈`                                                    | def (prelude) + slice         |
| 19 | `cat`          | `loop(snoc)`                                                   | def + slice                   |
| 20 | `uncat`        | `⦇e₀ × e₀, uncatS⦈`  (`= cat°`)                                | def + slice                   |
| 21 | `zip`          | `⟨⟨nil, π₂⟩, π₁⟩ ≫ loop(zipS) ≫ π₁`                            | def + slice                   |
| 22 | `snoc`         | —                                                              | **primitive** (§3)            |
| 23 | `unsnoc`       | `snoc°`                                                        | `snoc` with `ran` known       |
| 24 | `setify`       | `E(𝟙)`                                                         | def; gap 3 → gap 5            |
| 25 | `distinct`     | `⦇e₀, m ≫ π₁ ∪ (𝟙 − m) ≫ snoc⦈`                                | def + order kernels           |
| 26 | `asc`          | `⟨𝟙, inits ≫ F(length)⟩ ≫ zip ≫ E(𝟙) ≫ F(π₁)` if `KeyInj`      | **primitive** (§3)            |
| 27 | `tic`          | `((τ ≫ τ) × 𝟙) ≫ loop(initsS)`                                 | def + slice                   |

Count: 2 primitive (`snoc`, `asc`), 2 become constructors (`inl`, `inr`), 1 is a primitive read the other way
(`unsnoc`), 23 are definitions: 21 by `fold` (`foldI`, `loop` included) and `snoc`, `setify` by `E`, `merge` by
`hylo`. `cons` is used only where a row builds or reads from the head: `rev` (so `thinL`, `tails`) and `merge`;
`uncons` (a forward definition through `uncat`) only in `zip` and `merge`.

Dependency order of the definitions (no cycle; each uses only names to its left): `snoc` → `τ`, `∋`, `F`, `filter`,
`takewhile`, `length`, `sum`, `suffix`, `distinct`, `inits`, `uncat`, `loop` → `prefix`, `uncons`, `cat`, `tic` →
`concat`, `zip`, `cons` → `rev`, `merge` → `thinL`, `tails`.

Changed shape against the `[nil, cons]` version: `loop` (no `rev`: its row is already a left fold), `cat = loop(snoc)`
(no swap), `tic` (a `loop`, no `cons`/`uncons`), `inits` (a fold, no `rev`), `tails` (now the `rev` form), `prefix`
and `suffix` (swap: `suffix` is the fold, `prefix` reads `uncat`), `zip` (a `loop`, no `hylo`), `distinct` (a fold,
no `loop`), `takewhile` (a second array), `thinL` (`rev` on both sides), `merge` (`uncons` on one side per branch).

Other forms of the same rows:
- `τ = Λ(𝟙)`, `inits = Λ(prefix)`: true because `Obj.lt` on `[A]` puts a prefix before its extensions
  (`Obj.key`, `Rel/ObjOrder.lean`), but both move a row with a lemma under gap 5.
- `zip = hylo X. (dom(π₁ ≫ e₀) ∪ dom(π₂ ≫ e₀)) ≫ nil ∪ (uncons × uncons) ≫ ⟨⟨π₁ ≫ π₁, π₂ ≫ π₁⟩, ⟨π₁ ≫ π₂, π₂ ≫
  π₂⟩ ≫ X⟩ ≫ cons`: the `[nil, cons]` table's form, now with `cons` and under gap 4.
- `merge` has no `fold` form found: it recurses on two arrays at once and which one shrinks depends on `Q`. A `hylo`
  on `(acc, (as, bs))` that appends with `snoc` drops `cons` but keeps `uncons`.
- `⦇e₀, thinS(Q)⦈` without `rev` is the left thin: each element against the last kept one, index 0 first. It is not
  the row: with `Q = {(a,b) : b = a+1}` on `[1,2,3]` the row gives `[1]`, the left thin `[1,3]`.
- `takewhile(p) = uncat ≫ (dom(F(p)) × (e₀ ∪ dom(uncons ≫ π₁ ≫ (𝟙 − p)))) ≫ π₁` for a coreflexive `p`: no second
  array, but `uncat` enumerates every split.

## 3. The rows that stay primitive

- **`snoc`** (with `unsnoc`). `nil` and `snoc` are the two halves of the algebra `[nil, snoc]` that `fold`
  eliminates; `nil` is a constructor of `Tm`, `snoc` is not, and every definition in §2 builds its arrays with it.
  `snoc` and not `cons`: appending at the end writes into the array's spare capacity, prepending moves every
  element. The other constructors with target `[B]` cannot replace it: `lam`, `E`, `thin` produce only the strictly
  ascending array of a set. Taking `cat` as the primitive instead (`snoc = (𝟙 × Λ(𝟙)) ≫ cat`) puts gap 5 under
  every row. `unsnoc` is not a second primitive: under the lazy `Rel`, `snoc` given `Known.ran` is `unsnoc`
  (`rep (f ⟨K,L⟩) = K ≫ R ≫ L`), so one `lazy` value serves `snoc` and `snoc°`. Proposal: `snoc` becomes a
  constructor of `Tm` beside `nil`, as 4.1 does for `inl`, `inr`, and rows 22, 23 go.
- **`asc`**. Two reasons. (a) Its meaning is `perm ≫ ordered(≤)` at the order `Obj.lt` of an arbitrary object, and
  `Tm` has that order as a term only at `long` (`leq`, `lt`); elsewhere it enters only through the canonical array
  of `lam`, `E`, `thin`. (b) The term in the table (tag each element with its position, canonicalise, drop the
  tags) is the stable sort; it equals the row only where `Obj.key` is injective (`KeyInj`, false at floats until
  R7), and below that it is `⊑` the row. It is also circular as code: `E` is computed by the `asc` kernel.
  `asc` stays a row, or becomes a constructor in the power group.

## 4. Findings for Q5 and for the later steps

- **Q5 answered L: every `+ slice` row stays a fused kernel.** `fold` runs one round per array position; the rows
  marked `+ slice` are computed today from `lo`/`hi` and one pass over the payload: `cons`, `∋`, `F`, `filter`,
  `takewhile`, `uncons`, `length`, `sum`, `inits`, `tails`, `prefix`, `suffix`, `concat`, `cat`, `uncat`, `zip`,
  `tic`. Each keeps its kernel; its definition is its specification, with the theorem `⟦row⟧ = ⟦definition⟧`.
  `Prim.prelude` already does this for six rows: the prelude's fold is the definition and the slice code runs in its
  place (`rep_tailsC`, `rep_prefixC`, …).
- **`thinL`, `merge`, `loop` lose nothing.** `thinLOnC`, `mergeOnC`, `loopOnC` run a round per position today
  (`doc/rel-avoid-cons.md` class Q), so their rows, codes and `*_sound` lemmas can go once the definitions run.
- **Direction.** Two row meanings are right folds today and do not follow from a left fold by reordering the step:
  `thinLDen` (`Rel/CRelFold.lean:450-465`, the chain from the end), hence the `rev` on both sides of `thinL`; and
  `sum`'s side condition, stated on suffix sums (`List.drop t`) where `⦇z, arith(add)⦈` checks prefix sums
  (`[2⁶², 2⁶², −2⁶²]` passes the row and overflows the fold). `sum`'s meaning moves to `List.take t`.
- **Converses.** `uncat = cat°` and `uncons = cons°` hold as meanings, but `conv` of a derived term has no table when
  only its `ran` is known, so `uncat` and `uncons` get the forward definitions of the table and the equations
  become rewrite lemmas `⟦uncat⟧ρ = ⟦cat°⟧ρ`. They replace `Prim.conv` (`convTm`). Only `snoc°` is used as a
  converse of an on-demand term in §2.
- **Gaps move.** `merge` (as `hylo`) has a lemma today and would wait for `den_local` (5.3); `zip` avoids it through
  `loop`. `setify = E(𝟙)` is `EDen 𝟙 = lamDen (∋ ≫ 𝟙)`, the row's meaning verbatim: its row gap (5.2) becomes
  `E_sound` (5.4b), one proof instead of two.
- **`length`.** The row is `Int64.ofNat xs.length`, which wraps; `succ` (`intStep add`) stops at the null
  `Int64.minValue`. The two differ on arrays of 2⁶³ elements or more, which no `Vals` holds; the equation needs
  that bound as a hypothesis.
- **`succ`, `arith` universes.** Today both take a universe `U`; the rows `length`, `sum` have none. The equations
  hold with the lazy `succ`, `arith` (bounded by `Known`), not with today's `succ(U)`.
- **`distinct` the row is not `distinct` the kernel.** The row keeps first occurrences of an unsorted array
  (`List.eraseDups`); the target kernel returns the first row of each group of a sorted input. The row's fused form
  is `asc` on (array, value, position) → kernel `distinct` → `asc` by position.
- **Polarity.** `thinL`, `merge` have `mono := false`; as definitions `Q` sits under `−` (`𝟙 − q`), so `Tm.pol`
  derives the same answer (R11).
- **Needs P3.** `snoc° × 𝟙`, `uncons` inside a step (`prod`, `conv` on on-demand terms) and `𝟙 − t` (`diff` from
  `𝟙`) do not type-check under the index `d`; `foldI` as a definition needs 4.3. No row can change before those.
- **Indices.** Deleting rows shifts `rows`' indices 0-27 (`Rows.lean`) and `Calc.toTerm`'s readings (R9); each
  deleted row with `aop := .ok _` needs its reading moved to the definition's name.
