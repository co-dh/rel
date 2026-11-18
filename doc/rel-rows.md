# Rel: the 28 rows of `prims` as terms (PLAN.md step 2.6)

Source: `rowCodes` (`Rel/Run/Lang/Compile.lean` 77-112), their meanings `rowDens` (`Rel/Lang/Den.lean` 201-239), the
prelude (`Rel/Programs/Prelude.lean`), at e78e922. Analysis only: no term below was type-checked or proved; each
equation is against the row's meaning in `rowDens`. Feeds Q5 of PLAN.md. Owner rules:
- **Build only by appending.** The kept list primitive is `snoc` (appending uses the array's spare capacity; `cons`
  shifts every element). No row term builds an array with `cons` or reverses one (`rev`).
- **Read left to right where the meaning allows, right to left only where it needs it.** `fold` is the left fold
  over `[nil, snoc]` (index 0 first, as `scan` runs); the right fold (input read from the end) stays for the rows
  whose meaning is a right-to-left process: `sum` and `thinL` (§4 Direction). Reading either way is a slice
  (`uncons`, `unsnoc`), so it costs nothing; what a reading order changes is the meaning.

Today `foldDen` (`Den.lean:107-113`) and the fold kernel (`Alg.foldRound`, `Run/Alg.lean:686-700`, element `k`
from the end) are the right fold only.

## 1. Notation

One symbol per target constructor of `Tm` (`doc/rel-architecture.zh.typ` §2, after P3 removes the index `d` and
P4 changes the constructors). `≫` binds tighter than `∩`, `∪`, `−`.

| written                    | `Tm`                                                                               |
|----------------------------|------------------------------------------------------------------------------------|
| `R ≫ S`, `R°`, `𝟙`         | `comp`, `conv`, `id`                                                               |
| `R ∩ S`, `R ∪ S`, `R − S`  | `meet`, `join`, `diff`                                                             |
| `dom(R)`, `ran(R)`         | `dom`, `ran`                                                                       |
| `π₁`, `π₂`, `⟨R,S⟩`, `R×S` | `outl`, `outr`, `pair`, `prod`                                                     |
| `nil`, `at(k)`, `E(R)`     | `nil`, `atPos k`, `E`                                                              |
| `succ`, `arith(add)`, `⊤`  | `succ`, `arith Ew.add`, `top`                                                      |
| `⦇e, S⦈`                   | `fold e S`: left fold, index 0 first; seed the coreflexive `e`, step `S : V×E ⟶ V` |
|                            | reading `(acc, x)`                                                                 |
| `⦇e, S⦈ʳ`                  | `foldr e S` (today's `fold`): right fold, index `n−1` first; step `S : E×V ⟶ V`    |
|                            | reading `(x, acc)`                                                                 |
| `hylo X. b`                | `hylo k what ch b`: `X` is variable `k`, `ch` the part of `b` before `X`           |
| `snoc`                     | `prim snocRow`, the one row kept (§3); `snoc° = unsnoc`                            |

Named parts, each a term in the constructors above:

```
e₀         = ran(nil)                                   -- the coreflexive on [A] holding []
z          = uni [0]                                    -- the coreflexive on long holding 0
cᵢ         = ⊤ ≫ uni [i]                                -- the constant i : long (i = 0, 1, 2)
τ°         = snoc° ≫ dom(π₁ ≫ e₀) ≫ π₂                  -- [a] ↦ a, written so it runs from the array
t          = dom(π₂ ≫ p)                                -- on V×A: the element passes p
m          = dom(π₁ ≫ ∋ ∩ π₂)                           -- on [A]×A: the element is in the array
foldI(e,S) = (π₁ ≫ π₁° ∩ π₂ ≫ ⦇ran⟨𝟙, e ≫ π₂⟩, S ∩ π₁ ≫ π₁ ≫ π₁°⦈) ≫ π₂   -- 2.3, 4.3: S : (I×V)×E ⟶ I×V
initsS     = ⟨π₁, ⟨π₁ ≫ snoc° ≫ π₂, π₂⟩ ≫ snoc⟩ ≫ snoc  -- (yss,x) ↦ yss ++ [last yss ++ [x]]
tailsS     = ⟨⟨π₁ ≫ π₁, π₁ ≫ π₂⟩ ≫ snoc, π₁ ≫ π₂ ≫ uncons ≫ π₂⟩
             -- ((yss,r),x) ↦ (yss ++ [r], tail r): r is the input from x on, a slice
twS(p)     = w ≫ ⟨⟨π₁ ≫ π₁, π₂⟩ ≫ snoc, π₁ ≫ π₂⟩ ∪ (𝟙 − w) ≫ ⟨π₁ ≫ π₁, ⟨π₁ ≫ π₂, π₂⟩ ≫ snoc⟩
             where w = dom(π₁ ≫ π₂ ≫ e₀) ≫ t        -- ((k,d),x): nothing dropped yet and x passes p
uncatS     = ⟨π₁ ≫ π₁, ⟨π₁ ≫ π₂, π₂⟩ ≫ snoc⟩ ∪ dom(π₁ ≫ π₂ ≫ e₀) ≫ ⟨⟨π₁ ≫ π₁, π₂⟩ ≫ snoc, nil⟩
             -- ((p,s),a) ↦ (p, s ++ [a]), and (p ++ [a], []) where s = []
zipS       = dom(π₁ ≫ π₂ ≫ e₀) ≫ π₁ ∪ ⟨⟨π₁ ≫ π₁, ⟨π₂, π₁ ≫ π₂ ≫ uncons ≫ π₁⟩⟩ ≫ snoc, π₁ ≫ π₂ ≫ uncons ≫ π₂⟩
             -- ((zs,ys),x) ↦ (zs ++ [(x, head ys)], tail ys), unchanged once ys = []
thinA(Q)   = dom(π₂ ≫ π₁ ≫ e₀) ≫ ⟨π₁ ≫ τ, ⟨π₂ ≫ π₂, c₀⟩ ≫ snoc⟩
           ∪ (𝟙 × (τ° × 𝟙)) ≫ (q ≫ ⟨π₁ ≫ τ, ⟨π₂ ≫ π₂, c₁⟩ ≫ snoc⟩ ∪ q' ≫ ⟨π₂ ≫ π₁ ≫ τ, ⟨π₂ ≫ π₂, c₂⟩ ≫ snoc⟩
                                ∪ (𝟙 − (q ∪ q')) ≫ ⟨π₁ ≫ τ, ⟨π₂ ≫ π₂, c₀⟩ ≫ snoc⟩)
             where q = dom(⟨π₁, π₂ ≫ π₁⟩ ≫ Q), q' = dom(⟨π₂ ≫ π₁, π₁⟩ ≫ Q)     -- on (x,(b,as)): x Q b, b Q x
             -- (x,(h,as)): h = [b] the last element pushed, as the actions so far: 0 push, 1 replace b, 2 drop x
thinF(Q)   = ⦇e₀ × e₀, thinA(Q)⦈ʳ ≫ π₂                 -- the actions, the one of x[n−1] first
thinK      = d ≫ ⟨π₁ ≫ π₁, a'⟩ ∪ (𝟙 − d) ≫ ⟨⟨k ≫ ⟨π₁ ≫ π₁ ≫ π₁, π₂⟩ ≫ snoc ∪ (𝟙 − k) ≫ π₁ ≫ π₁ ≫ π₁, a⟩, a'⟩
             where a = π₁ ≫ π₂ ≫ snoc° ≫ π₂, a' = π₁ ≫ π₂ ≫ snoc° ≫ π₁,
                   d = dom(a ≫ uni [2]), k = dom(π₁ ≫ π₁ ≫ π₂ ≫ uni [0])
             -- (((o,c),as),x): a = x's action, the last of as; x is appended to o unless a drops it or the
             -- last non-drop action left of it (c) replaced it; c becomes a when a is not a drop
mergeB(Q,X) = dom(π₂ ≫ π₁ ≫ e₀) ≫ ⟨π₁, π₂ ≫ π₂⟩ ≫ cat ∪ dom(π₂ ≫ π₂ ≫ e₀) ≫ ⟨π₁, π₂ ≫ π₁⟩ ≫ cat
            ∪ r ≫ ⟨⟨π₁, π₂ ≫ π₁ ≫ uncons ≫ π₁⟩ ≫ snoc, ⟨π₂ ≫ π₁ ≫ uncons ≫ π₂, π₂ ≫ π₂⟩⟩ ≫ X
            ∪ (𝟙 − r) ≫ ⟨⟨π₁, π₂ ≫ π₂ ≫ uncons ≫ π₁⟩ ≫ snoc, ⟨π₂ ≫ π₁, π₂ ≫ π₂ ≫ uncons ≫ π₂⟩⟩ ≫ X
             where r = dom(⟨π₂ ≫ π₁ ≫ uncons ≫ π₁, π₂ ≫ π₂ ≫ uncons ≫ π₁⟩ ≫ Q)     -- (o,(as,bs)): heads pass Q
```

`Q` is the pair test `B×B ⟶ B×B` the rows `thinL`, `merge` take today. `thinL` is two passes: `thinF` reads the
input from the end, as the row's chain runs, and records each element's action by appending; `thinK` reads the
input from the start and those actions from their end (`snoc°`), and appends the elements kept. An element pushed
by `thinF` is removed only by the next element pushed to its left, which is why the keep decision needs the second
pass.

## 2. The table

Verdict: `def` = the row's meaning is the definition; `def` alone = its `RowCode`, `rowDens` entry and `*_sound`
lemma go. `+ slice` = Q5 answered L: the row stays a fused kernel, its present code computing it without a round per
position, and the definition is its specification, tied to it by the theorem `⟦row⟧ = ⟦definition⟧` (§4).
`no slice` = its present code already runs a round per position, so nothing is lost by running the definition.
Reads: `→` the input from index 0 up, `←` from the end (why: §4 Direction), `←, →` a pass each way; `—` no array
read by a fold.

| #  | row            | equals                                               | reads | verdict                      |
|----|----------------|------------------------------------------------------|-------|------------------------------|
| 0  | `τ`            | `⟨nil, 𝟙⟩ ≫ snoc`                                    | —     | def                          |
| 1  | `cons`         | `(τ × 𝟙) ≫ cat`                                      | →     | def + slice; only `cons°`    |
| 2  | `∋`            | `⦇e₀, π₁ ∪ π₂ ≫ τ⦈ ≫ at(0)`                          | →     | def + slice                  |
| 3  | `inl`          | `Tm.inl`                                             | —     | constructor (4.1)            |
| 4  | `inr`          | `Tm.inr`                                             | —     | constructor (4.1)            |
| 5  | `F(R)`         | `⦇e₀, (𝟙 × R) ≫ snoc⦈`                               | →     | def + slice                  |
| 6  | `filter(p)`    | `⦇e₀, t ≫ snoc ∪ (𝟙 − t) ≫ π₁⦈`                      | →     | def (prelude) + slice        |
| 7  | `takewhile(p)` | `⦇e₀ × e₀, twS(p)⦈ ≫ π₁`                             | →     | def (prelude) + slice        |
| 8  | `thinL(Q)`     | `⟨⟨⟨nil, c₀⟩, thinF(Q)⟩, 𝟙⟩ ≫ loop(thinK) ≫ π₁ ≫ π₁` | ←, →  | def, no slice                |
| 9  | `merge(Q)`     | `⟨nil, 𝟙⟩ ≫ hylo X. mergeB(Q, X)`                    | →     | def, hylo (gap 4), no slice  |
| 10 | `loop(F)`      | `foldI(⟨𝟙, 𝟙⟩, ⟨π₁ ≫ π₁, (π₂ × 𝟙) ≫ F⟩)`             | →     | def, no slice                |
| 11 | `uncons`       | `uncat ≫ (τ° × 𝟙)`  (`= cons°`)                      | →     | def + slice                  |
| 12 | `length`       | `⦇z, π₁ ≫ succ⦈`                                     | →     | def below 2⁶³ + slice        |
| 13 | `sum`          | `⦇z, arith(add)⦈ʳ`                                   | ←     | def + slice                  |
| 14 | `inits`        | `⦇ran(nil ≫ τ), initsS⦈`                             | →     | def + slice                  |
| 15 | `tails`        | `⟨⟨nil, 𝟙⟩, 𝟙⟩ ≫ loop(tailsS) ≫ snoc`                | →     | def (prelude) + slice        |
| 16 | `prefix`       | `uncat ≫ π₁`                                         | →     | def (prelude) + slice        |
| 17 | `suffix`       | `⦇e₀, nil ∪ snoc⦈`                                   | →     | def (prelude) + slice        |
| 18 | `concat`       | `⦇e₀, cat⦈`                                          | →     | def (prelude) + slice        |
| 19 | `cat`          | `loop(snoc)`                                         | →     | def + slice                  |
| 20 | `uncat`        | `⦇e₀ × e₀, uncatS⦈`  (`= cat°`)                      | →     | def + slice                  |
| 21 | `zip`          | `⟨⟨nil, π₂⟩, π₁⟩ ≫ loop(zipS) ≫ π₁`                  | →     | def + slice                  |
| 22 | `snoc`         | —                                                    | —     | **primitive** (§3)           |
| 23 | `unsnoc`       | `snoc°`                                              | —     | `snoc` with `ran` known      |
| 24 | `setify`       | `E(𝟙)`                                               | —     | def; gap 3 → gap 5           |
| 25 | `distinct`     | `⦇e₀, m ≫ π₁ ∪ (𝟙 − m) ≫ snoc⦈`                      | →     | def + order kernels          |
| 26 | `asc`          | `⟨𝟙, inits ≫ F(length)⟩ ≫ zip ≫ E(𝟙) ≫ F(π₁)`        | —     | **primitive** (§3, `KeyInj`) |
| 27 | `tic`          | `((τ ≫ τ) × 𝟙) ≫ loop(initsS)`                       | →     | def + slice                  |

Count: 2 primitive (`snoc`, `asc`), 2 become constructors (`inl`, `inr`), 1 is a primitive read the other way
(`unsnoc`), 23 are definitions: 21 by `fold` (`foldI`, `loop` included) and `snoc`, `setify` by `E`, `merge` by
`hylo`. No row builds an array with `cons` or reverses one. Right fold (`⦇ ⦈ʳ`): `sum`, and `thinL`'s first pass.
Read from the end by `snoc°` inside a step: `τ°`, `initsS`, and `thinK` (the actions `thinF` wrote last-first).
`uncons` (a forward definition through `uncat`) reads heads in `zip`, `tails`, `merge`.

Dependency order of the definitions (no cycle; each uses only names to its left): `snoc` → `τ`, `∋`, `F`, `filter`,
`takewhile`, `length`, `sum`, `suffix`, `distinct`, `inits`, `uncat`, `loop` → `prefix`, `uncons`, `cat`, `tic`,
`thinL` → `concat`, `zip`, `cons`, `tails`, `merge`.

Changed shape against the `[nil, cons]` version: `loop` (no `rev`: its row is already a left fold), `cat = loop(snoc)`
(no swap), `tic` (a `loop`, no `cons`/`uncons`), `inits` (a fold, no `rev`), `tails` (a `loop` carrying the rest of
the input), `prefix` and `suffix` (swap: `suffix` is the fold, `prefix` reads `uncat`), `zip` (a `loop`, no `hylo`),
`distinct` (a fold, no `loop`), `takewhile` (a second array), `thinL` (two passes, right then left), `merge` (an
accumulator appended to, the rest of the longer array `cat` onto it: tail recursive), `sum` (a right fold, step
`(x, acc)`).

Other forms of the same rows:
- `τ = Λ(𝟙)`, `inits = Λ(prefix)`: true because `Obj.lt` on `[A]` puts a prefix before its extensions
  (`Obj.key`, `Rel/ObjOrder.lean`), but both move a row with a lemma under gap 5.
- `merge` has no `fold` form found: it recurses on two arrays at once and which one shrinks depends on `Q`.
- `thinL` in one pass does not exist under the rules. The left thin `⦇e₀, S⦈` (each element against the last kept
  one, index 0 first) is not the row: with `Q = {(a,b) : b = a+1}` on `[1,2,3]` the row gives `[1]`, the left thin
  `[1,3]`. The right fold that appends what it keeps (replace = `snoc°` then `snoc`) keeps the row's elements but
  last index first: on `[1,3]` with the same `Q` it gives `[3,1]`, the row `[1,3]`.
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
  (`doc/rel-avoid-cons.md` class Q), so their rows, codes and `*_sound` lemmas can go once the definitions run;
  `thinL` runs two such passes where `thinLOnC` runs one.
- **Direction: every meaning is kept.** Two rows are right-to-left processes, and no left fold gives their meaning:
  - `thinL`: `thinLDen` (`Rel/CRelFold.lean:450-465`) is the chain from the end, each element tested against the
    head of the thinned rest to its right. Its first pass is the right fold `thinF`; its output is built by `thinK`
    from index 0 up, so the kept elements come out in index order with no `rev` and no prepend.
  - `sum`: the side condition of `rowDens` bounds the suffix sums (`List.drop t`), which are the right fold's
    partial results; a left fold's are the prefix sums, and `[2⁶², 2⁶², −2⁶²]` passes the row and overflows the
    left fold. So `sum` is the right fold and its meaning is unchanged. Its result is one value: nothing is built.
  `tails` and `merge` were written with `rev`/`cons` in the `[nil, cons]` version but are left-to-right processes:
  both read the input by `uncons` and append, meaning unchanged.
- **Converses.** `uncat = cat°` and `uncons = cons°` hold as meanings, but `conv` of a derived term has no table when
  only its `ran` is known, so `uncat` and `uncons` get the forward definitions of the table and the equations
  become rewrite lemmas `⟦uncat⟧ρ = ⟦cat°⟧ρ`. They replace `Prim.conv` (`convTm`). Only `snoc°` is used as a
  converse of an on-demand term in §2. `cons` survives only through `cons° = uncons`.
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
- **Polarity.** `thinL`, `merge` have `mono := false`; as definitions `Q` sits under `−` (`𝟙 − (q ∪ q')`, `𝟙 − r`),
  so `Tm.pol` derives the same answer (R11).
- **Needs P3.** `snoc° × 𝟙`, `uncons` inside a step (`prod`, `conv` on on-demand terms) and `𝟙 − t` (`diff` from
  `𝟙`) do not type-check under the index `d`; `foldI` as a definition needs 4.3, `⦇ ⦈ʳ` beside `⦇ ⦈` needs 4.5.
  No row can change before those.
- **Indices.** Deleting rows shifts `rows`' indices 0-27 (`Rows.lean`) and `Calc.toTerm`'s readings (R9); each
  deleted row with `aop := .ok _` needs its reading moved to the definition's name.
