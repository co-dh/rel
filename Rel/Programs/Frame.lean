import Rel.Programs.Prelude

/-! # The dataframe library, part 1 (`doc/dataframe-design.zh.typ` §2, §3.1): a frame is `x : ν ⟶ β`, positions to
    rows, and a verb whose result is a new frame is a position map `ι` followed by `x`. Every definition is generic
    in the position object `ν`; a new frame's positions are numbered by the row `asc` (one sort). -/

namespace Rel.Programs

open Rel.Programs.prelude in
rel_program frame where
    -- aggregation: `f` reads the image of `R` as an array of positions, ascending (Λ's order)
    agg(R : α ⟶ ν, f : [ν] ⟶ δ) : α ⟶ δ ≜ dom(R) ^(R) f
    -- `(dom(x) ⊤)°`, not `⊤ dom(x)`: at an unbounded `ν` the leaf `⊤ : 1 ⟶ ν` has no domain to run on
    summarize(f : [ν] ⟶ δ, x : ν ⟶ β) : 1 ⟶ δ ≜ agg((dom(x) ⊤)°, f)
    count(x : ν ⟶ β) : 1 ⟶ ν ≜ summarize(length, x)
    over(a : β ⟶ γ, f : [ν] ⟶ δ, x : ν ⟶ β) : ν ⟶ β×δ ≜ ⟨x, x a agg((x a)°, f)⟩

    -- row windows: `(<n)` keeps `hi`; `drop` moves `x`'s own positions down by `n` (`(+n)` on demand has no domain
    -- at an unbounded `ν`), keeping those `≥ n` since below 0 is a position there
    take(n : 1 ⟶ ν, x : ν ⟶ β) : ν ⟶ β ≜ dom(< n°) x
    drop(n : 1 ⟶ ν, x : ν ⟶ β) : ν ⟶ β ≜ (dom(x) dom(≥ n°) ⟨𝟙, ⊤ n⟩minus)° x
    range(a : 1 ⟶ ν, b : 1 ⟶ ν, x : ν ⟶ β) : ν ⟶ β ≜ take(⟨b, a⟩minus, drop(a, x))
    -- `dom(x)` before `asc`: a kept row's new position is one of `x`'s, the demand `asc` needs at an unbounded `ν`
    filterBy(p : β ⟶ β, x : ν ⟶ β) : ν ⟶ β ≜ dom(x) asc(dom(x p)) x
    -- `count − n` is negative when `n` exceeds the rows: `take` of it is empty; `takeLast` keeps what `dropLast`
    -- drops, since `i + n` or `count − n` may fall outside a declared object
    dropLast(n : 1 ⟶ ν, x : ν ⟶ β) : ν ⟶ β ≜ take(⟨count(x), n⟩minus, x)
    takeLast(n : 1 ⟶ ν, x : ν ⟶ β) : ν ⟶ β ≜ dom(x) asc(dom(x) − dom(dropLast(n, x))) x
    -- rolling window: `i = j + d`, `d < w`, written from the `j` side so no position below 0 is formed; the offsets
    -- `d` are `x`'s own positions below `w`, so m·w pairs are built, not the m²/2 of `≥ ∩ (j + w > i)`
    win(w : 1 ⟶ ν, x : ν ⟶ β) : ν ⟶ ν ≜ (dom(x) ⟨𝟙, ⊤ (dom(x) < w°)°⟩plus dom(x))°
    rolling(w : 1 ⟶ ν, f : [ν] ⟶ δ, x : ν ⟶ β) : ν ⟶ δ ≜ agg(win(w, x), f)
    -- cumulative aggregate (polars cum_sum, q's sums with `f` = sum): row `i` folds rows `j ≤ i`; m²/2 pairs
    cumAgg(f : [ν] ⟶ δ, x : ν ⟶ β) : ν ⟶ δ ≜ agg(dom(x) ≥ dom(x), f)
    -- q's `sums` within each group `g` (polars cum_sum().over(g)), linear: the row `sums` scans `(g(i), i)` in order
    sumsBy(g : ν ⟶ κ, c : ν ⟶ γ) : ν ⟶ γ ≜ ⟨g, 𝟙⟩ sums(⟨g, 𝟙⟩° c)
    -- `cumAgg(F(c) sum, c)` in m rows, not m²/2: one group
    cumSum(c : ν ⟶ γ) : ν ⟶ γ ≜ sumsBy(dom(c) ⊤ 𝟙(1), c)
    -- at each point of `D` the length of `R`'s image, 0 where it has none: a count lives in `R`'s position object `ν`,
    -- which `length` gives it, so a generic body's count needs no numeral put at an object variable
    counts(D : α ⟶ α, R : α ⟶ ν) : α ⟶ ν ≜ agg(R, length) ∪ ((D − dom(R)) ⊤ {(∗,0)})

    -- columns: `tot(R)` makes a partial column total, null where `R` has no value
    tot(R : α ⟶ β) : α ⟶ 1+β ≜ R inr ∪ ((𝟙 − dom(R)) ⊤ inl)
    -- the rows whose nullable column `c` holds a value, or holds the null
    filterJust(c : β ⟶ 1+γ, x : ν ⟶ β) : ν ⟶ β ≜ filterBy(dom(c inr°), x)
    filterNothing(c : β ⟶ 1+γ, x : ν ⟶ β) : ν ⟶ β ≜ filterBy(dom(c inl°), x)
    -- q's xprev: row `i` reads row `i − n`, null where there is none; `diff` subtracts it from row `i`
    shift(n : 1 ⟶ ν, x : ν ⟶ β) : ν ⟶ 1+β ≜ dom(x) tot(⟨𝟙, ⊤ n⟩minus x)
    diff(n : 1 ⟶ ν, x : ν ⟶ γ) : ν ⟶ 1+γ ≜ dom(x) tot(⟨x, ⟨𝟙, ⊤ n⟩minus x⟩minus)
    -- q's next, `n` rows ahead (polars shift(−n), q's `(−n) xprev`): `plus`, as `−n` is no element of a bounded `ν`
    next(n : 1 ⟶ ν, x : ν ⟶ β) : ν ⟶ 1+β ≜ dom(x) tot(⟨𝟙, ⊤ n⟩plus x)
    -- the first and last row, null on an empty frame (`head` of the ascending positions is the first)
    firstOrNothing(x : ν ⟶ β) : 1 ⟶ 1+β ≜ tot(summarize(head, x) x)
    lastOrNothing(x : ν ⟶ β) : 1 ⟶ 1+β ≜ tot(summarize(last, x) x)
    -- the null rows of the nullable column `c`
    nulls(c : β ⟶ 1+γ, x : ν ⟶ β) : 1 ⟶ ν ≜ count(filterNothing(c, x))
    -- q's fills: `r(i)` counts the valued rows `j ≤ i`, so `p` sends `i` to the valued row of equal count, the last
    -- one `≤ i`; at count 0 there is none and the null stays
    fills(c : ν ⟶ 1+γ) : ν ⟶ 1+γ ≜ (p ∪ (dom(c) − dom(p))) c where r ≜ cumSum(counts(dom(c), dom(c inr°))), p ≜ r (dom(c inr°) r)°
    -- `|||` (polars hstack, q's `,'`): the rows side by side, none unless both frames have the same length
    hstack(x : ν ⟶ β, y : ν ⟶ δ) : ν ⟶ β×δ ≜ dom(⟨x, y⟩ ⊤ count(x) count(y)°) ⟨x, y⟩
    applyWhere(p : β ⟶ β, e : β ⟶ β) : β ⟶ β ≜ (p e) ∪ (𝟙 − p)
    -- DataHaskell's function lifts (F7): the element function `f` is a Rel definition passed as a relation, never a
    -- host function, which would be a kernel outside the primitives; a partial `f` leaves its rows without an image
    lift(f : γ ⟶ δ, c : β ⟶ γ) : β ⟶ δ ≜ c f
    lift2(f : γ×δ ⟶ ε, a : β ⟶ γ, b : β ⟶ δ) : β ⟶ ε ≜ ⟨a, b⟩ f
    -- the frame form: column `a` replaced by `f` of it, in front of the columns `b` kept
    apply(f : γ ⟶ ε, a : β ⟶ γ, b : β ⟶ δ, x : ν ⟶ β) : ν ⟶ ε×δ ≜ x ⟨lift(f, a), b⟩
    -- on `1+X` the null passes: `bind`'s `f` may itself give the null, `nullLift`'s gives a value; `nullLift2` is
    -- the null where either column is
    bind(f : γ ⟶ 1+δ, c : β ⟶ 1+γ) : β ⟶ 1+δ ≜ c [inl, f]
    nullLift(f : γ ⟶ δ, c : β ⟶ 1+γ) : β ⟶ 1+δ ≜ bind(f inr, c)
    nullLift2(f : γ×δ ⟶ ε, a : β ⟶ 1+γ, b : β ⟶ 1+δ) : β ⟶ 1+ε ≜ (lift2(f, a inr°, b inr°) inr) ∪ ((dom(⟨a, b⟩) − dom(⟨a inr°, b inr°⟩)) ⊤ inl)
    contains(s : [α] ⟶ [α]) : [α] ⟶ [α] ≜ dom(suffix prefix s)
    -- q's `vs` at the separator `s` (a coreflexive, as `contains` takes it): a left fold appends each element to the
    -- last piece and cuts that piece where it ends in `s`; a fold, not `where` of the matches, because q keeps the
    -- leftmost non-overlapping ones, which only a left-to-right scan can pick (`"aba"` in `"ababa"` once)
    splitOn(s : [α] ⟶ [α]) : [α] ⟶ [[α]] ≜ ⦇[nil τ, a (e ∪ ((𝟙 − dom(e)) snoc))]⦈ where a ≜ ⟨π₁ init, ⟨π₁ last, π₂⟩snoc⟩, e ≜ (𝟙 × (cat° (𝟙 × s))) ⟨⟨π₁, π₂ π₁⟩snoc, nil⟩snoc
    -- a regex as its automaton, the cells some run from the start `q` ends in an accepting state of `A`: the fold's
    -- step is the transition relation `T` (a relation, so `T` may be an NFA); compiling a regex to `T` is outside
    match(T : σ×α ⟶ σ, q : 1 ⟶ σ, A : σ ⟶ σ) : [α] ⟶ [α] ≜ dom(⦇[q, T]⦈ A)
    -- each cell to each of its contiguous pieces (`suffix prefix`, as `contains` forms them) that `match` accepts
    matchAll(T : σ×α ⟶ σ, q : 1 ⟶ σ, A : σ ⟶ σ) : [α] ⟶ [α] ≜ suffix prefix match(T, q, A)

end Rel.Programs
