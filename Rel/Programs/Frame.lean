import Rel.Programs.Prelude

/-! # The dataframe library, part 1 (`doc/dataframe-design.zh.typ` §2, §3.1): a frame is `x : ν ⟶ β`, positions to
    rows, and a verb whose result is a new frame is a position map `ι` followed by `x`. Every definition is generic
    in the position object `ν`; a new frame's positions are numbered by the row `asc` (one sort). -/

namespace Rel.Programs

open Rel.Programs.prelude in
rel_program frame where
    -- aggregation: `f` reads the image of `R` as an array of positions, ascending (Λ's order)
    agg(R : α ⟶ ν, f : [ν] ⟶ δ) : α ⟶ δ ≜ dom(R) Λ(R) f
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
    tot(R : α ⟶ β) : α ⟶ β+1 ≜ R inl ∪ ((𝟙 − dom(R)) ⊤ inr)
    -- the rows whose nullable column `c` holds a value, or holds the null
    filterJust(c : β ⟶ γ+1, x : ν ⟶ β) : ν ⟶ β ≜ filterBy(dom(c inl°), x)
    filterNothing(c : β ⟶ γ+1, x : ν ⟶ β) : ν ⟶ β ≜ filterBy(dom(c inr°), x)
    -- q's xprev: row `i` reads row `i − n`, null where there is none; `diff` subtracts it from row `i`
    shift(n : 1 ⟶ ν, x : ν ⟶ β) : ν ⟶ β+1 ≜ dom(x) tot(⟨𝟙, ⊤ n⟩minus x)
    diff(n : 1 ⟶ ν, x : ν ⟶ γ) : ν ⟶ γ+1 ≜ dom(x) tot(⟨x, ⟨𝟙, ⊤ n⟩minus x⟩minus)
    -- q's next, `n` rows ahead (polars shift(−n), q's `(−n) xprev`): `plus`, as `−n` is no element of a bounded `ν`
    next(n : 1 ⟶ ν, x : ν ⟶ β) : ν ⟶ β+1 ≜ dom(x) tot(⟨𝟙, ⊤ n⟩plus x)
    -- the first and last row, null on an empty frame (`head` of the ascending positions is the first)
    firstOrNothing(x : ν ⟶ β) : 1 ⟶ β+1 ≜ tot(summarize(head, x) x)
    lastOrNothing(x : ν ⟶ β) : 1 ⟶ β+1 ≜ tot(summarize(last, x) x)
    -- the null rows of the nullable column `c`
    nulls(c : β ⟶ γ+1, x : ν ⟶ β) : 1 ⟶ ν ≜ count(filterNothing(c, x))
    -- q's fills: `r(i)` counts the valued rows `j ≤ i`, so `p` sends `i` to the valued row of equal count, the last
    -- one `≤ i`; at count 0 there is none and the null stays
    fills(c : ν ⟶ γ+1) : ν ⟶ γ+1 ≜ (p ∪ (dom(c) − dom(p))) c where r ≜ cumSum(counts(dom(c), dom(c inl°))), p ≜ r (dom(c inl°) r)°
    -- describe, its exact part: count, min, max of a column (the mean needs float `sum` and `div`)
    describe(c : ν ⟶ γ) : 1 ⟶ ν×(γ×γ) ≜ ⟨count(c), ⟨summarize(F(c) Λ(∋) head, c), summarize(F(c) Λ(∋) last, c)⟩⟩
    -- `|||` (polars hstack, q's `,'`): the rows side by side, none unless both frames have the same length
    hstack(x : ν ⟶ β, y : ν ⟶ δ) : ν ⟶ β×δ ≜ dom(⟨x, y⟩ ⊤ count(x) count(y)°) ⟨x, y⟩
    applyWhere(p : β ⟶ β, e : β ⟶ β) : β ⟶ β ≜ (p e) ∪ (𝟙 − p)
    contains(s : [α] ⟶ [α]) : [α] ⟶ [α] ≜ dom(suffix prefix s)

end Rel.Programs
