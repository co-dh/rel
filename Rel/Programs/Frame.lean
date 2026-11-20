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
    -- rolling window: `j ≤ i < j + w`, written from the `j` side so no position below 0 is formed
    win(w : 1 ⟶ ν, x : ν ⟶ β) : ν ⟶ ν ≜ ≥ ∩ (dom(x) ⟨𝟙, ⊤ w⟩plus > dom(x))°
    rolling(w : 1 ⟶ ν, f : [ν] ⟶ δ, x : ν ⟶ β) : ν ⟶ δ ≜ agg(win(w, x), f)

    -- columns: `tot(R)` makes a partial column total, null where `R` has no value
    tot(R : α ⟶ β) : α ⟶ β+1 ≜ R inl ∪ ((𝟙 − dom(R)) ⊤ inr)
    -- the rows whose nullable column `c` holds a value, or holds the null
    filterJust(c : β ⟶ γ+1, x : ν ⟶ β) : ν ⟶ β ≜ filterBy(dom(c inl°), x)
    filterNothing(c : β ⟶ γ+1, x : ν ⟶ β) : ν ⟶ β ≜ filterBy(dom(c inr°), x)
    -- q's xprev: row `i` reads row `i − n`, null where there is none; `diff` subtracts it from row `i`
    shift(n : 1 ⟶ ν, x : ν ⟶ β) : ν ⟶ β+1 ≜ dom(x) tot(⟨𝟙, ⊤ n⟩minus x)
    diff(n : 1 ⟶ ν, x : ν ⟶ γ) : ν ⟶ γ+1 ≜ dom(x) tot(⟨x, ⟨𝟙, ⊤ n⟩minus x⟩minus)
    -- the first and last row, null on an empty frame (`head` of the ascending positions is the first)
    firstOrNothing(x : ν ⟶ β) : 1 ⟶ β+1 ≜ tot(summarize(head, x) x)
    lastOrNothing(x : ν ⟶ β) : 1 ⟶ β+1 ≜ tot(summarize(last, x) x)
    applyWhere(p : β ⟶ β, e : β ⟶ β) : β ⟶ β ≜ (p e) ∪ (𝟙 − p)
    contains(s : [α] ⟶ [α]) : [α] ⟶ [α] ≜ dom(suffix prefix s)

end Rel.Programs
