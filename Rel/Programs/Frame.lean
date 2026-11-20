import Rel.Programs.Prelude

/-! # The dataframe library, part 1 (`doc/dataframe-design.zh.typ` §2, §3.1): a frame is `x : ν ⟶ β`, positions to
    rows, and a verb whose result is a new frame is a position map `ι` followed by `x`. Every definition is generic
    in the position object `ν`; today it runs at a declared number object (`<` needs one), quadratic in the rows. -/

namespace Rel.Programs

open Rel.Programs.prelude in
rel_program frame where
    -- numbering: `rank(L)` counts what `L` puts before `i`; `nth(L, Q)` numbers the elements of `Q` in `L`'s order
    rank(L : α ⟶ α) : α ⟶ ν ≜ Λ(L) length
    nth(L : α ⟶ α, Q : α ⟶ α) : ν ⟶ α ≜ (Q rank(L Q))°
    -- `<` runs on a declared object only, so an order on pairs is built from its components
    lex(L : α ⟶ α, M : β ⟶ β) : α×β ⟶ α×β ≜ π₁ L π₁° ∪ ((π₁ π₁°) ∩ (π₂ M π₂°))

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
    filterBy(p : β ⟶ β, x : ν ⟶ β) : ν ⟶ β ≜ nth(>, dom(x p)) x
    -- `count − n` is negative when `n` exceeds the rows: `take` of it is empty; `takeLast` keeps what `dropLast`
    -- drops, since `i + n` or `count − n` may fall outside a declared object
    dropLast(n : 1 ⟶ ν, x : ν ⟶ β) : ν ⟶ β ≜ take(⟨count(x), n⟩minus, x)
    takeLast(n : 1 ⟶ ν, x : ν ⟶ β) : ν ⟶ β ≜ nth(>, dom(x) − dom(dropLast(n, x))) x
    -- rolling window: `j ≤ i < j + w`, written from the `j` side so no position below 0 is formed
    win(w : 1 ⟶ ν, x : ν ⟶ β) : ν ⟶ ν ≜ ≥ ∩ (dom(x) ⟨𝟙, ⊤ w⟩plus > dom(x))°
    rolling(w : 1 ⟶ ν, f : [ν] ⟶ δ, x : ν ⟶ β) : ν ⟶ δ ≜ agg(win(w, x), f)

    -- columns: `tot(R)` makes a partial column total, null where `R` has no value
    tot(R : α ⟶ β) : α ⟶ β+1 ≜ R inl ∪ ((𝟙 − dom(R)) ⊤ inr)
    -- the first and last row, null on an empty frame (`head` of the ascending positions is the first)
    firstOrNothing(x : ν ⟶ β) : 1 ⟶ β+1 ≜ tot(summarize(head, x) x)
    lastOrNothing(x : ν ⟶ β) : 1 ⟶ β+1 ≜ tot(summarize(last, x) x)
    applyWhere(p : β ⟶ β, e : β ⟶ β) : β ⟶ β ≜ (p e) ∪ (𝟙 − p)
    contains(s : [α] ⟶ [α]) : [α] ⟶ [α] ≜ dom(suffix prefix s)

end Rel.Programs
