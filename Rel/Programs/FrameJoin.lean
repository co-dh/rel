import Rel.Programs.FrameGroup

/-! # The dataframe library, part 3: joins and row concatenation (`doc/dataframe-design.zh.typ` §3.2, §3.3): a join
    numbers its matching position pairs with `asc` (lexicographic `(i, j)` order) and reads both frames there. -/

namespace Rel.Programs

open Rel.Programs.prelude Rel.Programs.frame Rel.Programs.frameGroup in
rel_program frameJoin where
    -- the matching position pairs
    J(a : β ⟶ κ, b : δ ⟶ κ, x : ν ⟶ β, y : μ ⟶ δ) : ν ⟶ μ ≜ x a (y b)°
    joinOn(K : ν ⟶ μ, x : ν ⟶ β, y : μ ⟶ δ) : ρ ⟶ β×δ ≜ asc(ran(⟨𝟙, K⟩)) (x × y)
    innerJoin(a : β ⟶ κ, b : δ ⟶ κ, x : ν ⟶ β, y : μ ⟶ δ) : ρ ⟶ β×δ ≜ joinOn(J(a, b, x, y), x, y)
    -- the inner join on the constant key: `⊤ : ν ⟶ μ` would read the universe of `μ`, which an unbounded `μ` has not
    crossJoin(x : ν ⟶ β, y : μ ⟶ δ) : ρ ⟶ β×δ ≜ innerJoin(⊤ 𝟙(1), ⊤ 𝟙(1), x, y)
    semiJoin(a : β ⟶ κ, b : δ ⟶ κ, x : ν ⟶ β, y : μ ⟶ δ) : ν ⟶ β ≜ dom(x) asc(dom(J(a, b, x, y))) x
    antiJoin(a : β ⟶ κ, b : δ ⟶ κ, x : ν ⟶ β, y : μ ⟶ δ) : ν ⟶ β ≜ dom(x) asc(dom(x) − dom(J(a, b, x, y))) x
    -- every row of `x` with each match in `y`, or once with the null when it has none
    -- `x × (y ⊕ 𝟙)` as its pair: `×` with a table on the left does not hand its right operand a domain at `N`
    leftJoin(a : β ⟶ κ, b : δ ⟶ κ, x : ν ⟶ β, y : μ ⟶ δ) : ρ ⟶ β×(δ+1) ≜ asc(ran(⟨𝟙, dom(x) tot(J(a, b, x, y))⟩)) ⟨π₁ x, π₂ (y ⊕ 𝟙)⟩
    rightJoin(a : β ⟶ κ, b : δ ⟶ κ, x : ν ⟶ β, y : μ ⟶ δ) : ρ ⟶ (β+1)×δ ≜ leftJoin(b, a, y, x) ⟨π₂, π₁⟩
    -- q's aj: each row of `x` with the row of `y` of equal key `k`/`h` and the latest time `u` not after its `t`;
    -- `m` keeps the candidates `l` that no candidate exceeds in time; `dom(x)` before `tot`: its `𝟙 − dom(R)` has
    -- no universe at an unbounded `ν`
    aj(k : β ⟶ κ, t : β ⟶ τ, h : δ ⟶ κ, u : δ ⟶ τ, x : ν ⟶ β, y : μ ⟶ δ) : ν ⟶ β×(δ+1) ≜ ⟨x, dom(x) tot(m y)⟩ where m ≜ (x ⟨k, t⟩ (𝟙 × (ran(x t) ≥ ran(y u))) ⟨h, u⟩° y°) − (x ⟨k, t⟩ (𝟙 × (ran(x t) ≥ ran(y u))) ⟨h, u⟩° y° y u > u° y°)

    -- `<>`: `y`'s positions shifted past `x`'s, written as `(dom(y) (+n))°` since `(+n)°` reads its whole universe
    append(x : ν ⟶ β, y : ν ⟶ β) : ν ⟶ β ≜ x ∪ ((dom(y) ⟨𝟙, ⊤ count(x)⟩plus)° y)
    -- the left join, then `y`'s rows with no match, null on the left
    fullOuterJoin(a : β ⟶ κ, b : δ ⟶ κ, x : ν ⟶ β, y : μ ⟶ δ) : μ ⟶ (β+1)×(δ+1) ≜ append(leftJoin(a, b, x, y) ⟨π₁ inl, π₂⟩, antiJoin(b, a, y, x) ⟨⊤ inr, inl⟩)
    union(x : ν ⟶ β, y : ν ⟶ β) : ν ⟶ β ≜ distinct(append(x, y))
    intersect(x : ν ⟶ β, y : μ ⟶ β) : ν ⟶ β ≜ distinct(semiJoin(𝟙, 𝟙, x, y))
    difference(x : ν ⟶ β, y : μ ⟶ β) : ν ⟶ β ≜ distinct(antiJoin(𝟙, 𝟙, x, y))
    symmetricDifference(x : ν ⟶ β, y : ν ⟶ β) : ν ⟶ β ≜ append(difference(x, y), difference(y, x))
    -- pivot long: each row once per value column `a`, `b`, as (id, column name, value); `melt` drops the id
    pivotLong(i : β ⟶ η, s : 1 ⟶ θ, a : β ⟶ ω, t : 1 ⟶ θ, b : β ⟶ ω, x : ν ⟶ β) : ν ⟶ η×(θ×ω) ≜ append(x ⟨i, ⟨⊤ s, a⟩⟩, x ⟨i, ⟨⊤ t, b⟩⟩)
    melt(s : 1 ⟶ θ, a : β ⟶ ω, t : 1 ⟶ θ, b : β ⟶ ω, x : ν ⟶ β) : ν ⟶ θ×ω ≜ pivotLong(𝟙, s, a, t, b, x) π₂
    -- pivot wide: one row per key `k`, one column per declared value `s`, `t` of `q`: `f` of the rows with that
    -- (key, value), null where there are none (doc F1: the columns are the declared ones)
    pivotWide(k : β ⟶ κ, q : β ⟶ θ, s : 1 ⟶ θ, t : 1 ⟶ θ, f : [ν] ⟶ δ, x : ν ⟶ β) : ν ⟶ κ×((δ+1)×(δ+1)) ≜ firstOcc(x k) x k ⟨𝟙, ⟨tot(⟨𝟙, ⊤ s⟩ agg((x ⟨k, q⟩)°, f)), tot(⟨𝟙, ⊤ t⟩ agg((x ⟨k, q⟩)°, f))⟩⟩

end Rel.Programs
