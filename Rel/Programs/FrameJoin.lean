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
    crossJoin(x : ν ⟶ β, y : μ ⟶ δ) : ρ ⟶ β×δ ≜ joinOn(dom(x) ⊤ dom(y), x, y)
    semiJoin(a : β ⟶ κ, b : δ ⟶ κ, x : ν ⟶ β, y : μ ⟶ δ) : ν ⟶ β ≜ dom(x) asc(dom(J(a, b, x, y))) x
    antiJoin(a : β ⟶ κ, b : δ ⟶ κ, x : ν ⟶ β, y : μ ⟶ δ) : ν ⟶ β ≜ dom(x) asc(dom(x) − dom(J(a, b, x, y))) x
    -- every row of `x` with each match in `y`, or once with the null when it has none
    leftJoin(a : β ⟶ κ, b : δ ⟶ κ, x : ν ⟶ β, y : μ ⟶ δ) : ρ ⟶ β×(δ+1) ≜ asc(ran(⟨𝟙, dom(x) tot(J(a, b, x, y))⟩)) (x × (y ⊕ 𝟙))

    -- `<>`: `y`'s positions shifted past `x`'s, written as `(dom(y) (+n))°` since `(+n)°` reads its whole universe
    append(x : ν ⟶ β, y : ν ⟶ β) : ν ⟶ β ≜ x ∪ ((dom(y) ⟨𝟙, ⊤ count(x)⟩plus)° y)
    union(x : ν ⟶ β, y : ν ⟶ β) : ν ⟶ β ≜ distinct(append(x, y))
    intersect(x : ν ⟶ β, y : μ ⟶ β) : ν ⟶ β ≜ distinct(semiJoin(𝟙, 𝟙, x, y))
    difference(x : ν ⟶ β, y : μ ⟶ β) : ν ⟶ β ≜ distinct(antiJoin(𝟙, 𝟙, x, y))
    -- pivot long: each row once per value column `a`, `b`, as (id, column name, value); `melt` drops the id
    pivotLong(i : β ⟶ η, s : 1 ⟶ θ, a : β ⟶ ω, t : 1 ⟶ θ, b : β ⟶ ω, x : ν ⟶ β) : ν ⟶ η×(θ×ω) ≜ append(x ⟨i, ⟨⊤ s, a⟩⟩, x ⟨i, ⟨⊤ t, b⟩⟩)
    melt(s : 1 ⟶ θ, a : β ⟶ ω, t : 1 ⟶ θ, b : β ⟶ ω, x : ν ⟶ β) : ν ⟶ θ×ω ≜ pivotLong(𝟙, s, a, t, b, x) π₂

end Rel.Programs
