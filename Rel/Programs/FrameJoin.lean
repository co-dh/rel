import Rel.Programs.FrameGroup

/-! # The dataframe library, part 3: joins and row concatenation (`doc/dataframe-design.zh.typ` §3.2, §3.3): a join
    numbers its matching position pairs with `asc` (lexicographic `(i, j)` order) and reads both frames there. -/

namespace Rel.Programs

open Rel.Programs.prelude Rel.Programs.frame Rel.Programs.frameGroup in
rel_program frameJoin where
    -- the matching position pairs
    J(a : β ⟶ κ, b : δ ⟶ κ, x : ν ⟶ β, y : μ ⟶ δ) : ν ⟶ μ ≜ x a (y b)°
    -- `⟨π₁ x, π₂ y⟩`, not `x × y`: the product of the two tables would be built whole before the pairs select from it
    joinOn(K : ν ⟶ μ, x : ν ⟶ β, y : μ ⟶ δ) : ρ ⟶ β×δ ≜ asc(ran(⟨𝟙, K⟩)) ⟨π₁ x, π₂ y⟩
    innerJoin(a : β ⟶ κ, b : δ ⟶ κ, x : ν ⟶ β, y : μ ⟶ δ) : ρ ⟶ β×δ ≜ joinOn(J(a, b, x, y), x, y)
    -- the inner join on the constant key: `⊤ : ν ⟶ μ` would read the universe of `μ`, which an unbounded `μ` has not
    crossJoin(x : ν ⟶ β, y : μ ⟶ δ) : ρ ⟶ β×δ ≜ innerJoin(⊤ 𝟙(1), ⊤ 𝟙(1), x, y)
    semiJoin(a : β ⟶ κ, b : δ ⟶ κ, x : ν ⟶ β, y : μ ⟶ δ) : ν ⟶ β ≜ dom(x) asc(dom(J(a, b, x, y))) x
    antiJoin(a : β ⟶ κ, b : δ ⟶ κ, x : ν ⟶ β, y : μ ⟶ δ) : ν ⟶ β ≜ dom(x) asc(dom(x) − dom(J(a, b, x, y))) x
    -- every row of `x` with each match in `y`, or once with the null when it has none
    -- `x × (𝟙 ⊕ y)` as its pair: `×` with a table on the left does not hand its right operand a domain at `N`
    leftJoin(a : β ⟶ κ, b : δ ⟶ κ, x : ν ⟶ β, y : μ ⟶ δ) : ρ ⟶ β×(1+δ) ≜ asc(ran(⟨𝟙, dom(x) tot(J(a, b, x, y))⟩)) ⟨π₁ x, π₂ (𝟙 ⊕ y)⟩
    rightJoin(a : β ⟶ κ, b : δ ⟶ κ, x : ν ⟶ β, y : μ ⟶ δ) : ρ ⟶ (1+β)×δ ≜ leftJoin(b, a, y, x) ⟨π₂, π₁⟩
    -- q's aj, linear: `r` counts `y`'s rows of a key up to a time (`sums` along `τ`, in `μ`), so `m` meets the latest
    -- `u ≤ t`; `agg(m, last)` is q's tie-break; `dom(x)` before `tot`: its `𝟙 − dom(R)` has no universe at unbounded `ν`
    aj(k : β ⟶ κ, t : β ⟶ τ, h : δ ⟶ κ, u : δ ⟶ τ, x : ν ⟶ β, y : μ ⟶ δ) : ν ⟶ β×(1+δ) ≜ ⟨x, dom(x) tot(agg(m, last) y)⟩ where r ≜ ⟨π₁, sums(counts(ran(x ⟨k, t⟩), (y ⟨h, u⟩)°))⟩, m ≜ x ⟨k, t⟩ r (y ⟨h, u⟩ r)°

    -- `<>`: `y`'s positions shifted past `x`'s, written as `(dom(y) (+n))°` since `(+n)°` reads its whole universe
    append(x : ν ⟶ β, y : ν ⟶ β) : ν ⟶ β ≜ x ∪ ((dom(y) ⟨𝟙, ⊤ count(x)⟩plus)° y)
    -- the left join, then `y`'s rows with no match, null on the left
    fullOuterJoin(a : β ⟶ κ, b : δ ⟶ κ, x : ν ⟶ β, y : μ ⟶ δ) : μ ⟶ (1+β)×(1+δ) ≜ append(leftJoin(a, b, x, y) ⟨π₁ inr, π₂⟩, antiJoin(b, a, y, x) ⟨⊤ inl, inr⟩)
    union(x : ν ⟶ β, y : ν ⟶ β) : ν ⟶ β ≜ distinct(append(x, y))
    intersect(x : ν ⟶ β, y : μ ⟶ β) : ν ⟶ β ≜ distinct(semiJoin(𝟙, 𝟙, x, y))
    difference(x : ν ⟶ β, y : μ ⟶ β) : ν ⟶ β ≜ distinct(antiJoin(𝟙, 𝟙, x, y))
    symmetricDifference(x : ν ⟶ β, y : ν ⟶ β) : ν ⟶ β ≜ append(difference(x, y), difference(y, x))
    -- pivot long: each row once per value column `a`, `b`, as (id, column name, value); `melt` drops the id
    pivotLong(i : β ⟶ η, s : 1 ⟶ θ, a : β ⟶ ω, t : 1 ⟶ θ, b : β ⟶ ω, x : ν ⟶ β) : ν ⟶ η×(θ×ω) ≜ append(x ⟨i, ⟨⊤ s, a⟩⟩, x ⟨i, ⟨⊤ t, b⟩⟩)
    melt(s : 1 ⟶ θ, a : β ⟶ ω, t : 1 ⟶ θ, b : β ⟶ ω, x : ν ⟶ β) : ν ⟶ θ×ω ≜ pivotLong(𝟙, s, a, t, b, x) π₂
    -- pivot wide: one row per key `k` of `x`, in first-occurrence order, its columns `w`; over a finite object `V`
    -- every value is a column, `w = ⟨v ∈ V ↦ pivotCol(k, q, v, f, x)⟩` (doc F1)
    pivotOn(k : β ⟶ κ, w : κ ⟶ ω, x : ν ⟶ β) : ν ⟶ κ×ω ≜ firstOcc(x k) x k ⟨𝟙, w⟩
    -- the column of the value `s` of `q`: `f` of the rows with that (key, value), null at a key with none
    pivotCol(k : β ⟶ κ, q : β ⟶ θ, s : 1 ⟶ θ, f : [ν] ⟶ δ, x : ν ⟶ β) : κ ⟶ 1+δ ≜ ran(x k) tot(⟨𝟙, ⊤ s⟩ agg((x ⟨k, q⟩)°, f))
    pivotWide(k : β ⟶ κ, q : β ⟶ θ, s : 1 ⟶ θ, t : 1 ⟶ θ, f : [ν] ⟶ δ, x : ν ⟶ β) : ν ⟶ κ×((1+δ)×(1+δ)) ≜ pivotOn(k, ⟨pivotCol(k, q, s, f, x), pivotCol(k, q, t, f, x)⟩, x)
    -- get_dummies' column of the value `s` of `c`: `inr` where a row's `c` is `s` (`c s° s`, the coreflexive `c ≫ (= s)`),
    -- `inl` elsewhere; over a finite object `V`, `⟨v ∈ V ↦ dummy(c, v, x)⟩` is every column (doc F1)
    dummy(c : β ⟶ θ, s : 1 ⟶ θ, x : ν ⟶ β) : ν ⟶ 1+1 ≜ dom(x) tot(x c s°)

end Rel.Programs
